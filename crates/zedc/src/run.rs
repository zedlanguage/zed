//! Running a program against its ports (step L1.19): `main`'s header names the ports, each
//! input is read once, whole, the wave runs, and each output is written once, at the end.
//!
//! An input `Lines` port is the family of its lines, keyed by line from 0; a `Files`
//! port is a lookup, `Path ->? String | #ioError(op:, path:, why:)`, answered by the world at each path read and
//! kept, so the wave sees one value per path. An output `Lines` port takes one whole-value
//! push, a `String` (one line) or a family of them (one line per entry, in key order); keyed
//! and multi-site pushes arrive at layer L7. The writes are buffered and committed when the
//! wave ends, each with its acknowledgment, `#ok` or `#ioError(op:, path:, why:)`; the program has no name
//! for the acknowledgment, so a failed write takes the default policy and aborts the wave.
//!
//! A [`Record`] holds every input the wave read and the content address of its program, so
//! [`Program::replay`] runs it again without reading the world, and only against that program
//! (step L1.19b).

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{OsStr, OsString};
use std::io::{Read, Write};
use std::sync::{Arc, OnceLock};

use zed_kernel::{Evaluator, Family, Lookup, Provenance, Shared, Term, Value, World};

use crate::address::ContentAddress;
use crate::ast::{self, Function, Stmt, StmtKind, TypeKind};
use crate::build::Build;
use crate::elab::Unit;
use crate::front::{Diagnostic, Quoted, Unloaded, compile};
use crate::lex::Span;
use crate::source::io_reason;
use crate::suppress::{InFile, Severity, Suppress};
use crate::work::{self, Stage};
use crate::{canon, interp, source, stage};

/// The kinds of input port `main` declares at L1.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PortKind {
    /// `Lines`, a stream read whole.
    Lines,
    /// `Files`, a lookup by path.
    Files,
    /// `CommandLine`, the arguments after `--`, keyed from 0 (step L1.19a).
    CommandLine,
    /// `String ->? String`, the environment variables, a lookup by name (step L1.19c).
    Env,
}

/// A way to run a closed term in an evaluator, in place of [`Evaluator::run`]: through
/// another form, such as ZIR lowered and raised back (step L1.33) or run by the reference
/// counting machine (step L1.34). The evaluator holds the wave's ports.
pub type Through<'a> = dyn Fn(&Term, &mut Evaluator) -> Result<Value, String> + 'a;

/// [`Evaluator::run`] itself.
pub fn direct(t: &Term, ev: &mut Evaluator) -> Result<Value, String> {
    ev.run(t).map_err(|e| e.to_string())
}

/// A program ready to run: its elaboration and `main`'s ports.
pub struct Program {
    /// The elaboration, shared with the front end's result it was made from.
    pub(crate) unit: Arc<Unit>,
    /// `main` closed over the definitions it reaches, made at the first wave.
    main: std::sync::OnceLock<Term>,
    /// The program's content address, or why it could not be taken, at the first wave or
    /// replay.
    address: std::sync::OnceLock<Result<ContentAddress, String>>,
    ports: Ports,
    /// The name of `main`'s parameter, `m` in `main(m: MainArgs)`, if written.
    param: Option<String>,
    /// The warnings, placed in the source: they do not stop the build.
    warnings: Arc<[Diagnostic]>,
}

/// `main`'s ports: what a wave reads and writes, and all an executable built by `zedc build`
/// (step L1.36a) keeps of the program besides its code.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ports {
    /// The input ports, in header order.
    pub inputs: Vec<(String, PortKind)>,
    /// The output ports, in header order.
    pub outputs: Vec<String>,
}

impl Ports {
    /// The ports as text, one per line, `lines`, `files`, `args`, `env` or `out` and the name:
    /// what an executable holds.
    pub fn to_text(&self) -> String {
        let mut text = String::new();
        for (name, kind) in &self.inputs {
            let word = match kind {
                PortKind::Lines => "lines",
                PortKind::Files => "files",
                PortKind::CommandLine => "args",
                PortKind::Env => "env",
            };
            text.push_str(&format!("{word} {name}\n"));
        }
        for name in &self.outputs {
            text.push_str(&format!("out {name}\n"));
        }
        text
    }

    /// The ports `text` holds, as [`Ports::to_text`] writes them.
    pub fn from_text(text: &str) -> Result<Ports, String> {
        let mut ports = Ports {
            inputs: Vec::new(),
            outputs: Vec::new(),
        };
        for line in text.lines() {
            let kind = match line.split_once(' ') {
                Some(("lines", name)) => Some((name, PortKind::Lines)),
                Some(("files", name)) => Some((name, PortKind::Files)),
                Some(("args", name)) => Some((name, PortKind::CommandLine)),
                Some(("env", name)) => Some((name, PortKind::Env)),
                Some(("out", name)) => {
                    ports.outputs.push(name.to_string());
                    continue;
                }
                _ => None,
            };
            let (name, kind) = kind.ok_or_else(|| format!("`{line}` is not a port"))?;
            ports.inputs.push((name.to_string(), kind));
        }
        Ok(ports)
    }

    /// Runs one wave on these ports, as [`Program::run_args`] does, with the wave run by `run`
    /// in an evaluator that holds the ports: an executable's way to run its own code. `files`
    /// gives the lookup behind each `Files` and environment input by its name. The wave's
    /// record names no program, since ports alone do not say which; the caller names it.
    pub fn run(
        &self,
        lines: &BTreeMap<String, Arc<[u8]>>,
        args: &[String],
        files: impl Fn(&str) -> Arc<dyn Lookup>,
        run: impl FnOnce(&mut Evaluator) -> Result<Value, String>,
    ) -> Result<Wave, String> {
        Ok(self.wave(lines, args, files, false, run)?.0)
    }

    /// The content address of the program that runs `term` on these ports (step L1.19b): the
    /// BLAKE3-256 hash of `zed-program\0`, the address the canonicalizer gives `term` as the
    /// definition `main` (sec:ir, "Identity"), and the ports as [`Ports::to_text`] writes
    /// them, since the term reads each input by its name and not by its kind. Two programs
    /// that differ only in local names, layout or comments have one address. O(t log t) for a
    /// term of size t, the canonicalizer's cost. An error when the system refuses the memory
    /// to write one of the term's exact numbers.
    pub fn address(&self, term: Term) -> Result<ContentAddress, String> {
        let main = canon::Def {
            name: "main".into(),
            domain: None,
            facets: Vec::new(),
            body: term,
        };
        let term = canon::address(&main, &|_| None).map_err(|e| {
            format!(
                "zedc could not compile the program: one of its constants takes {} bytes, and the \
                 system refused zedc that much memory to write the constant out and compute \
                 the program's content address. The program is not wrong. Repair: free memory \
                 and run again.",
                e.bytes()
            )
        })?;
        let ports = self.to_text();
        let mut h = blake3::Hasher::new();
        h.update(b"zed-program\0");
        h.update(&term.0);
        h.update(&(ports.len() as u64).to_le_bytes());
        h.update(ports.as_bytes());
        Ok(ContentAddress::hashed(&h))
    }

    fn wave(
        &self,
        lines: &BTreeMap<String, Arc<[u8]>>,
        args: &[String],
        files: impl Fn(&str) -> Arc<dyn Lookup>,
        trace: bool,
        run: impl FnOnce(&mut Evaluator) -> Result<Value, String>,
    ) -> Result<(Wave, Option<Provenance>), String> {
        let mut world = World::new();
        let mut record = Record::default();
        for (name, kind) in &self.inputs {
            match kind {
                PortKind::Lines => {
                    let Some(bytes) = lines.get(name) else {
                        return Err(format!(
                            "the input port `{name}` was given nothing to read: a run gives each \
                             `Lines` input its bytes by the name of its port, and no bytes were \
                             given for `{name}`."
                        ));
                    };
                    world = world.input(name, split_lines(name, bytes));
                    record.lines.insert(name.clone(), Arc::clone(bytes));
                }
                PortKind::Files | PortKind::Env => world = world.source(name, files(name)),
                PortKind::CommandLine => {
                    world = world.input(name, arguments(args));
                    record.args = args.to_vec();
                }
            }
        }
        for name in &self.outputs {
            world = world.output(name);
        }
        let mut ev = Evaluator::new(world);
        if trace {
            ev = ev.with_provenance(vec![Value::Int(0)]);
        }
        let status = exit_status(&run(&mut ev)?)?;
        let mut writes = Vec::new();
        for name in &self.outputs {
            match ev.world.log(name) {
                [] => {}
                [v] => writes.push((name.clone(), join_lines(name, v)?)),
                pushes => {
                    return Err(format!(
                        "`{name}` was pushed to {} times in this run, and it takes one push per \
                         run, which holds everything it writes. Gather \
                         the lines into one family of strings and push it once, as `{name} <- \
                         lines;`, where `lines` holds one entry per line; a push in a branch \
                         that does not run does not count.",
                        pushes.len()
                    ));
                }
            }
        }
        record.files = std::mem::take(&mut ev.world.reads);
        Ok((
            Wave {
                writes,
                record,
                status,
            },
            ev.provenance(),
        ))
    }
}

/// The exit status of a wave whose `main` gave `value` (DESIGN.md sec:ports, step L1.19): its
/// `int` result, which the checker proves is in `0..=255`, or 0 when the body exports
/// nothing.
fn exit_status(value: &Value) -> Result<u8, String> {
    match value {
        Value::Int(n) => u8::try_from(*n).map_err(|_| status_range(&n.to_string())),
        Value::Tuple(items) if items.is_empty() => Ok(0),
        v => Err(status_range(&v.to_string())),
    }
}

/// Why `main`'s result `n` is no exit status. The checker rejects a `main` whose result it
/// does not prove to be in `0..=255`, so a run meets this only through a form that skips the
/// check (a mutant's `main`, step L25.8).
fn status_range(n: &str) -> String {
    format!(
        "`main` gave {n}, and the result of `main` is the program's exit status, a number from \
         0 to 255. Give a status in that range: `code.clamp(0, 255)`, `code mod 256`, or `if \
         code in 0..=255 {{ code }} else {{ 1 }}`."
    )
}

/// The outcome of one wave: the writes, by port in header order, and the inputs it read.
pub struct Wave {
    /// Each output port pushed, and the bytes it writes.
    pub writes: Vec<(String, Vec<u8>)>,
    /// What a replay needs.
    pub record: Record,
    /// The exit status `main` gave: its `int` result, 0 when its body exports nothing.
    pub status: u8,
}

/// The inputs a wave read: each `Lines` port's bytes, each `Files` and environment port's
/// reads, and the command-line arguments when a `CommandLine` port reads them; and the content
/// address of the program that read them.
#[derive(Clone, PartialEq, Debug, Default)]
pub struct Record {
    /// The content address of the program whose wave this is ([`Program::address`]); `None`
    /// in a record written before step L1.19b, and in the wave of a mutant's `main`, which
    /// is no program's.
    pub program: Option<ContentAddress>,
    /// The bytes of each `Lines` port, shared with the input the wave was given.
    pub lines: BTreeMap<String, Arc<[u8]>>,
    /// The keys read from each `Files` port (paths) and each environment port (names), and
    /// what each read gave.
    pub files: BTreeMap<String, BTreeMap<Value, Value>>,
    /// The arguments after `--`, in order; empty when `main` has no `CommandLine` port.
    pub args: Vec<String>,
}

/// The program in `bytes`, built for the machine zedc runs on with no option on, or its errors,
/// each as `line:col: why` with its derivation and its menu of fixes ([`Unloaded::report`]).
pub fn load(bytes: &[u8]) -> Result<Program, String> {
    load_for(bytes, &Build::default())
}

/// The program in `bytes` built for `build` (step L2.8d), or its errors, as [`load`] gives them.
pub fn load_for(bytes: &[u8], build: &Build) -> Result<Program, String> {
    loaded(bytes, build).map_err(|why| why.report(None, |_| String::new()))
}

/// The program in `bytes` built for `build`, or why it was not loaded.
fn loaded(bytes: &[u8], build: &Build) -> Result<Program, Unloaded> {
    let text = work::stage(Stage::Load, None, || source::load(bytes))
        .map_err(|e| Unloaded::Refused(e.render(bytes)))?;
    let (stmts, unit, warnings) = compile(&text, build).map_err(Unloaded::Rejected)?;
    let mut program = work::stage(Stage::Program, None, || program(&stmts, unit))
        .map_err(|e| Unloaded::Rejected(refusal(&text, &stmts, e)))?;
    program.warnings = warnings.into();
    Ok(program)
}

/// The refusal `e` of [`program`] for the unit `text` whose top-level statements are `stmts`,
/// placed as a rejection: its place, its derivation and its address, which names the
/// top-level declaration it lies in.
pub(crate) fn refusal(text: &str, stmts: &[Stmt], e: ast::Error) -> Vec<Diagnostic> {
    let lines = source::Lines::new(text.as_bytes());
    crate::front::placed(text, &lines, stmts, Severity::Rejection, vec![e])
}

/// Writes each warning of `warnings`, of the unit read from `file`, which is `at`, that
/// `suppress` does not name to `out` as `file:` then the warning, then, under `--addresses`, its address on a
/// line of its own: what `zedc run` and `zedc test` print before they run the unit. Each source
/// line is shown once over the warnings printed ([`Quoted`]).
pub(crate) fn write_warnings(
    out: &mut dyn Write,
    file: &str,
    at: InFile,
    warnings: &[Diagnostic],
    suppress: &mut Suppress,
) -> std::io::Result<()> {
    let mut quoted = Quoted::default();
    for w in warnings {
        let address = at.address(w);
        if !suppress.hides(address) {
            let w = quoted.show(w);
            writeln!(out, "{file}:{w}{}", suppress.address_line(address))?;
        }
    }
    Ok(())
}

/// The program `unit` is, with the ports its one `main` reads and writes; or why it is
/// refused, at the declaration it concerns (DIAG-addr-rest): a second `main` at that
/// declaration with each `main` a step of the derivation, and no `main` at the start of the
/// unit. The caller places the error, so it prints a place and an address as every rejection
/// does. The parser has already checked `main`'s header (`main(m: MainArgs) -> int`), and
/// given `main` a parameter for each field of `MainArgs` it reads and a port for each it
/// pushes to ([`ast::MainHeader`]), so each parameter here is an input port.
pub(crate) fn program(stmts: &[Stmt], unit: Arc<Unit>) -> Result<Program, ast::Error> {
    let mains: Vec<(&Stmt, &Function)> = stmts
        .iter()
        .filter_map(|s| match &s.kind {
            StmtKind::Function(f) if f.name == "main" => Some((s, f)),
            _ => None,
        })
        .collect();
    let [(_, main)] = mains[..] else {
        let message = match mains.len() {
            0 => "This file declares no `main` to start the program at. Try adding \
                  `main(m: MainArgs) { m.stdout <- \"hello\"; }`."
                .to_string(),
            n => format!(
                "this file declares {n} functions named `main`, at the places listed below, and \
                 a program starts at exactly one. Keep the `main` the program should start at, \
                 and rename or remove each of the others."
            ),
        };
        return Err(ast::Error {
            row: None,
            menu: String::new(),
            span: mains
                .get(1)
                .map_or(Span { start: 0, end: 0 }, |(s, _)| s.span),
            message,
            notes: match mains.len() {
                0 => vec![ast::Note {
                    span: Span { start: 0, end: 0 },
                    text: "`zedc run` runs a program, which starts at the function `main`; a \
                           file of definitions to test runs with `zedc test`"
                        .into(),
                }],
                _ => mains
                    .iter()
                    .map(|(s, _)| ast::Note {
                        span: s.span,
                        text: "`main` is declared here".into(),
                    })
                    .collect(),
            },
        });
    };
    let kind = |p: &ast::Param| match p.ty.as_ref().map(|t| &t.kind) {
        Some(TypeKind::Name(n)) if n == "Lines" => PortKind::Lines,
        Some(TypeKind::Name(n)) if n == "Files" => PortKind::Files,
        Some(TypeKind::Name(n)) if n == "CommandLine" => PortKind::CommandLine,
        Some(TypeKind::Arrow { partial: true, .. }) => PortKind::Env,
        _ => unreachable!("the parser gives `main` only the parameters of `MainArgs`' inputs"),
    };
    let inputs = main
        .params
        .iter()
        .map(|p| (p.name.clone(), kind(p)))
        .collect();
    let outputs = main
        .ports()
        .into_iter()
        .flatten()
        .map(|p| p.name.clone())
        .collect();
    Ok(Program {
        unit,
        main: std::sync::OnceLock::new(),
        address: std::sync::OnceLock::new(),
        ports: Ports { inputs, outputs },
        param: main
            .main
            .as_ref()
            .and_then(|h| h.param.as_ref())
            .map(|(name, ..)| name.clone()),
        warnings: Arc::from([]),
    })
}

impl Program {
    /// The input ports, in header order.
    pub fn inputs(&self) -> &[(String, PortKind)] {
        &self.ports.inputs
    }

    /// The ports.
    pub fn ports(&self) -> &Ports {
        &self.ports
    }

    /// The term a wave runs: `main` closed over the definitions it reaches, applied to a read
    /// of each input port, under the prelude. What `zedc build` compiles (step L1.36a).
    pub fn term(&self) -> Term {
        let main = self
            .main
            .get_or_init(|| self.unit.get("main").expect("`main` was elaborated"));
        self.term_of(main.clone())
    }

    /// The program's content address (step L1.19b), [`Ports::address`] of [`Program::term`].
    /// Taken once, at the first wave or replay.
    pub fn address(&self) -> Result<ContentAddress, String> {
        self.address
            .get_or_init(|| self.ports.address(self.term()))
            .clone()
    }

    /// `main` applied to a read of each input port, under the prelude.
    fn term_of(&self, main: Term) -> Term {
        let args = self
            .ports
            .inputs
            .iter()
            .map(|(name, _)| Term::Read(name.as_str().into()))
            .collect();
        interp::prelude(Term::App(Shared::new(main), args))
    }

    /// The warnings, placed in the source, in order of place.
    pub fn warnings(&self) -> &[Diagnostic] {
        &self.warnings
    }

    /// The elaboration.
    pub fn unit(&self) -> &Unit {
        &self.unit
    }

    /// This program with its demanded build-stage terms evaluated where their form shows they
    /// end (step L1.28), and what the build did.
    pub fn stage(&self) -> (Program, stage::Report) {
        let (unit, report) = stage::mix(&self.unit, &["main"]);
        let program = Program {
            unit: Arc::new(unit),
            main: std::sync::OnceLock::new(),
            address: std::sync::OnceLock::new(),
            ports: self.ports.clone(),
            param: self.param.clone(),
            warnings: Arc::clone(&self.warnings),
        };
        (program, report)
    }

    /// The name of `main`'s parameter, `m` in `main(m: MainArgs)`, if written.
    pub fn param(&self) -> Option<&str> {
        self.param.as_deref()
    }

    /// The output ports, in header order.
    pub fn outputs(&self) -> &[String] {
        &self.ports.outputs
    }

    /// Runs one wave with no command-line arguments: `lines` gives the bytes of each `Lines`
    /// input, and `files` the lookup behind each `Files` input. An error stops the wave before
    /// anything is written.
    pub fn run(
        &self,
        lines: &BTreeMap<String, Arc<[u8]>>,
        files: impl Fn(&str) -> Arc<dyn Lookup>,
    ) -> Result<Wave, String> {
        self.run_args(lines, &[], files)
    }

    /// Runs one wave as [`Program::run`] does, with `args` the arguments after `--` that each
    /// `CommandLine` input holds.
    pub fn run_args(
        &self,
        lines: &BTreeMap<String, Arc<[u8]>>,
        args: &[String],
        files: impl Fn(&str) -> Arc<dyn Lookup>,
    ) -> Result<Wave, String> {
        Ok(self.wave(lines, args, files, false, &direct, None)?.0)
    }

    /// Runs one wave as [`Program::run_args`] does, with the wave's term run by `map`: the
    /// test runner's way to run a program through another form.
    pub fn run_through(
        &self,
        lines: &BTreeMap<String, Arc<[u8]>>,
        args: &[String],
        files: impl Fn(&str) -> Arc<dyn Lookup>,
        map: &Through<'_>,
    ) -> Result<Wave, String> {
        Ok(self.wave(lines, args, files, false, map, None)?.0)
    }

    /// Runs one wave as [`Program::run_through`] does, with `main` in place of the program's
    /// `main` closed over its unit: `main` closed over a changed unit (step L25.8, a mutant).
    pub fn run_main_through(
        &self,
        main: &Term,
        lines: &BTreeMap<String, Arc<[u8]>>,
        args: &[String],
        files: impl Fn(&str) -> Arc<dyn Lookup>,
        map: &Through<'_>,
    ) -> Result<Wave, String> {
        Ok(self.wave(lines, args, files, false, map, Some(main))?.0)
    }

    /// Runs one wave as [`Program::run`] does, and records its provenance (step L1.20): the
    /// fact address of every value, the wave stamp 0 first in each keypath.
    pub fn provenance(
        &self,
        lines: &BTreeMap<String, Arc<[u8]>>,
        files: impl Fn(&str) -> Arc<dyn Lookup>,
    ) -> Result<(Wave, Provenance), String> {
        let (wave, prov) = self.wave(lines, &[], files, true, &direct, None)?;
        Ok((wave, prov.expect("provenance was recorded")))
    }

    fn wave(
        &self,
        lines: &BTreeMap<String, Arc<[u8]>>,
        args: &[String],
        files: impl Fn(&str) -> Arc<dyn Lookup>,
        trace: bool,
        map: &Through<'_>,
        main: Option<&Term>,
    ) -> Result<(Wave, Option<Provenance>), String> {
        let (term, program) = match main {
            Some(main) => (self.term_of(main.clone()), None),
            None => (self.term(), Some(self.address()?)),
        };
        let mut out = self
            .ports
            .wave(lines, args, files, trace, |ev| map(&term, ev))?;
        out.0.record.program = program;
        Ok(out)
    }

    /// Checks that `record` is a record of this program: it names a content address, and the
    /// address is this program's.
    pub fn check_record(&self, record: &Record) -> Result<(), String> {
        let ours = self.address()?;
        match record.program {
            Some(a) if a == ours => Ok(()),
            Some(_) => Err(
                "this record was written by a run of a different program: `main` \
                 or a definition it uses, or a port of `main`, has changed since. A replay \
                 must run the program that wrote the record. Replay it with the source as it \
                 was when the record was written, or run this program again with `--record \
                 <out>` to make a record of it."
                    .to_string(),
            ),
            None => Err(
                "this record does not name the program that wrote it, so it \
                 cannot be checked against this one; it was written by an older zedc. Run the \
                 program again with `--record <out>` to make a record that names it."
                    .to_string(),
            ),
        }
    }

    /// Runs the wave `record` holds, reading nothing from the world, once
    /// [`Program::check_record`] finds it a record of this program.
    pub fn replay(&self, record: &Record) -> Result<Wave, String> {
        self.check_record(record)?;
        // A run records the input of every `Lines` port of the program, so a record of this
        // program that lacks one has been changed since it was written.
        for (name, kind) in &self.ports.inputs {
            if *kind == PortKind::Lines && !record.lines.contains_key(name) {
                return Err(format!(
                    "the record holds no input for the port `{name}`, which the program \
                     reads, so the replay cannot go on: a replay reads nothing from outside, \
                     only what the record holds. Every run records the input of each port it \
                     reads, so the record has been changed since it was written. Replay with \
                     the record as it was written, or make a new record with `zedc run <file> \
                     --record <out>`."
                ));
            }
        }
        self.run_args(&record.lines, &record.args, |name| {
            Arc::new(Recorded(
                record.files.get(name).cloned().unwrap_or_default(),
            ))
        })
    }
}

/// Commits `writes` in order through `sink`, giving each write's acknowledgment, `#ok` or
/// `#ioError(op: "write", path:, why:)` from the path and reason `sink` fails with. The first
/// failure aborts the wave, as the default policy does, so no later port is written.
pub fn commit(
    writes: &[(String, Vec<u8>)],
    mut sink: impl FnMut(&str, &[u8]) -> Result<(), (String, String)>,
) -> Vec<(String, Value)> {
    let mut acks = Vec::new();
    for (port, bytes) in writes {
        match sink(port, bytes) {
            Ok(()) => acks.push((port.clone(), Value::atom("ok"))),
            Err((path, why)) => {
                acks.push((port.clone(), Value::io_error("write", &path, &why)));
                break;
            }
        }
    }
    acks
}

/// The lines of `bytes`, the input of `Lines` port `port`, keyed from 0. A line ends at `\n`,
/// every `\r` right before its end is dropped, and a last line needs no `\n`; a `\r` inside a
/// line is kept. Each line costs O(its length). A line that is not UTF-8 is
/// `#ioError(op: "read", path: port, why:)`, its path the port's name, since standard input
/// has no path.
pub fn split_lines(port: &str, bytes: &[u8]) -> Value {
    let mut parts: Vec<&[u8]> = bytes.split(|b| *b == b'\n').collect();
    if parts.last().is_some_and(|l| l.is_empty()) {
        parts.pop();
    }
    let lines = parts.into_iter().enumerate().map(|(i, line)| {
        let mut line = line;
        while let [rest @ .., b'\r'] = line {
            line = rest;
        }
        let v = match std::str::from_utf8(line) {
            Ok(s) => Value::str(s),
            Err(_) => Value::io_error("read", port, &not_utf8(i)),
        };
        (Value::Int(i as i64), v)
    });
    Value::Family(Family::of(lines))
}

/// The value of a `CommandLine` input: the family of `args`, keyed from 0.
pub fn arguments(args: &[String]) -> Value {
    let args = args
        .iter()
        .enumerate()
        .map(|(i, a)| (Value::Int(i as i64), Value::str(a)));
    Value::Family(Family::of(args))
}

/// The bytes a push of `v` writes to `Lines` port `port`: each string, then `\n`.
pub fn join_lines(port: &str, v: &Value) -> Result<Vec<u8>, String> {
    let lines: Vec<Value> = match v {
        // An empty level holds no line, so it writes nothing, as before empty levels were
        // kept (DESIGN.md says only that a family of strings writes one line per entry).
        Value::Family(f) => f
            .leaves()
            .into_iter()
            .map(|(_, v)| v)
            .filter(|v| !matches!(v, Value::Family(f) if f.is_empty()))
            .collect(),
        v => vec![v.clone()],
    };
    let mut out = Vec::new();
    for line in lines {
        let Value::Str(s) = line else {
            return Err(format!(
                "port `{port}` writes lines of text, and the program pushed {line} to it, which is \
                     not a string: a `Lines` port takes a `Utf8String`, written as one line, or a \
                     family of strings, written one line per entry in key order. Repair: push the \
                     value's text in its place, made with `Utf8String(…)`"
            ));
        };
        s.chunks().for_each(|c| out.extend_from_slice(c.as_bytes()));
        out.push(b'\n');
    }
    Ok(out)
}

/// A `Files` port over the file system: each path is read when the program reads it.
#[derive(Debug)]
pub struct Disk;

impl Lookup for Disk {
    fn get(&self, key: &Value) -> Result<Value, String> {
        let Value::Str(path) = key else {
            return Err(format!(
                "a `Files` port reads a file by its path, which is a string, and the program \
                 read it with {key}, which is not one. Write the path as a string, such as \
                 `\"data.txt\"`, or convert the value with `String(…)`."
            ));
        };
        let path = path.flat();
        Ok(match std::fs::read(&*path) {
            Ok(bytes) => match String::from_utf8(bytes) {
                Ok(s) => Value::str(&s),
                Err(_) => Value::io_error("read", &path, "the file is not UTF-8"),
            },
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Value::atom("notFound"),
            Err(e) => Value::io_error("read", &path, &e.to_string()),
        })
    }
}

/// An environment input port over a process's variables (step L1.19c), taken once before the
/// wave, so the wave sees one value per name: the value, or `#notFound` for a name that is not
/// set. A value that is not UTF-8 stops the wave as a usage error naming the variable, kept in
/// [`Environment::not_utf8`]; it is found at the read, so a variable the program does not read
/// stops nothing. Taking the variables costs O(n log n) for n variables, and a read O(log n).
#[derive(Debug)]
pub struct Environment {
    vars: BTreeMap<OsString, OsString>,
    not_utf8: OnceLock<String>,
}

impl Environment {
    /// The port over the variables `vars`, as [`std::env::vars_os`] gives them.
    pub fn new(vars: impl IntoIterator<Item = (OsString, OsString)>) -> Environment {
        Environment {
            vars: vars.into_iter().collect(),
            not_utf8: OnceLock::new(),
        }
    }

    /// The usage error of the first read of a variable whose value is not UTF-8, if any.
    pub fn not_utf8(&self) -> Option<&str> {
        self.not_utf8.get().map(String::as_str)
    }
}

impl Lookup for Environment {
    fn get(&self, key: &Value) -> Result<Value, String> {
        let Value::Str(name) = key else {
            return Err(format!(
                "an environment port reads a variable by its name, which is a string, and the \
                 program read it with {key}, which is not one. Write the name as a string, \
                 such as `\"HOME\"`."
            ));
        };
        let name = name.flat();
        match self.vars.get(OsStr::new(&*name)) {
            None => Ok(Value::atom("notFound")),
            Some(v) => match v.to_str() {
                Some(v) => Ok(Value::str(v)),
                None => {
                    let why = format!(
                        "the program reads the environment variable `{name}`, and its value is \
                         not UTF-8 text, which a Zed string must be. Set `{name}` to UTF-8 text \
                         before running, or unset it, which the program reads as `#notFound`."
                    );
                    // A second such read cannot happen: the first stops the wave.
                    let _ = self.not_utf8.set(why.clone());
                    Err(why)
                }
            },
        }
    }
}

/// The lookup behind each `Files` and environment input of `ports` in a run on this machine,
/// by the port's name: the file system, or `env` for an environment port.
fn local(ports: &Ports, env: &Arc<Environment>) -> impl Fn(&str) -> Arc<dyn Lookup> {
    let envs: BTreeSet<String> = ports
        .inputs
        .iter()
        .filter(|(_, k)| *k == PortKind::Env)
        .map(|(n, _)| n.clone())
        .collect();
    let env = Arc::clone(env);
    move |name| match envs.contains(name) {
        true => Arc::clone(&env) as Arc<dyn Lookup>,
        false => Arc::new(Disk),
    }
}

/// The exit status and message of a wave that stopped with `why`: a usage error, 2, when it
/// stopped at a variable of `env` that is not UTF-8, and otherwise 1.
fn stopped(env: &Environment, why: String) -> (u8, String) {
    match env.not_utf8() {
        Some(usage) => (2, usage.to_string()),
        None => (1, why),
    }
}

/// Why line `n` of a `Lines` input is `#ioError`. The port runtime (`zed_rt::ports`) gives
/// the same text.
fn not_utf8(key: usize) -> String {
    format!("the line at key {key} is not UTF-8")
}

/// A `Files` port answered from a [`Record`].
#[derive(Debug)]
struct Recorded(BTreeMap<Value, Value>);

impl Lookup for Recorded {
    fn get(&self, key: &Value) -> Result<Value, String> {
        self.0.get(key).cloned().ok_or_else(|| {
            format!(
                "the program reads {key} here, and the record holds no read of it, so the \
                     replay cannot go on: a replay reads nothing from outside, only what the \
                     record holds. The run that wrote the record did not read {key}, so its \
                     inputs differed from these, or the record has been changed. Replay with \
                     the inputs of the recorded run, or make a new record with `zedc run \
                     <file> --record <out>`."
            )
        })
    }
}

const MAGIC: &str = "zed record 1\n";

impl Record {
    /// The record as bytes. After a first line `zed record 1`, each entry is a line of words,
    /// its kind and the lengths of its fields, then the fields' bytes and a `\n`:
    /// `lines P B` (port, bytes), `text P K B` (port, path, contents), and `missing P K` and
    /// `error P K O W` (port, path, operation, reason) for a read that gave `#notFound` or
    /// `#ioError(op: O, path: K, why: W)`, and `arg A` for each command-line argument, in
    /// order. An `error P K` entry, as a record written before the payload has it, reads back
    /// as a bare `#ioError`. The first entry, `program A`, is the program's content address
    /// in 64 hexadecimal digits; a record written before step L1.19b has none.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = MAGIC.as_bytes().to_vec();
        let mut entry = |kind: &str, fields: &[&[u8]]| {
            let lens: Vec<String> = fields.iter().map(|f| f.len().to_string()).collect();
            out.extend_from_slice(format!("{kind} {}\n", lens.join(" ")).as_bytes());
            for f in fields {
                out.extend_from_slice(f);
            }
            out.push(b'\n');
        };
        if let Some(a) = self.program {
            entry("program", &[a.to_string().as_bytes()]);
        }
        for (port, bytes) in &self.lines {
            entry("lines", &[port.as_bytes(), bytes]);
        }
        for (port, reads) in &self.files {
            for (path, v) in reads {
                let Value::Str(path) = path else {
                    unreachable!("a read path is a String")
                };
                let path = path.flat();
                let (p, k) = (port.as_bytes(), path.as_bytes());
                match v {
                    Value::Str(s) => entry("text", &[p, k, s.flat().as_bytes()]),
                    Value::Atom(a) if a.name.as_ref() == "notFound" => entry("missing", &[p, k]),
                    Value::Atom(a) if a.name.as_ref() == "ioError" => {
                        let field = |f: &str| match a.fields.binary_search_by(|x| (**x).cmp(f)) {
                            Ok(i) => match &a.args[i] {
                                Value::Str(s) => Some(s.flat()),
                                _ => None,
                            },
                            Err(_) => None,
                        };
                        match (field("op"), field("why")) {
                            (Some(o), Some(w)) => {
                                entry("error", &[p, k, o.as_bytes(), w.as_bytes()])
                            }
                            _ => entry("error", &[p, k]),
                        }
                    }
                    v => unreachable!("a file read gives a String or an atom, not {v}"),
                }
            }
        }
        for a in &self.args {
            entry("arg", &[a.as_bytes()]);
        }
        out
    }

    /// The record `bytes` holds, or why they are not one: where the first entry that cannot be
    /// read starts. O(length of `bytes`).
    pub fn from_bytes(bytes: &[u8]) -> Result<Record, String> {
        let Some(mut rest) = bytes.strip_prefix(MAGIC.as_bytes()) else {
            return Err(
                "this file is not a record that `zedc run --record` writes: such a \
                 record starts with the line `zed record 1`, and this file does not. Name the \
                 file `--record` wrote, or make a record with `zedc run <file> --record <out>`."
                    .to_string(),
            );
        };
        let mut record = Record::default();
        let mut first = true;
        while !rest.is_empty() {
            let at = bytes.len() - rest.len();
            if Record::entry(&mut rest, &mut record, first).is_none() {
                return Err(format!(
                    "this record, which `zedc run --record` writes, cannot be read from byte \
                     {at} on: the entry that starts there is cut short or has been changed. \
                     A record is read only as it was written; make it again with `zedc run \
                     <file> --record <out>`."
                ));
            }
            first = false;
        }
        Ok(record)
    }

    /// Reads the entry at the start of `rest` into `record`, and moves `rest` past it; `first`
    /// when it is the first entry, the only place a `program` entry may be. `None` when the
    /// bytes are not an entry.
    fn entry(rest: &mut &[u8], record: &mut Record, first: bool) -> Option<()> {
        let end = rest.iter().position(|b| *b == b'\n')?;
        let head = std::str::from_utf8(&rest[..end]).ok()?;
        *rest = &rest[end + 1..];
        let mut words = head.split(' ');
        let kind = words.next()?;
        let mut fields = Vec::new();
        for w in words {
            let n: usize = w.parse().ok()?;
            fields.push(rest.get(..n)?);
            *rest = &rest[n..];
        }
        *rest = rest.strip_prefix(b"\n")?;
        let text = |f: &[u8]| String::from_utf8(f.to_vec()).ok();
        match (kind, &fields[..]) {
            // One `program` entry, before every other.
            ("program", [a]) if first => {
                let a = std::str::from_utf8(a).ok().and_then(ContentAddress::parse);
                record.program = Some(a?);
            }
            ("lines", [p, b]) => {
                record.lines.insert(text(p)?, Arc::from(*b));
            }
            ("text" | "missing" | "error", [p, k, more @ ..]) => {
                let v = match (kind, more) {
                    ("text", [b]) => Value::str(&text(b)?),
                    ("missing", []) => Value::atom("notFound"),
                    ("error", []) => Value::atom("ioError"),
                    ("error", [o, w]) => Value::io_error(&text(o)?, &text(k)?, &text(w)?),
                    _ => return None,
                };
                let reads = record.files.entry(text(p)?).or_default();
                reads.insert(Value::str(&text(k)?), v);
            }
            ("arg", [a]) => record.args.push(text(a)?),
            _ => return None,
        }
        Some(())
    }
}

/// `zedc run <file> [--record <out>] [--option <name> …] [-- arg …]` and
/// `zedc replay <file> <record> [--option <name> …] [-- arg …]`, with `args` the words after
/// `zedc`. `m.stdin` reads standard input, `m.args` holds the words after `--`, which a
/// replay ignores for the recorded ones, `m.env` holds this process's variables, and
/// `m.stdout` and `m.stderr` write standard output and standard error. Returns the exit
/// status: `main`'s result, 0 when its body exports nothing, 1 when the program fails or a
/// write fails, 2 for a usage error, among them a word that is not UTF-8 or a read of an
/// environment variable whose value is not.
pub fn command(
    args: &[impl AsRef<std::ffi::OsStr>],
    stdin: &mut dyn Read,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> u8 {
    command_in(args, std::env::vars_os(), stdin, stdout, stderr)
}

/// [`command`] with `vars` the variables an environment input holds.
pub fn command_in(
    args: &[impl AsRef<std::ffi::OsStr>],
    vars: impl IntoIterator<Item = (OsString, OsString)>,
    stdin: &mut dyn Read,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> u8 {
    let env = Arc::new(Environment::new(vars));
    let words = match words(args) {
        Ok(words) => words,
        Err(why) => {
            let _ = writeln!(stderr, "{why}");
            return 2;
        }
    };
    match command_inner(&words, &env, stdin, stdout, stderr) {
        Ok(status) => status,
        Err((status, why)) => {
            let _ = writeln!(stderr, "{why}");
            status
        }
    }
}

/// The words of a command line: those before the first `--`, and the arguments after it.
struct Words<'a> {
    command: Vec<&'a str>,
    args: Vec<String>,
}

/// The words `args` of a command line as text, or why one is not UTF-8: a word before `--`
/// is named by its place among the words after `zedc`, an argument after it by its key
/// from 0, the key `m.args` gives it.
fn words(args: &[impl AsRef<std::ffi::OsStr>]) -> Result<Words<'_>, String> {
    let args: Vec<&std::ffi::OsStr> = args.iter().map(AsRef::as_ref).collect();
    let split = args.iter().position(|w| *w == "--");
    let (before, after) = match split {
        Some(i) => (&args[..i], &args[i + 1..]),
        None => (&args[..], &[][..]),
    };
    let command = before
        .iter()
        .copied()
        .enumerate()
        .map(|(i, w)| {
            w.to_str().ok_or_else(|| {
                format!(
                    "word {} of the command line is not UTF-8, and the words before `--` \
                         (the program's file and options) are read as UTF-8 text. Name each file by \
                         a path written in UTF-8, or rename the file.",
                    i + 1
                )
            })
        })
        .collect::<Result<_, _>>()?;
    let args = after
        .iter()
        .enumerate()
        .map(|(i, w)| {
            w.to_str().map(str::to_string).ok_or_else(|| {
                format!(
                    "the command-line argument at key {i} of `m.args` (the first word after \
                         `--` is key 0) is not UTF-8, and `m.args` gives the program each \
                         argument as a string, which must be UTF-8 text. Pass the argument as \
                         UTF-8 text, or pass the path of a file that holds it.",
                )
            })
        })
        .collect::<Result<_, _>>()?;
    Ok(Words { command, args })
}

fn command_inner(
    words: &Words<'_>,
    env: &Arc<Environment>,
    stdin: &mut dyn Read,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> Result<u8, (u8, String)> {
    let usage = |why: String| {
        (
            2,
            format!(
                "{why}\n\nThe forms are:\n  \
                 zedc run <file> [--record <out>] [--suppress <address> …] \
                 [--addresses] [--option <name> …] [-- arg …]\n  \
                 zedc replay <file> <record> [--suppress <address> …] \
                 [--addresses] [--option <name> …] [-- arg …]"
            ),
        )
    };
    let (replay, file, rest) = match &words.command[..] {
        [cmd, file, rest @ ..] if *cmd == "run" => (None, file, rest),
        [cmd, file, record, rest @ ..] if *cmd == "replay" => (Some(record), file, rest),
        [cmd, ..] if *cmd == "replay" => {
            return Err(usage(
                "`zedc replay` needs the file of the program and then the record of an earlier \
                 run of it (written by `zedc run <file> --record <out>`) after it."
                    .into(),
            ));
        }
        _ => {
            return Err(usage(
                "`zedc run` needs the file of the program to run after it.".into(),
            ));
        }
    };
    let (mut suppress, rest) = Suppress::take(rest).map_err(|why| (2, why))?;
    let (on, rest) = crate::build::take(&rest).map_err(|why| (2, why))?;
    let options = Options::parse(&rest, replay.is_none()).map_err(usage)?;
    let program = load_file(file, &on, &mut suppress, stderr)?;
    let wave = match replay {
        Some(path) => {
            let bytes = std::fs::read(path).map_err(|e| (2, unreadable(path, &e)))?;
            let record = Record::from_bytes(&bytes).map_err(|e| (2, format!("{path}: {e}")))?;
            // A record of another program, or of none, is a usage error, as a damaged one is.
            program
                .check_record(&record)
                .map_err(|e| (2, format!("{path}: {e}")))?;
            work::stage(Stage::Run, Some("main"), || program.replay(&record))
        }
        None => {
            let lines = options.read_lines(program.ports(), stdin)?;
            let files = local(program.ports(), env);
            work::stage(Stage::Run, Some("main"), || {
                program.run_args(&lines, &words.args, files)
            })
        }
    }
    .map_err(|e| stopped(env, e))?;
    options.finish(&wave, stdout, stderr)
}

/// The program in `file`, built for the machine zedc runs on with the options `on` turned on
/// ([`Build::at`]), its warnings that `suppress` does not name written to `stderr` as `zedc run`
/// writes them, then a line for each address `suppress` names that no warning has; or the exit
/// status and message: 2 when the file cannot be read or resolved to the place its addresses
/// name ([`crate::place::Place`]) or an option of `on` is not one its manifest declares, 1 when
/// the program is rejected (by its package, by the front end or by `program`), each rejection
/// as `file:line:col: why` and its derivation, followed, under `--addresses`, by its address,
/// and then a line for each rejection `suppress` names, since a rejection cannot be suppressed.
pub fn load_file(
    file: &str,
    on: &[&str],
    suppress: &mut Suppress,
    stderr: &mut dyn Write,
) -> Result<Program, (u8, String)> {
    work::unit(file);
    let bytes = std::fs::read(file).map_err(|e| (2, unreadable(file, &e)))?;
    let path = std::path::Path::new(file);
    let place = crate::place::Place::of(path).map_err(|e| (2, e))?;
    let at = InFile::at(&place);
    // An option the manifest does not list, or a manifest that cannot be read, is a usage
    // error, reported before the package is read; a manifest that does not parse is reported
    // with the package, before the build it declares is needed.
    let build = match Build::at(&place, on) {
        Err((2, why)) => return Err((2, why)),
        build => build,
    };
    let host = Build::default();
    // A unit under a manifest that imports a unit, or sees a prelude unit, is read with its
    // package (step L2.3); linking it to the units it imports is step L2.4.
    if let Ok(text) = std::str::from_utf8(&bytes)
        && let Some(report) = crate::unit::package_report(
            path,
            place,
            text,
            build.as_ref().unwrap_or(&host),
            suppress,
        )
        .map_err(|e| (1, e))?
        && !report.is_empty()
    {
        return Err((1, report.join("\n")));
    }
    let build = build?;
    let program = match loaded(&bytes, &build) {
        Ok(program) => program,
        Err(why) => {
            let mut text = why.report(Some(file), |d| suppress.address_line(at.address(d)));
            if let Unloaded::Rejected(ds) = &why {
                for line in suppress.refused(file, at, ds) {
                    text.push('\n');
                    text.push_str(&line);
                }
            }
            return Err((1, text));
        }
    };
    let written = write_warnings(stderr, file, at, program.warnings(), suppress).and_then(|()| {
        suppress
            .unmatched()
            .iter()
            .try_for_each(|line| writeln!(stderr, "{file}: {line}"))
    });
    written.map_err(|e| {
        (
            2,
            format!(
                "zedc could not write its warnings to standard error: {}.",
                io_reason(&e)
            ),
        )
    })?;
    Ok(program)
}

/// The words of a command line after the program: the file `--record` names.
struct Options<'a> {
    record_to: Option<&'a str>,
}

/// Why zedc could not read the file at `path`, which the command line names, with the repair.
pub(crate) fn unreadable(path: &str, e: &std::io::Error) -> String {
    format!(
        "{path}: zedc could not read this file: {}. Check the path and that you may read the file.",
        io_reason(e)
    )
}

/// The field of `main`'s argument the port `port` is: `stdin` for `m.stdin`.
fn field(port: &str) -> &str {
    port.rsplit_once('.').map_or(port, |(_, f)| f)
}

/// Why zedc could not write what the output port `port` holds to the process's own stream,
/// standard output for `m.stdout` and standard error for `m.stderr`, the reason being `why`.
fn write_failed(port: &str, why: &str) -> String {
    let stream = if field(port) == "stdout" {
        "output"
    } else {
        "error"
    };
    format!(
        "the program wrote to `{port}`, and zedc could not write it to the standard {stream} \
         of this process: {why}. Send the standard {stream} to a place that accepts it, such as \
         a file, with `> out.txt` for standard output or `2> err.txt` for standard error."
    )
}

impl<'a> Options<'a> {
    /// The options `rest` holds, `--record <out>` among them only when `record`; or why a word
    /// is neither.
    fn parse(mut rest: &[&'a str], record: bool) -> Result<Options<'a>, String> {
        let mut options = Options { record_to: None };
        while let [word, more @ ..] = rest {
            rest = more;
            if *word == "--record" && record {
                let [out, more @ ..] = rest else {
                    return Err(
                        "`--record` is the last word before the program's arguments, \
                         and it needs the file to write the record to after it: write \
                         `--record <out>`."
                            .into(),
                    );
                };
                options.record_to = Some(out);
                rest = more;
            } else if *word == "--record" {
                return Err(
                    "`--record` is not an option of `zedc replay`, which writes no \
                     record: a replay reads only the record it is given. Remove `--record`."
                        .into(),
                );
            } else if let Some((port, path)) = word.split_once('=') {
                return Err(format!(
                    "`{word}` names the file `{path}` for a port `{port}`, and a program's ports \
                     are not named on the command line: `main(m: MainArgs)` reads standard \
                     input from `m.stdin` and writes `m.stdout` and `m.stderr` to standard \
                     output and standard error, and a program opens a file by its path with \
                     `files()`. To read a file as standard input, write `< {path}`; to write \
                     standard output to a file, write `> {path}`; to give the path to the \
                     program, put it after `--`, where `m.args` reads it."
                ));
            } else {
                return Err(format!(
                    "`{word}` is not understood here: before `--` comes only `--record <out>`, \
                     which writes a record of the run; after `--` come the program's own \
                     arguments. If `{word}` is meant for the program, put it after `--`."
                ));
            }
        }
        Ok(options)
    }

    /// The bytes of each `Lines` input of `ports`, `m.stdin`, read from `stdin`.
    fn read_lines(&self, ports: &Ports, stdin: &mut dyn Read) -> Result<LineInputs, (u8, String)> {
        let mut lines = BTreeMap::new();
        for (name, kind) in &ports.inputs {
            if *kind != PortKind::Lines {
                continue;
            }
            let bytes = read_shared(stdin, 0).map_err(|e| {
                let why = io_reason(&e);
                let why = format!(
                    "zedc could not read standard input, which `{name}` reads: {why}. Give zedc \
                     a standard input it may read, such as a file, with `< in.txt`."
                );
                (2, why)
            })?;
            lines.insert(name.clone(), bytes);
        }
        Ok(lines)
    }

    /// Writes the record, when `--record` names a file, and commits the wave's writes: `m.stdout`
    /// to `stdout` and `m.stderr` to `stderr`. Gives the wave's exit status, or 1 and why
    /// when a write fails.
    fn finish(
        &self,
        wave: &Wave,
        stdout: &mut dyn Write,
        stderr: &mut dyn Write,
    ) -> Result<u8, (u8, String)> {
        if let Some(out) = self.record_to {
            std::fs::write(out, wave.record.to_bytes()).map_err(|e| {
                let why = io_reason(&e);
                let why = format!(
                    "{out}: zedc could not write the record of this run to this file: {why}. \
                     Name a file in a directory you may write to."
                );
                (1, why)
            })?;
        }
        let mut failed = None;
        commit(&wave.writes, |port, bytes| {
            let (stream, written) = match field(port) {
                "stdout" => ("stdout", stdout.write_all(bytes)),
                _ => ("stderr", stderr.write_all(bytes)),
            };
            written.map_err(|e| {
                let why = io_reason(&e);
                failed = Some(write_failed(port, &why));
                (stream.to_string(), why)
            })
        });
        failed.map_or(Ok(wave.status), |why| Err((1, why)))
    }
}

/// The command line of an executable `zedc build` makes (step L1.36a), `name
/// [--record <out>] [-- arg …]`, with `args` the words after `name`: the ports are read and
/// written as `zedc run` reads and writes them, and the wave is run by `run`, the
/// executable's own code, in an evaluator that holds the ports. The record `--record` writes
/// names `address`, the content address of the program the executable was built from
/// ([`Program::address`]), so `zedc replay` runs it against that program's source. Returns
/// the exit status, as [`command`] does.
#[expect(
    clippy::too_many_arguments,
    reason = "the executable's name, ports, address, command line, three streams and code are \
              each a separate input of the run, and the executable's start passes each once"
)]
pub fn executable(
    name: &str,
    ports: &Ports,
    address: ContentAddress,
    args: &[impl AsRef<std::ffi::OsStr>],
    stdin: &mut dyn Read,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
    run: impl FnOnce(&mut Evaluator) -> Result<Value, String>,
) -> u8 {
    let outcome = words(args).map_err(|why| (2, why)).and_then(|words| {
        let options = Options::parse(&words.command, true).map_err(|why| {
            (
                2,
                format!("{why}\n\nusage: {name} [--record <out>] [-- arg …]"),
            )
        })?;
        let lines = options.read_lines(ports, stdin)?;
        let env = Arc::new(Environment::new(std::env::vars_os()));
        let mut wave = ports
            .run(&lines, &words.args, local(ports, &env), run)
            .map_err(|e| stopped(&env, e))?;
        wave.record.program = Some(address);
        options.finish(&wave, stdout, stderr)
    });
    match outcome {
        Ok(status) => status,
        Err((status, why)) => {
            let _ = writeln!(stderr, "{why}");
            status
        }
    }
}

/// The bytes of each `Lines` input, by port name, as a wave is given them.
type LineInputs = BTreeMap<String, Arc<[u8]>>;

/// The bytes `source` gives until its end, as one shared block. `size` is the length expected
/// (a file's length, or 0 when it is not known): a block of that size is allocated and read
/// into, so a source of that length is read with no copy. A source that ends sooner (a file
/// that shrank) is copied into a block of its length; one that gives more (a file that grew, a
/// pipe, standard input) has the rest read into a buffer and joined to the block in a new one,
/// one copy, as reading into a `Vec` and converting it would make.
fn read_shared(source: &mut dyn Read, size: usize) -> std::io::Result<Arc<[u8]>> {
    // Collected from an iterator of known length, so the block is allocated once at its size.
    let mut block: Arc<[u8]> = std::iter::repeat_n(0, size).collect();
    let into = Arc::get_mut(&mut block).expect("a block just made has one owner");
    let mut filled = 0;
    while filled < size {
        match source.read(&mut into[filled..]) {
            Ok(0) => return Ok(Arc::from(&into[..filled])),
            Ok(k) => filled += k,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    let mut rest = Vec::new();
    source.read_to_end(&mut rest)?;
    if rest.is_empty() {
        return Ok(block);
    }
    Ok(block.iter().chain(&rest).copied().collect())
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::{program, read_shared};
    use crate::query::Db;

    /// A source that gives at most `step` bytes per read and is interrupted before each.
    struct Slow<'a> {
        bytes: &'a [u8],
        step: usize,
        interrupt: bool,
    }

    impl std::io::Read for Slow<'_> {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            self.interrupt = !self.interrupt;
            if self.interrupt {
                return Err(std::io::ErrorKind::Interrupted.into());
            }
            let k = buf.len().min(self.step).min(self.bytes.len());
            buf[..k].copy_from_slice(&self.bytes[..k]);
            self.bytes = &self.bytes[k..];
            Ok(k)
        }
    }

    #[test]
    fn a_source_is_read_whole_whatever_length_was_expected() {
        let bytes: Vec<u8> = (0..1000_u32).map(|i| (i % 251) as u8).collect();
        // Expected exactly, shorter (a file that grew, standard input with 0), longer (a file
        // that shrank), and empty; each read in pieces of 7 bytes with interruptions between.
        for size in [1000, 999, 600, 0, 1001, 4000] {
            let mut source = Slow {
                bytes: &bytes,
                step: 7,
                interrupt: false,
            };
            let read = read_shared(&mut source, size).unwrap();
            assert_eq!(&read[..], &bytes[..], "expected length {size}");
        }
        let mut empty = Slow {
            bytes: &[],
            step: 7,
            interrupt: false,
        };
        assert!(read_shared(&mut empty, 0).unwrap().is_empty());
        assert!(read_shared(&mut &b""[..], 5).unwrap().is_empty());
    }

    #[test]
    fn a_failed_read_is_reported() {
        struct Fails;
        impl std::io::Read for Fails {
            fn read(&mut self, _: &mut [u8]) -> std::io::Result<usize> {
                Err(std::io::Error::other("the device is gone"))
            }
        }
        for size in [0, 10] {
            let e = read_shared(&mut Fails, size).unwrap_err();
            assert_eq!(e.to_string(), "the device is gone");
        }
    }

    #[test]
    fn a_program_shares_the_unit_of_the_front_end_it_was_made_from() {
        let front = Db::new().front("main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n");
        let Ok((stmts, unit, _)) = &*front else {
            panic!("the unit is accepted")
        };
        let p = program(stmts, Arc::clone(unit)).expect("one `main`");
        assert!(Arc::ptr_eq(&p.unit, unit));
        // A refused program, one with no `main`, leaves the front end's unit for the tables, which still read it.
        let front = Db::new().front("f(positional x: int) = x;\n");
        let Ok((stmts, unit, _)) = &*front else {
            panic!("the unit is accepted")
        };
        assert!(program(stmts, Arc::clone(unit)).is_err());
        assert_eq!(Arc::strong_count(unit), 1);
        assert!(unit.defs.iter().any(|d| d.name == "f"));
    }
}

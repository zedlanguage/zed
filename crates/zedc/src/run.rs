//! Running a program against its ports (step L1.19): `main`'s header names the ports, each
//! input is read once, whole, the wave runs, and each output is written once, at the end.
//!
//! An input `Lines` port is the family of its lines, keyed by line number from 1; a `Files`
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

use std::collections::BTreeMap;
use std::io::{Read, Write};
use std::sync::Arc;

use zed_kernel::{Evaluator, Family, Lookup, Provenance, Shared, Term, Value, World};

use crate::address::ContentAddress;
use crate::ast::{self, Function, Stmt, StmtKind, TypeKind};
use crate::elab::Unit;
use crate::front::{Diagnostic, compile};
use crate::lex::Span;
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
    /// `CommandLine`, the arguments after `--`, keyed by position from 1 (step L1.19a).
    CommandLine,
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
    pub(crate) unit: Unit,
    /// `main` closed over the definitions it reaches, made at the first wave.
    main: std::sync::OnceLock<Term>,
    /// The program's content address, or why it could not be taken, at the first wave or
    /// replay.
    address: std::sync::OnceLock<Result<ContentAddress, String>>,
    ports: Ports,
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
    /// The ports as text, one per line, `lines`, `files`, `args` or `out` and the name: what
    /// an executable holds.
    pub fn to_text(&self) -> String {
        let mut text = String::new();
        for (name, kind) in &self.inputs {
            let word = match kind {
                PortKind::Lines => "lines",
                PortKind::Files => "files",
                PortKind::CommandLine => "args",
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
    /// in an evaluator that holds the ports: an executable's way to run its own code. The
    /// wave's record names no program, since ports alone do not say which; the caller names it.
    pub fn run(
        &self,
        lines: &BTreeMap<String, Vec<u8>>,
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
                "a constant is so large that the system refused the {} bytes of memory asked \
                 to take the program's content address",
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
        lines: &BTreeMap<String, Vec<u8>>,
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
                        return Err(format!("no input for port `{name}`"));
                    };
                    world = world.input(name, split_lines(name, bytes));
                    record.lines.insert(name.clone(), bytes.clone());
                }
                PortKind::Files => world = world.source(name, files(name)),
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
        run(&mut ev)?;
        let mut writes = Vec::new();
        for name in &self.outputs {
            match ev.world.log(name) {
                [] => {}
                [v] => writes.push((name.clone(), join_lines(name, v)?)),
                pushes => {
                    return Err(format!(
                        "port `{name}` is pushed {} times in one wave; several pushes to one \
                         port arrive at layer L7",
                        pushes.len()
                    ));
                }
            }
        }
        record.files = std::mem::take(&mut ev.world.reads);
        Ok((Wave { writes, record }, ev.provenance()))
    }
}

/// The outcome of one wave: the writes, by port in header order, and the inputs it read.
pub struct Wave {
    /// Each output port pushed, and the bytes it writes.
    pub writes: Vec<(String, Vec<u8>)>,
    /// What a replay needs.
    pub record: Record,
}

/// The inputs a wave read: each `Lines` port's bytes, each `Files` port's reads, and the
/// command-line arguments when a `CommandLine` port reads them; and the content address of the
/// program that read them.
#[derive(Clone, PartialEq, Debug, Default)]
pub struct Record {
    /// The content address of the program whose wave this is ([`Program::address`]); `None`
    /// in a record written before step L1.19b, and in the wave of a mutant's `main`, which
    /// is no program's.
    pub program: Option<ContentAddress>,
    /// The bytes of each `Lines` port.
    pub lines: BTreeMap<String, Vec<u8>>,
    /// The paths read from each `Files` port and what each read gave.
    pub files: BTreeMap<String, BTreeMap<Value, Value>>,
    /// The arguments after `--`, in order; empty when `main` has no `CommandLine` port.
    pub args: Vec<String>,
}

/// The program in `bytes`, or its errors, one per line as `line:col: why`.
pub fn load(bytes: &[u8]) -> Result<Program, String> {
    loaded(bytes).map_err(|why| match why {
        Unloaded::Rejected(ds) => {
            let lines: Vec<String> = ds.iter().map(Diagnostic::to_string).collect();
            lines.join("\n")
        }
        Unloaded::Refused(why) => why,
    })
}

/// Why a program was not loaded.
enum Unloaded {
    /// The diagnostics of the phase that rejected it, or the refusal of [`program`]: it is not
    /// a program's unit.
    Rejected(Vec<Diagnostic>),
    /// Why it was refused where no diagnostic is placed: its bytes are not a source.
    Refused(String),
}

/// The program in `bytes`, or why it was not loaded.
fn loaded(bytes: &[u8]) -> Result<Program, Unloaded> {
    let text = work::stage(Stage::Load, None, || source::load(bytes))
        .map_err(|e| Unloaded::Refused(e.render(bytes)))?;
    let (stmts, unit, warnings) = compile(&text).map_err(Unloaded::Rejected)?;
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
/// `suppress` does not name to `out` as `file:` then the warning, then its address on a line of
/// its own: what `zedc run` and `zedc test` print before they run the unit.
pub(crate) fn write_warnings(
    out: &mut dyn Write,
    file: &str,
    at: InFile,
    warnings: &[Diagnostic],
    suppress: &mut Suppress,
) -> std::io::Result<()> {
    for w in warnings {
        let address = at.address(w);
        if !suppress.hides(address) {
            writeln!(out, "{file}:{w}\n  address: {address}")?;
        }
    }
    Ok(())
}

/// The program `unit` is, with the ports its one `main` declares; or why it is refused, at the
/// declaration it concerns (DIAG-addr-rest): a port of `main` at the port, a second `main` at
/// that declaration with each `main` a step of the derivation, and no `main` at the start of
/// the unit. The caller places the error, so it prints a place and an address as every
/// rejection does.
pub(crate) fn program(stmts: &[Stmt], unit: Unit) -> Result<Program, ast::Error> {
    let mains: Vec<(&Stmt, &Function)> = stmts
        .iter()
        .filter_map(|s| match &s.kind {
            StmtKind::Function(f) if f.name == "main" => Some((s, f)),
            _ => None,
        })
        .collect();
    let [(_, main)] = mains[..] else {
        let message = format!(
            "a program declares one `main` function; this one declares {}",
            mains.len()
        );
        return Err(ast::Error {
            row: None,
            span: mains
                .get(1)
                .map_or(Span { start: 0, end: 0 }, |(s, _)| s.span),
            message,
            notes: mains
                .iter()
                .map(|(s, _)| ast::Note {
                    span: s.span,
                    text: "`main` is declared here".into(),
                })
                .collect(),
        });
    };
    let refused = |span: Span, message: String| ast::Error {
        row: None,
        span,
        message,
        notes: Vec::new(),
    };
    let kind = |p: &ast::Param| match p.ty.as_ref().map(|t| &t.kind) {
        Some(TypeKind::Name(n)) if n == "Lines" => Ok(PortKind::Lines),
        Some(TypeKind::Name(n)) if n == "Files" => Ok(PortKind::Files),
        Some(TypeKind::Name(n)) if n == "CommandLine" => Ok(PortKind::CommandLine),
        _ => Err(refused(
            p.span,
            format!(
                "port `{}` of `main` is `Lines`, `Files` or `CommandLine` at layer L1",
                p.name
            ),
        )),
    };
    let inputs = main
        .params
        .iter()
        .map(|p| Ok((p.name.clone(), kind(p)?)))
        .collect::<Result<_, ast::Error>>()?;
    let mut outputs = Vec::new();
    for p in main.ports.iter().flatten() {
        if !matches!(&p.ty.kind, TypeKind::Name(n) if n == "Lines") {
            return Err(refused(
                p.span,
                format!("output port `{}` of `main` is `Lines` at layer L1", p.name),
            ));
        }
        outputs.push(p.name.clone());
    }
    Ok(Program {
        unit,
        main: std::sync::OnceLock::new(),
        address: std::sync::OnceLock::new(),
        ports: Ports { inputs, outputs },
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
            unit,
            main: std::sync::OnceLock::new(),
            address: std::sync::OnceLock::new(),
            ports: self.ports.clone(),
            warnings: Arc::clone(&self.warnings),
        };
        (program, report)
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
        lines: &BTreeMap<String, Vec<u8>>,
        files: impl Fn(&str) -> Arc<dyn Lookup>,
    ) -> Result<Wave, String> {
        self.run_args(lines, &[], files)
    }

    /// Runs one wave as [`Program::run`] does, with `args` the arguments after `--` that each
    /// `CommandLine` input holds.
    pub fn run_args(
        &self,
        lines: &BTreeMap<String, Vec<u8>>,
        args: &[String],
        files: impl Fn(&str) -> Arc<dyn Lookup>,
    ) -> Result<Wave, String> {
        Ok(self.wave(lines, args, files, false, &direct, None)?.0)
    }

    /// Runs one wave as [`Program::run_args`] does, with the wave's term run by `map`: the
    /// test runner's way to run a program through another form.
    pub fn run_through(
        &self,
        lines: &BTreeMap<String, Vec<u8>>,
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
        lines: &BTreeMap<String, Vec<u8>>,
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
        lines: &BTreeMap<String, Vec<u8>>,
        files: impl Fn(&str) -> Arc<dyn Lookup>,
    ) -> Result<(Wave, Provenance), String> {
        let (wave, prov) = self.wave(lines, &[], files, true, &direct, None)?;
        Ok((wave, prov.expect("provenance was recorded")))
    }

    fn wave(
        &self,
        lines: &BTreeMap<String, Vec<u8>>,
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
            Some(a) => Err(format!(
                "the record is of the program with content address {a}, not of this program, \
                 {ours}"
            )),
            None => Err(
                "the record names no program, as records written before programs were \
                 named in them do; run the program again with `--record`"
                    .to_string(),
            ),
        }
    }

    /// Runs the wave `record` holds, reading nothing from the world, once
    /// [`Program::check_record`] finds it a record of this program.
    pub fn replay(&self, record: &Record) -> Result<Wave, String> {
        self.check_record(record)?;
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

/// The lines of `bytes`, the input of `Lines` port `port`, keyed from 1. A line ends at `\n`,
/// a `\r` before it is dropped, and a last line needs no `\n`; a line that is not UTF-8 is
/// `#ioError(op: "read", path: port, why:)`, its path the port's name, since standard input
/// has no path.
pub fn split_lines(port: &str, bytes: &[u8]) -> Value {
    let mut parts: Vec<&[u8]> = bytes.split(|b| *b == b'\n').collect();
    if parts.last().is_some_and(|l| l.is_empty()) {
        parts.pop();
    }
    let lines = parts.into_iter().enumerate().map(|(i, line)| {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        let v = match std::str::from_utf8(line) {
            Ok(s) => Value::str(s),
            Err(_) => Value::io_error("read", port, &not_utf8(i + 1)),
        };
        (Value::Int(i as i64 + 1), v)
    });
    Value::Family(Family::of(lines))
}

/// The value of a `CommandLine` input: the family of `args`, keyed by position from 1.
pub fn arguments(args: &[String]) -> Value {
    let args = args
        .iter()
        .enumerate()
        .map(|(i, a)| (Value::Int(i as i64 + 1), Value::str(a)));
    Value::Family(Family::of(args))
}

/// The bytes a push of `v` writes to `Lines` port `port`: each string, then `\n`.
pub fn join_lines(port: &str, v: &Value) -> Result<Vec<u8>, String> {
    let lines: Vec<Value> = match v {
        Value::Family(f) => f.leaves().into_iter().map(|(_, v)| v).collect(),
        v => vec![v.clone()],
    };
    let mut out = Vec::new();
    for line in lines {
        let Value::Str(s) = line else {
            return Err(format!("port `{port}` takes strings; {line} was pushed"));
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
            return Err(format!("a path is a String, not {key}"));
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

/// Why line `n` of a `Lines` input is `#ioError`. The port runtime (`zed_rt::ports`) gives
/// the same text.
fn not_utf8(n: usize) -> String {
    format!("line {n} is not UTF-8")
}

/// A `Files` port answered from a [`Record`].
#[derive(Debug)]
struct Recorded(BTreeMap<Value, Value>);

impl Lookup for Recorded {
    fn get(&self, key: &Value) -> Result<Value, String> {
        self.0
            .get(key)
            .cloned()
            .ok_or_else(|| format!("the record holds no read of {key}"))
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

    /// The record `bytes` holds, or why they are not one.
    pub fn from_bytes(bytes: &[u8]) -> Result<Record, String> {
        let bad = || "not a Zed record".to_string();
        let mut rest = bytes.strip_prefix(MAGIC.as_bytes()).ok_or_else(bad)?;
        let mut record = Record::default();
        let mut first = true;
        while !rest.is_empty() {
            let end = rest.iter().position(|b| *b == b'\n').ok_or_else(bad)?;
            let head = std::str::from_utf8(&rest[..end]).map_err(|_| bad())?;
            rest = &rest[end + 1..];
            let mut words = head.split(' ');
            let kind = words.next().ok_or_else(bad)?;
            let mut fields = Vec::new();
            for w in words {
                let n: usize = w.parse().map_err(|_| bad())?;
                let field = rest.get(..n).ok_or_else(bad)?;
                fields.push(field);
                rest = &rest[n..];
            }
            rest = rest.strip_prefix(b"\n").ok_or_else(bad)?;
            let text = |f: &[u8]| String::from_utf8(f.to_vec()).map_err(|_| bad());
            match (kind, &fields[..]) {
                // One `program` entry, before every other.
                ("program", [a]) if first => {
                    let a = std::str::from_utf8(a).ok().and_then(ContentAddress::parse);
                    record.program = Some(a.ok_or_else(bad)?);
                }
                ("lines", [p, b]) => {
                    record.lines.insert(text(p)?, b.to_vec());
                }
                ("text" | "missing" | "error", [p, k, more @ ..]) => {
                    let v = match (kind, more) {
                        ("text", [b]) => Value::str(&text(b)?),
                        ("missing", []) => Value::atom("notFound"),
                        ("error", []) => Value::atom("ioError"),
                        ("error", [o, w]) => Value::io_error(&text(o)?, &text(k)?, &text(w)?),
                        _ => return Err(bad()),
                    };
                    let reads = record.files.entry(text(p)?).or_default();
                    reads.insert(Value::str(&text(k)?), v);
                }
                ("arg", [a]) => record.args.push(text(a)?),
                _ => return Err(bad()),
            }
            first = false;
        }
        Ok(record)
    }
}

/// `zedc run <file> [port=path …] [--record <out>] [-- arg …]` and
/// `zedc replay <file> <record> [port=path …] [-- arg …]`, with `args` the words after
/// `zedc`. A `Lines` input reads the file bound to it, or standard input if it is `stdin`; a
/// `CommandLine` input holds the words after `--`, which a replay ignores for the recorded
/// ones; a `Lines` output writes the file bound to it, or standard output or error if it is
/// `stdout` or `stderr`. Returns the exit status: 0, 1 when the program fails or a write
/// fails, 2 for a usage error, among them a word that is not UTF-8.
pub fn command(
    args: &[impl AsRef<std::ffi::OsStr>],
    stdin: &mut dyn Read,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> u8 {
    let words = match words(args) {
        Ok(words) => words,
        Err(why) => {
            let _ = writeln!(stderr, "{why}");
            return 2;
        }
    };
    match command_inner(&words, stdin, stdout, stderr) {
        Ok(()) => 0,
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
/// is named by its place among the words after `zedc`, an argument after it by its position
/// from 1, the key a `CommandLine` port gives it.
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
            w.to_str()
                .ok_or_else(|| format!("word {} of the command line is not UTF-8", i + 1))
        })
        .collect::<Result<_, _>>()?;
    let args = after
        .iter()
        .enumerate()
        .map(|(i, w)| {
            w.to_str()
                .map(str::to_string)
                .ok_or_else(|| format!("command-line argument {} is not UTF-8", i + 1))
        })
        .collect::<Result<_, _>>()?;
    Ok(Words { command, args })
}

fn command_inner(
    words: &Words<'_>,
    stdin: &mut dyn Read,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> Result<(), (u8, String)> {
    let usage = || {
        (
            2,
            "usage: zedc run <file> [port=path …] [--record <out>] [--suppress <address> …] \
             [-- arg …]\n       \
             zedc replay <file> <record> [port=path …] [--suppress <address> …] [-- arg …]"
                .to_string(),
        )
    };
    let (replay, file, rest) = match &words.command[..] {
        [cmd, file, rest @ ..] if *cmd == "run" => (None, file, rest),
        [cmd, file, record, rest @ ..] if *cmd == "replay" => (Some(record), file, rest),
        _ => return Err(usage()),
    };
    let (mut suppress, rest) = Suppress::take(rest).map_err(|why| (2, why))?;
    let options = Options::parse(&rest, replay.is_none()).ok_or_else(usage)?;
    let program = load_file(file, &mut suppress, stderr)?;
    options.check(program.ports())?;
    let wave = match replay {
        Some(path) => {
            let bytes = std::fs::read(path).map_err(|e| (2, format!("{path}: {e}")))?;
            let record = Record::from_bytes(&bytes).map_err(|e| (2, format!("{path}: {e}")))?;
            // A record of another program, or of none, is a usage error, as a damaged one is.
            program
                .check_record(&record)
                .map_err(|e| (2, format!("{path}: {e}")))?;
            work::stage(Stage::Run, Some("main"), || program.replay(&record))
        }
        None => {
            let lines = options.read_lines(program.ports(), stdin)?;
            work::stage(Stage::Run, Some("main"), || {
                program.run_args(&lines, &words.args, |_| Arc::new(Disk))
            })
        }
    }
    .map_err(|e| (1, e))?;
    options.finish(&wave, stdout, stderr)
}

/// The program in `file`, its warnings that `suppress` does not name written to `stderr` as
/// `zedc run` writes them, then a line for each address `suppress` names that no warning has;
/// or the exit status and message: 2 when the file cannot be read or resolved to the place its
/// addresses name ([`crate::unit::Place`]), 1 when the program is rejected (by its package, by
/// the front end or by `program`), each rejection as `file:line:col: why` and its derivation,
/// followed by its address, and then a line for each rejection `suppress` names, since a
/// rejection cannot be suppressed.
pub fn load_file(
    file: &str,
    suppress: &mut Suppress,
    stderr: &mut dyn Write,
) -> Result<Program, (u8, String)> {
    work::unit(file);
    let bytes = std::fs::read(file).map_err(|e| (2, format!("{file}: {e}")))?;
    let path = std::path::Path::new(file);
    let place = crate::unit::Place::of(path).map_err(|e| (2, e))?;
    let at = InFile::at(&place);
    // A unit under a manifest that imports a unit, or sees a prelude unit, is read with its
    // package (step L2.3); linking it to the units it imports is step L2.4.
    if let Ok(text) = std::str::from_utf8(&bytes)
        && let Some(report) =
            crate::unit::package_report(path, place, text, suppress).map_err(|e| (1, e))?
        && !report.is_empty()
    {
        return Err((1, report.join("\n")));
    }
    let program = match loaded(&bytes) {
        Ok(program) => program,
        Err(Unloaded::Refused(why)) => return Err((1, format!("{file}:{why}"))),
        Err(Unloaded::Rejected(ds)) => {
            let mut lines: Vec<String> = ds
                .iter()
                .map(|d| format!("{file}:{d}\n  address: {}", at.address(d)))
                .collect();
            lines.extend(suppress.refused(file, at, &ds));
            return Err((1, lines.join("\n")));
        }
    };
    let written = write_warnings(stderr, file, at, program.warnings(), suppress).and_then(|()| {
        suppress
            .unmatched()
            .iter()
            .try_for_each(|line| writeln!(stderr, "{file}: {line}"))
    });
    written.map_err(|e| (2, format!("standard error: {e}")))?;
    Ok(program)
}

/// The words of a command line after the program: each port bound to a path, and the file
/// `--record` names.
struct Options<'a> {
    binds: BTreeMap<String, String>,
    record_to: Option<&'a str>,
}

impl<'a> Options<'a> {
    /// The options `rest` holds, `--record <out>` among them only when `record`; `None` when a
    /// word is neither.
    fn parse(mut rest: &[&'a str], record: bool) -> Option<Options<'a>> {
        let mut options = Options {
            binds: BTreeMap::new(),
            record_to: None,
        };
        while let [word, more @ ..] = rest {
            rest = more;
            if *word == "--record" && record {
                let [out, more @ ..] = rest else {
                    return None;
                };
                options.record_to = Some(out);
                rest = more;
            } else if let Some((port, path)) = word.split_once('=') {
                options.binds.insert(port.to_string(), path.to_string());
            } else {
                return None;
            }
        }
        Some(options)
    }

    /// Checks the bindings against `ports`: each names a port, binds no input that reads no
    /// file, and leaves no output but `stdout` and `stderr` without a file.
    fn check(&self, ports: &Ports) -> Result<(), (u8, String)> {
        let binds = &self.binds;
        let known =
            |p: &String| ports.inputs.iter().any(|(n, _)| n == p) || ports.outputs.contains(p);
        if let Some(p) = binds.keys().find(|p| !known(p)) {
            return Err((2, format!("`main` has no port `{p}`")));
        }
        // A `Files` or `CommandLine` input reads no file, so a binding of one would be ignored.
        if let Some((p, _)) = ports
            .inputs
            .iter()
            .find(|(n, k)| *k != PortKind::Lines && binds.contains_key(n))
        {
            return Err((
                2,
                format!("input port `{p}` reads no file: remove `{p}={}`", binds[p]),
            ));
        }
        for name in &ports.outputs {
            if !binds.contains_key(name) && name != "stdout" && name != "stderr" {
                return Err((
                    2,
                    format!("output port `{name}` needs a file: `{name}=path`"),
                ));
            }
        }
        Ok(())
    }

    /// The bytes of each `Lines` input of `ports`: the file bound to it, or `stdin` for the
    /// port `stdin`.
    fn read_lines(
        &self,
        ports: &Ports,
        stdin: &mut dyn Read,
    ) -> Result<BTreeMap<String, Vec<u8>>, (u8, String)> {
        let mut lines = BTreeMap::new();
        for (name, kind) in &ports.inputs {
            if *kind != PortKind::Lines {
                continue;
            }
            let mut bytes = Vec::new();
            match self.binds.get(name) {
                Some(path) => {
                    bytes = std::fs::read(path).map_err(|e| (2, format!("{path}: {e}")))?
                }
                None if name == "stdin" => {
                    stdin
                        .read_to_end(&mut bytes)
                        .map_err(|e| (2, format!("standard input: {e}")))?;
                }
                None => {
                    return Err((
                        2,
                        format!("input port `{name}` needs a file: `{name}=path`"),
                    ));
                }
            }
            lines.insert(name.clone(), bytes);
        }
        Ok(lines)
    }

    /// Writes the record, when `--record` names a file, and commits the wave's writes.
    fn finish(
        &self,
        wave: &Wave,
        stdout: &mut dyn Write,
        stderr: &mut dyn Write,
    ) -> Result<(), (u8, String)> {
        if let Some(out) = self.record_to {
            std::fs::write(out, wave.record.to_bytes()).map_err(|e| (1, format!("{out}: {e}")))?;
        }
        let acks = commit(&wave.writes, |port, bytes| match self.binds.get(port) {
            Some(path) => std::fs::write(path, bytes).map_err(|e| (path.clone(), e.to_string())),
            None if port == "stdout" => stdout
                .write_all(bytes)
                .map_err(|e| ("stdout".into(), e.to_string())),
            None => stderr
                .write_all(bytes)
                .map_err(|e| ("stderr".into(), e.to_string())),
        });
        for (port, ack) in acks {
            if let Value::Atom(a) = &ack
                && a.name.as_ref() == "ioError"
            {
                return Err((1, format!("writing port `{port}` failed: {ack}")));
            }
        }
        Ok(())
    }
}

/// The command line of an executable `zedc build` makes (step L1.36a), `name [port=path …]
/// [--record <out>] [-- arg …]`, with `args` the words after `name`: the ports are bound and
/// written as `zedc run` binds and writes them, and the wave is run by `run`, the
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
        let options = Options::parse(&words.command, true).ok_or_else(|| {
            (
                2,
                format!("usage: {name} [port=path …] [--record <out>] [-- arg …]"),
            )
        })?;
        options.check(ports)?;
        let lines = options.read_lines(ports, stdin)?;
        let mut wave = ports
            .run(&lines, &words.args, |_| Arc::new(Disk), run)
            .map_err(|e| (1, e))?;
        wave.record.program = Some(address);
        options.finish(&wave, stdout, stderr)
    });
    match outcome {
        Ok(()) => 0,
        Err((status, why)) => {
            let _ = writeln!(stderr, "{why}");
            status
        }
    }
}

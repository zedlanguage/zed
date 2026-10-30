//! Running a program against its ports (step L1.19): `main`'s header names the ports, each
//! input is read once, whole, the wave runs, and each output is written once, at the end.
//!
//! An input `Lines` port is the family of its lines, keyed by line number from 1; a `Files`
//! port is a lookup, `Path ->? String | #ioError`, answered by the world at each path read and
//! kept, so the wave sees one value per path. An output `Lines` port takes one whole-value
//! push, a `String` (one line) or a family of them (one line per entry, in key order); keyed
//! and multi-site pushes arrive at layer L7. The writes are buffered and committed when the
//! wave ends, each with its acknowledgment, `#ok` or `#ioError(why)`; the program has no name
//! for the acknowledgment, so a failed write takes the default policy and aborts the wave.
//!
//! A [`Record`] holds every input the wave read, so [`Program::replay`] runs it again without
//! reading the world.

use std::collections::BTreeMap;
use std::io::{Read, Write};
use std::sync::Arc;

use zed_kernel::{Evaluator, Family, Lookup, Provenance, Term, Value, World};

use crate::ast::{self, Function, Stmt, StmtKind, TypeKind};
use crate::elab::{Unit, elaborate};
use crate::parse::{TOP, parse};
use crate::{interp, lex, resolve, source, stage};

/// The kinds of input port `main` declares at L1.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PortKind {
    /// `Lines`, a stream read whole.
    Lines,
    /// `Files`, a lookup by path.
    Files,
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
    inputs: Vec<(String, PortKind)>,
    outputs: Vec<String>,
}

/// The outcome of one wave: the writes, by port in header order, and the inputs it read.
pub struct Wave {
    /// Each output port pushed, and the bytes it writes.
    pub writes: Vec<(String, Vec<u8>)>,
    /// What a replay needs.
    pub record: Record,
}

/// The inputs a wave read: each `Lines` port's bytes and each `Files` port's reads.
#[derive(Clone, PartialEq, Debug, Default)]
pub struct Record {
    /// The bytes of each `Lines` port.
    pub lines: BTreeMap<String, Vec<u8>>,
    /// The paths read from each `Files` port and what each read gave.
    pub files: BTreeMap<String, BTreeMap<Value, Value>>,
}

/// The program in `bytes`, or its errors, one per line as `line:col: why`.
pub fn load(bytes: &[u8]) -> Result<Program, String> {
    let text = source::load(bytes).map_err(|e| e.to_string())?;
    let (stmts, unit) = compile(&text).map_err(|ds| {
        let lines: Vec<String> = ds.iter().map(Diagnostic::to_string).collect();
        lines.join("\n")
    })?;
    program(&stmts, unit)
}

/// A message of the compiler, at a line and column of the source, both counted from 1, with
/// its derivation (DESIGN.md "Diagnostics").
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Diagnostic {
    /// The line.
    pub line: usize,
    /// The column.
    pub col: usize,
    /// Why.
    pub message: String,
    /// Each constraint and step that led to it, in the order the compiler met them.
    pub steps: Vec<Step>,
}

/// One step of a derivation, placed in the source.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Step {
    /// The line.
    pub line: usize,
    /// The column.
    pub col: usize,
    /// What holds there.
    pub text: String,
    /// The source line.
    pub source: String,
    /// How many characters of the source line the step covers, at least 1.
    pub width: usize,
}

impl std::fmt::Display for Diagnostic {
    /// The message on one line; then each step numbered, with its source line and the text
    /// it covers underlined, a source line shown once for consecutive steps on one place.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.col, self.message)?;
        let gutter = self
            .steps
            .iter()
            .map(|s| s.line.to_string().len())
            .max()
            .unwrap_or(0);
        let number = self.steps.len().to_string().len();
        let pad = " ".repeat(number + 4);
        let mut last = None;
        for (i, s) in self.steps.iter().enumerate() {
            let n = format!("[{}]", i + 1);
            write!(
                f,
                "\n  {n:<w$} {}:{}: {}",
                s.line,
                s.col,
                s.text,
                w = number + 2
            )?;
            if last == Some((s.line, s.col, s.width)) {
                continue;
            }
            last = Some((s.line, s.col, s.width));
            write!(f, "\n{pad} {:>gutter$} | {}", s.line, s.source)?;
            write!(
                f,
                "\n{pad} {:>gutter$} | {}{}",
                "",
                " ".repeat(s.col - 1),
                "^".repeat(s.width)
            )?;
        }
        Ok(())
    }
}

/// The statements and elaboration of the unit `text`, or the diagnostics of the first phase
/// that rejects it.
pub(crate) fn compile(text: &str) -> Result<(Vec<Stmt>, Unit), Vec<Diagnostic>> {
    let at = |start: usize, message: String| {
        let (line, col) = source::line_col(text.as_bytes(), start);
        Diagnostic {
            line,
            col,
            message,
            steps: Vec::new(),
        }
    };
    let all = |errors: Vec<ast::Error>| {
        errors
            .into_iter()
            .map(|e| Diagnostic {
                steps: e.notes.iter().map(|n| step(text, n)).collect(),
                ..at(e.span.start, e.message)
            })
            .collect::<Vec<_>>()
    };
    let tokens = lex::lex(text).map_err(|e| vec![at(e.span.start, e.to_string())])?;
    let tree =
        parse(text, &tokens, "Unit", TOP).map_err(|e| vec![at(e.span.start, e.to_string())])?;
    let stmts = ast::unit(text, &tokens, &tree).map_err(|e| all(vec![e]))?;
    let res = resolve::resolve(&stmts).map_err(all)?;
    let unit = elaborate(&stmts, &res).map_err(all)?;
    Ok((stmts, unit))
}

/// The step a note is in `text`: its line and column, the source line, and the characters of
/// the note's span on that line.
fn step(text: &str, n: &ast::Note) -> Step {
    let (line, col) = source::line_col(text.as_bytes(), n.span.start);
    let begin = text[..n.span.start]
        .rfind(['\n', '\r'])
        .map_or(0, |i| i + 1);
    let end = text[n.span.start..]
        .find(['\n', '\r'])
        .map_or(text.len(), |i| n.span.start + i);
    let width = text[n.span.start..n.span.end.clamp(n.span.start, end)]
        .chars()
        .count();
    Step {
        line,
        col,
        text: n.text.clone(),
        source: text[begin..end].to_string(),
        width: width.max(1),
    }
}

/// The program `unit` is, with the ports its one `main` declares.
pub(crate) fn program(stmts: &[Stmt], unit: Unit) -> Result<Program, String> {
    let mains: Vec<&Function> = stmts
        .iter()
        .filter_map(|s| match &s.kind {
            StmtKind::Function(f) if f.name == "main" => Some(f),
            _ => None,
        })
        .collect();
    let [main] = mains[..] else {
        return Err(format!(
            "a program declares one `main` function; this one declares {}",
            mains.len()
        ));
    };
    let kind = |name: &str, ty: Option<&ast::Type>| match ty.map(|t| &t.kind) {
        Some(TypeKind::Name(n)) if n == "Lines" => Ok(PortKind::Lines),
        Some(TypeKind::Name(n)) if n == "Files" => Ok(PortKind::Files),
        _ => Err(format!(
            "port `{name}` of `main` is `Lines` or `Files` at layer L1"
        )),
    };
    let inputs = main
        .params
        .iter()
        .map(|p| Ok((p.name.clone(), kind(&p.name, p.ty.as_ref())?)))
        .collect::<Result<_, String>>()?;
    let mut outputs = Vec::new();
    for p in main.ports.iter().flatten() {
        if kind(&p.name, Some(&p.ty))? != PortKind::Lines {
            return Err(format!(
                "output port `{}` of `main` is `Lines` at layer L1",
                p.name
            ));
        }
        outputs.push(p.name.clone());
    }
    Ok(Program {
        unit,
        inputs,
        outputs,
    })
}

impl Program {
    /// The input ports, in header order.
    pub fn inputs(&self) -> &[(String, PortKind)] {
        &self.inputs
    }

    /// The elaboration.
    pub fn unit(&self) -> &Unit {
        &self.unit
    }

    /// This program with its demanded build-stage terms evaluated under `fuel` each (step
    /// L1.28), and what the build did.
    pub fn stage(&self, fuel: u64) -> (Program, stage::Report) {
        let (unit, report) = stage::mix(&self.unit, &["main"], fuel);
        let program = Program {
            unit,
            inputs: self.inputs.clone(),
            outputs: self.outputs.clone(),
        };
        (program, report)
    }

    /// The output ports, in header order.
    pub fn outputs(&self) -> &[String] {
        &self.outputs
    }

    /// Runs one wave: `lines` gives the bytes of each `Lines` input, and `files` the lookup
    /// behind each `Files` input. An error stops the wave before anything is written.
    pub fn run(
        &self,
        lines: &BTreeMap<String, Vec<u8>>,
        files: impl Fn(&str) -> Arc<dyn Lookup>,
    ) -> Result<Wave, String> {
        Ok(self.wave(lines, files, false, &direct)?.0)
    }

    /// Runs one wave as [`Program::run`] does, with the wave's term run by `map`: the test
    /// runner's way to run a program through another form.
    pub fn run_through(
        &self,
        lines: &BTreeMap<String, Vec<u8>>,
        files: impl Fn(&str) -> Arc<dyn Lookup>,
        map: &Through<'_>,
    ) -> Result<Wave, String> {
        Ok(self.wave(lines, files, false, map)?.0)
    }

    /// Runs one wave as [`Program::run`] does, and records its provenance (step L1.20): the
    /// fact address of every value, the wave stamp 0 first in each keypath.
    pub fn provenance(
        &self,
        lines: &BTreeMap<String, Vec<u8>>,
        files: impl Fn(&str) -> Arc<dyn Lookup>,
    ) -> Result<(Wave, Provenance), String> {
        let (wave, prov) = self.wave(lines, files, true, &direct)?;
        Ok((wave, prov.expect("provenance was recorded")))
    }

    fn wave(
        &self,
        lines: &BTreeMap<String, Vec<u8>>,
        files: impl Fn(&str) -> Arc<dyn Lookup>,
        trace: bool,
        map: &Through<'_>,
    ) -> Result<(Wave, Option<Provenance>), String> {
        let mut world = World::new();
        let mut record = Record::default();
        for (name, kind) in &self.inputs {
            match kind {
                PortKind::Lines => {
                    let Some(bytes) = lines.get(name) else {
                        return Err(format!("no input for port `{name}`"));
                    };
                    world = world.input(name, split_lines(bytes));
                    record.lines.insert(name.clone(), bytes.clone());
                }
                PortKind::Files => world = world.source(name, files(name)),
            }
        }
        for name in &self.outputs {
            world = world.output(name);
        }
        let main = self.unit.get("main").expect("`main` was elaborated");
        let args = self
            .inputs
            .iter()
            .map(|(name, _)| Term::Read(name.as_str().into()))
            .collect();
        let term = interp::prelude(Term::App(Arc::new(main), args));
        let mut ev = Evaluator::new(world);
        if trace {
            ev = ev.with_provenance(vec![Value::Int(0)]);
        }
        map(&term, &mut ev)?;
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

    /// Runs the wave `record` holds, reading nothing from the world.
    pub fn replay(&self, record: &Record) -> Result<Wave, String> {
        self.run(&record.lines, |name| {
            Arc::new(Recorded(
                record.files.get(name).cloned().unwrap_or_default(),
            ))
        })
    }
}

/// Commits `writes` in order through `sink`, giving each write's acknowledgment, `#ok` or
/// `#ioError(why)`. The first failure aborts the wave, as the default policy does, so no
/// later port is written.
pub fn commit(
    writes: &[(String, Vec<u8>)],
    mut sink: impl FnMut(&str, &[u8]) -> Result<(), String>,
) -> Vec<(String, Value)> {
    let mut acks = Vec::new();
    for (port, bytes) in writes {
        match sink(port, bytes) {
            Ok(()) => acks.push((port.clone(), Value::atom("ok"))),
            Err(why) => {
                acks.push((port.clone(), io_error(&why)));
                break;
            }
        }
    }
    acks
}

/// `#ioError(why)`.
fn io_error(why: &str) -> Value {
    Value::atom_with("ioError", vec![Value::str(why)])
}

/// The lines of `bytes`, keyed from 1. A line ends at `\n`, a `\r` before it is dropped,
/// and a last line needs no `\n`; a line that is not UTF-8 is `#ioError`, bare, as a failed
/// read of a `Files` port is (`LineNo -> String | #ioError`).
pub fn split_lines(bytes: &[u8]) -> Value {
    let mut parts: Vec<&[u8]> = bytes.split(|b| *b == b'\n').collect();
    if parts.last().is_some_and(|l| l.is_empty()) {
        parts.pop();
    }
    let lines = parts.into_iter().enumerate().map(|(i, line)| {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        let v = match std::str::from_utf8(line) {
            Ok(s) => Value::str(s),
            Err(_) => Value::atom("ioError"),
        };
        (Value::Int(i as i64 + 1), v)
    });
    Value::Family(Family::of(lines))
}

/// The bytes a push of `v` writes to `Lines` port `port`: each string, then `\n`.
fn join_lines(port: &str, v: &Value) -> Result<Vec<u8>, String> {
    let lines: Vec<Value> = match v {
        Value::Family(f) => f.leaves().into_iter().map(|(_, v)| v).collect(),
        v => vec![v.clone()],
    };
    let mut out = Vec::new();
    for line in lines {
        let Value::Str(s) = line else {
            return Err(format!("port `{port}` takes strings; {line} was pushed"));
        };
        out.extend_from_slice(s.as_bytes());
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
        Ok(match std::fs::read(&**path) {
            Ok(bytes) => match String::from_utf8(bytes) {
                Ok(s) => Value::str(&s),
                Err(_) => Value::atom("ioError"),
            },
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Value::atom("notFound"),
            Err(_) => Value::atom("ioError"),
        })
    }
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
    /// `error P K` (port, path) for a read that gave `#notFound` or `#ioError`.
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
        for (port, bytes) in &self.lines {
            entry("lines", &[port.as_bytes(), bytes]);
        }
        for (port, reads) in &self.files {
            for (path, v) in reads {
                let Value::Str(path) = path else {
                    unreachable!("a read path is a String")
                };
                let (p, k) = (port.as_bytes(), path.as_bytes());
                match v {
                    Value::Str(s) => entry("text", &[p, k, s.as_bytes()]),
                    Value::Atom(a) if a.name.as_ref() == "notFound" => entry("missing", &[p, k]),
                    Value::Atom(a) if a.name.as_ref() == "ioError" => entry("error", &[p, k]),
                    v => unreachable!("a file read gives a String or an atom, not {v}"),
                }
            }
        }
        out
    }

    /// The record `bytes` holds, or why they are not one.
    pub fn from_bytes(bytes: &[u8]) -> Result<Record, String> {
        let bad = || "not a Zed record".to_string();
        let mut rest = bytes.strip_prefix(MAGIC.as_bytes()).ok_or_else(bad)?;
        let mut record = Record::default();
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
                ("lines", [p, b]) => {
                    record.lines.insert(text(p)?, b.to_vec());
                }
                ("text" | "missing" | "error", [p, k, more @ ..]) => {
                    let v = match (kind, more) {
                        ("text", [b]) => Value::str(&text(b)?),
                        ("missing", []) => Value::atom("notFound"),
                        ("error", []) => Value::atom("ioError"),
                        _ => return Err(bad()),
                    };
                    let reads = record.files.entry(text(p)?).or_default();
                    reads.insert(Value::str(&text(k)?), v);
                }
                _ => return Err(bad()),
            }
        }
        Ok(record)
    }
}

/// `zedc run <file> [port=path …] [--record <out>]` and
/// `zedc replay <file> <record> [port=path …]`, with `args` the words after `zedc`. A
/// `Lines` input reads the file bound to it, or standard input if it is `stdin`; a `Lines`
/// output writes the file bound to it, or standard output or error if it is `stdout` or
/// `stderr`. Returns the exit status: 0, 1 when the program fails or a write fails, 2 for
/// a usage error.
pub fn command(
    args: &[String],
    stdin: &mut dyn Read,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> u8 {
    match command_inner(args, stdin, stdout, stderr) {
        Ok(()) => 0,
        Err((status, why)) => {
            let _ = writeln!(stderr, "{why}");
            status
        }
    }
}

fn command_inner(
    args: &[String],
    stdin: &mut dyn Read,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> Result<(), (u8, String)> {
    let usage = || {
        (
            2,
            "usage: zedc run <file> [port=path …] [--record <out>]\n       \
             zedc replay <file> <record> [port=path …]"
                .to_string(),
        )
    };
    let (replay, file, mut rest) = match args {
        [cmd, file, rest @ ..] if cmd == "run" => (None, file, rest),
        [cmd, file, record, rest @ ..] if cmd == "replay" => (Some(record), file, rest),
        _ => return Err(usage()),
    };
    let mut record_to = None;
    let mut binds = BTreeMap::new();
    while let [word, more @ ..] = rest {
        rest = more;
        if word == "--record" && replay.is_none() {
            let [out, more @ ..] = rest else {
                return Err(usage());
            };
            record_to = Some(out);
            rest = more;
        } else if let Some((port, path)) = word.split_once('=') {
            binds.insert(port.to_string(), path.to_string());
        } else {
            return Err(usage());
        }
    }
    let bytes = std::fs::read(file).map_err(|e| (2, format!("{file}: {e}")))?;
    let program = load(&bytes).map_err(|e| (1, format!("{file}:{e}")))?;
    let known =
        |p: &String| program.inputs.iter().any(|(n, _)| n == p) || program.outputs.contains(p);
    if let Some(p) = binds.keys().find(|p| !known(p)) {
        return Err((2, format!("`main` has no port `{p}`")));
    }
    for name in &program.outputs {
        if !binds.contains_key(name) && name != "stdout" && name != "stderr" {
            return Err((
                2,
                format!("output port `{name}` needs a file: `{name}=path`"),
            ));
        }
    }
    let wave = match replay {
        Some(path) => {
            let bytes = std::fs::read(path).map_err(|e| (2, format!("{path}: {e}")))?;
            let record = Record::from_bytes(&bytes).map_err(|e| (2, format!("{path}: {e}")))?;
            program.replay(&record)
        }
        None => {
            let mut lines = BTreeMap::new();
            for (name, kind) in &program.inputs {
                if *kind != PortKind::Lines {
                    continue;
                }
                let mut bytes = Vec::new();
                match binds.get(name) {
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
            program.run(&lines, |_| Arc::new(Disk))
        }
    }
    .map_err(|e| (1, e))?;
    if let Some(out) = record_to {
        std::fs::write(out, wave.record.to_bytes()).map_err(|e| (1, format!("{out}: {e}")))?;
    }
    let acks = commit(&wave.writes, |port, bytes| match binds.get(port) {
        Some(path) => std::fs::write(path, bytes).map_err(|e| format!("{path}: {e}")),
        None if port == "stdout" => stdout.write_all(bytes).map_err(|e| e.to_string()),
        None => stderr.write_all(bytes).map_err(|e| e.to_string()),
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

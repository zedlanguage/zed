//! Step L1.19d: a record replayed against another program, `zedc replay old.zed record
//! --program new.zed` (DESIGN.md sec:incremental, "An edit to a running program", *Replay*).
//! The record is checked against `old.zed`, the program that wrote it, as a plain replay checks
//! it; each recorded input is then checked against the ports of `new.zed`; both programs run on
//! the recorded inputs; and each output port's lines are compared, giving the first line that
//! differs and each program's count of lines.
//!
//! What fits (DESIGN.md L1.19d, "Where this document does not say"): at L1 a recorded value
//! fits a port when it is of the port's kind. The record keeps a `Lines` port's bytes under
//! `lines`, the reads of the file port and of the environment port under one form, a key and
//! what its read gave ([`Record::files`]), and the command line as its arguments
//! ([`Record::args`]). So recorded lines fit only a `Lines` port, recorded reads fit the file
//! port or the environment port, and recorded arguments fit only a `CommandLine` port. The
//! record does not say whether its reads were of files or of the environment; a port's name
//! says it (`main::files`, `m.env`), and the name is what a replay looks the reads up by, so a
//! read recorded for one is never given to the other. A refined port type is checked by the
//! layer that brings refinements, not here.

use std::collections::BTreeSet;

use zed_kernel::text::Text;

use super::{PortKind, Program, Record, Wave};

/// What a record holds for one input port.
enum Held<'a> {
    /// The bytes of a `Lines` port.
    Lines(&'a [u8]),
    /// The reads of the file port or of the environment port: how many keys, and the first.
    Reads(usize, Option<String>),
    /// The command-line arguments.
    Args(&'a [String]),
}

impl Held<'_> {
    /// Whether this fits a port of kind `kind`: lines a `Lines` port, reads the file or the
    /// environment port, arguments a `CommandLine` port.
    fn fits(&self, kind: PortKind) -> bool {
        matches!(
            (self, kind),
            (Held::Lines(_), PortKind::Lines)
                | (Held::Reads(..), PortKind::Files | PortKind::Env)
                | (Held::Args(_), PortKind::CommandLine)
        )
    }

    /// The value as the error that rejects it names it: its kind, its size and its first item.
    /// O(the bytes of the value) for lines, which are counted; O(1) otherwise.
    fn describe(&self) -> String {
        match self {
            Held::Lines(bytes) => {
                let (mut count, mut first) = (0usize, None);
                zed_kernel::lines::LineReader::whole(bytes, |line| {
                    count += 1;
                    first.get_or_insert(line);
                });
                match first {
                    None => "the lines of a `Lines` input, no lines".to_string(),
                    Some(line) => format!(
                        "the lines of a `Lines` input, {count} {}, the first {}",
                        plural(count, "line"),
                        quoted(line)
                    ),
                }
            }
            Held::Reads(count, first) => match first {
                None => "the reads of the file port or the environment, no reads".to_string(),
                Some(key) => format!(
                    "the reads of the file port or the environment, {count} {}, the first of {key}",
                    plural(*count, "read")
                ),
            },
            Held::Args(args) => match args.first() {
                None => "the command-line arguments, none".to_string(),
                Some(arg) => format!(
                    "the command-line arguments, {} {}, the first {}",
                    args.len(),
                    plural(args.len(), "argument"),
                    Text::from(arg.as_str()).literal()
                ),
            },
        }
    }
}

/// The kind of port `kind` as the errors name it, with the type of its field of `MainArgs`.
fn kind_name(kind: PortKind) -> &'static str {
    match kind {
        PortKind::Lines => "a `Lines` input",
        PortKind::Files => "the file port, `Files`",
        PortKind::CommandLine => "the command line, `CommandLine`",
        PortKind::Env => "the environment, `(String) ->? String`",
    }
}

/// `noun`, with an `s` unless `n` is 1.
fn plural(n: usize, noun: &str) -> String {
    match n {
        1 => noun.to_string(),
        _ => format!("{noun}s"),
    }
}

/// The bytes of a line as a Zed string literal; a byte that is not UTF-8 is shown as U+FFFD,
/// which no line a program writes holds, since a program writes strings.
fn quoted(line: &[u8]) -> String {
    Text::from(String::from_utf8_lossy(line).as_ref())
        .literal()
        .to_string()
}

/// What `record` holds for the input port `name` of kind `kind` in `old`, the program that
/// wrote it: the entry the record keeps for that name, or, for a port `old` reads that left no
/// entry (a file port or an environment port no read of which ran, or a command line with no
/// arguments), the empty value of the kind `old` reads it as. `None` when the record holds
/// nothing for `name`.
fn held<'a>(old: &Program, record: &'a Record, name: &str) -> Option<Held<'a>> {
    if let Some(bytes) = record.lines.get(name) {
        return Some(Held::Lines(bytes));
    }
    if let Some(reads) = record.files.get(name) {
        return Some(Held::Reads(
            reads.len(),
            reads.keys().next().map(|k| format!("{k:?}")),
        ));
    }
    // The record keeps the arguments under no port's name: they are the command line's, which
    // `old` reads under its name.
    let (_, kind) = old.inputs().iter().find(|(n, _)| n == name)?;
    Some(match kind {
        PortKind::CommandLine => Held::Args(&record.args),
        PortKind::Files | PortKind::Env => Held::Reads(0, None),
        // Cannot be reached for a record `old` accepts: a run records the bytes of each
        // `Lines` port, and the caller has checked that the record holds them
        // (`Program::lacks_input`). A record that lacks them holds nothing for the port.
        PortKind::Lines => return None,
    })
}

/// Checks the record `record`, read from the file `path` and accepted by `old`, against the
/// input ports of `new`, read from `new_file`: each port `new` reads must be one the record holds
/// a value for, and the value must fit the port's kind ([`Held::fits`]); and each port the record
/// holds must be one `new` reads. Gives every problem, one paragraph each, or none. Each is a
/// usage error: the record and the program given do not go together. At L1 a record holds one
/// wave, wave 0.
///
/// O(p log p + l) for p ports and l bytes of recorded lines (each rejected `Lines` value is
/// counted once to name it), each port looked up in the record's maps once.
pub(super) fn check_inputs(
    old: &Program,
    new: &Program,
    record: &Record,
    path: &str,
    new_file: &str,
) -> Result<(), String> {
    let mut problems = Vec::new();
    for (name, kind) in new.inputs() {
        match held(old, record, name) {
            None => problems.push(format!(
                "{new_file} reads the port `{name}`, and the record {path} holds nothing for it: \
                 the run that wrote the record did not read `{name}`, and a replay reads only \
                 what the record holds. Remove the read of `{name}` from {new_file}, or make a \
                 record that holds it with `zedc run {new_file} --record <out>`."
            )),
            Some(value) if !value.fits(*kind) => problems.push(format!(
                "wave 0 of the record {path} holds, for the port `{name}`, {}, and {new_file} \
                 reads `{name}` as {}, which that value does not fit. Read `{name}` in \
                 {new_file} as the run that wrote the record read it, or make a record of \
                 {new_file} with `zedc run {new_file} --record <out>`.",
                value.describe(),
                kind_name(*kind)
            )),
            Some(_) => {}
        }
    }
    let reads: BTreeSet<&str> = new.inputs().iter().map(|(n, _)| n.as_str()).collect();
    let recorded: BTreeSet<&str> = record
        .lines
        .keys()
        .chain(record.files.keys())
        .chain(old.inputs().iter().map(|(n, _)| n))
        .map(String::as_str)
        .collect();
    for name in recorded.difference(&reads) {
        problems.push(format!(
            "the record {path} holds the input of the port `{name}`, and {new_file} does not \
             read `{name}`, so a replay of {new_file} would not use it and its outputs could \
             not be compared with those of the recorded run. Read `{name}` in {new_file}, or \
             replay {path} without `--program`."
        ));
    }
    match problems.is_empty() {
        true => Ok(()),
        false => Err(problems.join("\n")),
    }
}

/// The report of `zedc replay old.zed record --program new.zed`: for each output port of either
/// program, in `old`'s header order and then `new`'s, one line saying whether the two waves
/// wrote the same lines to it and, if not, the first line that differs, at its key from 0, with
/// both texts, and each program's count of lines on the port; a port only one program has is
/// said to be so, with its count of lines. A line for the exit status follows when the two
/// differ. A program with no output port writes no lines; when neither has one, the report says
/// so.
///
/// Complexity: one pass over each port's bytes in each program, O(b) for b bytes written in all,
/// plus O(p log p) to match p ports by name, so the report is linear in the ports and in the
/// lines (DESIGN.md L1.19d: "compared in one pass per port"). Test:
/// `l01_19_whole_file_ports::bench::comparing_the_outputs_of_n_and_8n_lines_scales`.
pub(super) fn report(old: (&Program, &Wave, &str), new: (&Program, &Wave, &str)) -> String {
    let (old_p, old_w, old_file) = old;
    let (new_p, new_w, new_file) = new;
    let old_ports: BTreeSet<&str> = old_p.outputs().iter().map(String::as_str).collect();
    let new_ports: BTreeSet<&str> = new_p.outputs().iter().map(String::as_str).collect();
    let ports = old_p.outputs().iter().chain(
        new_p
            .outputs()
            .iter()
            .filter(|p| !old_ports.contains(p.as_str())),
    );
    let mut out = String::new();
    for port in ports {
        let line = match (
            old_ports.contains(port.as_str()),
            new_ports.contains(port.as_str()),
        ) {
            (true, true) => compare(
                port,
                (written(old_w, port), old_file),
                (written(new_w, port), new_file),
            ),
            (only_old, _) => {
                let (file, other, wave) = match only_old {
                    true => (old_file, new_file, old_w),
                    false => (new_file, old_file, new_w),
                };
                let n = lines_of(written(wave, port)).len();
                format!(
                    "{port}: only {file} has this port, and {other} does not write it; {file} \
                     writes {n} {} to it.",
                    plural(n, "line")
                )
            }
        };
        out.push_str(&line);
        out.push('\n');
    }
    if old_p.outputs().is_empty() && new_p.outputs().is_empty() {
        out.push_str("neither program has an output port, so no lines are compared.\n");
    }
    if old_w.status != new_w.status {
        out.push_str(&format!(
            "the exit status: {old_file} ends with {}, and {new_file} with {}.\n",
            old_w.status, new_w.status
        ));
    }
    out
}

/// The bytes the wave `wave` wrote to the port `port`: none when it did not push to it.
fn written<'a>(wave: &'a Wave, port: &str) -> &'a [u8] {
    wave.writes
        .iter()
        .find(|(p, _)| p == port)
        .map_or(&[], |(_, bytes)| bytes.as_slice())
}

/// The lines of `bytes`, each a slice of it, by the line ends of a `Lines` input
/// ([`zed_kernel::lines::LineReader::whole`]). O(len), nothing copied.
fn lines_of(bytes: &[u8]) -> Vec<&[u8]> {
    let mut lines = Vec::new();
    zed_kernel::lines::LineReader::whole(bytes, |line| lines.push(line));
    lines
}

/// The line of the report for the port `port`, which both programs have: what `old` and `new`,
/// each its bytes and its file, wrote to it, compared line by line in one pass.
///
/// Why the first differing key is the right one to give, and the counts the rest: the lines
/// are compared at keys 0, 1, … up to the shorter count, and the first key where they differ is
/// the first line that differs. When no key up to the shorter count differs, the shorter output
/// is a prefix of the longer one, and the counts alone say where they part: the line at the
/// shorter count's key is in one only. When the counts are equal too, the outputs are the same.
fn compare(port: &str, old: (&[u8], &str), new: (&[u8], &str)) -> String {
    let (a, b) = (lines_of(old.0), lines_of(new.0));
    let (old_file, new_file) = (old.1, new.1);
    let counts = format!(
        "{old_file} writes {} {}, and {new_file} {}",
        a.len(),
        plural(a.len(), "line"),
        b.len()
    );
    match a.iter().zip(&b).position(|(x, y)| x != y) {
        Some(k) => format!(
            "{port}: the line at key {k} differs: {old_file} writes {}, and {new_file} writes {}; \
             {counts}.",
            quoted(a[k]),
            quoted(b[k])
        ),
        None if a.len() == b.len() => format!(
            "{port}: no difference: both write the same {} {}.",
            a.len(),
            plural(a.len(), "line")
        ),
        None => {
            format!("{port}: the lines both write are the same, and one writes more: {counts}.")
        }
    }
}

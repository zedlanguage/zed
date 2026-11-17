//! `sync [SPEC_DIR] [--check]` brings this repository's grammar and fixtures up to the spec
//! checkout at `SPEC_DIR`, or at `ZED_SPEC_DIR` when no directory is given. It is run by hand
//! after the spec changes; no test and no build step runs it, so this repository builds and
//! tests with no access to the spec. It writes:
//!
//! - `zed/grammar/syntax.peg`, `notation.peg`, `lexical.peg` and `desugar.txt`: the grammars of
//!   sec:grammar and the desugaring rules (step L1.8), which the build reads;
//! - `zed/grammar/words.md`: the table of defined words by layer, each cell cut to its
//!   backquoted words, from which the layer of a fence is computed;
//! - `zed/fences/design.md` and `examples.md`: the `zed` fences of DESIGN.md and EXAMPLES.md,
//!   each under a header naming its source line, its layer (step L1.7) and its section and place
//!   in the section (by which the tests key it, so an edit in one section moves no other
//!   section's keys);
//! - `zed/fences/messages.md`: their ```` ```text ```` fences, the messages and reports the spec
//!   prints, each under a header naming its source line and section;
//! - `zed/fences/rejections.txt`: the row names of the rejection table (step L1.29);
//! - `zed/fences/kernel-rules.txt`: the names no message prints (sec:diagnostics);
//! - `zed/fences/canon-serial.md`: the tables of step M0.7's serialization, each node's tag and
//!   its fields in order, and each primitive's code, which
//!   `m0_07_canonicalization::serial_text` serializes by;
//! - `zed/synced-from`: the spec commit the copies were written from ([`STAMP`]), and that of
//!   each copy held back with `--hold COPY`, not written or compared with `--check`.
//!
//! It then runs the checks that read the spec's prose, which this repository does not hold:
//! the prelude laws against `docs/mathlib-study.md`, the build modes and the kinds of build
//! DESIGN.md names ([`crate::spec_checks`]), and the citations of this repository
//! ([`crate::cite`]). With `--check` it writes nothing and fails if a file is out of date; either
//! way it fails if a check fails.

use std::collections::HashSet;
use std::fmt::Write;

use crate::fence_layers::{of_document, rejection_rows};
use crate::layer::spans;
use crate::spec::{Spec, fence_texts, fences_in};
use crate::spec_checks::{build_modes, kernel_rules, prelude_laws};
use crate::text::{base_name, read_text, strip};
use crate::{Outcome, impl_root, say};

/// The variable that names the spec checkout when no directory is given.
pub const VAR: &str = "ZED_SPEC_DIR";

/// The usage line.
const USAGE: &str = "usage: sync [SPEC_DIR] [--check] [--hold COPY]...";

/// The spec checkout the tool reads: the directory among `args` (all but `--check` and each
/// `--hold COPY`), or else `var`, the value of [`VAR`].
pub fn spec_dir(args: &[String], var: Option<String>) -> Result<String, String> {
    let (_, rest) = held(args)?;
    let mut dirs = rest.into_iter().filter(|a| *a != "--check");
    match (dirs.next(), dirs.next()) {
        (Some(dir), None) => Ok(dir.clone()),
        (None, None) => var
            .filter(|v| !v.is_empty())
            .ok_or_else(|| format!("{USAGE}, or set {VAR}")),
        _ => Err(USAGE.into()),
    }
}

/// The copies `args` hold back, each named by `--hold COPY`, and the other arguments.
fn held(args: &[String]) -> Result<(Vec<String>, Vec<&String>), String> {
    let (mut hold, mut rest) = (Vec::new(), Vec::new());
    let mut args = args.iter();
    while let Some(a) = args.next() {
        if a == "--hold" {
            hold.push(args.next().ok_or(USAGE)?.clone());
        } else {
            rest.push(a);
        }
    }
    Ok((hold, rest))
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let check = args.iter().any(|a| a == "--check");
    let dir = spec_dir(args, std::env::var(VAR).ok())?;
    let (hold, _) = held(args)?;
    let spec = Spec::open(&dir)?;
    let root = impl_root();
    let copies_ok = sync_holding(&spec, &format!("{root}/zed"), check, &hold, out)?;
    let design = read_text(&spec.design)?;
    let page = read_text(&format!("{root}/docs/mathlib-study.md"))?;
    let mut checks_ok = true;
    for (what, result) in [
        ("the prelude laws", prelude_laws(&design, &page)),
        ("the build modes", build_modes(&design)),
    ] {
        if let Err(e) = result {
            say!(out, "{what}: {e}");
            checks_ok = false;
        }
    }
    let cited_ok = crate::cite::run(&[dir], out)?;
    Ok(copies_ok && checks_ok && cited_ok)
}

/// The copy of the `zed` fences of the document at `path`, laid out against `spec`.
fn render(path: &str, spec: &Spec) -> Result<String, String> {
    let name = base_name(path);
    let mut out = format!(
        "<!-- The `zed` fences of the spec's {name}, copied by the sync tool: do not edit. -->\n"
    );
    for f in of_document(path, spec)? {
        let word = f
            .word
            .map_or("none".to_string(), |(k, w)| format!("L{k} ({w})"));
        let label = f.label.map_or("none".to_string(), |k| format!("L{k}"));
        let doc = if f.notation {
            ", documentation notation"
        } else {
            ""
        };
        let (layer, ring) = (f.layer, f.ring);
        let f = f.fence;
        let (line, section, index, text) = (f.line, f.section, f.index, f.text);
        writeln!(
            out,
            "\n<!-- {name}:{line} layer L{layer}: ring L{ring}, word {word}, label {label}{doc}; \
             section [{section}] {index} -->\n```zed\n{text}\n```"
        )
        .expect("writing to a String");
    }
    Ok(out)
}

/// The ```` ```text ```` fences of the documents at `paths`, each under a header naming its
/// line and section, with the indentation of its opening line taken off each of its lines, so
/// that a report printed inside a list item reads as the program prints it. O(size of the
/// documents).
fn messages(paths: &[String]) -> Result<String, String> {
    let mut out = String::from(
        "<!-- The `text` fences of the spec's DESIGN.md and EXAMPLES.md, copied by the sync tool: \
         do not edit. -->\n",
    );
    for path in paths {
        let name = base_name(path);
        let text = read_text(path)?;
        let lines: Vec<&str> = text.split('\n').collect();
        for f in fences_in(&text, "text", path)? {
            let open = lines[f.line - 1];
            let indent = open.len() - open.trim_start_matches(' ').len();
            let body: Vec<&str> = f
                .text
                .split('\n')
                .map(|l| {
                    let spaces = l.len() - l.trim_start_matches(' ').len();
                    &l[spaces.min(indent)..]
                })
                .collect();
            let (line, section, index) = (f.line, f.section, f.index);
            writeln!(
                out,
                "\n<!-- {name}:{line}; section [{section}] {index} -->\n```text\n{}\n```",
                body.join("\n")
            )
            .expect("writing to a String");
        }
    }
    Ok(out)
}

/// The table of defined words by layer (sec:grammar) of the document `design`: its head, then
/// each row with each cell cut to its backquoted words, each word once, where it first appears
/// (a note in a cell may name a word of the cell again, as row L3's note names `split` and
/// `concat`; a word only a note names, as row L15's tactics, is kept). That is all of a cell
/// that [`crate::layer::WordTable::read`] reads. O(size of `design`).
fn words(design: &str) -> Result<String, String> {
    let mut lines = design
        .split('\n')
        .skip_while(|l| !l.starts_with("| Layer | Annotations | Facet words"));
    let (Some(head), Some(rule)) = (lines.next(), lines.next()) else {
        return Err("DESIGN.md has no table of defined words".into());
    };
    let mut out = format!(
        "<!-- The table of defined words of the spec's DESIGN.md (sec:grammar), each cell cut to \
         its backquoted words, copied by the sync tool: do not edit. -->\n\n{head}\n{rule}\n"
    );
    for row in lines.take_while(|l| l.starts_with('|')) {
        let cells: Vec<String> = strip(row)
            .trim_matches('|')
            .split('|')
            .enumerate()
            .map(|(k, cell)| {
                // Complexity tradeoff: a word is checked against the cell's earlier words by a
                // hash set, O(1) per word, rather than by a search of the words kept so far,
                // O(w²) in the w words of the cell (measured 2026-11-15: ratio 39.2 at 2000 and
                // 16000 words by the search, 4.9 by the set). Costs one set per cell, nothing is
                // given up. Test: m0_03 bench `sync_scales_with_the_words_of_a_table_cell`.
                let mut seen = HashSet::new();
                let words: Vec<String> = spans(cell)
                    .into_iter()
                    .filter(|w| seen.insert(*w))
                    .map(|w| format!("`{w}`"))
                    .collect();
                match (k, words.is_empty()) {
                    (0, _) => strip(cell).to_string(),
                    (_, true) => "—".to_string(),
                    (_, false) => words.join(", "),
                }
            })
            .collect();
        writeln!(out, "| {} |", cells.join(" | ")).expect("writing to a String");
    }
    Ok(out)
}

/// The header of each table of step M0.7's serialization ends with this text.
pub const SERIAL_HEADER: &str = " | Tag | Fields in order |";

/// The header of step M0.7's table of the primitives' codes.
pub const PRIM_HEADER: &str = "| Primitive | Code |";

/// The tables of step M0.7's serialization, each a table of DESIGN.md whose header ends with
/// [`SERIAL_HEADER`] or is [`PRIM_HEADER`]: its header and rows as written, without the line
/// under the header, the tables one after another. O(size of `design`).
pub fn serial_tables(design: &str) -> String {
    let mut out = String::new();
    let mut lines = design.lines();
    while let Some(line) = lines.next() {
        if !((line.starts_with("| ") && line.ends_with(SERIAL_HEADER)) || line == PRIM_HEADER) {
            continue;
        }
        writeln!(out, "{line}").expect("writing to a String");
        for row in lines.by_ref().skip(1).take_while(|l| l.starts_with("| ")) {
            writeln!(out, "{row}").expect("writing to a String");
        }
    }
    out
}

/// The lines `lines`, each followed by a newline.
fn lines_of(lines: &[String]) -> String {
    lines.iter().map(|l| format!("{l}\n")).collect()
}

/// Brings the grammar and fixtures under `zed` up to `spec`, or with `check` only names each
/// file that is out of date.
pub fn sync_into(spec: &Spec, zed: &str, check: bool, out: &mut String) -> Outcome {
    sync_holding(spec, zed, check, &[], out)
}

/// [`sync_into`], holding back the copies named in `hold` (by file name, as `syntax.peg`): a held
/// copy that is out of date is not written, and [`STAMP`] keeps the commit it was written from
/// on a line of its own (SYNC-held-files-stamp), so that `--check` and merge-push's report of
/// the lag give its own lag, not that of the other copies.
pub fn sync_holding(
    spec: &Spec,
    zed: &str,
    check: bool,
    hold: &[String],
    out: &mut String,
) -> Outcome {
    let copies = copies(spec, zed)?;
    if let Some(h) = hold
        .iter()
        .find(|h| !copies.iter().any(|(dest, _)| base_name(dest) == h.as_str()))
    {
        return Err(format!(
            "--hold {h}: no copy of the spec is named so; {USAGE}"
        ));
    }
    let stamp_path = format!("{zed}/{STAMP}");
    let old = read_text(&stamp_path).ok();
    let mut stale = false;
    let mut kept = String::new();
    for (dest, want) in copies {
        if read_text(&dest).ok().as_ref() == Some(&want) {
            continue;
        }
        let name = base_name(&dest);
        let own = old.as_deref().and_then(|s| own_commit(s, name));
        if check {
            stale = true;
            match own {
                Some(from) => say!(out, "{name} is out of date, copied from zed {from}"),
                None => say!(out, "{name} is out of date"),
            }
        } else if hold.iter().any(|h| h == name) {
            // A held copy that was current at the last sync was written from the commit that
            // sync names on its first line.
            let from = own
                .or_else(|| old.as_deref().and_then(|s| s.lines().next()))
                .unwrap_or("unknown");
            say!(out, "{name} is held, copied from zed {from}");
            writeln!(kept, "{name} {from}").expect("writing to a String");
        } else {
            say!(out, "{name} is written");
            std::fs::write(&dest, want).map_err(|e| format!("{dest}: {e}"))?;
        }
    }
    if !check {
        // The stamp is not a copy, so --check does not compare it: a copy is current or not
        // whatever commit it was written from.
        let want = format!("{}\n{kept}", spec_commit(&spec.root));
        if old.as_ref() != Some(&want) {
            say!(out, "{STAMP} is written");
            std::fs::write(&stamp_path, want).map_err(|e| format!("{stamp_path}: {e}"))?;
        }
    }
    Ok(!(stale && check))
}

/// The commit the stamp text `stamp` names for the copy `name` on a line of its own, which it
/// has when the copy was held back from a later sync.
fn own_commit<'a>(stamp: &'a str, name: &str) -> Option<&'a str> {
    stamp
        .lines()
        .skip(1)
        .find_map(|l| l.strip_prefix(name)?.strip_prefix(' '))
}

/// Each copy under `zed` with the text `spec` gives it.
fn copies(spec: &Spec, zed: &str) -> Result<Vec<(String, String)>, String> {
    let root = &spec.root;
    let (design_path, examples_path) = (spec.design.clone(), format!("{root}/EXAMPLES.md"));
    let design = read_text(&design_path)?;
    Ok(vec![
        (
            format!("{zed}/fences/design.md"),
            render(&design_path, spec)?,
        ),
        (
            format!("{zed}/fences/examples.md"),
            render(&examples_path, spec)?,
        ),
        (
            format!("{zed}/fences/messages.md"),
            messages(&[design_path.clone(), examples_path])?,
        ),
        (
            format!("{zed}/grammar/syntax.peg"),
            format!("{}\n", spec.syn_text),
        ),
        (
            format!("{zed}/grammar/notation.peg"),
            format!("{}\n", spec.doc_text),
        ),
        (
            format!("{zed}/grammar/lexical.peg"),
            format!("{}\n", spec.lex_text),
        ),
        (
            format!("{zed}/grammar/desugar.txt"),
            format!("{}\n", fence_texts(&design_path, "desugar")?.join("\n")),
        ),
        (format!("{zed}/grammar/words.md"), words(&design)?),
        (
            format!("{zed}/fences/rejections.txt"),
            lines_of(&rejection_rows(&design)),
        ),
        (
            format!("{zed}/fences/kernel-rules.txt"),
            lines_of(&kernel_rules(&design)?),
        ),
        (
            format!("{zed}/fences/canon-serial.md"),
            serial_tables(&design),
        ),
    ])
}

/// The file under `zed/` that names the spec commit the copies were last written from
/// (MERGE-spec-lag-by-pin), read by /home/luke/Work/wt/merge-push.sh to list the spec commits
/// not yet synced. Its first line is that commit ([`spec_commit`]); each copy held back
/// ([`sync_holding`]) that is out of date has a further line, its name, a space and the commit
/// it was written from.
pub const STAMP: &str = "synced-from";

/// The line [`STAMP`] holds for the spec checkout at `root`: its HEAD commit, followed by
/// ` with uncommitted changes` when DESIGN.md or EXAMPLES.md differ from it there, or `unknown`
/// when `root` is not the top of a git checkout (a test's spec, or a copy of the files alone,
/// whose enclosing repository is not the spec's) or git fails.
pub fn spec_commit(root: &str) -> String {
    let git = |args: &[&str]| -> Option<String> {
        let out = std::process::Command::new("git")
            .arg("-C")
            .arg(root)
            .args(args)
            .output()
            .ok()?;
        out.status
            .success()
            .then(|| String::from_utf8_lossy(&out.stdout).trim().to_string())
    };
    let top = git(&["rev-parse", "--show-toplevel"]).map(std::path::PathBuf::from);
    let here = std::fs::canonicalize(root).ok();
    let (Some(top), Some(here)) = (top, here) else {
        return "unknown".into();
    };
    if std::fs::canonicalize(top).ok() != Some(here) {
        return "unknown".into();
    }
    let (Some(head), Some(changed)) = (
        git(&["rev-parse", "HEAD"]),
        git(&["status", "--porcelain", "--", "DESIGN.md", "EXAMPLES.md"]),
    ) else {
        return "unknown".into();
    };
    if changed.is_empty() {
        head
    } else {
        format!("{head} with uncommitted changes")
    }
}

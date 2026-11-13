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
//! - `zed/fences/kernel-rules.txt`: the names no message prints (sec:diagnostics).
//!
//! It then runs the checks that read the spec's prose, which this repository does not hold:
//! the prelude laws against `docs/mathlib-study.md`, the build modes and the kinds of build
//! DESIGN.md names ([`crate::spec_checks`]), and the citations of this repository
//! ([`crate::cite`]). With `--check` it writes nothing and fails if a file is out of date; either
//! way it fails if a check fails.

use std::fmt::Write;

use crate::fence_layers::{of_document, rejection_rows};
use crate::layer::spans;
use crate::spec::{Spec, fence_texts, fences_in};
use crate::spec_checks::{build_modes, kernel_rules, prelude_laws};
use crate::text::{base_name, read_text, strip};
use crate::{Outcome, impl_root, say};

/// The variable that names the spec checkout when no directory is given.
pub const VAR: &str = "ZED_SPEC_DIR";

/// The spec checkout the tool reads: the directory among `args` (all but `--check`), or else
/// `var`, the value of [`VAR`].
pub fn spec_dir(args: &[String], var: Option<String>) -> Result<String, String> {
    let mut dirs = args.iter().filter(|a| *a != "--check");
    match (dirs.next(), dirs.next()) {
        (Some(dir), None) => Ok(dir.clone()),
        (None, None) => var
            .filter(|v| !v.is_empty())
            .ok_or_else(|| format!("usage: sync [SPEC_DIR] [--check], or set {VAR}")),
        _ => Err("usage: sync [SPEC_DIR] [--check]".into()),
    }
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let check = args.iter().any(|a| a == "--check");
    let dir = spec_dir(args, std::env::var(VAR).ok())?;
    let spec = Spec::open(&dir)?;
    let root = impl_root();
    let copies_ok = sync_into(&spec, &format!("{root}/zed"), check, out)?;
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
/// each row with each cell cut to its backquoted words, which is all of a cell that
/// [`crate::layer::WordTable::read`] reads. O(size of `design`).
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
                let words: Vec<String> = spans(cell).iter().map(|w| format!("`{w}`")).collect();
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

/// The lines `lines`, each followed by a newline.
fn lines_of(lines: &[String]) -> String {
    lines.iter().map(|l| format!("{l}\n")).collect()
}

/// Brings the grammar and fixtures under `zed` up to `spec`, or with `check` only names each
/// file that is out of date.
pub fn sync_into(spec: &Spec, zed: &str, check: bool, out: &mut String) -> Outcome {
    let root = &spec.root;
    let (design_path, examples_path) = (spec.design.clone(), format!("{root}/EXAMPLES.md"));
    let design = read_text(&design_path)?;
    let copies = vec![
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
    ];
    refresh(copies, check, out)
}

/// Writes each copy `(dest, want)` whose file does not already hold `want`, or with `check` only
/// names it; fails with `check` if any is out of date.
fn refresh(copies: Vec<(String, String)>, check: bool, out: &mut String) -> Outcome {
    let mut stale = false;
    for (dest, want) in copies {
        if read_text(&dest).ok().as_ref() == Some(&want) {
            continue;
        }
        stale = true;
        let state = if check { "out of date" } else { "written" };
        say!(out, "{} is {state}", base_name(&dest));
        if !check {
            std::fs::write(&dest, want).map_err(|e| format!("{dest}: {e}"))?;
        }
    }
    Ok(!(stale && check))
}

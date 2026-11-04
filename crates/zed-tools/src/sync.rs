//! `sync SPEC_DIR [--check]` copies the `zed` fences of the spec's `DESIGN.md` and `EXAMPLES.md`
//! into `zed/fences/design.md` and `zed/fences/examples.md`, each under a header naming its
//! source line, its layer (step L1.7) and its section and place in the section (by which the
//! tests key it, so an edit in one section moves no other section's keys), and the syntactic
//! grammar, the documentation notation, the lexical grammar and the desugaring rules into
//! `zed/grammar` (step L1.8), and the row names of the rejection table into
//! `zed/fences/rejections.txt`. With `--check` it writes nothing and fails if a copy is out of
//! date.
//!
//! CI does not read the spec repository, so the copies are the fixtures; run this by hand after
//! the spec changes. The layer is computed as the M0.4 layer checker computes a corpus
//! program's: the lowest ring at which the fence parses (as a `Unit`, or else under the
//! documentation notation), raised to the layer of any defined word it uses (the table of
//! sec:grammar) and to a `// layer Lk` label.

use std::fmt::Write;

use zedc::parse::TOP;

use crate::layer::{Parsed, WordTable, add_holes, analyze, label_at};
use crate::spec::{Spec, fence_texts, zed_fences};
use crate::syntax::{lex, parse};
use crate::text::{base_name, read_text};
use crate::{Outcome, impl_root, say};

/// The layer named by a `// layer Lk` line. A fence's label may be on any line, since its first
/// line is usually its `// [d4]` header; the layer checker reads only a program's first line.
fn label_of(line: &str) -> Option<u32> {
    label_at(line.trim_start_matches(zedc::parse::is_space))
}

/// The layer of a fence and how it was reached.
struct FenceLayer {
    layer: u32,
    ring: u32,
    word: Option<(u32, String)>,
    label: Option<u32>,
    doc: bool,
}

fn layer_of(text: &str, spec: &Spec, table: &WordTable) -> Result<FenceLayer, String> {
    let lexical = &spec.lexical;
    let toks = lex(lexical, &text.replace('…', "elided"))?;
    let (g, start, doc, tree) = match parse(&spec.syntactic, lexical, &toks, TOP, "Unit") {
        Ok(tree) => (&spec.syntactic, "Unit", false, tree),
        Err(_) => (
            &spec.all,
            "DocFence",
            true,
            parse(&spec.all, lexical, &toks, TOP, "DocFence")?,
        ),
    };
    let ring = (1..=TOP)
        .find(|&k| parse(g, lexical, &toks, k, start).is_ok())
        .expect("the fence parses at the full ring");
    let mut trees = Vec::new();
    add_holes(spec, &toks, &mut trees)?;
    trees.push(Parsed { tree, toks });
    let word = analyze(spec, &trees, table)
        .last()
        .map(|(k, w, _)| (*k, w.clone()));
    let most = text.split('\n').filter_map(label_of).max().unwrap_or(0);
    let label = (most != 0).then_some(most);
    let table_layer = word.as_ref().map_or(1, |w| w.0);
    Ok(FenceLayer {
        layer: ring.max(table_layer).max(most),
        ring,
        word,
        label,
        doc,
    })
}

/// The copy of the fences of the document at `path`.
fn render(path: &str, spec: &Spec, table: &WordTable) -> Result<String, String> {
    let name = base_name(path);
    let mut out = format!(
        "<!-- The `zed` fences of the spec's {name}, copied by the sync tool: do not edit. -->\n"
    );
    for f in zed_fences(path)? {
        let l = layer_of(&f.text, spec, table).map_err(|e| format!("{name}:{}: {e}", f.line))?;
        let word = l
            .word
            .map_or("none".to_string(), |(k, w)| format!("L{k} ({w})"));
        let label = l.label.map_or("none".to_string(), |k| format!("L{k}"));
        let doc = if l.doc {
            ", documentation notation"
        } else {
            ""
        };
        let (line, layer, ring, text) = (f.line, l.layer, l.ring, f.text);
        let (section, index) = (f.section, f.index);
        writeln!(
            out,
            "\n<!-- {name}:{line} layer L{layer}: ring L{ring}, word {word}, label {label}{doc}; \
             section [{section}] {index} -->\n```zed\n{text}\n```"
        )
        .expect("writing to a String");
    }
    Ok(out)
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let check = args.iter().any(|a| a == "--check");
    let rest: Vec<&String> = args.iter().filter(|a| *a != "--check").collect();
    let spec = Spec::open(rest.first().ok_or("usage: sync SPEC_DIR [--check]")?)?;
    sync_into(&spec, &format!("{}/zed", impl_root()), check, out)
}

/// The rows of the rejection table of DESIGN sec:diagnostics (step L1.29), one per line: each
/// row's first column up to any parenthesis, which is what a `// ✗ Row: …` comment names. A
/// document with no table gives no rows.
fn rejections(design: &str) -> String {
    let mut out = String::new();
    let rows = design
        .split('\n')
        .skip_while(|l| !l.starts_with("| Rejection |"))
        .skip(2)
        .take_while(|l| l.starts_with("| "));
    for row in rows {
        let first = row[2..].split(" | ").next().unwrap_or_default();
        let name = first.split('(').next().unwrap_or_default().trim();
        out.push_str(name);
        out.push('\n');
    }
    out
}

/// Copies from `spec` into `zed/fences` and `zed/grammar` under `zed`.
pub fn sync_into(spec: &Spec, zed: &str, check: bool, out: &mut String) -> Outcome {
    let table = WordTable::read(&spec.design)?;
    let root = &spec.root;
    let copies = [
        (
            format!("{zed}/fences/design.md"),
            render(&format!("{root}/DESIGN.md"), spec, &table)?,
        ),
        (
            format!("{zed}/fences/examples.md"),
            render(&format!("{root}/EXAMPLES.md"), spec, &table)?,
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
            format!("{}\n", fence_texts(&spec.design, "desugar")?.join("\n")),
        ),
        (
            format!("{zed}/fences/rejections.txt"),
            rejections(&read_text(&spec.design)?),
        ),
    ];
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

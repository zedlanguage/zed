//! The `zed` fences of a document, each with its layer (step L1.7), and the row names of the
//! rejection table (step L1.29), read from the spec in place. The tests read DESIGN.md and
//! EXAMPLES.md this way, and this repository's README.md against the spec's grammar (item
//! README-fences); no copy of either is kept in this repository.
//!
//! The layer is computed as the M0.4 layer checker computes a corpus program's: the lowest ring
//! at which the fence parses (as a `Unit`, or else under the documentation notation), raised to
//! the layer of any defined word it uses (the table of sec:grammar) and to a `// layer Lk`
//! label.

use zedc::parse::TOP;

use crate::layer::{Parsed, WordTable, add_holes, analyze, label_at};
use crate::spec::{Fence, Spec, zed_fences};
use crate::syntax::{lex, parse};
use crate::text::base_name;

/// The layer named by a `// layer Lk` line. A fence's label may be on any line, since its first
/// line is usually its `// [d4]` header; the layer checker reads only a program's first line.
fn label_of(line: &str) -> Option<u32> {
    label_at(line.trim_start_matches(zedc::parse::is_space))
}

/// A fence with its layer and how it parses.
#[derive(Clone, Debug)]
pub struct LaidFence {
    /// The fence.
    pub fence: Fence,
    /// The layer from which it is parsed, checked and run.
    pub layer: u32,
    /// The lowest ring of sec:grammar at which it parses.
    pub ring: u32,
    /// Whether it parses only under the documentation notation.
    pub notation: bool,
}

/// The layer of the fence `text`, its lowest ring, and whether it needs the documentation
/// notation.
fn layer_of(text: &str, spec: &Spec, table: &WordTable) -> Result<(u32, u32, bool), String> {
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
        .map_or(1, |(k, _, _)| *k);
    let label = text.split('\n').filter_map(label_of).max().unwrap_or(0);
    Ok((ring.max(word).max(label), ring, doc))
}

/// The `zed` fences of the document at `path`, in order, each with its layer against `spec`.
/// O(F · (TOP + 1) parses) for F fences.
pub fn of_document(path: &str, spec: &Spec) -> Result<Vec<LaidFence>, String> {
    let table = WordTable::read(&spec.design)?;
    let name = base_name(path);
    zed_fences(path)?
        .into_iter()
        .map(|fence| {
            let (layer, ring, notation) = layer_of(&fence.text, spec, &table)
                .map_err(|e| format!("{name}:{}: {e}", fence.line))?;
            Ok(LaidFence {
                fence,
                layer,
                ring,
                notation,
            })
        })
        .collect()
}

/// The rows of the rejection table of DESIGN sec:diagnostics (step L1.29) in the document
/// `design`, in order: each row's first column up to its first parenthesis outside a code span,
/// which is what a `// ✗ Row: …` comment names: the gloss in parentheses after a name is
/// dropped, and a call in code, as in ``Stack depth over `@stack(bytes: b)` ``, is kept whole. A
/// document with no table gives no rows. One pass over `design`.
pub fn rejection_rows(design: &str) -> Vec<String> {
    design
        .split('\n')
        .skip_while(|l| !l.starts_with("| Rejection |"))
        .skip(2)
        .take_while(|l| l.starts_with("| "))
        .map(|row| {
            let first = row[2..].split(" | ").next().unwrap_or_default();
            let mut code = false;
            let end = first.find(|c| {
                code ^= c == '`';
                c == '(' && !code
            });
            // A table cell writes `|` as `\|`; the row's name is the text a reader sees.
            first[..end.unwrap_or(first.len())]
                .trim()
                .replace("\\|", "|")
        })
        .collect()
}

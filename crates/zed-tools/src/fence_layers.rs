//! The `zed` fences of a document, each with its layer (step L1.7), and the row names of the
//! rejection table (step L1.29). The `sync` tool lays out the spec's DESIGN.md and EXAMPLES.md
//! this way into `zed/fences/`, and the tests lay out this repository's README.md against this
//! repository's own grammar ([`Spec::of_impl`], item README-fences).
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
    /// The layer from which it is parsed, checked and run: the most of `ring`, the layer of
    /// `word` and `label`.
    pub layer: u32,
    /// The lowest ring of sec:grammar at which it parses.
    pub ring: u32,
    /// The defined word of the latest layer it uses, with that layer, if it uses one.
    pub word: Option<(u32, String)>,
    /// The layer its `// layer Lk` lines name, the latest if several do.
    pub label: Option<u32>,
    /// Whether it parses only under the documentation notation.
    pub notation: bool,
}

/// The fence `fence` laid out against `spec` and the words of `table`.
fn lay(fence: Fence, spec: &Spec, table: &WordTable) -> Result<LaidFence, String> {
    let lexical = &spec.lexical;
    let toks = lex(lexical, &fence.text.replace('…', "elided"))?;
    let (g, start, notation, tree) = match parse(&spec.syntactic, lexical, &toks, TOP, "Unit") {
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
    let label = fence.text.split('\n').filter_map(label_of).max();
    let layer = ring
        .max(word.as_ref().map_or(1, |w| w.0))
        .max(label.unwrap_or(0));
    Ok(LaidFence {
        fence,
        layer,
        ring,
        word,
        label,
        notation,
    })
}

/// The `zed` fences of the document at `path`, in order, each with its layer against `spec`.
/// O(F · (TOP + 1) parses) for F fences.
pub fn of_document(path: &str, spec: &Spec) -> Result<Vec<LaidFence>, String> {
    let table = WordTable::read(&spec.design)?;
    let name = base_name(path);
    zed_fences(path)?
        .into_iter()
        .map(|fence| {
            let line = fence.line;
            lay(fence, spec, &table).map_err(|e| format!("{name}:{line}: {e}"))
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

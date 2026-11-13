//! The front end of one unit's text (steps L1.29, L1.38 and L2.3): lexing through elaboration
//! and the linear questions (`compile`), the statements and imports of a unit read alone
//! (`parse_unit`), and the diagnostics they give, placed in the source. The queries
//! (`crate::query`) memoize both, and the package loader (`crate::unit`) and the commands
//! (`crate::run`) read them through the queries, so this file is below all three.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::sync::Arc;

use zed_kernel::{Shared, Term};

use crate::address::ContentAddress;
use crate::ast::{self, Error, Stmt, StmtKind};
use crate::elab::{Unit, elaborate_text};
use crate::lex::{self, Span};
use crate::parse::TOP;
use crate::resolve::{self, Alone};
use crate::suppress::{self, Severity};
use crate::terminal::Escaped;
use crate::work::{self, Stage};
use crate::{docs, interp, source, terminal};

/// The front end's result: the statements, elaboration and placed warnings, or the first
/// rejecting phase's diagnostics. The elaboration is shared, so a program made from it
/// (`run::program`) holds the same unit.
pub type Front = Result<(Vec<Stmt>, Arc<Unit>, Vec<Diagnostic>), Vec<Diagnostic>>;

/// A unit's statements that parse and its imports, each with the unit it names, the statement's
/// text and the content address it is pinned to, if written (step L2.8), in text order, and its
/// declarations that do not parse (step L1.29d); or the errors of lexing, or of building the
/// statements, with the syntax errors.
pub type Parsed = Result<(Vec<Stmt>, Vec<Imported>, Broken), Vec<ast::Error>>;

/// An import statement of a unit: the unit it names, the statement's text, its `;` included,
/// and the content address it is pinned to, if written.
pub type Imported = (Arc<str>, Span, Option<ContentAddress>);

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
    /// The menu of fixes, written after the steps: its heading line, then each fix on a line
    /// of its own, every line starting with a newline. Empty when it has none.
    pub menu: String,
    /// The row of the rejection table (DESIGN.md sec:diagnostics) it is a case of, if any.
    pub row: Option<crate::rejection::Row>,
    /// The part of its address that the unit's text decides, the same on every run of the same
    /// text; the address printed and suppressed joins it with the file's part
    /// ([`crate::suppress::InFile::address`]).
    pub address: ContentAddress,
}

/// One step of a derivation, placed in the source.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Step {
    /// The line.
    pub line: usize,
    /// The column, counted in characters.
    pub col: usize,
    /// What holds there.
    pub text: String,
    /// The source line, one copy shared by every step on it.
    pub source: Arc<str>,
    /// How many characters of the source line the step covers, at least 1.
    pub width: usize,
}

impl std::fmt::Display for Diagnostic {
    /// The message on one line; then each step numbered; then the menu of fixes. The first
    /// step on a line is followed by that line, shown once for all the steps of the diagnostic
    /// on it (`shown`), with the text each covers marked below it (`layout`, `draw`); a step
    /// that `layout` leaves undrawn is given by its range, `3:11 to 3:19`, instead. Each line
    /// of the source is shown once and each row under it is at most as long as it and the
    /// numbers in the row, so k steps on one line of L characters print O(k log k + L·r)
    /// characters, r the rows under it (`layout` bounds r), not O(k·L). A listing of several
    /// diagnostics shows each line once over all of them ([`Quoted`]).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.write(f, &HashSet::new())
    }
}

/// The source lines a listing of diagnostics of one file has shown, so that it shows each line
/// once: the first diagnostic with a step on a line shows the line, with its marks, as
/// [`Diagnostic`]'s `Display` does, and each later diagnostic gives its steps on that line by
/// their ranges, `1:20 to 1:52`, under the note that the line is shown above. A diagnostic
/// shown first, or alone, prints as `Display` prints it.
#[derive(Default)]
pub struct Quoted {
    /// The lines shown, each by its number.
    lines: HashSet<usize>,
}

impl Quoted {
    /// `d` as the listing prints it after the diagnostics shown so far; its lines count as
    /// shown from now on. O(L + s log s) for the s steps of `d` and the L characters of the
    /// lines it shows first, O(s) for steps on lines shown before.
    //
    // Complexity tradeoff: the naive listing prints each diagnostic as `Display` does, the
    // whole line under every one, so n diagnostics on one line of L characters print O(n·L)
    // characters, Θ(n²) when each error is one of n parts of the line (a `sum` of n untracked
    // components gives about 3n errors on a line of about 5n characters). A window of the
    // line around each diagnostic's marks is no better, since the marked stretches themselves
    // grow with n (the k-th `+` of a sum covers its first k components). This shows each line
    // once per listing, so the listing prints O(L + S) characters for S steps in all, and
    // lays out no line twice. The cost: a later diagnostic on a shown line is not readable
    // without the earlier one's quote, so its steps carry their ranges; a single diagnostic
    // and the first on each line print as before (COMPLEXITY.md RENDER-line-per-error).
    pub fn show(&mut self, d: &Diagnostic) -> String {
        let text = Shown(d, &self.lines).to_string();
        self.lines.extend(d.steps.iter().map(|s| s.line));
        text
    }
}

/// A diagnostic written with the lines `.1` already shown above it.
struct Shown<'a>(&'a Diagnostic, &'a HashSet<usize>);

impl std::fmt::Display for Shown<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.write(f, self.1)
    }
}

impl Diagnostic {
    /// Writes the diagnostic as `Display` does, except that each step on a line of `above` is
    /// given by its range, and the line is not shown again: in its place, after the first step
    /// on it, a note says it is shown above.
    fn write(&self, f: &mut std::fmt::Formatter<'_>, above: &HashSet<usize>) -> std::fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.col, Escaped(&self.message))?;
        let gutter = self
            .steps
            .iter()
            .map(|s| s.line.to_string().len())
            .max()
            .unwrap_or(0);
        let number = self.steps.len().to_string().len();
        let pad = " ".repeat(number + 4);
        let margin = format!("\n{pad} {:>gutter$} | ", "");
        // The numbers of the steps on each line, in order.
        let mut on: HashMap<usize, Vec<usize>> = HashMap::new();
        for (i, s) in self.steps.iter().enumerate() {
            on.entry(s.line).or_default().push(i + 1);
        }
        // How each line is drawn, worked out before any step is written, since a step given by
        // its range may come before the line is shown. A line shown above is not drawn, and
        // each of its steps is given by its range.
        let mut ranged = vec![false; self.steps.len()];
        let mut drawn: HashMap<usize, Layout> = HashMap::new();
        for (&line, here) in &on {
            if above.contains(&line) {
                for &n in here {
                    ranged[n - 1] = true;
                }
            } else {
                let l = layout(&self.steps[here[0] - 1].source, &self.steps, here);
                for &n in &l.ranged {
                    ranged[n - 1] = true;
                }
                drawn.insert(line, l);
            }
        }
        for (i, s) in self.steps.iter().enumerate() {
            let n = format!("[{}]", i + 1);
            write!(f, "\n  {n:<w$} {}:{}", s.line, s.col, w = number + 2)?;
            if ranged[i] {
                write!(f, " to {}:{}", s.line, s.col + s.width.max(1) - 1)?;
            }
            write!(f, ": {}", Escaped(&s.text))?;
            if let Some(here) = on.get(&s.line)
                && here[0] == i + 1
            {
                if let Some(l) = drawn.get(&s.line) {
                    write!(f, "\n{pad} {:>gutter$} | {}", s.line, l.text)?;
                    draw(f, &margin, l)?;
                } else {
                    write!(f, "\n{pad} line {} is shown above", s.line)?;
                }
            }
        }
        write!(f, "{}", Escaped(&self.menu))
    }
}

/// The line `source` as a diagnostic quotes it, each tab shown as four spaces so that every
/// character has a known column, each other character a terminal would not show as itself
/// ([`terminal::hidden`]: an ESC, a NUL, a lone CR, U+202E) in its escape form `\u{1B}`, and the
/// column, counted from 0, at which each character starts, then the column after the line. A
/// character takes as many columns as it does on a terminal: none for a combining mark, two for a
/// wide character, and an escaped one the columns of its escape. O(L) for L characters.
fn shown(source: &str) -> (String, Vec<usize>) {
    use unicode_width::UnicodeWidthChar;
    let mut text = String::with_capacity(source.len());
    let mut at = Vec::with_capacity(source.len() + 1);
    let mut column = 0;
    for c in source.chars() {
        at.push(column);
        if c == '\t' {
            text.push_str("    ");
            column += 4;
        } else if terminal::hidden(c) {
            terminal::escape(c, &mut text).expect("writing to a String cannot fail");
            column += terminal::escape_width(c);
        } else {
            text.push(c);
            column += c.width().unwrap_or(0);
        }
    }
    at.push(column);
    (text, at)
}

/// How the steps on one source line are drawn under it (`layout`).
struct Layout {
    /// The line as quoted (`shown`).
    text: String,
    /// The stretches underlined in full, in the order of their first columns: the first column,
    /// the columns, and the numbers after the underline (` [2, 5]`, or nothing when the line has
    /// one stretch).
    full: Vec<(usize, usize, String)>,
    /// Each chain of nested stretches drawn by their ends, in the order of their first columns:
    /// the chain's carets in column order, each its column and the numbers written for it
    /// (`[4]`, or nothing).
    rulers: Vec<Vec<(usize, String)>>,
    /// The numbers of the steps given by their range instead of a mark.
    ranged: Vec<usize>,
}

/// A stretch of a line that one or more steps cover.
struct Stretch {
    /// Its first character, counted from 0.
    start: usize,
    /// Its length in characters, at least 1.
    width: usize,
    /// The numbers of the steps that cover it, increasing.
    numbers: Vec<usize>,
}

/// How the steps numbered `numbers` (counted from 1 in `steps`), all on the line `source`, are
/// drawn under it. Steps that cover the same text share one stretch. The stretches that nest
/// form a forest, each stretch's parent the least stretch that holds it. A child holding more
/// than half of its parent's stretches (itself and those it holds) is its parent's heavy child;
/// a parent has at most one. A heavy child that has a heavy child of its own is drawn by its
/// ends, on a rule with a caret under its first and its last column; each chain of such
/// stretches, one the heavy child of the next, shares one rule. Every other stretch is
/// underlined in full. A stretch that overlaps an earlier one without either holding the other
/// is not drawn, nor is a chain whose stretches share neither their first nor their last
/// column; their steps are given by their range (`ranged`). O(s log s) for s steps.
fn layout(source: &str, steps: &[Step], numbers: &[usize]) -> Layout {
    let (text, at) = shown(source);
    let end = at.len() - 1;
    let column = |i: usize| at.get(i).copied().unwrap_or_else(|| at[end] + i - end);
    // A stretch's first column and the column after it. A stretch past the end of the line gets
    // a column for each character it lacks; one on combining marks alone is marked under the
    // character they combine with.
    let columns = |s: &Stretch| match (column(s.start), column(s.start + s.width)) {
        (from, to) if to > from => (from, to),
        (from, _) => (from.saturating_sub(1), from.max(1)),
    };
    let mut spans: Vec<(usize, usize, usize)> = numbers
        .iter()
        .map(|&n| {
            let s = &steps[n - 1];
            (s.col - 1, s.width.max(1), n)
        })
        .collect();
    spans.sort_unstable();
    // In the order of their first characters, the shorter first.
    let mut covered: Vec<Stretch> = Vec::new();
    for (start, width, n) in spans {
        match covered.last_mut() {
            Some(s) if (s.start, s.width) == (start, width) => s.numbers.push(n),
            _ => covered.push(Stretch {
                start,
                width,
                numbers: vec![n],
            }),
        }
    }
    let labeled = covered.len() > 1;
    let list = |ns: &[usize]| {
        let ns: Vec<String> = ns.iter().map(usize::to_string).collect();
        format!("[{}]", ns.join(", "))
    };
    // The forest: each stretch is met after every stretch that holds it (first characters
    // increasing, the longer first), and the stretches still open when it is met form a chain,
    // each holding the next.
    let m = covered.len();
    let mut order: Vec<usize> = (0..m).collect();
    order.sort_unstable_by_key(|&k| (covered[k].start, Reverse(covered[k].width)));
    let after = |k: usize| covered[k].start + covered[k].width;
    let mut parent: Vec<Option<usize>> = vec![None; m];
    let mut crossing = vec![false; m];
    let mut placed = Vec::with_capacity(m);
    let mut open: Vec<usize> = Vec::new();
    for &k in &order {
        while open.last().is_some_and(|&o| after(o) <= covered[k].start) {
            open.pop();
        }
        match open.last() {
            Some(&o) if after(o) < after(k) => crossing[k] = true,
            top => {
                parent[k] = top.copied();
                open.push(k);
                placed.push(k);
            }
        }
    }
    // Each stretch's size, itself and the stretches it holds, summed from the last met.
    let mut size = vec![1usize; m];
    for &k in placed.iter().rev() {
        if let Some(p) = parent[k] {
            size[p] += size[k];
        }
    }
    let mut heavy: Vec<Option<usize>> = vec![None; m];
    for &k in &placed {
        if let Some(p) = parent[k]
            && 2 * size[k] > size[p]
        {
            heavy[p] = Some(k);
        }
    }
    let by_ends: Vec<bool> = (0..m)
        .map(|k| heavy[k].is_some() && parent[k].is_some_and(|p| heavy[p] == Some(k)))
        .collect();
    // Complexity tradeoff: a stretch nested in a chain of heavy children is drawn by its ends,
    // not underlined in full. What is given up: such a step's text is not marked under each of
    // its characters, only under its first and last on a rule it shares with the rest of its
    // chain, and a step whose text overlaps another's without either holding the other, or one
    // on a chain whose stretches share neither a first nor a last column (`f(g(h(x)))`), gets
    // no mark at all, only its range in its step line. Why: underlines that nest cannot share a row,
    // so a line whose steps nest d deep, such as a sum `a0 + a1 + … + an` whose every partial
    // sum is a step, would print d rows of up to L columns, O(d·L), quadratic when d grows with
    // L; any layout that draws each nested extent as one connected mark needs as many rows, so
    // the chain's extents must be split into ends. Which stretches: those on a chain of heavy
    // children, except its top and its bottom, decided by how the stretches nest, never by a
    // length. The bound: the stretches underlined in full that hold one column are, from the
    // outermost, roots, light children (each at most half its parent, so at most log₂ s of them)
    // and the bottoms of heavy chains (one per light child or root), so at most 2·log₂ s + 2;
    // the rules over one column likewise; overlapping stretches are left out, so the rest nest.
    // Rows are therefore O(log s) plus the rows that step numbers need beside each other, and a
    // line costs O((s + L) log s). A balanced nesting, such as `(a + b) * (c + d)` repeated, is
    // underlined in full and reaches that log factor. Tested by `l01_29_diagnostics::layout`
    // (COMPLEXITY.md MSG-line-quote-nested). A complete solution, every nested stretch in full
    // at O(s + L), is impossible by the row argument above.
    let mut full = Vec::new();
    let mut ranged = Vec::new();
    for (k, s) in covered.iter().enumerate() {
        if crossing[k] {
            ranged.extend_from_slice(&s.numbers);
        } else if !by_ends[k] {
            let (from, to) = columns(s);
            let label = if labeled {
                format!(" {}", list(&s.numbers))
            } else {
                String::new()
            };
            full.push((from, to - from, label));
        }
    }
    let mut rulers = Vec::new();
    for &k in &placed {
        if !by_ends[k] || parent[k].is_some_and(|p| by_ends[p]) {
            continue;
        }
        // The chain from its outermost stretch inward.
        let mut chain = vec![k];
        while let Some(c) = heavy[chain[chain.len() - 1]].filter(|&c| by_ends[c]) {
            chain.push(c);
        }
        let ends: Vec<(usize, usize)> = chain
            .iter()
            .map(|&c| {
                let (from, to) = columns(&covered[c]);
                (from, to - 1)
            })
            .collect();
        // Where every stretch of the chain starts at one column, that caret needs no numbers and
        // each step's numbers stand under the caret where it ends; where every one ends at one
        // column, the other way round. Where neither holds, a reader would have to pair each
        // first caret with its last one, so the chain's steps are given by their range instead.
        let one_start = ends.iter().all(|e| e.0 == ends[0].0);
        let one_end = !one_start && ends.iter().all(|e| e.1 == ends[0].1);
        if !one_start && !one_end {
            for &c in &chain {
                ranged.extend_from_slice(&covered[c].numbers);
            }
            continue;
        }
        // The first columns increase inward and the last columns outward, and the innermost
        // starts no later than it ends, so these are in column order.
        let carets = chain
            .iter()
            .zip(&ends)
            .map(|(&c, e)| (e.0, c, one_start))
            .chain(
                chain
                    .iter()
                    .zip(&ends)
                    .rev()
                    .map(|(&c, e)| (e.1, c, one_end)),
            );
        let mut ticks: Vec<(usize, Vec<usize>)> = Vec::new();
        for (col, c, bare) in carets {
            if ticks.last().is_none_or(|t| t.0 != col) {
                ticks.push((col, Vec::new()));
            }
            if !bare && let Some(t) = ticks.last_mut() {
                t.1.extend_from_slice(&covered[c].numbers);
            }
        }
        rulers.push(
            ticks
                .into_iter()
                .map(|(col, mut ns)| {
                    ns.sort_unstable();
                    ns.dedup();
                    let label = if ns.is_empty() {
                        String::new()
                    } else {
                        list(&ns)
                    };
                    (col, label)
                })
                .collect(),
        );
    }
    Layout {
        text,
        full,
        rulers,
        ranged,
    }
}

/// The rows that items placed from their first columns take, each item a first column and the
/// first column after it that another item on its row may use: an item goes on the row whose
/// last item ends first, if that is free at its column, else on a new row (interval
/// partitioning, as few rows as the most items over one column). The items come in the order
/// of their first columns. O(i log i) for i items.
///
/// Complexity tradeoff: naive version, each item tried against every row in turn, O(i·r) for
/// r rows, up to O(i²) when steps nest as deep as they are many; before MSG-line-quote-cost a
/// line was quoted again for each step on it, O(s·L) bytes. Used: the rows in a min-heap by
/// their first free column, O(i log i), with as few rows as the most items over one column.
/// Tradeoffs: none in the output's row count; the heap's memory, O(r). COMPLEXITY.md row
/// MSG-line-quote-cost (its nested case: the tradeoff in [`layout`]).
fn rows(items: impl Iterator<Item = (usize, usize)>) -> Vec<Vec<usize>> {
    let mut rows: Vec<Vec<usize>> = Vec::new();
    // Each row by the first column free after its last item.
    let mut free: BinaryHeap<Reverse<(usize, usize)>> = BinaryHeap::new();
    for (k, (from, after)) in items.enumerate() {
        let row = match free.peek() {
            Some(&Reverse((at, row))) if at <= from => {
                free.pop();
                row
            }
            _ => {
                rows.push(Vec::new());
                rows.len() - 1
            }
        };
        rows[row].push(k);
        free.push(Reverse((after, row)));
    }
    rows
}

/// Writes, each row after `margin`, the marks of `l`. First the underlines, each followed by
/// its numbers and one column clear of the next. Then the rules of the chains drawn by their
/// ends: a caret under the first and last column of each stretch in the chain, joined by `-`,
/// the numbers of the last caret after it; the numbers of the other carets go on the rows below
/// the rule, each starting under its caret. O(C) for C characters written, after the
/// partitioning (`rows`).
fn draw(f: &mut std::fmt::Formatter<'_>, margin: &str, l: &Layout) -> std::fmt::Result {
    let full = rows(
        l.full
            .iter()
            .map(|(from, width, label)| (*from, from + width + label.len() + 1)),
    );
    for row in &full {
        f.write_str(margin)?;
        let mut done = 0;
        for &k in row {
            let (from, width, label) = &l.full[k];
            repeat(f, ' ', from - done)?;
            repeat(f, '^', *width)?;
            f.write_str(label)?;
            done = from + width + label.len();
        }
    }
    // The numbers after a rule's last caret, with the space before them.
    let last = |ticks: &[(usize, String)]| match ticks.last() {
        Some((_, label)) if !label.is_empty() => format!(" {label}"),
        _ => String::new(),
    };
    let rules = rows(l.rulers.iter().map(|ticks| {
        let (first, end) = (ticks[0].0, ticks[ticks.len() - 1].0);
        (first, end + 1 + last(ticks).len() + 1)
    }));
    for row in &rules {
        f.write_str(margin)?;
        let mut done = 0;
        // The numbers of the carets other than the last, in column order.
        let mut below: Vec<(usize, &str)> = Vec::new();
        for &k in row {
            let ticks = &l.rulers[k];
            for (j, (col, label)) in ticks.iter().enumerate() {
                if j == 0 {
                    repeat(f, ' ', col - done)?;
                } else {
                    repeat(f, '-', col - done)?;
                }
                f.write_str("^")?;
                done = col + 1;
                if j + 1 < ticks.len() && !label.is_empty() {
                    below.push((*col, label));
                }
            }
            let tail = last(ticks);
            f.write_str(&tail)?;
            done += tail.len();
        }
        for under in rows(
            below
                .iter()
                .map(|(col, label)| (*col, col + label.len() + 1)),
        ) {
            f.write_str(margin)?;
            let mut done = 0;
            for k in under {
                let (col, label) = below[k];
                repeat(f, ' ', col - done)?;
                f.write_str(label)?;
                done = col + label.len();
            }
        }
    }
    Ok(())
}

/// A unit's syntax: its tokens, its doc comments and its statements.
pub(crate) type Syntax = (Vec<lex::Token>, Vec<lex::Doc>, Vec<Stmt>);

/// The declarations of a unit that did not parse (step L1.29d): the syntax error of each, and
/// the names they would define, had they parsed.
#[derive(Default, Debug)]
pub struct Broken {
    /// The syntax errors, in the order of the text.
    pub errors: Vec<ast::Error>,
    /// The names.
    pub defines: HashSet<String>,
}

/// The tokens of the unit `text`, whose lines are `lines`, its doc comments and its statements;
/// or the diagnostics of the phases of its syntax that reject it: lexing, parsing, where each
/// declaration that does not parse has its error (a `with` clause that gives a sentinel value
/// is placed with its statement and its repairs), and building the statements (every item's
/// error). `zedc fmt` reads only it, and `compile` starts as it does, so `zedc run`, `zedc
/// build`, `zedc test` and `zedc fmt` print a file's syntax errors alike.
pub(crate) fn syntax(text: &str, lines: &source::Lines) -> Result<Syntax, Vec<Diagnostic>> {
    let (syntax, broken) =
        recovered(text).map_err(|e| placed(text, lines, &[], Severity::Rejection, e))?;
    if broken.errors.is_empty() {
        return Ok(syntax);
    }
    Err(placed(text, lines, &[], Severity::Rejection, broken.errors))
}

/// The syntax of the unit `text` as [`syntax`] reads it, and the declarations that did not
/// parse, which the statements leave out; or the errors of lexing, or of building the
/// statements that parse, with the syntax errors.
fn recovered(text: &str) -> Result<(Syntax, Broken), Vec<ast::Error>> {
    let (tokens, docs) = work::stage(Stage::Lex, None, || lex::lex_with_docs(text))
        .map_err(|e| vec![lex_error(text, e)])?;
    let (tree, failed) = work::stage(Stage::Parse, None, || {
        crate::parse::parse_unit(text, &tokens, TOP)
    });
    let built = work::stage(Stage::Syntax, None, || built(text, &tokens, &tree, failed));
    let (stmts, broken) = built?;
    Ok(((tokens, docs, stmts), broken))
}

/// The statements of the unit `text` built from its tokens `tokens` and its tree `tree`, and
/// its declarations that `failed` holds, which do not parse ([`Broken`]); or the errors of
/// building the statements, with the syntax errors, in text order.
fn built(
    text: &str,
    tokens: &[lex::Token],
    tree: &crate::parse::Tree,
    failed: Vec<crate::parse::Error>,
) -> Result<(Vec<Stmt>, Broken), Vec<ast::Error>> {
    let defines = failed
        .iter()
        .flat_map(|e| e.recovery.defines.iter().cloned())
        .collect();
    let errors: Vec<ast::Error> = failed
        .into_iter()
        .map(|e| ast::Error::of_parse(text, e))
        .collect();
    match ast::unit_all_errors(text, tokens, tree) {
        Ok(stmts) => Ok((stmts, Broken { errors, defines })),
        Err(mut built) => {
            built.extend(errors);
            built.sort_by_key(|e| e.span);
            Err(built)
        }
    }
}

/// The lexical error `e` of `text` as an error of the source. The ASCII name it may offer for a
/// word beyond ASCII is no prelude name either, which the lexer does not know.
fn lex_error(text: &str, mut e: lex::Error) -> Error {
    e.avoid_names(text, &resolve::is_prelude_name);
    e.into()
}

/// Why a file's unit was not read: what `zedc run`, `zedc build` and `zedc fmt` print for it,
/// through [`Unloaded::report`].
pub enum Unloaded {
    /// The diagnostics of the phase that rejected it; for `zedc run` and `zedc build`, also
    /// the refusal of a unit that is not a program's.
    Rejected(Vec<Diagnostic>),
    /// Why it was refused where no diagnostic is placed: its bytes are not a source.
    Refused(String),
}

impl Unloaded {
    /// What zedc prints for it: the refusal, or each diagnostic, its derivation and its menu of
    /// fixes, then what `after` gives for it (the address line of `--addresses`), one after
    /// the other on lines of their own; each after `file` and a colon when `file` is given.
    /// Each source line is shown once over all the diagnostics ([`Quoted`]).
    pub fn report(
        &self,
        file: Option<&str>,
        mut after: impl FnMut(&Diagnostic) -> String,
    ) -> String {
        let place = file.map_or_else(String::new, |f| format!("{f}:"));
        match self {
            Unloaded::Refused(why) => format!("{place}{}", Escaped(why)),
            Unloaded::Rejected(ds) => {
                let mut quoted = Quoted::default();
                let lines: Vec<String> = ds
                    .iter()
                    .map(|d| format!("{place}{}{}", quoted.show(d), after(d)))
                    .collect();
                lines.join("\n")
            }
        }
    }
}

/// The statements, elaboration and warnings of the unit `text` built for `build`, the warnings
/// moved out of the elaboration and placed in the source, or the diagnostics of the first phase
/// that rejects it. The statements are those of `text` with each read of the build replaced by
/// the literal it reads ([`crate::build::read`]).
///
/// A unit with syntax errors is rejected with them, and the declarations that parse are
/// checked as well, but for those that use a name a declaration that did not parse would
/// define, and those that use theirs ([`without_broken`]): its diagnostics are the syntax
/// errors and those of the first phase that rejects the rest, each once, in the order of the
/// text (step L1.29d).
pub(crate) fn compile(text: &str, build: &crate::build::Build) -> Front {
    let lines = source::Lines::new(text.as_bytes());
    match unplaced(text, build) {
        Ok((stmts, mut unit)) => {
            let warnings = std::mem::take(&mut unit.warnings);
            let warnings = placed(text, &lines, &stmts, Severity::Warning, warnings);
            Ok((stmts, Arc::new(unit), warnings))
        }
        Err((stmts, errors)) => Err(placed(text, &lines, &stmts, Severity::Rejection, errors)),
    }
}

/// The errors [`compile`] rejects the unit `text` with, built for `build`, before they are
/// placed: what a package build reports of a unit that compiles alone (step L1.29d), placed
/// there with the unit's other problems. Empty when the unit compiles.
pub(crate) fn rejection(text: &str, build: &crate::build::Build) -> Vec<ast::Error> {
    unplaced(text, build)
        .err()
        .map_or_else(Vec::new, |(_, e)| e)
}

/// [`compile`] before its diagnostics are placed: the statements checked and the elaboration,
/// or the statements the errors are placed among and the errors.
fn unplaced(text: &str, build: &crate::build::Build) -> Checked {
    let ((tokens, docs, stmts), broken) = recovered(text).map_err(|e| (Vec::new(), e))?;
    if broken.errors.is_empty() {
        return checked(text, &tokens, &docs, stmts, build);
    }
    let stmts = without_broken(text, stmts, &broken.defines);
    let mut errors = broken.errors;
    // A syntax error lies in no statement that parses, so the statements checked place
    // every error as they place the rest. A stable sort, in the order of the text.
    let stmts = match checked(text, &tokens, &docs, stmts, build) {
        Ok((stmts, _)) => stmts,
        Err((stmts, rest)) => {
            errors.extend(rest);
            stmts
        }
    };
    errors.sort_by_key(|e| e.span.start);
    Err((stmts, errors))
}

/// The statements of a unit checked and its elaboration, or the statements its errors are
/// placed among and the errors, in the order they are reported.
type Checked = Result<(Vec<Stmt>, Unit), (Vec<Stmt>, Vec<ast::Error>)>;

/// The statements of a unit `text` with syntax errors that its checking reads: `stmts`, those
/// that parse, but for those [`dropped`] leaves out. A use of a name in `broken` that nothing
/// defines so gets no error: its declaration has one (step L1.29d).
fn without_broken(text: &str, stmts: Vec<Stmt>, broken: &HashSet<String>) -> Vec<Stmt> {
    let resolved = work::stage(Stage::Resolve, None, || {
        resolve::resolve_in_text(&stmts, &Alone, Some(text))
    });
    let dropped = dropped(text, &stmts, &resolved, broken);
    stmts
        .into_iter()
        .zip(dropped)
        .filter_map(|(s, d)| (!d).then_some(s))
        .collect()
}

/// The resolution of the unit `text` in its package, whose statements that parse are `stmts`,
/// whose declarations that do not parse would define the names `broken`, and which reads the
/// other units through `units`: of the statements [`dropped`] keeps, its exports holding as
/// broken the names `broken` and those the statements left out define, which the unit then does
/// not define, so its importers leave out the statements that use them (step L1.29d). A unit
/// with no such name, and none from the units it reads, is resolved once, as before.
// Complexity tradeoff: dropping a statement and resolving again until no further name is lost
// costs O(r·d) for a resolution of cost r and a chain of d statements. Here a unit with a
// broken name is resolved twice, once to find every statement to leave out ([`dropped`]) and
// once over the rest, O(r), and the names its exports lose are found by one lookup each,
// O(x log x) for x exports. A unit with none is resolved once.
pub(crate) fn resolve_recovered(
    text: &str,
    stmts: &[Stmt],
    broken: &HashSet<String>,
    units: &dyn resolve::Units,
) -> resolve::Resolved {
    let all = resolve::resolve_in_text(stmts, units, Some(text));
    if broken.is_empty() && all.res.broken.is_empty() {
        return all;
    }
    let keep: Vec<bool> = dropped(text, stmts, &all, broken)
        .into_iter()
        .map(|d| !d)
        .collect();
    let mut r = resolve::resolve_kept(stmts, Some(&keep), units, Some(text));
    let lost: Vec<String> = (all.res.exports.names())
        .filter(|n| r.res.exports.get(n).is_none())
        .map(String::from)
        .collect();
    r.res.exports.set_broken(broken.iter().cloned().chain(lost));
    r
}

/// Which of `stmts`, the statements that parse of a unit `text` whose resolution is `resolved`,
/// are left out of its checking: each top-level statement that uses a name in `broken`, which
/// a declaration that did not parse would define, or a name an imported unit would define but
/// for its syntax errors ([`resolve::Resolution::broken`]), and each that uses a name one of
/// those defines, at any distance (step L1.29d).
// Complexity tradeoff: dropping the statements with an unresolved use and resolving the rest
// again until no new name goes unresolved is O(n·d) for n statements and a chain of d
// statements each using the one before, O(n²) for a chain through the unit. Here one
// resolution finds every use; each use across statements is listed under its name, and a
// search from the statements with a broken use drops each statement once and reads each
// listed use once, O((n + b + u) log n) for b binders and u uses, then one more resolution.
fn dropped(
    text: &str,
    stmts: &[Stmt],
    resolved: &resolve::Resolved,
    broken: &HashSet<String>,
) -> Vec<bool> {
    let resolve::Resolved { res, errors, .. } = resolved;
    // The statement whose text holds position `at`, by the statements' starts in text order.
    let mut by_start: Vec<(usize, usize, usize)> = stmts
        .iter()
        .enumerate()
        .map(|(i, s)| (s.span.start, s.span.end, i))
        .collect();
    by_start.sort_unstable();
    let owner = |at: usize| {
        let k = by_start.partition_point(|&(start, _, _)| start <= at);
        let (_, end, i) = *by_start.get(k.checked_sub(1)?)?;
        (at < end).then_some(i)
    };
    let mut dropped = vec![false; stmts.len()];
    let mut work = Vec::new();
    let unresolved = errors.iter().filter_map(|e| {
        let name = &text[e.span.start..e.span.end];
        let undefined =
            e.message == resolve::undefined(name) || e.message == resolve::undefined_type(name);
        (undefined && broken.contains(name)).then_some(e.span.start)
    });
    let imported = res.broken.iter().map(|span| span.start);
    for at in unresolved.chain(imported) {
        if let Some(i) = owner(at)
            && !std::mem::replace(&mut dropped[i], true)
        {
            work.push(i);
        }
    }
    // The names each statement binds, and the statements that use each name a statement other
    // than their own binds. A local binder of a dropped statement drops the users of a
    // top-level binder of its name too: a statement more left out, never a wrong error.
    let mut binds: Vec<Vec<&str>> = vec![Vec::new(); stmts.len()];
    for b in &res.binders {
        if let Some(i) = owner(b.span.start) {
            binds[i].push(&b.name);
        }
    }
    let mut users: HashMap<&str, Vec<usize>> = HashMap::new();
    for (span, r) in &res.uses {
        let resolve::Ref::Bound(ids) = r else {
            continue;
        };
        let b = &res.binders[ids[0]];
        if let Some(u) = owner(span.start)
            && owner(b.span.start) != Some(u)
        {
            users.entry(&b.name).or_default().push(u);
        }
    }
    while let Some(i) = work.pop() {
        for name in std::mem::take(&mut binds[i]) {
            for u in users.remove(name).unwrap_or_default() {
                if !std::mem::replace(&mut dropped[u], true) {
                    work.push(u);
                }
            }
        }
    }
    dropped
}

/// [`unplaced`] for the statements `stmts` of the unit `text`, its tokens `tokens` and its doc
/// comments `docs`, which parse.
fn checked(
    text: &str,
    tokens: &[lex::Token],
    docs: &[lex::Doc],
    mut stmts: Vec<Stmt>,
    build: &crate::build::Build,
) -> Checked {
    let resolved = work::stage(Stage::Resolve, None, || {
        resolve::resolve_text(&stmts, Some(text))
    });
    let mut res = match resolved {
        Ok(res) => res,
        Err(errors) => return Err((stmts, errors)),
    };
    let misread = crate::build::read(&mut stmts, &mut res, build);
    if !misread.is_empty() {
        return Err((stmts, misread));
    }
    // Doc comments are checked after parsing; their errors join elaboration's.
    let mut errors = work::stage(Stage::Docs, None, || docs::check(text, tokens, docs, &res));
    let elaborated = work::stage(Stage::Elaborate, None, || {
        elaborate_text(&stmts, &res, Some(text))
    });
    let unit = match elaborated {
        Ok(unit) if errors.is_empty() => unit,
        Ok(_) => return Err((stmts, errors)),
        Err(es) => {
            errors.extend(es);
            errors.sort_by_key(|e| e.span);
            return Err((stmts, errors));
        }
    };
    let refused = work::stage(Stage::Linear, None, || {
        linear_questions(text, tokens, &stmts, &unit)
    });
    if !refused.is_empty() {
        return Err((stmts, refused));
    }
    Ok((stmts, unit))
}

/// The operands of the outermost `&&` of `e`, in written order, each as `text` writes it, a
/// grouped operand with its parentheses: what the menu of a refused linear question rewrites
/// (DESIGN.md sec:diagnostics, row "Linear question outside the polynomial fragment"; the
/// menu is `presburger::Refusal::repairs`, tested by
/// `l01_38_presburger::checker::following_each_repair_of_the_menu_makes_the_program_check`).
/// An operand looser than `&&` (an `||`, an `else`, a lambda, a `for`) not written in
/// parentheses is given them, so a repair that joins it to another condition by `&&` keeps
/// its meaning. A walk with an explicit stack, O(the nodes).
fn conjuncts(text: &str, e: &ast::Expr) -> Vec<String> {
    let mut out = Vec::new();
    let mut stack = vec![e];
    while let Some(e) = stack.pop() {
        match &e.kind {
            ast::ExprKind::Binary(ast::BinaryOp::And, l, r) => {
                stack.push(r);
                stack.push(l);
            }
            kind => {
                let written = &text[e.span.start..e.span.end];
                let loose = matches!(
                    kind,
                    ast::ExprKind::Binary(ast::BinaryOp::Or, ..)
                        | ast::ExprKind::Else { .. }
                        | ast::ExprKind::Lambda { .. }
                        | ast::ExprKind::For { .. }
                );
                out.push(if loose && !grouped(written) {
                    format!("({written})")
                } else {
                    written.to_string()
                });
            }
        }
    }
    out
}

/// Every name `tokens` write, those in the holes of strings included, borrowed from the
/// tokens: the names a new top-level function must not take, since it would then be a second
/// definition of one of the program's names, and one written inside a function, a parameter
/// or a local, would hide it there. A walk with an explicit stack, O(the tokens).
fn names_written(tokens: &[lex::Token]) -> std::collections::HashSet<&str> {
    let mut out = std::collections::HashSet::new();
    let mut stack = vec![tokens];
    while let Some(tokens) = stack.pop() {
        for t in tokens {
            match &t.tok {
                lex::Tok::Name(n) => {
                    out.insert(n.as_str());
                }
                lex::Tok::Str(parts) => stack.extend(parts.iter().filter_map(|p| match p {
                    lex::Part::Hole { tokens, .. } => Some(tokens.as_slice()),
                    lex::Part::Text(_) => None,
                })),
                _ => {}
            }
        }
    }
    out
}

/// `written` with each run of white space that holds a line break made one space, so that a
/// repair prints on one line.
fn one_line(written: &str) -> String {
    let mut out = String::with_capacity(written.len());
    let mut run = String::new();
    for c in written.chars() {
        if c.is_whitespace() {
            run.push(c);
            continue;
        }
        out.push_str(if run.contains('\n') { " " } else { &run });
        run.clear();
        out.push(c);
    }
    out.push_str(if run.contains('\n') { " " } else { &run });
    out
}

/// Whether `written` is one parenthesized group: it opens with `(` whose match is its last
/// character.
fn grouped(written: &str) -> bool {
    let mut depth = 0usize;
    for (i, c) in written.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return i + 1 == written.len();
                }
            }
            _ if depth == 0 => return false,
            _ => {}
        }
    }
    false
}

/// The linear questions of the unit (step L1.38): for each function other than `main` whose
/// body the linear-relation domain states over its parameters, whether the body can hold and
/// whether it can fail. A question the solver refuses is a rejection at the function, with
/// its cause and the constraints (DESIGN.md "Diagnostics") and the menu of repairs that
/// `presburger::Refusal::repairs` builds from the cause and the function as `text` writes it;
/// a decided question rejects nothing, since a test that never holds is an unreachable arm
/// (step L1.39).
///
/// Complexity tradeoff: a function whose question the solver refuses is rejected, though the
/// program may be correct; the message names the function, its condition as written and the
/// cause. Why:
/// the solver decides only the fragment it can decide without exponential search (the
/// causes, their costs and their triggers are at `presburger::Refusal`'s raise sites:
/// Growth in `Omega::run`, Shadows in `splinters`, Disjuncts in `pick`). Tests:
/// `l01_38_presburger::checker::a_satisfiable_question_with_no_elimination_that_keeps_the_rows_is_refused`,
/// `l01_38_presburger::checker::a_question_whose_point_lies_past_one_splinter_is_rejected`,
/// `l01_38_presburger::checker::the_linear_questions_of_a_unit_scale`. COMPLEXITY.md row S18.
/// A complete solution would need a complete Presburger procedure, exponential in the worst
/// case, or would accept the function with a warning in place of the rejection.
/// Naive version: a complete Presburger procedure, exponential in the worst case; used: the
/// solver's fragment, with each refusal at the cost named at its raise site.
///
/// Public for the test that times the questions alone, on a unit loaded before the timing:
/// loading the unit of 64 functions there costs 3.5 times its questions, so a scaling test that
/// times the whole load cannot see a quadratic here (COMPLEXITY.md F85).
#[doc(hidden)]
pub fn linear_questions(
    text: &str,
    tokens: &[lex::Token],
    stmts: &[Stmt],
    unit: &Unit,
) -> Vec<ast::Error> {
    use crate::store::{preimage, presburger};
    // The names the program writes, which the split repair's new functions must not take
    // (`presburger::free_names`): read from `tokens` at the first refused question, once for
    // the unit, and the split's names once for each function name refused. Only this unit's
    // names: an importer reaches them only by writing them, and the front end, memoized by the
    // unit's text, cannot know its importers.
    let mut taken: Option<std::collections::HashSet<&str>> = None;
    let mut split_names: std::collections::HashMap<&str, [String; 2]> =
        std::collections::HashMap::new();
    // The functions of the unit by name and written parameter names, so each overload of a name
    // finds its own definition; overloads alike in both, which differ in types only, are matched
    // to their definitions in the order of the unit's definitions. A kernel name is the written
    // name or the written name and `@k` (`crate::elab`), and a written name holds no `@`
    // (`crate::lex::name`). O(n) in the size of the parameter lists.
    type Key<'a> = (&'a str, Vec<&'a str>);
    type Lams<'a> = Vec<(&'a [Arc<str>], &'a Shared, &'a Arc<str>)>;
    let mut defs: std::collections::HashMap<Key, Lams> = std::collections::HashMap::new();
    for d in unit.defs.iter().rev() {
        if let Term::Lam(ps, body) = &*d.term {
            let written = ps.iter().map(|k| crate::elab::written_name(k));
            (defs
                .entry((d.name.as_str(), written.collect()))
                .or_default())
            .push((ps, body, &d.kernel));
        }
    }
    // The prelude and every definition, as one chain of lets, each after those it uses, as
    // `Cones::close` binds a body's cone: numbered once and read once for all the functions,
    // where closing each body over its cone read a chain of n calls n times (LOAD-chain).
    let lets = interp::prelude(
        unit.defs
            .iter()
            .rev()
            .fold(Term::Lit(zed_kernel::Value::Bool(true)), |body, d| {
                Term::Let(d.kernel.clone(), d.term.clone(), Shared::new(body))
            }),
    );
    let mut scoped = preimage::Scoped::new(&lets);
    let mut extending = presburger::extend::Extending::new();
    let mut out = Vec::new();
    for s in stmts {
        let StmtKind::Function(f) = &s.bare().kind else {
            continue;
        };
        if f.name == "main" {
            continue;
        }
        let key = (
            f.name.as_str(),
            f.params.iter().map(|p| p.name.as_str()).collect(),
        );
        let Some((ps, body, kernel)) = defs.get_mut(&key).and_then(Vec::pop) else {
            continue;
        };
        work::stage(Stage::Linear, Some(&f.name), || {
            // A caller's relation holds its callee's as one shared part (`preimage::Scoped`), and
            // is decided from the callee's answers and its own new constraints
            // (`presburger::extend`), so a chain of n tests `p{i}(x) = p{i-1}(x: x) && x > i`,
            // over one variable or several, costs O(n) in all. Complexity tradeoff: a chain
            // whose links each exclude the point found for their callee is decided whole at each
            // link, O(n²) (at `Extending::defined`). Tests `l01_38_presburger::one_scope::
            // the_questions_of_a_chain_of_tests_scale` and `..._over_two_variables_scale`.
            // COMPLEXITY.md rows LOAD-chain and LOAD-chain-share. A chain whose links define
            // auxiliary variables (`x mod 7`) costs O(n) as well: they are numbered once for the
            // scope, and each question reads the definitions its new parts reach (LOAD-chain-aux).
            // So does one whose links pass their callee any affine terms of their parameters
            // (`p{i-1}(x: x + 1)`, `p{i-1}(x: 2*x)`, `p{i-1}(y: x, z: x)`, constants): each body is
            // read once over its parameters' canonical atoms, and a call binds them to its
            // arguments (`preimage::Scoped::relation`, LOAD-chain-affine).
            // A link whose point extends a small callee beside the chain reads the chain
            // through its face, the chain projected onto the atoms its call binds
            // (`preimage::Scoped::interface`, LOAD-call-summary).
            // The question is stated over the names the user wrote: elaboration renames a binder
            // `x` to `x@k` when another binder of the unit is named `x` too (`crate::elab`), which
            // the user cannot write, so the question, its refusal and its constraints print `x`,
            // and their names do not change with the other functions of the unit. The auxiliary
            // variables of the constraints are numbered from 0 in the order the scope made them,
            // which an earlier function that made one of them first may change.
            // Rung 2 reads arithmetic as integer arithmetic, so a question is asked only of a
            // function whose parameters all take only `int`s (RUNG2-carrier): one of `f64`,
            // `rat`, `bool` or a type variable that may be `f64` or `rat` is outside the domain,
            // as a float or rational literal is. `Scoped::relation` reads every parameter as an
            // integer input, so a function with an `int` parameter beside a `f64` one asks
            // nothing, even of a body that reads only the `int`. A function the checker gave no
            // signature asks nothing.
            let all_int = (unit.int_params.get(kernel))
                .is_some_and(|ints| ints.len() == f.params.len() && ints.iter().all(|&i| i));
            if !all_int {
                return;
            }
            let inputs: Vec<Arc<str>> = f.params.iter().map(|p| p.name.as_str().into()).collect();
            if let Some(r) = scoped.relation(body, ps, &inputs, true) {
                let mut answers =
                    extending.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
                // A relation is read over canonical atoms (LOAD-chain-affine), so a refusal names
                // them; a refused question is asked again over the inputs, its bindings
                // substituted (`preimage::Scoped::written`), and its refusal, if it stays, names
                // the caller's parameters. Complexity tradeoff: that question is decided whole,
                // O(the relation) and more, where its answer came from its callee's; only a
                // refused question, which is printed whole in its note, pays it. A complete
                // solution would write the refusal's rows back through the bindings.
                if answers.holds.is_err() || answers.fails.is_err() {
                    let w = scoped.written(&r);
                    let with = |f| presburger::Formula::and(vec![w.defined(), f]);
                    answers.holds = presburger::decide(&with(w.body.clone()));
                    answers.fails =
                        presburger::decide(&with(presburger::Formula::negate(w.body.clone())));
                }
                // On one line, as the message is: a condition written over several lines has its
                // line breaks and indentation read as single spaces.
                let condition = text[f.body.span.start..f.body.span.end]
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .join(" ");
                let params = (f.params.iter())
                    .map(|p| format!("`{}`", p.name))
                    .collect::<Vec<_>>()
                    .join(", ");
                for (can, answer) in [("true", answers.holds), ("false", answers.fails)] {
                    if let Err(why) = answer {
                        let relation = scoped.written(&r);
                        let constraints = relation.to_string();
                        // The moduli of the remainders and quotients the conditions take, each
                        // once, in increasing order, for the reason (I4.11).
                        // Complexity tradeoff: O(d log d) for the d definitions reached, on a
                        // refusal only, against the O(the function's text) of the message.
                        let mut moduli: Vec<&str> = (relation.defs.iter())
                            .filter_map(|(_, what, _)| {
                                what.rsplit_once(" mod ").or(what.rsplit_once(" div "))
                            })
                            .map(|(_, m)| m)
                            .collect();
                        moduli.sort_unstable_by_key(|m| (m.len(), *m));
                        moduli.dedup();
                        // The menu rewrites the function as written, on one line: its
                        // parameters the question reads, in written order, and the conditions
                        // of its value, the body of an equation or the value a block ends
                        // with, with the text before and after them. O(the function's text)
                        // per refused question.
                        let found: std::collections::HashSet<&str> =
                            presburger::names_in(&constraints).into_iter().collect();
                        let names: Vec<&str> = (f.params.iter().map(|p| p.name.as_str()))
                            .filter(|p| found.contains(p))
                            .collect();
                        let value = match &f.body.kind {
                            ast::ExprKind::Block(body) if !f.equation => match body.last() {
                                Some(Stmt {
                                    kind: StmtKind::Return(v),
                                    ..
                                }) if v.len() == 1 => &v[0],
                                _ => &f.body,
                            },
                            _ => &f.body,
                        };
                        let head = one_line(&text[s.span.start..value.span.start]);
                        let tail = one_line(&text[value.span.end..s.span.end]);
                        let parts: Vec<String> = (conjuncts(text, value).iter())
                            .map(|c| one_line(c))
                            .collect();
                        let parts: Vec<&str> = parts.iter().map(String::as_str).collect();
                        let what = format!("`{}`", f.name);
                        let into = split_names.entry(f.name.as_str()).or_insert_with(|| {
                            let taken = taken.get_or_insert_with(|| names_written(tokens));
                            presburger::free_names(&f.name, taken)
                        });
                        // A function's statement begins with its name (`Function = Name '('`
                        // in sec:grammar); were it not to, no split is offered rather than one
                        // that renames another word.
                        let split =
                            head.strip_prefix(f.name.as_str())
                                .map(|rest| presburger::Split {
                                    name: &f.name,
                                    rest,
                                    into: [&into[0], &into[1]],
                                });
                        let written = presburger::Written {
                            what: &what,
                            head: &head,
                            tail: &tail,
                            split,
                            conjuncts: &parts,
                            names: &names,
                        };
                        let repairs = why.repairs(&written).into_iter().map(|text| ast::Note {
                            span: f.body.span,
                            text,
                        });
                        // A cause that ends in a sentence of its own, such as a repair, keeps
                        // its full stop, and the message adds none.
                        let why = why.said(&names, &moduli);
                        let stop = if why.ends_with('.') { "" } else { "." };
                        out.push(ast::Error {
                            row: Some(crate::rejection::Row::NonLinearQuestion),
                            menu: String::new(),
                            span: s.span,
                            message: format!(
                                "zedc could not decide whether the condition of `{}`, written \
                                 `{condition}`, can be {can} for whole-number values of {params}, \
                                 which it works out for every test function: {why}{stop}",
                                f.name
                            ),
                            notes: std::iter::once(ast::Note {
                                span: f.body.span,
                                text: format!("the constraints: {constraints}"),
                            })
                            .chain(repairs)
                            .collect(),
                        });
                    }
                }
            } else if scoped.unbuilt() {
                // A constant written as a power (`2 ^ 200`) is built to be read, and the system
                // refused the memory for it (`preimage::Scoped::unbuilt`): the question is
                // refused with a message rather than dropped (I4.5, I5.6).
                let condition = one_line(&text[f.body.span.start..f.body.span.end]);
                let params = (f.params.iter())
                    .map(|p| format!("`{}`", p.name))
                    .collect::<Vec<_>>()
                    .join(", ");
                out.push(ast::Error {
                    row: Some(crate::rejection::Row::NonLinearQuestion),
                    menu: String::new(),
                    span: s.span,
                    message: format!(
                        "zedc could not decide whether the condition of `{}`, written \
                         `{condition}`, can be true or false for whole-number values of \
                         {params}, which it works out for every test function: the condition \
                         holds a number written as a power whose digits are too many to hold \
                         in memory.",
                        f.name
                    ),
                    notes: Vec::new(),
                });
            }
        });
    }
    out
}

/// The errors `errors` of `text`, of `severity`, as diagnostics, each placed with its steps and
/// its address; `stmts` are the unit's top-level statements, empty when it was rejected before
/// it had them.
pub(crate) fn placed(
    text: &str,
    lines: &source::Lines,
    stmts: &[Stmt],
    severity: Severity,
    errors: Vec<ast::Error>,
) -> Vec<Diagnostic> {
    let addresses = suppress::addresses(text, stmts, severity, &errors);
    let mut read = Read {
        text,
        lines,
        seen: HashMap::new(),
    };
    errors
        .into_iter()
        .zip(addresses)
        .map(|(mut e, address)| {
            // Every headline is a sentence (DESIGN.md sec:diagnostics, "A short headline").
            e.sentence();
            let (line, col) = read.place(e.span.start);
            Diagnostic {
                line,
                col,
                steps: e.notes.into_iter().map(|n| read.step(n)).collect(),
                message: e.message,
                menu: e.menu,
                row: e.row,
                address,
            }
        })
        .collect()
}

/// The lines of `text` that diagnostics are placed on, each read once, so that placing a step
/// costs a search for its line and O(1) after it, not a decoding of the line up to it, and the
/// steps on one line share one copy of it: k steps on a line of L bytes cost O(L + k log n)
/// for n lines, not O(k·L).
struct Read<'t> {
    /// The text.
    text: &'t str,
    /// Its line starts.
    lines: &'t source::Lines,
    /// Each line read, by the byte it starts at.
    seen: HashMap<usize, Line>,
}

/// A line of the source.
struct Line {
    /// Its 1-based number.
    number: usize,
    /// Its text, without its line break.
    source: Arc<str>,
    /// For each byte of it and the end, the number of characters before it.
    chars: Vec<usize>,
}

impl Read<'_> {
    /// The line holding byte `offset`, read the first time it is asked for, and its first byte.
    fn line(&mut self, offset: usize) -> (&Line, usize) {
        let (begin, number) = self.lines.line_start(offset);
        let text = self.text;
        let line = self.seen.entry(begin).or_insert_with(|| {
            let end = text[begin..]
                .find(['\n', '\r'])
                .map_or(text.len(), |i| begin + i);
            let source = &text[begin..end];
            let mut chars = Vec::with_capacity(source.len() + 1);
            let mut count = 0;
            for b in source.bytes() {
                chars.push(count);
                // A byte that is not a continuation byte starts a character.
                count += usize::from(b & 0xC0 != 0x80);
            }
            chars.push(count);
            Line {
                number,
                source: source.into(),
                chars,
            }
        });
        (line, begin)
    }

    /// The 1-based line and column of byte `offset`, the column counted in characters.
    fn place(&mut self, offset: usize) -> (usize, usize) {
        let (line, begin) = self.line(offset);
        (line.number, line.chars[offset - begin] + 1)
    }

    /// The step a note is: its line and column, the source line, and the characters of the
    /// note's span on that line.
    fn step(&mut self, n: ast::Note) -> Step {
        let (line, begin) = self.line(n.span.start);
        let end = begin + line.source.len();
        let first = line.chars[n.span.start - begin];
        let width = line.chars[n.span.end.clamp(n.span.start, end) - begin] - first;
        Step {
            line: line.number,
            col: first + 1,
            text: n.text,
            source: Arc::clone(&line.source),
            width: width.max(1),
        }
    }
}

/// An error at `span` with no derivation.
pub(crate) fn error(span: Span, message: String) -> Error {
    Error {
        row: None,
        menu: String::new(),
        span,
        message,
        notes: Vec::new(),
    }
}

/// The statements of the unit `text` and its imports ([`Imported`]), in text order; or the
/// errors of the first phase that rejects it. What [`Query::Parse`] computes.
///
/// [`Query::Parse`]: crate::query::Query::Parse
pub(crate) fn parse_unit(text: &str) -> Parsed {
    let tokens = lex::lex(text).map_err(|e| vec![lex_error(text, e)])?;
    // Every declaration that does not parse has its error, and the others are read
    // (step L1.29d).
    let (tree, failed) = crate::parse::parse_unit(text, &tokens, TOP);
    let (stmts, broken) = built(text, &tokens, &tree, failed)?;
    // The imports are found by the resolver's own walk, which meets every import in every
    // scope; read alone, the unit resolves with no other unit, and only the imports are kept.
    let mut imports = resolve::resolve_in(&stmts, &Alone).res.units;
    imports.sort_by_key(|i| i.1);
    Ok((stmts, imports, broken))
}

/// Writes `n` copies of `c`. A width in a format string takes at most 2^16 - 1, so a mark at a
/// column past that, on a line of 65,536 characters or more, cannot be placed by one. O(n).
fn repeat(f: &mut std::fmt::Formatter<'_>, c: char, n: usize) -> std::fmt::Result {
    (0..n).try_for_each(|_| std::fmt::Write::write_char(f, c))
}

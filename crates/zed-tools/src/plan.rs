//! `plan [--fix] [PLAN_DAG.md]` checks the table "Items by level" of `docs/plan_dag.md` (this
//! repository's, when no file is named): no id has two rows, every id in a `needs` column has a
//! row, each row's level is one more than the highest level among its needs (0 with no
//! needs), and no row has more than [`MAX_NEEDS`] distinct needs. It prints one line per
//! problem, then the table's counts of items, edges and levels, and fails if there is any
//! problem.
//!
//! The counts and the file-conflict lists of the `conflicts` tool are not kept in the file
//! (TOOL-plan-counts-after-rebase, 2026-11-19). They were: the sentence "It has N items, E edges
//! and L levels (0 to M)." in the first paragraph, and the sections "File conflicts at the same
//! level" and "File conflicts across levels" (5442 of the file's 10607 lines). Both follow from
//! the whole table, so when two branches each changed the table, the rebase of one onto the other
//! left them stale even where git merged every row cleanly, and each landing needed a commit of
//! `plan --fix` output (139 commits that changed nothing else from 2026-11-18 to 2026-11-19).
//! Now `plan` prints the counts and `conflicts` prints the lists, both from the table as it is,
//! and the check reports the sentence or the sections if a file still holds them.
//!
//! With `--fix` it first rewrites the file: each row's level cell becomes the level its needs
//! give, and the count sentence and the conflict sections are taken out. Nothing else changes,
//! not even the order of the rows. It refuses, writing nothing, when the levels cannot be
//! computed: an id with two rows, a need with no row, or a cycle.
//!
//! The table is read the way GitHub renders it (GitHub-flavored Markdown): a row is split into
//! cells at every `|`, also one inside backticks, except a `|` written `\|`, which is part of the
//! cell's text (and shows as `|`, in code too). Before both modes the tool refuses the file, with
//! one line per bad line, unless the section holds, after blank lines, exactly the header
//! `| Level | Id | Title | Size | Hard | Needs | Paths |`, the delimiter row, and then only rows
//! of exactly seven cells whose level is a number, with no blank line between two rows (a blank
//! line ends a Markdown table). A `\|` may stand only in the Title cell, since the other readers
//! of this table (tools/dagview, tools/plan_merge.sh) split at every `|` and read the cells
//! after the title from the right. So a row whose last cells were written twice
//! (TOOL-plan-row-columns) and a `|` in a title written without its `\` are both refused.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt::Write;
use std::ops::Range;

use crate::text::{self, read_text};
use crate::{Outcome, impl_root, say};

/// The heading of the table the tool reads; the table ends at the next `## ` heading.
const TABLE: &str = "## Items by level";

/// The names of the table's columns, in order.
const COLUMNS: [&str; 7] = ["Level", "Id", "Title", "Size", "Hard", "Needs", "Paths"];

/// The heading of the list of pairs at one level that `conflicts` prints, and of the first of
/// the two sections that once held the lists in the file.
pub(crate) const SAME: &str = "## File conflicts at the same level";

/// The heading of the list of paths across levels; in the file, its section ended at the next
/// `## ` heading.
pub(crate) const CROSS: &str = "## File conflicts across levels";

/// The most distinct needs a row may have: the fan-in of the largest join row after the
/// restructure of author P381 (2026-11-17). A row with more is split into join rows of at most
/// this many needs each, by crate or area. Until DAG-fanin-split-2026-11-25 the limit was kept
/// only by `wt/board-check-fanin.mjs` (outside this repository), which read dagview's state when
/// someone ran `wt/board-check.sh`; no landing ran it, so L1.41-join-tools-tests reached 47 needs
/// and L1.41-join-zedc-preimage-perf 41. This check replaces it: the test
/// `m0_03_grammar_tools::plan::this_repository_s_plan_passes` runs it on the plan, and
/// tools/merge_check.sh selects that test for every landing that changes the plan or this tool.
pub const MAX_NEEDS: usize = 32;

/// The table's header line and delimiter row, as they must be written.
const HEADER: &str = "| Level | Id | Title | Size | Hard | Needs | Paths |";
const DELIMITER: &str = "|---|---|---|---|---|---|---|";

/// One row of the table.
pub(crate) struct Row<'a> {
    /// The line number in the file, from 1.
    pub(crate) line: usize,
    /// The level column as written.
    pub(crate) level: &'a str,
    /// The id.
    pub(crate) id: &'a str,
    /// The title column as written, a `|` in it as `\|`.
    pub(crate) title: &'a str,
    /// The ids in the `needs` column; empty for `none`.
    pub(crate) needs: Vec<&'a str>,
    /// The paths column as written.
    pub(crate) paths: &'a str,
}

/// The cells of the table line `l`, trimmed: the text between one `|` and the next, where a `|`
/// written `\|` is text (see the module comment); `None` unless `l` starts and ends with a `|`
/// that splits.
fn cells(l: &str) -> Option<Vec<&str>> {
    // The line must start with a bar and end at a splitting one, with nothing after it.
    let inner = l.strip_prefix('|')?.strip_suffix('|')?;
    (!inner.ends_with('\\')).then(|| crate::table::split_cells(inner))
}

/// The rows of the table in `text`, read as the module comment states; refused with one line per
/// bad line of the table. O(m) for `m` the length of `text` up to the end of the section.
// Proof of the bound: `lines` and the search for the heading read each byte before the section
// once (the search starts at the top of `text`), and nothing after the section's end is read
// but its first line, which `take_while` refuses. Each line of
// the section then costs O(its length): the compare with `HEADER` or `DELIMITER`, `cells`
// (two strips and `table::split_cells`, one pass), the `\|` search over its cells, the digit
// check and the split of the needs each read the line's bytes a fixed number of times, and a
// message for a bad line copies at most the line and a fixed text. So the sum is O(length),
// in a fixed number of passes, not one. Not timed by a test.
pub(crate) fn rows(text: &str) -> Result<Vec<Row<'_>>, String> {
    let mut lines = text.lines().enumerate();
    lines
        .by_ref()
        .find(|(_, l)| *l == TABLE)
        .ok_or_else(|| format!("no heading `{TABLE}`"))?;
    let mut rows = Vec::new();
    let mut bad = String::new();
    // What the next non-blank line must be: the header, then the delimiter, then rows.
    let mut seen = 0;
    // The first blank line after the delimiter, if a row may still follow it.
    let mut blank: Option<usize> = None;
    for (i, l) in lines.take_while(|(_, l)| !l.starts_with("## ")) {
        let line = i + 1;
        if l.trim().is_empty() {
            if seen == 2 && blank.is_none() {
                blank = Some(line);
            }
            continue;
        }
        if seen < 2 {
            let want = [HEADER, DELIMITER][seen];
            if l != want {
                say!(
                    &mut bad,
                    "line {line}: `{l}` where the table must have `{want}`"
                );
                return Err(bad.trim_end().into());
            }
            seen += 1;
            continue;
        }
        if let Some(b) = blank.take() {
            say!(
                &mut bad,
                "line {b}: a blank line inside the table, which ends it in Markdown"
            );
        }
        let Some(cells) = cells(l) else {
            say!(
                &mut bad,
                "line {line}: not a table row: a row starts and ends with `|`"
            );
            continue;
        };
        if cells.len() != COLUMNS.len() {
            say!(
                &mut bad,
                "line {line}: the row has {} cells, not {} ({}); a `|` in a cell's text, also \
                 inside backticks, is written `\\|`",
                cells.len(),
                COLUMNS.len(),
                COLUMNS.join(", ")
            );
            continue;
        }
        if let Some(k) = (0..COLUMNS.len()).find(|&k| k != 2 && cells[k].contains("\\|")) {
            say!(
                &mut bad,
                "line {line}: the {} cell holds `\\|`; only the Title may",
                COLUMNS[k]
            );
            continue;
        }
        if cells[0].is_empty() || !cells[0].bytes().all(|b| b.is_ascii_digit()) {
            say!(
                &mut bad,
                "line {line}: {} has level `{}`, not a number",
                cells[1],
                cells[0]
            );
            continue;
        }
        let needs = match cells[5] {
            "none" => Vec::new(),
            list => list.split(',').map(str::trim).collect(),
        };
        rows.push(Row {
            line,
            level: cells[0],
            id: cells[1],
            title: cells[2],
            needs,
            paths: cells[6],
        });
    }
    if seen < 2 {
        say!(
            &mut bad,
            "the section `{TABLE}` has no table: it must start with `{HEADER}` and `{DELIMITER}`"
        );
    }
    if bad.is_empty() {
        Ok(rows)
    } else {
        Err(bad.trim_end().into())
    }
}

/// The counts the first paragraph states: items, edges, levels and the highest level, from the
/// sentence "It has N items, E edges and L levels (0 to M).", with the byte range in `text` from
/// "It has" to the end of M.
fn stated(text: &str) -> Option<([usize; 4], Range<usize>)> {
    let start = text.find("It has ")?;
    let rest = start + "It has ".len();
    // Each separator is one byte, so a word starts one byte after the end of the one before.
    let mut at = rest;
    let mut words = text[rest..]
        .split([' ', ',', '(', ')', '.'])
        .map(|w| {
            let word = (at, w);
            at += w.len() + 1;
            word
        })
        .filter(|(_, w)| !w.is_empty());
    let mut word = || words.next().map(|(_, w)| w);
    let mut n = [0; 4];
    for (k, after) in [(0, "items"), (1, "edges"), (2, "levels")] {
        n[k] = word()?.parse().ok()?;
        (word()? == after).then_some(())?;
        if k == 1 {
            (word()? == "and").then_some(())?;
        }
    }
    (word()? == "0").then_some(())?;
    (word()? == "to").then_some(())?;
    let (top_at, top) = words.next()?;
    n[3] = top.parse().ok()?;
    Some((n, start..top_at + top.len()))
}

/// The byte range of the count sentence in `text` that [`fix_plan`] takes out: from "It has" to
/// its closing `).`, and one space after it. tools/plan_merge.sh takes out the same text.
fn sentence(text: &str) -> Option<Range<usize>> {
    let (_, span) = stated(text)?;
    let mut end = span.end;
    if text[end..].starts_with(").") {
        end += 2;
        if text[end..].starts_with(' ') {
            end += 1;
        }
    }
    Some(span.start..end)
}

/// The byte range of the two conflict sections in `text`: from the start of the `SAME` heading
/// to the start of the next `#` or `## ` heading after `CROSS`, or the end of the text; `None`
/// when the file does not have both headings, each a line of its own, `CROSS` after `SAME`.
/// tools/plan_merge.sh takes out the same lines (it ends at `## ` alone; the lines of the
/// sections are table rows and `- ` items, never a `# ` heading).
fn sections(text: &str) -> Option<Range<usize>> {
    let same = text::section(text, SAME)?.start;
    let cross = text::section(&text[same..], CROSS)?;
    Some(same..same + cross.end)
}

/// Writes to `out` the counts of a table (items, edges, levels and the highest level), the line
/// `plan` prints last.
fn say_counts(out: &mut String, [items, edges, levels, top]: [usize; 4]) {
    say!(
        out,
        "the table has {items} items, {edges} edges and {levels} levels (0 to {top})"
    );
}

/// A map from each id to the index of its first row in `rows`, writing a line to `out` for each
/// row whose id has an earlier row; with the number of such lines.
fn index_rows<'a>(rows: &[Row<'a>], out: &mut String) -> (HashMap<&'a str, usize>, usize) {
    let mut bad = 0;
    let mut by_id: HashMap<&str, usize> = HashMap::with_capacity(rows.len());
    for (i, row) in rows.iter().enumerate() {
        match by_id.entry(row.id) {
            Entry::Vacant(e) => {
                e.insert(i);
            }
            Entry::Occupied(e) => {
                say!(
                    out,
                    "line {}: {} has a second row (the first is at line {})",
                    row.line,
                    row.id,
                    rows[*e.get()].line
                );
                bad += 1;
            }
        }
    }
    (by_id, bad)
}

/// The ids of the rows of the table "Items by level" in the plan `text`.
pub fn row_ids(text: &str) -> Result<Vec<&str>, String> {
    Ok(rows(text)?.into_iter().map(|r| r.id).collect())
}

/// Checks the plan `text`, writing one line per problem to `out`; true when there is none.
///
/// Levels are checked against the levels written in the table, one row at a time: each row's
/// level must be one more than the highest written level among its needs. When every row
/// passes, levels rise strictly along every edge, so the graph has no cycle and each written
/// level is the length of the longest path from a root. One pass over the rows and their needs
/// with a hash map from id to row: O(rows + edges).
pub fn check_plan(text: &str, out: &mut String) -> Result<bool, String> {
    Ok(check_counts(text, out)?.0)
}

/// [`check_plan`], with the table's counts: items, edges, levels and the highest written level.
fn check_counts(text: &str, out: &mut String) -> Result<(bool, [usize; 4]), String> {
    let rows = rows(text)?;
    let (by_id, mut bad) = index_rows(&rows, out);
    let level = |row: &Row<'_>| row.level.parse::<usize>().ok();
    let (mut edges, mut top) = (0, 0);
    for row in &rows {
        let Some(own) = level(row) else {
            say!(
                out,
                "line {}: {} has level `{}`, not a number",
                row.line,
                row.id,
                row.level
            );
            bad += 1;
            continue;
        };
        top = top.max(own);
        edges += row.needs.len();
        // Distinct needs, as the join rows count them: O(k log k) for a row of k needs.
        let mut distinct = row.needs.clone();
        zed_collections::sorted::sort_dedup(&mut distinct);
        if distinct.len() > MAX_NEEDS {
            say!(
                out,
                "line {}: {} has {} needs, more than {MAX_NEEDS}; split it into join rows of at \
                 most {MAX_NEEDS} needs each, by crate or area",
                row.line,
                row.id,
                distinct.len()
            );
            bad += 1;
        }
        let mut want = 0;
        for need in &row.needs {
            match by_id.get(need) {
                None => {
                    say!(
                        out,
                        "line {}: {} needs {need}, which has no row",
                        row.line,
                        row.id
                    );
                    bad += 1;
                }
                Some(&n) => want = want.max(level(&rows[n]).map_or(0, |l| l + 1)),
            }
        }
        if own != want {
            say!(
                out,
                "line {}: {} is at level {own}; one more than the highest level among its needs is {want}",
                row.line,
                row.id
            );
            bad += 1;
        }
    }
    if stated(text).is_some() {
        say!(
            out,
            "the first paragraph states the counts (\"It has N items, E edges and L levels (0 to \
             M).\"), which a rebase leaves stale; `plan` prints them, and `plan --fix` takes the \
             sentence out"
        );
        bad += 1;
    }
    if let Some(r) = sections(text) {
        say!(
            out,
            "line {}: the file holds the sections \"File conflicts at the same level\" and \"File \
             conflicts across levels\", which a rebase leaves stale; `conflicts` prints them, and \
             `plan --fix` takes them out",
            zedc::source::line_col(text.as_bytes(), r.start).0
        );
        bad += 1;
    }
    Ok((bad == 0, [rows.len(), edges, top + 1, top]))
}

/// What [`fix_plan`] made of a plan.
#[derive(Debug, PartialEq, Eq)]
pub struct Fixed {
    /// The plan with its levels set and the count sentence and conflict sections taken out.
    pub text: String,
    /// The number of rows whose level cell changed.
    pub changed: usize,
    /// The table's counts: items, edges, levels and the highest level.
    pub counts: [usize; 4],
    /// What was taken out of the file: "the count sentence", "the conflict sections", or both.
    pub took_out: Vec<&'static str>,
}

/// The plan `text` with each row's level cell set to the length of the longest path to the row
/// from a root, and the count sentence and the conflict sections taken out; every other byte as
/// written. Refused, with one line per problem, when an id has two rows, a need has no row or
/// the needs form a cycle.
///
/// Levels are set in topological order (Kahn's algorithm): a row is placed once every row it
/// needs is, at one more than the highest level among them. Each row and each edge is visited
/// once, and the text is rebuilt in one pass over its lines: O(rows + edges + length). Kahn:
/// A. B. Kahn, "Topological sorting of large networks", CACM 5(11), 558-562, 1962,
/// doi:10.1145/368996.369025, read 2026-11-21 (PDF from OpenAlex's cache, verification only),
/// quoted with the method at `zed_graph::order`. The longest path is not in the paper: its
/// serial numbers are an order only (p. 559, "the sequence numbers represent the sorting key"),
/// and its one bound on path length is the estimate of M, the "longest possible chain" of a
/// PERT network (p. 561). The level here is correct because a row is placed only after every
/// row it needs, whose levels are then final, so `1 + max` of them is the longest path to it.
/// `fix_sets_each_level_to_the_longest_path_from_a_root` checks the levels on a plan where the
/// last need placed is not the highest (red with `max` dropped), and
/// `fix_refuses_a_cycle_and_names_its_rows` the refusal.
pub fn fix_plan(text: &str) -> Result<Fixed, String> {
    let rows = rows(text)?;
    let mut problems = String::new();
    let (by_id, mut bad) = index_rows(&rows, &mut problems);
    // needed_by[j]: the rows that list row j among their needs, once per listing, so a need
    // written twice is counted twice here and in `waiting`, as the check counts edges.
    let mut needed_by: Vec<Vec<usize>> = vec![Vec::new(); rows.len()];
    let mut waiting: Vec<usize> = rows.iter().map(|r| r.needs.len()).collect();
    for (i, row) in rows.iter().enumerate() {
        for need in &row.needs {
            match by_id.get(need) {
                Some(&j) => needed_by[j].push(i),
                None => {
                    say!(
                        &mut problems,
                        "line {}: {} needs {need}, which has no row",
                        row.line,
                        row.id
                    );
                    bad += 1;
                }
            }
        }
    }
    if bad > 0 {
        return Err(problems.trim_end().into());
    }

    let mut level = vec![0; rows.len()];
    let mut ready: Vec<usize> = zed_graph::sources(&waiting).collect();
    // A row placed passes its level, one up, to each row that needs it.
    let placed = zed_graph::kahn(
        &mut waiting,
        &mut ready,
        |j| needed_by[j].iter().copied(),
        |j| {
            for &i in &needed_by[j] {
                level[i] = level[i].max(level[j] + 1);
            }
        },
    );
    if placed < rows.len() {
        let left: Vec<&str> = rows
            .iter()
            .zip(&waiting)
            .filter(|(_, w)| **w > 0)
            .map(|(r, _)| r.id)
            .collect();
        return Err(format!(
            "these items need each other in a cycle, or need an item that does: {}",
            left.join(", ")
        ));
    }

    let top = level.iter().copied().max().unwrap_or(0);
    let edges = rows.iter().map(|r| r.needs.len()).sum();
    let counts = [rows.len(), edges, top + 1, top];
    let cut = sentence(text);
    let lists = sections(text);
    let mut took_out = Vec::new();
    if cut.is_some() {
        took_out.push("the count sentence");
    }
    if lists.is_some() {
        took_out.push("the conflict sections");
    }
    let mut out = String::with_capacity(text.len() + 16);
    let mut changed = 0;
    let mut next = rows.iter().zip(&level).peekable();
    let mut start = 0;
    for (k, line) in text.split_inclusive('\n').enumerate() {
        let end = start + line.len();
        if let Some((row, &l)) = next.next_if(|(row, _)| row.line == k + 1) {
            // The level cell is the text between the first two bars; keep its spacing.
            let lead = 1 + line[1..].len() - line[1..].trim_start().len();
            out.push_str(&line[..lead]);
            write!(out, "{l}").expect("writing to a String");
            out.push_str(&line[lead + row.level.len()..]);
            changed += usize::from(row.level.parse() != Ok(l));
        } else if lists.as_ref().is_some_and(|r| r.contains(&start)) {
            // A line of the conflict sections, which begin and end at the start of a line.
        } else if let Some(c) = cut.as_ref().filter(|c| c.start >= start && c.end <= end) {
            out.push_str(&line[..c.start - start]);
            out.push_str(&line[c.end - start..]);
        } else {
            out.push_str(line);
        }
        start = end;
    }
    Ok(Fixed {
        text: out,
        changed,
        counts,
        took_out,
    })
}

/// The plan file a tool reads: the path given on its command line, else the implementation's
/// [`crate::cite::PLAN`]. `plan` and `conflicts` both take it (row DRY-ast-walkers,
/// REPORT-dryA5 row 25).
pub fn plan_path(given: Option<&String>) -> String {
    given
        .cloned()
        .unwrap_or_else(|| format!("{}/{}", impl_root(), crate::cite::PLAN))
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let usage = "usage: plan [--fix] [PLAN_DAG.md]";
    let fixing = args.first().is_some_and(|a| a == "--fix");
    let rest = &args[usize::from(fixing)..];
    if rest.len() > 1 || rest.first().is_some_and(|a| a.starts_with("--")) {
        return Err(usage.into());
    }
    let path = &plan_path(rest.first());
    let text = read_text(path)?;
    if !fixing {
        let (ok, counts) = check_counts(&text, out)?;
        say_counts(out, counts);
        return Ok(ok);
    }
    let fixed = fix_plan(&text).map_err(|e| {
        format!("{path}: the levels cannot be computed, so nothing was written:\n{e}")
    })?;
    if fixed.text != text {
        std::fs::write(path, &fixed.text).map_err(|e| format!("{path}: {e}"))?;
    }
    say!(out, "levels changed: {}", fixed.changed);
    if !fixed.took_out.is_empty() {
        say!(
            out,
            "taken out of the file: {}",
            fixed.took_out.join(" and ")
        );
    }
    let ok = check_plan(&fixed.text, out)?;
    say_counts(out, fixed.counts);
    Ok(ok)
}

#[cfg(test)]
mod tests {
    use super::{check_plan, fix_plan};

    /// A plan whose table holds `rows`, with a count sentence (wrong, as a rebase leaves it).
    fn plan(rows: &[&str]) -> String {
        let mut t = String::from(
            "# Plan\n\nIt has 0 items, 0 edges and 0 levels (0 to 0).\n\n## Items by level\n\n\
             | Level | Id | Title | Size | Hard | Needs | Paths |\n|---|---|---|---|---|---|---|\n",
        );
        for r in rows {
            t.push_str(r);
            t.push('\n');
        }
        t
    }

    /// Each level is the longest path from a root: D needs C (level 2) and the root E, and E is
    /// placed after C, so a level set by the last need placed would be 1, not 3.
    #[test]
    fn fix_sets_each_level_to_the_longest_path_from_a_root() {
        let text = plan(&[
            "| 9 | E | e | S | no | none | - |",
            "| 9 | D | d | S | no | C, E | - |",
            "| 9 | C | c | S | no | B | - |",
            "| 9 | A | a | S | no | none | - |",
            "| 9 | B | b | S | no | A | - |",
        ]);
        let fixed = fix_plan(&text).unwrap();
        let levels: Vec<&str> = fixed
            .text
            .lines()
            .skip_while(|l| !l.starts_with("|---"))
            .skip(1)
            .map(|l| l.split('|').nth(1).unwrap().trim())
            .collect();
        assert_eq!(levels, ["0", "3", "2", "0", "1"]);
        assert_eq!(fixed.counts, [5, 4, 4, 3]);
        assert_eq!(fixed.changed, 5);
        // The counts are printed by `plan`, not written: the sentence is taken out.
        assert_eq!(fixed.took_out, ["the count sentence"]);
        assert!(!fixed.text.contains("It has"), "{}", fixed.text);
        assert!(check_plan(&fixed.text, &mut String::new()).unwrap());
        assert!(!check_plan(&text, &mut String::new()).unwrap());
    }

    /// A cycle is refused, naming the rows on it and the rows after it.
    #[test]
    fn fix_refuses_a_cycle_and_names_its_rows() {
        let text = plan(&[
            "| 0 | A | a | S | no | none | - |",
            "| 0 | B | b | S | no | A, C | - |",
            "| 0 | C | c | S | no | B | - |",
            "| 0 | D | d | S | no | C | - |",
        ]);
        let err = fix_plan(&text).unwrap_err();
        assert!(err.ends_with("B, C, D"), "{err}");
    }
}

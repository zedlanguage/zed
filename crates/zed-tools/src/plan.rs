//! `plan [--fix] [PLAN_DAG.md]` checks the table "Items by level" of `docs/plan_dag.md` (this
//! repository's, when no file is named): no id has two rows, every id in a `needs` column has a
//! row, each row's level is one more than the highest level among its needs (0 with no needs),
//! and the first paragraph's counts of items, edges and levels match the table. It prints one
//! line per problem and fails if there is any.
//!
//! With `--fix` it first rewrites the file: each row's level cell becomes the level its needs
//! give, and the count sentence of the first paragraph becomes the table's counts. Nothing else
//! changes, not even the order of the rows. It refuses, writing nothing, when the levels cannot
//! be computed: an id with two rows, a need with no row, or a cycle.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt::Write;
use std::ops::Range;

use crate::text::read_text;
use crate::{Outcome, impl_root, say};

/// The heading of the table the tool reads; the table ends at the next `## ` heading.
const TABLE: &str = "## Items by level";

/// One row of the table.
pub(crate) struct Row<'a> {
    /// The line number in the file, from 1.
    pub(crate) line: usize,
    /// The level column as written.
    pub(crate) level: &'a str,
    /// The id.
    pub(crate) id: &'a str,
    /// The start of the title column: the text after the id, up to the first `|`.
    pub(crate) title: &'a str,
    /// The ids in the `needs` column; empty for `none`.
    pub(crate) needs: Vec<&'a str>,
    /// The paths column as written.
    pub(crate) paths: &'a str,
}

/// The rows of the table in `text`. The title column may hold a `|`, so `needs` is read from the
/// right: it is the second-last cell, before the paths.
pub(crate) fn rows(text: &str) -> Result<Vec<Row<'_>>, String> {
    let mut lines = text.lines().enumerate();
    lines
        .by_ref()
        .find(|(_, l)| *l == TABLE)
        .ok_or_else(|| format!("no heading `{TABLE}`"))?;
    let mut rows = Vec::new();
    for (i, l) in lines.take_while(|(_, l)| !l.starts_with("## ")) {
        let Some(inner) = l.strip_prefix('|').and_then(|l| l.strip_suffix('|')) else {
            continue;
        };
        let cells: Vec<&str> = inner.split('|').map(str::trim).collect();
        if cells.len() < 7 || !cells[0].bytes().all(|b| b.is_ascii_digit()) || cells[0].is_empty() {
            continue;
        }
        let needs = match cells[cells.len() - 2] {
            "none" => Vec::new(),
            list => list.split(',').map(str::trim).collect(),
        };
        rows.push(Row {
            line: i + 1,
            level: cells[0],
            id: cells[1],
            title: cells[2],
            needs,
            paths: cells[cells.len() - 1],
        });
    }
    Ok(rows)
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

/// The sentence of the first paragraph that states `counts`, as [`stated`] reads it, up to the
/// end of the highest level.
fn sentence([items, edges, levels, top]: [usize; 4]) -> String {
    format!("It has {items} items, {edges} edges and {levels} levels (0 to {top}")
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
    let counted = [rows.len(), edges, top + 1, top];
    match stated(text).map(|(said, _)| said) {
        None => {
            say!(
                out,
                "no sentence \"It has N items, E edges and L levels (0 to M).\""
            );
            bad += 1;
        }
        Some(said) if said != counted => {
            say!(
                out,
                "the first paragraph says {} items, {} edges and {} levels (0 to {}); the table has {} items, {} edges and {} levels (0 to {})",
                said[0],
                said[1],
                said[2],
                said[3],
                counted[0],
                counted[1],
                counted[2],
                counted[3]
            );
            bad += 1;
        }
        Some(_) => {}
    }
    Ok(bad == 0)
}

/// What [`fix_plan`] made of a plan.
#[derive(Debug, PartialEq, Eq)]
pub struct Fixed {
    /// The plan with its levels and counts set.
    pub text: String,
    /// The number of rows whose level cell changed.
    pub changed: usize,
    /// The counts the first paragraph now states: items, edges, levels and the highest level.
    pub counts: [usize; 4],
}

/// The plan `text` with each row's level cell set to the length of the longest path to the row
/// from a root, and the first paragraph's count sentence set to the table's counts; every other
/// byte as written. Refused, with one line per problem, when an id has two rows, a need has no
/// row, the needs form a cycle or there is no count sentence.
///
/// Levels are set in topological order (Kahn's algorithm): a row is placed once every row it
/// needs is, at one more than the highest level among them. Each row and each edge is visited
/// once, and the text is rebuilt in one pass over its lines: O(rows + edges + length).
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
    let Some((_, span)) = stated(text) else {
        say!(
            &mut problems,
            "no sentence \"It has N items, E edges and L levels (0 to M).\""
        );
        return Err(problems.trim_end().into());
    };
    if bad > 0 {
        return Err(problems.trim_end().into());
    }

    let mut level = vec![0; rows.len()];
    let mut ready: Vec<usize> = (0..rows.len()).filter(|&i| waiting[i] == 0).collect();
    let mut placed = 0;
    while let Some(j) = ready.pop() {
        placed += 1;
        for &i in &needed_by[j] {
            level[i] = level[i].max(level[j] + 1);
            waiting[i] -= 1;
            if waiting[i] == 0 {
                ready.push(i);
            }
        }
    }
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
        } else if span.start >= start && span.end <= end {
            out.push_str(&line[..span.start - start]);
            out.push_str(&sentence(counts));
            out.push_str(&line[span.end - start..]);
        } else {
            out.push_str(line);
        }
        start = end;
    }
    Ok(Fixed {
        text: out,
        changed,
        counts,
    })
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let usage = "usage: plan [--fix] [PLAN_DAG.md]";
    let fixing = args.first().is_some_and(|a| a == "--fix");
    let rest = &args[usize::from(fixing)..];
    if rest.len() > 1 || rest.first().is_some_and(|a| a.starts_with("--")) {
        return Err(usage.into());
    }
    let default;
    let path = match rest.first() {
        Some(p) => p.as_str(),
        None => {
            default = format!("{}/docs/plan_dag.md", impl_root());
            &default
        }
    };
    let text = read_text(path)?;
    if !fixing {
        return check_plan(&text, out);
    }
    let fixed = fix_plan(&text).map_err(|e| {
        format!("{path}: the levels cannot be computed, so nothing was written:\n{e}")
    })?;
    if fixed.text != text {
        std::fs::write(path, &fixed.text).map_err(|e| format!("{path}: {e}"))?;
    }
    let [items, edges, levels, top] = fixed.counts;
    say!(
        out,
        "levels changed: {}; the first paragraph says {items} items, {edges} edges and {levels} \
         levels (0 to {top})",
        fixed.changed
    );
    check_plan(&fixed.text, out)
}

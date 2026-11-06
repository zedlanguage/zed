//! `plan [PLAN_DAG.md]` checks the table "Items by level" of `docs/plan_dag.md` (this
//! repository's, when no file is named): no id has two rows, every id in a `needs` column has a
//! row, each row's level is one more than the highest level among its needs (0 with no needs),
//! and the first paragraph's counts of items, edges and levels match the table. It prints one
//! line per problem and fails if there is any.

use std::collections::HashMap;

use crate::text::read_text;
use crate::{Outcome, impl_root, say};

/// The heading of the table the tool reads; the table ends at the next `## ` heading.
const TABLE: &str = "## Items by level";

/// One row of the table.
struct Row<'a> {
    /// The line number in the file, from 1.
    line: usize,
    /// The level column as written.
    level: &'a str,
    /// The id.
    id: &'a str,
    /// The ids in the `needs` column; empty for `none`.
    needs: Vec<&'a str>,
}

/// The rows of the table in `text`. The title column may hold a `|`, so `needs` is read from the
/// right: it is the second-last cell, before the paths.
fn rows(text: &str) -> Result<Vec<Row<'_>>, String> {
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
            needs,
        });
    }
    Ok(rows)
}

/// The counts the first paragraph states: items, edges, levels and the highest level, from the
/// sentence "It has N items, E edges and L levels (0 to M)."
fn stated(text: &str) -> Option<[usize; 4]> {
    let rest = &text[text.find("It has ")? + "It has ".len()..];
    let mut n = [0; 4];
    let mut words = rest
        .split([' ', ',', '(', ')', '.'])
        .filter(|w| !w.is_empty());
    for (k, after) in [(0, "items"), (1, "edges"), (2, "levels")] {
        n[k] = words.next()?.parse().ok()?;
        (words.next()? == after).then_some(())?;
        if k == 1 {
            (words.next()? == "and").then_some(())?;
        }
    }
    (words.next()? == "0").then_some(())?;
    (words.next()? == "to").then_some(())?;
    n[3] = words.next()?.parse().ok()?;
    Some(n)
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
    let mut bad = 0;
    let mut by_id: HashMap<&str, &Row<'_>> = HashMap::with_capacity(rows.len());
    for row in &rows {
        if let Some(first) = by_id.insert(row.id, row) {
            say!(
                out,
                "line {}: {} has a second row (the first is at line {})",
                row.line,
                row.id,
                first.line
            );
            bad += 1;
        }
    }
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
                Some(n) => want = want.max(level(n).map_or(0, |l| l + 1)),
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
    match stated(text) {
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

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let default;
    let path = match args.first() {
        Some(p) => p.as_str(),
        None => {
            default = format!("{}/docs/plan_dag.md", impl_root());
            &default
        }
    };
    check_plan(&read_text(path)?, out)
}

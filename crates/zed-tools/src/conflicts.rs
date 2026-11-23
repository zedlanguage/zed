//! `conflicts [PLAN_DAG.md]` prints two file-conflict lists, "File conflicts at the same level"
//! and "File conflicts across levels", from the table "Items by level" of `docs/plan_dag.md`
//! (this repository's, when no file is named). It writes nothing. The lists were once sections
//! of that file, which this tool rewrote and checked; every rebase of a branch that changed the
//! table left them stale, so they are printed instead (TOOL-plan-counts-after-rebase, see
//! `crate::plan`).
//!
//! An item touches a path when it is open (the title does not start with `Done:`) and lists the
//! path or, when the path is a directory (it ends in `/`), a path inside it. Two items share a
//! file when a path of one equals a path of the other or lies inside a directory path of the
//! other. Paths are compared as written, with a trailing ` (new)` removed, so a glob such as
//! `tests/steps/*/scaling.rs` matches only itself. Paths under `tests/` and the files every step
//! touches are not compared.
//!
//! The first section lists the pairs of open items at one level that share a file. Two items at
//! one level are never joined by a path of needs, since the plan check requires each level to be
//! one more than the highest level among the item's needs, so every such pair may run in
//! parallel. The second section lists, for each path that open items at two or more levels
//! touch, those items by level; whether two of them are ordered by needs is left to the reader.
//!
//! The tool first runs the `plan` check on the table and stops if it fails, since a wrong level
//! would put an item in the wrong place.

use crate::plan::{CROSS, SAME, check_plan, plan_path, rows};
use crate::text::read_text;
use crate::{Outcome, say};

/// The files every step touches (the paragraph "Files every step touches" of the plan), left
/// out of the comparison since every pair would match.
const EVERY_STEP: [&str; 5] = [
    "tests/Cargo.toml",
    "tests/steps/m0_01_scaffolding/",
    "STATUS.md",
    "COMPLEXITY.md",
    "../zed/PROGRESS.md",
];

/// One row of the items table, as the tool needs it.
struct Item<'a> {
    id: &'a str,
    level: usize,
    open: bool,
    /// The paths that take part in the comparison, in the order written.
    paths: Vec<&'a str>,
}

/// Two items that conflict, as row numbers in the table, the earlier row first.
type Pair = (u32, u32);

/// A compared path of an open item: (path, row, position in the row's paths).
type Entry<'a> = (&'a str, u32, u32);

/// What the tool computes from the items table.
pub struct Conflicts<'a> {
    items: Vec<Item<'a>>,
    /// The pairs at one level, each with its shared paths, sorted by level and then by rows.
    pub same: Vec<(Pair, Vec<&'a str>)>,
    /// The paths that open items at two or more levels touch, sorted, each with the rows of the
    /// items that touch it, sorted by level and then by id.
    pub cross: Vec<(&'a str, Vec<u32>)>,
}

impl Conflicts<'_> {
    /// The ids of a pair.
    pub fn ids(&self, (a, b): Pair) -> (&str, &str) {
        (self.items[a as usize].id, self.items[b as usize].id)
    }

    /// The lines of the section across levels, each `` - `path`: level 0: A, B; level 1: C ``.
    fn cross_lines(&self) -> Vec<String> {
        self.cross
            .iter()
            .map(|(path, rows)| {
                let mut line = format!("- `{path}`:");
                let mut level = None;
                for &r in rows {
                    let it = &self.items[r as usize];
                    if level == Some(it.level) {
                        line.push_str(", ");
                    } else {
                        if level.is_some() {
                            line.push(';');
                        }
                        line.push_str(&format!(" level {}: ", it.level));
                        level = Some(it.level);
                    }
                    line.push_str(it.id);
                }
                line
            })
            .collect()
    }
}

/// The paths of a paths cell that take part in the comparison: each span in backticks, less a
/// trailing ` (new)`, other than the files every step touches and paths under `tests/`.
fn compared_paths(cell: &str) -> Vec<&str> {
    cell.split('`')
        .skip(1)
        .step_by(2)
        .map(|p| p.strip_suffix(" (new)").unwrap_or(p))
        .filter(|p| !p.starts_with("tests/") && !EVERY_STEP.contains(p))
        .collect()
}

/// Reads the items table of the plan `text`, which `check_plan` has passed. A span of a paths
/// cell holding a space is refused: a path cell holds only paths, and remarks go outside the
/// backticks.
fn items(text: &str) -> Result<Vec<Item<'_>>, String> {
    rows(text)?
        .iter()
        .map(|r| {
            let level = r
                .level
                .parse()
                .map_err(|_| format!("line {}: level `{}` is not a number", r.line, r.level))?;
            let paths = compared_paths(r.paths);
            if let Some(p) = paths.iter().find(|p| p.contains(char::is_whitespace)) {
                return Err(format!(
                    "line {}: the path `{p}` of {} holds a space; write only the path in \
                     backticks and any remark outside them",
                    r.line, r.id
                ));
            }
            Ok(Item {
                id: r.id,
                level,
                // A done row's title starts "Done": most write "Done: ...", some "Done by
                // <agent> ...", "Done (<agent>, <date>) ..." or "Done in <commit> ...".
                open: !r.title.starts_with("Done"),
                paths,
            })
        })
        .collect()
}

/// Computes the conflicts of the plan `text`, whose items table `check_plan` has passed.
///
/// Complexity tradeoff: the naive method compares every path of every open item with every path
/// of every other, O(n² p²) for n items of p paths. The earlier form of the second section
/// listed every pair of items at different levels that share a file and are not joined by a
/// path of needs; deciding that needs reachability for each sharing pair, at most the size of
/// the transitive closure, Θ(n²) on a chain of n items that all share one file, and its output
/// was Θ(n²) pairs too (11694 pairs, 116 KB, on the plan of 2026-11-10). The form here needs no
/// reachability at all: the first section's pairs are at one level, which no path of needs
/// joins, and the second lists per path the items that touch it. The m compared paths of open
/// items are sorted once, O(m log m) comparisons; equal paths then lie in one run, and the paths
/// inside a directory `d/` lie in the run of entries just after `d/`'s own. Each run is sorted
/// by level, so the pairs at one level come from the groups of one level, and an entry inside a
/// directory finds the directory's entries at its own level by binary search: each step yields
/// a pair or a line of the output. The entries visited inside directories number at most the m
/// entries times the depth of listed directories that hold them, which the count of `/` in the
/// paths bounds. The whole is O(m log m + D log m + output), D the number of (directory, path
/// inside it) pairs; on the plan of 2026-11-10 m is 1743. COMPLEXITY.md row
/// PLAN-conflict-lists-regen; tests/steps/m0_03_grammar_tools/conflicts.rs has the scaling test.
pub fn compute(text: &str) -> Result<Conflicts<'_>, String> {
    let items = items(text)?;
    let level = |r: u32| items[r as usize].level;
    let mut entries: Vec<Entry<'_>> = items
        .iter()
        .enumerate()
        .filter(|(_, it)| it.open)
        .flat_map(|(i, it)| {
            it.paths
                .iter()
                .enumerate()
                .map(move |(k, p)| (*p, i as u32, k as u32))
        })
        .collect();
    entries.sort_unstable();
    // An item that lists a path twice keeps its first position.
    entries.dedup_by(|b, a| a.0 == b.0 && a.1 == b.1);
    // Each match of two paths of items at one level: the pair, the positions of the two paths in
    // the rows' own lists, and the longer path.
    let mut matches: Vec<(Pair, u32, u32, &str)> = Vec::new();
    let mut cross = Vec::new();
    // The entries of one run, sorted by level.
    let mut run: Vec<(usize, Entry<'_>)> = Vec::new();
    let mut touching: Vec<u32> = Vec::new();
    let mut start = 0;
    while start < entries.len() {
        let path = entries[start].0;
        let end = start + entries[start..].partition_point(|e| e.0 == path);
        run.clear();
        run.extend(entries[start..end].iter().map(|e| (level(e.1), *e)));
        run.sort_unstable();
        let mut g = 0;
        while g < run.len() {
            let h = g + run[g..].partition_point(|x| x.0 == run[g].0);
            for i in g..h {
                for j in i + 1..h {
                    add(&mut matches, run[i].1, run[j].1, path);
                }
            }
            g = h;
        }
        touching.clear();
        touching.extend(run.iter().map(|x| x.1.1));
        if path.ends_with('/') {
            let inner = end + entries[end..].partition_point(|e| e.0.starts_with(path));
            for e in &entries[end..inner] {
                let l = level(e.1);
                let lo = run.partition_point(|x| x.0 < l);
                for outer in run[lo..].iter().take_while(|x| x.0 == l) {
                    add(&mut matches, outer.1, *e, e.0);
                }
                touching.push(e.1);
            }
        }
        touching.sort_unstable_by_key(|&r| (level(r), items[r as usize].id));
        touching.dedup();
        if let (Some(&a), Some(&b)) = (touching.first(), touching.last())
            && level(a) != level(b)
        {
            cross.push((path, touching.clone()));
        }
        start = end;
    }
    matches.sort_unstable();
    let mut same: Vec<(Pair, Vec<&str>)> = Vec::new();
    let mut shared: Vec<(&str, u32, u32)> = Vec::new();
    for group in matches.chunk_by(|x, y| x.0 == y.0) {
        // One path may match at two positions: keep its first, then restore the order of the
        // earlier row's paths.
        shared.clear();
        shared.extend(group.iter().map(|m| (m.3, m.1, m.2)));
        shared.sort_unstable();
        shared.dedup_by(|b, a| a.0 == b.0);
        shared.sort_unstable_by_key(|s| (s.1, s.2));
        same.push((group[0].0, shared.iter().map(|s| s.0).collect()));
    }
    same.sort_unstable_by_key(|(pair, _)| (level(pair.0), *pair));
    Ok(Conflicts { items, same, cross })
}

/// The text of both lists, each under its heading, as the tool prints it.
pub fn render(c: &Conflicts<'_>) -> String {
    let mut out = String::new();
    let w = &mut out;
    say!(w, "{SAME}\n");
    say!(
        w,
        "Each pair below is at one level, shares a file and is not yet done. No path of needs \
         joins two items at one level, since each level is one more than the highest level among \
         the item's needs. Under the rule of 2026-11-02 the two may run in parallel and the merge \
         resolves the overlap; run them apart where possible. There are {} pairs. This list and \
         the next are printed by `cargo run -q -p zed-tools --bin conflicts` from the items table \
         of docs/plan_dag.md. Two items share a file when a path of one equals a path of the other \
         or lies inside a directory path of the other, one that ends in `/`. Paths are compared \
         as written, less a trailing ` (new)`; files under `tests/` and the files every step \
         touches are not compared. The two items of a row are in the order of their rows in the \
         table, and the shared paths are the longer path of each match.\n",
        c.same.len()
    );
    say!(w, "| Level | Items | Shared paths |\n|---|---|---|");
    for &(pair, ref paths) in &c.same {
        let (a, b) = c.ids(pair);
        let level = c.items[pair.0 as usize].level;
        let paths: Vec<String> = paths.iter().map(|p| format!("`{p}`")).collect();
        say!(w, "| {level} | {a}, {b} | {} |", paths.join(", "));
    }
    say!(w, "\n{CROSS}\n");
    say!(
        w,
        "Each line below names a path and the open items that touch it, by level, when they lie \
         at two or more levels. An item touches a path when it lists the path or, for a \
         directory, a path inside it, compared as above. Two items of a line that no path of \
         needs joins may run in parallel, and the merge resolves the overlap; two that needs \
         join run in order. There are {} lines.\n",
        c.cross.len()
    );
    for line in c.cross_lines() {
        say!(w, "{line}");
    }
    out.push('\n');
    out
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    if args.len() > 1 || args.first().is_some_and(|a| a.starts_with("--")) {
        return Err(
            "usage: conflicts [PLAN_DAG.md]\n(the lists are no longer kept in \
                    docs/plan_dag.md, so there is nothing to check or rewrite: the tool prints \
                    them)"
                .into(),
        );
    }
    let path = &plan_path(args.first());
    let text = read_text(path)?;
    let mut problems = String::new();
    if !check_plan(&text, &mut problems)? {
        return Err(format!(
            "{path}: the file does not pass the plan check, whose levels place the items; fix \
             these first (`plan --fix` sets the levels and takes out the count sentence and the old \
             sections):\n{problems}"
        ));
    }
    let c = compute(&text).map_err(|e| format!("{path}: {e}"))?;
    out.push_str(&render(&c));
    Ok(true)
}

/// Records a match of the entries `x` and `y` of items at one level, whose longer path is
/// `shared`, unless both are of one row.
fn add<'a>(
    matches: &mut Vec<(Pair, u32, u32, &'a str)>,
    x: Entry<'a>,
    y: Entry<'a>,
    shared: &'a str,
) {
    if x.1 == y.1 {
        return;
    }
    let (a, b) = if x.1 < y.1 { (x, y) } else { (y, x) };
    matches.push(((a.1, b.1), a.2, b.2, shared));
}

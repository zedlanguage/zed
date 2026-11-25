//! The `plan` tool on small plans written the way `docs/plan_dag.md` is, and on that file
//! itself: an item whose need has no row, an id with two rows, a level that does not follow
//! from the needs, and a file that still holds the count sentence or the conflict sections.

use super::{Dir, tool};
use zed_tools::plan::{check_plan, fix_plan, run};

/// A plan whose table holds `rows`, each `(level, id, needs)`, followed by one more section.
fn plan(rows: &[(&str, &str, &str)]) -> String {
    let mut text = String::from(
        "# Plan DAG\n\nThis file lists the remaining work. It covers the TODO items.\n\n\
         ## Items by level\n\n| Level | Id | Title | Size | Hard | Needs | Paths |\n\
         |---|---|---|---|---|---|---|\n",
    );
    for (level, id, needs) in rows {
        text.push_str(&format!(
            "| {level} | {id} | Work on {id} | S | no | {needs} | `src/{id}.rs` |\n"
        ));
    }
    text.push_str("\n## Notes\n\nNone.\n");
    text
}

/// `text` written the way the file was until TOOL-plan-counts-after-rebase: the count sentence
/// `counts` in the first paragraph and the two conflict sections after the table.
fn with_old_parts(text: &str, counts: &str) -> String {
    text.replace(
        "remaining work. It covers",
        &format!("remaining work. {counts} It covers"),
    )
    .replace(
        "\n## Notes",
        "\n## File conflicts at the same level\n\n| 0 | A, B | `x` |\n\n\
         ## File conflicts across levels\n\n- A (0) and B (1) share `y`\n\n## Notes",
    )
}

/// What the tool prints for `text`, and whether it passed.
pub(super) fn checked(text: &str) -> (bool, String) {
    let mut out = String::new();
    let ok = check_plan(text, &mut out).expect("the plan has its table");
    (ok, out)
}

/// A store fix, the parser work it waits for, and the step that needs both.
const GOOD: &[(&str, &str, &str)] = &[
    ("0", "T4", "none"),
    ("0", "LR1", "none"),
    ("1", "ST1", "T4"),
    ("2", "L1.40", "T4, ST1, LR1"),
];

#[test]
fn a_plan_whose_levels_agree_passes() {
    assert_eq!(checked(&plan(GOOD)), (true, String::new()));
}

#[test]
fn a_need_on_an_item_with_no_row_is_reported() {
    // The case that started this check: T6-ratlit needed CAP-bits, which was done and had lost
    // its row.
    let rows = [("0", "T6", "none"), ("1", "T6-ratlit", "CAP-bits, T6")];
    let (ok, out) = checked(&plan(&rows));
    assert!(!ok);
    assert_eq!(out, "line 10: T6-ratlit needs CAP-bits, which has no row\n");
}

#[test]
fn an_id_with_two_rows_is_reported() {
    let rows = [("0", "T4", "none"), ("0", "T4", "none")];
    let (ok, out) = checked(&plan(&rows));
    assert!(!ok);
    assert_eq!(
        out,
        "line 10: T4 has a second row (the first is at line 9)\n"
    );
}

#[test]
fn an_item_at_the_level_of_its_need_is_reported() {
    // S22e-quad was written at level 2, the level of S22e, which it needs.
    let rows = [
        ("0", "S22a", "none"),
        ("1", "S22e", "S22a"),
        ("1", "S22e-quad", "S22e"),
    ];
    let (ok, out) = checked(&plan(&rows));
    assert!(!ok);
    assert_eq!(
        out,
        "line 11: S22e-quad is at level 1; one more than the highest level among its needs is 2\n"
    );
}

#[test]
fn an_item_above_the_level_its_needs_give_is_reported() {
    // A row left at its old level after a need was dropped.
    let rows = [("0", "T4", "none"), ("2", "ST1", "T4")];
    let (ok, out) = checked(&plan(&rows));
    assert!(!ok);
    assert!(
        out.contains("ST1 is at level 2; one more than the highest level among its needs is 1")
    );
}

/// The rows of a join `J` that needs the roots `N0` .. `N{k-1}`, each written `copies` times in
/// its needs.
fn join(k: usize, copies: usize) -> String {
    let ids: Vec<String> = (0..k).map(|i| format!("N{i}")).collect();
    let mut rows: Vec<(&str, &str, String)> =
        ids.iter().map(|id| ("0", &**id, "none".into())).collect();
    let needs: Vec<&str> = (0..copies).flat_map(|_| ids.iter().map(|s| &**s)).collect();
    rows.push(("1", "J", needs.join(", ")));
    let rows: Vec<(&str, &str, &str)> = rows.iter().map(|(l, id, n)| (*l, *id, &**n)).collect();
    plan(&rows)
}

#[test]
fn a_row_with_more_than_32_needs_is_reported() {
    // DAG-fanin-split-2026-11-25: L1.41-join-tools-tests reached 47 needs and
    // L1.41-join-zedc-preimage-perf 41, with no landing failing; the limit is author P381's.
    assert_eq!(zed_tools::plan::MAX_NEEDS, 32);
    let (ok, out) = checked(&join(33, 1));
    assert!(!ok);
    assert_eq!(
        out,
        "line 42: J has 33 needs, more than 32; split it into join rows of at most 32 needs \
         each, by crate or area\n"
    );
    // The control: 32 needs pass, and a need written twice counts once.
    assert_eq!(checked(&join(32, 1)), (true, String::new()));
    assert_eq!(checked(&join(32, 2)), (true, String::new()));
}

#[test]
fn a_cycle_cannot_pass_the_level_check() {
    // Levels must rise along each edge, which no cycle allows.
    let rows = [("0", "A", "B"), ("1", "B", "A")];
    let (ok, out) = checked(&plan(&rows));
    assert!(!ok);
    assert!(out.contains("A is at level 0; one more than the highest level among its needs is 2"));
}

#[test]
fn a_plan_still_holding_the_count_sentence_and_the_conflict_sections_is_reported() {
    // TOOL-plan-counts-after-rebase: both follow from the whole table, so a rebase left them
    // stale. Even counts that agree with the table are reported, since the next rebase can make
    // them wrong.
    let text = with_old_parts(
        &plan(GOOD),
        "It has 4 items, 4 edges and 3 levels (0 to 2).",
    );
    let (ok, out) = checked(&text);
    assert!(!ok);
    assert_eq!(
        out,
        "the first paragraph states the counts (\"It has N items, E edges and L levels (0 to \
         M).\"), which a rebase leaves stale; `plan` prints them, and `plan --fix` takes the \
         sentence out\n\
         line 14: the file holds the sections \"File conflicts at the same level\" and \"File \
         conflicts across levels\", which a rebase leaves stale; `conflicts` prints them, and \
         `plan --fix` takes them out\n"
    );
}

#[test]
fn fix_takes_out_the_count_sentence_and_the_conflict_sections() {
    let text = with_old_parts(
        &plan(GOOD),
        "It has 3 items, 4 edges and 3 levels (0 to 2).",
    );
    let fixed = fix_plan(&text).unwrap();
    assert_eq!(fixed.text, plan(GOOD));
    assert_eq!(
        fixed.took_out,
        ["the count sentence", "the conflict sections"]
    );
    assert_eq!(fixed.counts, [4, 4, 3, 2]);
}

#[test]
fn a_file_ending_in_the_conflict_sections_is_fixed_to_end_after_the_table() {
    // The sections ran to the end of the file when no `## ` heading followed them.
    let text = with_old_parts(
        &plan(GOOD),
        "It has 4 items, 4 edges and 3 levels (0 to 2).",
    )
    .replace("\n## Notes\n\nNone.\n", "");
    let want = plan(GOOD).replace("## Notes\n\nNone.\n", "");
    assert_eq!(fixed(&text), want);
    assert_eq!(checked(&want), (true, String::new()));
}

#[test]
fn a_bar_in_a_title_does_not_move_the_needs_column() {
    let text = plan(GOOD).replace("Work on ST1", "Work on `a \\| b` in ST1");
    assert_eq!(checked(&text), (true, String::new()));
}

/// The plan `text` read by the tool, which must refuse it; what it says.
fn refused(text: &str) -> String {
    let err = check_plan(text, &mut String::new()).unwrap_err();
    assert_eq!(fix_plan(text), Err(err.clone()));
    err
}

#[test]
fn a_row_whose_last_cells_are_written_twice_is_refused() {
    // The case that made the column count check (found by edits-spec, 2026-11-16): `plan --fix`
    // read the needs and paths from the right and took this row as good.
    let text = plan(GOOD).replace(
        "| T4 | `src/ST1.rs` |",
        "| T4 | `src/ST1.rs` | S | no | T4 | `src/ST1.rs` |",
    );
    assert_eq!(
        refused(&text),
        "line 11: the row has 11 cells, not 7 (Level, Id, Title, Size, Hard, Needs, Paths); a `|` \
         in a cell's text, also inside backticks, is written `\\|`"
    );
}

#[test]
fn a_row_with_one_cell_too_few_is_refused() {
    let text = plan(GOOD).replace("| S | no | T4 |", "| S | T4 |");
    assert!(refused(&text).starts_with("line 11: the row has 6 cells, not 7"));
}

#[test]
fn a_row_with_an_escaped_bar_in_backticks_is_read_with_the_right_fields() {
    // TOOL-plan-row-columns' own row, whose title holds `|` inside backticks, written `\|` as
    // GitHub needs it. Its needs (none, at level 0) and the row after it (needing it, at level 1)
    // are read from the right cells, and the fix leaves both as written.
    let row = "| 0 | TOOL-plan-row-columns | Found by edits-spec (2026-11-16): a naive split on \
               ` \\| ` gives 6 to 11 fields | S | yes | none | `crates/zed-tools/src/plan.rs` |\n\
               | 1 | NEXT | Uses it, `a \\| b \\| c` | S | no | TOOL-plan-row-columns | `x/` |\n";
    let text = plan(GOOD).replace("\n## Notes", &format!("{row}\n## Notes"));
    assert_eq!(checked(&text), (true, String::new()));
    assert_eq!(fixed(&text), text);
    assert_eq!(
        zed_tools::plan::row_ids(&text).unwrap(),
        ["T4", "LR1", "ST1", "L1.40", "TOOL-plan-row-columns", "NEXT"]
    );
    // One cell off would show: NEXT at level 0 is then reported against its need.
    let moved = text.replace("| 1 | NEXT |", "| 0 | NEXT |");
    let (ok, out) = checked(&moved);
    assert!(!ok);
    assert!(
        out.contains("NEXT is at level 0; one more than the highest level among its needs is 1")
    );
}

#[test]
fn a_bar_in_backticks_written_without_its_backslash_is_refused() {
    // GitHub splits a table row at a `|` inside a code span too, so such a row shows broken
    // there; the tool reads the row the same way and names the repair.
    let text = plan(GOOD).replace("Work on ST1", "Work on `a | b` in ST1");
    assert!(
        refused(&text).starts_with("line 11: the row has 8 cells, not 7"),
        "{}",
        refused(&text)
    );
}

#[test]
fn an_escaped_bar_outside_the_title_is_refused() {
    let text = plan(GOOD).replace("`src/ST1.rs`", "`src/a\\|b.rs`");
    assert_eq!(
        refused(&text),
        "line 11: the Paths cell holds `\\|`; only the Title may"
    );
}

#[test]
fn a_blank_line_inside_the_table_is_refused() {
    // A blank line ends a Markdown table: the rows after it show as one paragraph.
    let text = plan(GOOD).replace("| 1 | ST1 |", "\n| 1 | ST1 |");
    assert_eq!(
        refused(&text),
        "line 11: a blank line inside the table, which ends it in Markdown"
    );
}

#[test]
fn a_line_in_the_table_that_is_not_a_row_is_refused() {
    let text = plan(GOOD).replace("| 1 | ST1 |", "Note.\n| 1 | ST1 |");
    assert_eq!(
        refused(&text),
        "line 11: not a table row: a row starts and ends with `|`"
    );
}

#[test]
fn a_table_with_another_header_is_refused() {
    let text = plan(GOOD).replace("| Hard |", "| Hard? |");
    assert!(refused(&text).starts_with(
        "line 7: `| Level | Id | Title | Size | Hard? | Needs | Paths |` where the table must have"
    ));
}

#[test]
fn every_bad_line_is_named_at_once() {
    let text = plan(GOOD)
        .replace("| 0 | LR1 |", "| x | LR1 |")
        .replace("| S | no | T4 |", "| S | T4 |");
    assert_eq!(
        refused(&text)
            .lines()
            .map(|l| l.split(':').next().unwrap())
            .collect::<Vec<_>>(),
        ["line 10", "line 11"]
    );
}

#[test]
fn a_file_with_no_table_stops_the_tool() {
    assert!(check_plan("# Plan DAG\n", &mut String::new()).is_err());
}

/// The plan `text` after `fix_plan`, which must succeed.
pub(super) fn fixed(text: &str) -> String {
    fix_plan(text).unwrap_or_else(|e| panic!("{e}")).text
}

#[test]
fn fix_leaves_a_plan_that_passes_unchanged() {
    let text = plan(GOOD);
    assert_eq!(fixed(&text), text);
    assert!(fix_plan(&text).unwrap().took_out.is_empty());
}

#[test]
fn fix_sets_stale_levels_and_nothing_else() {
    // The case that made the fix: rows added at the end of the table with the level of the row
    // above them. LAZY-hub was written at level 0 though it needs a level-1 item, and the row
    // that needs it was left at level 0 too.
    let stale = [
        ("0", "T4", "none"),
        ("0", "LR1", "none"),
        ("1", "ST1", "T4"),
        ("2", "L1.40", "T4, ST1, LR1"),
        ("0", "LAZY-hub", "ST1"),
        ("0", "LAZY-cleanups", "LAZY-hub, LR1"),
        ("7", "PRODUCT-main", "LR1"),
    ];
    let right = [
        ("0", "T4", "none"),
        ("0", "LR1", "none"),
        ("1", "ST1", "T4"),
        ("2", "L1.40", "T4, ST1, LR1"),
        ("2", "LAZY-hub", "ST1"),
        ("3", "LAZY-cleanups", "LAZY-hub, LR1"),
        ("1", "PRODUCT-main", "LR1"),
    ];
    let fixed_plan = fix_plan(&plan(&stale)).unwrap();
    assert_eq!(fixed_plan.text, plan(&right));
    assert_eq!(fixed_plan.changed, 3);
    assert_eq!(fixed_plan.counts, [7, 8, 4, 3]);
    assert_eq!(checked(&plan(&right)), (true, String::new()));
}

#[test]
fn fix_keeps_the_spacing_of_each_level_cell() {
    let text = plan(GOOD).replace("| 1 | ST1 |", "|  0| ST1 |");
    assert_eq!(
        fixed(&text),
        plan(GOOD).replace("| 1 | ST1 |", "|  1| ST1 |")
    );
}

#[test]
fn a_row_whose_level_is_not_a_number_is_refused() {
    // Until TOOL-plan-row-columns such a line was skipped, so ST1 seemed to have no row.
    let text = plan(GOOD).replace("| 1 | ST1 |", "| 1a | ST1 |");
    assert_eq!(refused(&text), "line 11: ST1 has level `1a`, not a number");
}

#[test]
fn fix_reads_the_needs_column_past_a_bar_in_a_title() {
    let text = plan(GOOD)
        .replace("Work on ST1", "Work on `a \\| b` in ST1")
        .replace("| 2 | L1.40 |", "| 1 | L1.40 |");
    assert_eq!(
        fixed(&text),
        plan(GOOD).replace("Work on ST1", "Work on `a \\| b` in ST1")
    );
}

#[test]
fn fix_refuses_a_need_with_no_row() {
    let rows = [("0", "T6", "none"), ("0", "T6-ratlit", "CAP-bits, T6")];
    assert_eq!(
        fix_plan(&plan(&rows)),
        Err("line 10: T6-ratlit needs CAP-bits, which has no row".into())
    );
}

#[test]
fn fix_refuses_an_id_with_two_rows() {
    let rows = [("0", "T4", "none"), ("0", "T4", "none")];
    assert_eq!(
        fix_plan(&plan(&rows)),
        Err("line 10: T4 has a second row (the first is at line 9)".into())
    );
}

#[test]
fn fix_refuses_a_cycle_and_names_its_items() {
    let rows = [
        ("0", "T4", "none"),
        ("0", "A", "B, T4"),
        ("0", "B", "C"),
        ("0", "C", "A"),
        ("0", "D", "C"),
    ];
    assert_eq!(
        fix_plan(&plan(&rows)),
        Err("these items need each other in a cycle, or need an item that does: A, B, C, D".into())
    );
}

#[test]
fn the_check_prints_the_counts_after_the_problems() {
    let dir = Dir::new("plan_counts");
    let stale = plan(GOOD).replace("| 2 | L1.40 |", "| 1 | L1.40 |");
    let path = dir.write("plan_dag.md", &stale);
    let (outcome, out) = tool(run, &[&path]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert_eq!(
        out,
        "line 12: L1.40 is at level 1; one more than the highest level among its needs is 2\n\
         the table has 4 items, 4 edges and 2 levels (0 to 1)\n"
    );
}

#[test]
fn fix_writes_the_file_and_then_checks_it() {
    let dir = Dir::new("plan_fix");
    let stale = with_old_parts(
        &plan(GOOD).replace("| 2 | L1.40 |", "| 0 | L1.40 |"),
        "It has 4 items, 4 edges and 3 levels (0 to 2).",
    );
    let path = dir.write("plan_dag.md", &stale);
    let (outcome, out) = tool(run, &["--fix", &path]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert_eq!(
        out,
        "levels changed: 1\n\
         taken out of the file: the count sentence and the conflict sections\n\
         the table has 4 items, 4 edges and 3 levels (0 to 2)\n"
    );
    assert_eq!(std::fs::read_to_string(&path).unwrap(), plan(GOOD));
}

#[test]
fn fix_of_a_plan_it_cannot_fix_writes_nothing() {
    let dir = Dir::new("plan_fix_refused");
    let rows = [("0", "T6", "none"), ("1", "T6-ratlit", "CAP-bits, T6")];
    let text = with_old_parts(
        &plan(&rows),
        "It has 2 items, 2 edges and 2 levels (0 to 1).",
    );
    let path = dir.write("plan_dag.md", &text);
    let (outcome, _) = tool(run, &["--fix", &path]);
    let err = outcome.unwrap_err();
    assert!(
        err.contains("T6-ratlit needs CAP-bits, which has no row"),
        "{err}"
    );
    assert_eq!(std::fs::read_to_string(&path).unwrap(), text);
}

#[test]
fn an_unknown_flag_is_refused() {
    let (outcome, _) = tool(run, &["--fixx"]);
    assert!(outcome.unwrap_err().starts_with("usage: plan"));
}

#[test]
fn this_repository_s_plan_passes() {
    let mut out = String::new();
    assert_eq!(run(&[], &mut out), Ok(true), "{out}");
}

/// A chain of `n` items, each needing the one before.
pub(super) fn chain(n: usize) -> String {
    let rows: Vec<(String, String, String)> = (0..n)
        .map(|i| {
            let needs = if i == 0 {
                "none".into()
            } else {
                format!("I{}", i - 1)
            };
            (i.to_string(), format!("I{i}"), needs)
        })
        .collect();
    let refs: Vec<(&str, &str, &str)> = rows
        .iter()
        .map(|(l, i, n)| (l.as_str(), i.as_str(), n.as_str()))
        .collect();
    plan(&refs)
}

/// [`chain`]`(m)` with every level written as 0, so the fix rewrites every row but the first.
pub(super) fn stale_chain(m: usize) -> String {
    chain(m)
        .lines()
        .map(|l| match l.strip_prefix("| ") {
            Some(rest) if rest.starts_with(|c: char| c.is_ascii_digit()) => {
                format!("| 0 |{}\n", rest.split_once(" |").expect("a row").1)
            }
            _ => format!("{l}\n"),
        })
        .collect()
}

/// A chain passes the check and its stale copy is fixed back to it, at small sizes; the time of
/// both is held in `bench/plan.rs`.
#[test]
fn a_chain_passes_and_its_stale_levels_are_fixed_at_small_sizes() {
    for n in [1, 2, 9] {
        assert_eq!(checked(&chain(n)), (true, String::new()));
        assert_eq!(fixed(&stale_chain(n)), chain(n));
    }
}

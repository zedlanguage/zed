//! The `plan` tool on small plans written the way `docs/plan_dag.md` is, and on that file
//! itself: an item whose need has no row, an id with two rows, a level that does not follow
//! from the needs, and a first paragraph whose counts are out of date.

use zed_tests::scaling::check;
use zed_tools::plan::{check_plan, run};

/// A plan whose first paragraph states `head` and whose table holds `rows`, each
/// `(level, id, needs)`.
fn plan(head: &str, rows: &[(&str, &str, &str)]) -> String {
    let mut text = format!(
        "# Plan DAG\n\nThis file lists the remaining work. {head} It covers the TODO items.\n\n\
         ## Items by level\n\n| Level | Id | Title | Size | Hard | Needs | Paths |\n\
         |---|---|---|---|---|---|---|\n"
    );
    for (level, id, needs) in rows {
        text.push_str(&format!(
            "| {level} | {id} | Work on {id} | S | no | {needs} | `src/{id}.rs` |\n"
        ));
    }
    text.push_str("\n## File conflicts at the same level\n\n| 0 | A, B | `x` |\n");
    text
}

/// What the tool prints for `text`, and whether it passed.
fn checked(text: &str) -> (bool, String) {
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

const GOOD_HEAD: &str = "It has 4 items, 4 edges and 3 levels (0 to 2).";

#[test]
fn a_plan_whose_levels_and_counts_agree_passes() {
    assert_eq!(checked(&plan(GOOD_HEAD, GOOD)), (true, String::new()));
}

#[test]
fn a_need_on_an_item_with_no_row_is_reported() {
    // The case that started this check: T6-ratlit needed CAP-bits, which was done and had lost
    // its row.
    let rows = [("0", "T6", "none"), ("1", "T6-ratlit", "CAP-bits, T6")];
    let (ok, out) = checked(&plan(
        "It has 2 items, 2 edges and 2 levels (0 to 1).",
        &rows,
    ));
    assert!(!ok);
    assert_eq!(out, "line 10: T6-ratlit needs CAP-bits, which has no row\n");
}

#[test]
fn an_id_with_two_rows_is_reported() {
    let rows = [("0", "T4", "none"), ("0", "T4", "none")];
    let (ok, out) = checked(&plan(
        "It has 2 items, 0 edges and 1 levels (0 to 0).",
        &rows,
    ));
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
    let (ok, out) = checked(&plan(
        "It has 3 items, 2 edges and 2 levels (0 to 1).",
        &rows,
    ));
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
    let (ok, out) = checked(&plan(
        "It has 2 items, 1 edges and 3 levels (0 to 2).",
        &rows,
    ));
    assert!(!ok);
    assert!(
        out.contains("ST1 is at level 2; one more than the highest level among its needs is 1")
    );
}

#[test]
fn a_cycle_cannot_pass_the_level_check() {
    // Levels must rise along each edge, which no cycle allows.
    let rows = [("0", "A", "B"), ("1", "B", "A")];
    let (ok, out) = checked(&plan(
        "It has 2 items, 2 edges and 2 levels (0 to 1).",
        &rows,
    ));
    assert!(!ok);
    assert!(out.contains("A is at level 0; one more than the highest level among its needs is 2"));
}

#[test]
fn stale_counts_in_the_first_paragraph_are_reported() {
    let (ok, out) = checked(&plan(
        "It has 3 items, 4 edges and 3 levels (0 to 2).",
        GOOD,
    ));
    assert!(!ok);
    assert_eq!(
        out,
        "the first paragraph says 3 items, 4 edges and 3 levels (0 to 2); the table has 4 items, \
         4 edges and 3 levels (0 to 2)\n"
    );
}

#[test]
fn a_plan_with_no_count_sentence_is_reported() {
    let (ok, out) = checked(&plan("It lists the work.", GOOD));
    assert!(!ok);
    assert!(out.contains("no sentence"));
}

#[test]
fn a_bar_in_a_title_does_not_move_the_needs_column() {
    let text = plan(GOOD_HEAD, GOOD).replace("Work on ST1", "Work on `a | b` in ST1");
    assert_eq!(checked(&text), (true, String::new()));
}

#[test]
fn a_file_with_no_table_stops_the_tool() {
    assert!(check_plan("# Plan DAG\n", &mut String::new()).is_err());
}

#[test]
fn this_repository_s_plan_passes() {
    let mut out = String::new();
    assert_eq!(run(&[], &mut out), Ok(true), "{out}");
}

/// A chain of `n` items, each needing the one before, with the counts that match.
fn chain(n: usize) -> String {
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
    plan(
        &format!(
            "It has {n} items, {} edges and {n} levels (0 to {}).",
            n - 1,
            n - 1
        ),
        &refs,
    )
}

#[test]
fn plan_scales_with_the_number_of_rows() {
    let n = 500;
    let texts = [chain(n), chain(8 * n)];
    check("plan, by rows", n, |m| {
        let text = &texts[usize::from(m != n)];
        assert_eq!(checked(text), (true, String::new()));
    });
}

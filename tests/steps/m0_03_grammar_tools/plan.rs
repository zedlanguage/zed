//! The `plan` tool on small plans written the way `docs/plan_dag.md` is, and on that file
//! itself: an item whose need has no row, an id with two rows, a level that does not follow
//! from the needs, and a first paragraph whose counts are out of date.

use super::{Dir, tool};
use zed_tests::scaling::check;
use zed_tools::plan::{check_plan, fix_plan, run};

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

/// The plan `text` after `fix_plan`, which must succeed.
fn fixed(text: &str) -> String {
    fix_plan(text).unwrap_or_else(|e| panic!("{e}")).text
}

#[test]
fn fix_leaves_a_plan_that_passes_unchanged() {
    let text = plan(GOOD_HEAD, GOOD);
    assert_eq!(fixed(&text), text);
}

#[test]
fn fix_sets_stale_levels_and_counts_and_nothing_else() {
    // The case that made the fix: rows added at the end of the table with the level of the row
    // above them. LAZY-hub was written at level 0 though it needs a level-1 item, and the row
    // that needs it was left at level 0 too, as were the counts.
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
    let text = plan("It has 4 items, 4 edges and 3 levels (0 to 2).", &stale);
    let want = plan("It has 7 items, 8 edges and 4 levels (0 to 3).", &right);
    assert_eq!(fixed(&text), want);
    assert_eq!(checked(&want), (true, String::new()));
}

#[test]
fn fix_keeps_the_spacing_of_each_level_cell() {
    let text = plan(GOOD_HEAD, GOOD).replace("| 1 | ST1 |", "|  0| ST1 |");
    assert_eq!(
        fixed(&text),
        plan(GOOD_HEAD, GOOD).replace("| 1 | ST1 |", "|  1| ST1 |")
    );
}

#[test]
fn fix_does_not_read_a_row_whose_level_is_not_a_number() {
    let text = plan(GOOD_HEAD, GOOD).replace("| 1 | ST1 |", "| 1a | ST1 |");
    // A level cell that is not all digits is not a row to the reader, so ST1 has no row.
    assert!(
        fix_plan(&text)
            .unwrap_err()
            .contains("ST1, which has no row")
    );
}

#[test]
fn fix_reads_the_needs_column_past_a_bar_in_a_title() {
    let text = plan(GOOD_HEAD, GOOD)
        .replace("Work on ST1", "Work on `a | b` in ST1")
        .replace("| 2 | L1.40 |", "| 1 | L1.40 |");
    assert_eq!(
        fixed(&text),
        plan(GOOD_HEAD, GOOD).replace("Work on ST1", "Work on `a | b` in ST1")
    );
}

#[test]
fn fix_refuses_a_need_with_no_row() {
    let rows = [("0", "T6", "none"), ("0", "T6-ratlit", "CAP-bits, T6")];
    let text = plan("It has 2 items, 2 edges and 2 levels (0 to 1).", &rows);
    assert_eq!(
        fix_plan(&text),
        Err("line 10: T6-ratlit needs CAP-bits, which has no row".into())
    );
}

#[test]
fn fix_refuses_an_id_with_two_rows() {
    let rows = [("0", "T4", "none"), ("0", "T4", "none")];
    let text = plan("It has 2 items, 0 edges and 1 levels (0 to 0).", &rows);
    assert_eq!(
        fix_plan(&text),
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
    let text = plan("It has 5 items, 5 edges and 1 levels (0 to 0).", &rows);
    assert_eq!(
        fix_plan(&text),
        Err("these items need each other in a cycle, or need an item that does: A, B, C, D".into())
    );
}

#[test]
fn fix_refuses_a_plan_with_no_count_sentence() {
    let err = fix_plan(&plan("It lists the work.", GOOD)).unwrap_err();
    assert!(err.contains("no sentence"), "{err}");
}

#[test]
fn fix_writes_the_file_and_then_checks_it() {
    let dir = Dir::new("plan_fix");
    let stale = plan(GOOD_HEAD, GOOD).replace("| 2 | L1.40 |", "| 0 | L1.40 |");
    let path = dir.write("plan_dag.md", &stale);
    let (outcome, out) = tool(run, &["--fix", &path]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert_eq!(
        out,
        "levels changed: 1; the first paragraph says 4 items, 4 edges and 3 levels (0 to 2)\n"
    );
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        plan(GOOD_HEAD, GOOD)
    );
}

#[test]
fn fix_of_a_plan_it_cannot_fix_writes_nothing() {
    let dir = Dir::new("plan_fix_refused");
    let rows = [("0", "T6", "none"), ("1", "T6-ratlit", "CAP-bits, T6")];
    let text = plan("It has 2 items, 2 edges and 2 levels (0 to 1).", &rows);
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

#[test]
fn fix_scales_with_the_number_of_rows() {
    // Every level written as 0, so the fix rewrites every row but the first.
    let n = 500;
    let stale = |m: usize| {
        chain(m)
            .lines()
            .map(|l| match l.strip_prefix("| ") {
                Some(rest) if rest.starts_with(|c: char| c.is_ascii_digit()) => {
                    format!("| 0 |{}\n", rest.split_once(" |").expect("a row").1)
                }
                _ => format!("{l}\n"),
            })
            .collect::<String>()
    };
    let texts = [stale(n), stale(8 * n)];
    let wants = [chain(n), chain(8 * n)];
    check("plan --fix, by rows", n, |m| {
        let k = usize::from(m != n);
        assert_eq!(fixed(&texts[k]), wants[k]);
    });
}

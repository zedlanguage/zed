//! The `conflicts` tool on small plans written the way `docs/plan_dag.md` is: which pairs of
//! items it lists at one level with which shared paths, which paths it lists across levels with
//! which items, what `--check` says of a stale list, and the cost of both on a plan of many
//! strands.

use zed_tests::scaling::{check as check_scaling, inputs};
use zed_tools::conflicts::{check, compute, render, rewrite, run};

/// A plan whose first paragraph states `head`, whose table holds `rows`, each `(level, id,
/// title, needs, paths)`, and whose two conflict sections hold `same` and `cross`.
fn plan(head: &str, rows: &[(usize, &str, &str, &str, &str)], same: &str, cross: &str) -> String {
    let mut text = format!(
        "# Plan DAG\n\nThis file lists the remaining work. {head} It covers the TODO items.\n\n\
         ## Items by level\n\n| Level | Id | Title | Size | Hard | Needs | Paths |\n\
         |---|---|---|---|---|---|---|\n"
    );
    for (level, id, title, needs, paths) in rows {
        text.push_str(&format!(
            "| {level} | {id} | {title} | S | no | {needs} | {paths} |\n"
        ));
    }
    text.push_str(&format!(
        "\n## File conflicts at the same level\n\n{same}\n\n## File conflicts across levels\n\n\
         {cross}\n\n## Why each item waits\n\nThe reasons.\n"
    ));
    text
}

const HEAD: &str = "It has 8 items, 3 edges and 3 levels (0 to 2).";

/// A checker directory, files in and under it, a file every step touches, a test folder, a done
/// item, a path with no `/` at its end, a glob, and needs that order some sharing pairs.
const ROWS: &[(usize, &str, &str, &str, &str)] = &[
    (
        0,
        "A",
        "The checker",
        "none",
        "`DESIGN.md`, `crates/zedc-check/src/check/`",
    ),
    (
        0,
        "B",
        "A checker rule",
        "none",
        "`crates/zedc-check/src/check/mod.rs`, `STATUS.md`, `tests/steps/x/`",
    ),
    (0, "C", "Done: a spec edit", "none", "`DESIGN.md`"),
    (
        0,
        "D",
        "A driver flag",
        "none",
        "`crates/zedc`, `tests/steps/*/scaling.rs`",
    ),
    (
        1,
        "E",
        "After the checker",
        "A",
        "`DESIGN.md`, `crates/zedc-check/src/check/mod.rs (new)`",
    ),
    (1, "F", "The checker crate", "C", "`crates/zedc-check/`"),
    (
        2,
        "G",
        "After E",
        "E",
        "`DESIGN.md`, `tests/steps/*/scaling.rs`, `STATUS.md`",
    ),
    (
        0,
        "H",
        "Another rule",
        "none",
        "`crates/zedc-check/src/check/mod.rs`, `DESIGN.md`, `docs/x.md`",
    ),
];

/// The rows and lines the tool writes for `ROWS`.
const SAME_ROWS: &str = "\
| 0 | A, B | `crates/zedc-check/src/check/mod.rs` |
| 0 | A, H | `DESIGN.md`, `crates/zedc-check/src/check/mod.rs` |
| 0 | B, H | `crates/zedc-check/src/check/mod.rs` |
| 1 | E, F | `crates/zedc-check/src/check/mod.rs` |
";
const CROSS_LINES: &str = "\
- `DESIGN.md`: level 0: A, H; level 1: E; level 2: G
- `crates/zedc-check/`: level 0: A, B, H; level 1: E, F
- `crates/zedc-check/src/check/`: level 0: A, B, H; level 1: E
- `crates/zedc-check/src/check/mod.rs`: level 0: B, H; level 1: E
";

#[test]
fn the_pairs_and_paths_follow_the_rule_of_the_plan() {
    // A and E share DESIGN.md and the checker at different levels, so they appear only in the
    // lines across levels, although E needs A. C is done, so DESIGN.md names A, E, G and H.
    // B's STATUS.md and test folder, D's `crates/zedc` (no `/`, so not a directory) and the glob
    // under tests/ match nothing, and docs/x.md has one item. F's directory holds A's directory
    // and both copies of mod.rs, so its line names every item but D and G.
    let text = plan(HEAD, ROWS, "old", "- old");
    let c = compute(&text).expect("a plan with both sections");
    let written = render(&c);
    assert!(written.contains("There are 4 pairs."), "{written}");
    assert!(written.contains("There are 4 lines."), "{written}");
    assert!(
        written.contains(&format!("|---|---|---|\n{SAME_ROWS}\n")),
        "{written}"
    );
    assert!(
        written.ends_with(&format!("\n\n{CROSS_LINES}\n")),
        "{written}"
    );
}

#[test]
fn shared_paths_follow_the_earlier_row_s_order() {
    // H lists mod.rs before DESIGN.md, A the other way; A's row comes first, so its order holds.
    let text = plan(HEAD, ROWS, "old", "- old");
    let written = render(&compute(&text).expect("a plan"));
    assert!(written.contains("| 0 | A, H | `DESIGN.md`, `crates/zedc-check/src/check/mod.rs` |"));
}

#[test]
fn check_reports_a_stale_list_and_passes_after_the_rewrite() {
    // A list written before D's path changed and before G was added: A and D no longer share a
    // file, and DESIGN.md has G at level 2. The line of mod.rs is still current.
    let stale = plan(
        HEAD,
        ROWS,
        "| Level | Items | Shared paths |\n|---|---|---|\n| 0 | A, D | `crates/zedc` |",
        "- `DESIGN.md`: level 0: A, H; level 1: E\n\
         - `crates/zedc-check/src/check/mod.rs`: level 0: B, H; level 1: E",
    );
    let c = compute(&stale).expect("a plan");
    let mut out = String::new();
    assert_eq!(check(&stale, &c, &mut out), Ok(false));
    assert_eq!(
        out,
        "pairs at one level: the items table gives 4; the list has 1, of which 1 are no longer \
         such a pair, and 4 are missing\n\
         lines across levels: the items table gives 4; the list has 2, of which 1 are not as the \
         table gives them, and 3 are missing\n\
         the conflict lists are out of date; run `cargo run -q -p zed-tools --bin conflicts` to \
         rewrite them\n"
    );
    let fresh = rewrite(&stale, &c).expect("both sections");
    assert!(fresh.ends_with("## Why each item waits\n\nThe reasons.\n"));
    let c = compute(&fresh).expect("a plan");
    let mut out = String::new();
    assert_eq!(check(&fresh, &c, &mut out), Ok(true));
    assert_eq!(
        out,
        "the conflict lists are current: 4 pairs at one level, 4 lines across levels\n"
    );
    assert_eq!(rewrite(&fresh, &c).expect("both sections"), fresh);
}

#[test]
fn check_names_a_change_of_text_with_the_same_pairs() {
    let text = plan(HEAD, ROWS, "old", "- old");
    let fresh = rewrite(&text, &compute(&text).expect("a plan")).expect("both sections");
    // The same pairs, with the shared paths of one row in another order.
    let edited = fresh.replace(
        "`DESIGN.md`, `crates/zedc-check/src/check/mod.rs` |",
        "`crates/zedc-check/src/check/mod.rs`, `DESIGN.md` |",
    );
    let mut out = String::new();
    let c = compute(&edited).expect("a plan");
    assert_eq!(check(&edited, &c, &mut out), Ok(false));
    assert!(
        out.contains("the pairs and lines agree, but the text of the sections differs"),
        "{out}"
    );
}

#[test]
fn a_plan_whose_table_fails_the_plan_check_stops_the_tool() {
    // E written at level 0, the level of A, which it needs.
    let mut rows = ROWS.to_vec();
    rows[4].0 = 0;
    let text = plan(HEAD, &rows, "old", "- old");
    let dir = std::env::temp_dir().join(format!("zed-conflicts-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a temporary directory");
    let path = dir.join("plan_dag.md");
    std::fs::write(&path, &text).expect("writing the plan");
    let args = ["--check".to_string(), path.display().to_string()];
    let why = run(&args, &mut String::new()).expect_err("a wrong level");
    assert!(why.contains("does not pass the plan check"), "{why}");
    assert!(why.contains("E is at level 0"), "{why}");
    // The rewrite on a correct table writes the file, and then the check passes.
    std::fs::write(&path, plan(HEAD, ROWS, "old", "- old")).expect("writing the plan");
    let mut out = String::new();
    assert_eq!(run(&args[1..], &mut out), Ok(true));
    assert_eq!(out, "4 pairs at one level, 4 lines across levels\n");
    assert_eq!(run(&args, &mut String::new()), Ok(true));
    std::fs::remove_file(&path).expect("removing the plan");
    std::fs::remove_dir(&dir).expect("removing the directory");
}

#[test]
fn a_plan_with_no_conflict_sections_stops_the_tool() {
    let text = plan(HEAD, ROWS, "old", "- old").replace("## File conflicts across levels", "## X");
    let c = compute(&text).expect("a plan");
    assert!(rewrite(&text, &c).is_err());
    assert!(check(&text, &c, &mut String::new()).is_err());
}

#[test]
fn an_unknown_option_is_refused() {
    let why = run(&["--write".to_string()], &mut String::new()).expect_err("an option");
    assert!(why.starts_with("usage: conflicts"), "{why}");
}

/// A plan of `n` strands of four items at levels 0 to 3, each needing the one before it. Every
/// item of a strand lists the strand's directory, a file of its own in it, and a file it shares
/// with the other strand of its pair (strands 2t and 2t + 1): each strand's directory gives a
/// line across levels, and each pair of strands gives 4 pairs at one level and a line for the
/// shared file.
fn strands(n: usize) -> String {
    let mut rows = Vec::new();
    for s in 0..n {
        for d in 0..4 {
            let needs = if d == 0 {
                "none".to_string()
            } else {
                format!("S{s}-{}", d - 1)
            };
            let paths = format!(
                "`crates/s{s}/`, `crates/s{s}/f{d}.rs`, `docs/pair{}.md`",
                s / 2
            );
            rows.push((d, format!("S{s}-{d}"), needs, paths));
        }
    }
    let refs: Vec<(usize, &str, &str, &str, &str)> = rows
        .iter()
        .map(|(d, id, needs, paths)| (*d, id.as_str(), "Work", needs.as_str(), paths.as_str()))
        .collect();
    let head = format!(
        "It has {} items, {} edges and 4 levels (0 to 3).",
        4 * n,
        3 * n
    );
    plan(&head, &refs, "old", "- old")
}

#[test]
fn conflicts_scale_with_the_number_of_items() {
    let n = 200;
    let texts = inputs(n, strands);
    check_scaling("conflicts, by items", n, |m| {
        let c = compute(&texts[&m]).expect("a plan");
        assert_eq!((c.same.len(), c.cross.len()), (2 * m, m + m / 2));
        assert!(!render(&c).is_empty());
    });
}

#[test]
fn a_path_span_holding_a_remark_is_refused() {
    // A remark inside the backticks would be read as part of the path and match nothing.
    let mut rows = ROWS.to_vec();
    rows[7].4 = "`crates/zedc/src/opt/ (the L3.11 pass)`";
    let text = plan(HEAD, &rows, "old", "- old");
    let why = compute(&text).err().expect("a remark in a path");
    assert!(
        why.contains("the path `crates/zedc/src/opt/ (the L3.11 pass)` of H holds a space"),
        "{why}"
    );
}

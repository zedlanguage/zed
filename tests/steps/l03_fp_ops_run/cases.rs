//! One program per case: `main` prints the value of one expression, and the test compares the
//! printed text. A family is compared inside the program with `==` against a display, so the
//! test does not depend on how a family prints.

use zed_tests::step_helpers::l01_19_whole_file_ports::run;

/// Runs `m.stdout <- "${expr}";` for each `(expr, want)` and reports every case that does not
/// print `want`, with what it printed and its error output.
#[track_caller]
fn prints(group: &str, cases: &[(&str, &str)]) {
    let wrong: Vec<String> = cases
        .iter()
        .enumerate()
        .filter_map(|(i, &(expr, want))| {
            let src = format!("main(m: MainArgs) {{\n  m.stdout <- \"${{{expr}}}\";\n}}\n");
            let out = run(&format!("fp_ops/{group}_{i}"), &src, "", &[]);
            let got = out.stdout.trim_end_matches('\n');
            (out.status != 0 || got != want).then(|| {
                format!(
                    "{expr}\n  want {want}\n  got  {got} (status {})\n  {}",
                    out.status,
                    out.stderr.trim_end()
                )
            })
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Each program must be rejected at compile time: status not 0, nothing printed, and not for
/// want of a form this zedc does not compile yet (that rejection says nothing about the rule).
#[track_caller]
fn rejected(group: &str, exprs: &[&str]) {
    let wrong: Vec<String> = exprs
        .iter()
        .enumerate()
        .filter_map(|(i, expr)| {
            let src = format!("main(m: MainArgs) {{\n  m.stdout <- \"${{{expr}}}\";\n}}\n");
            let out = run(&format!("fp_ops/{group}_rej_{i}"), &src, "", &[]);
            (out.status == 0
                || !out.stdout.is_empty()
                || out.stderr.contains("does not compile it yet"))
            .then(|| {
                format!(
                    "{expr}\n  status {}, printed {}\n  {}",
                    out.status,
                    out.stdout.trim_end(),
                    out.stderr.trim_end()
                )
            })
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Step L3.15a: `.any`, `.all`, `.find`, in key order; `.find` gives the first key or `#none`.
#[test]
fn quantifiers_decide_in_key_order() {
    prints(
        "quantifiers",
        &[
            ("[1, 2, 3].any(x -> x > 2)", "true"),
            ("[1, 2, 3].any(x -> x > 3)", "false"),
            ("{}.all(x -> x > 0)", "true"),
            ("[1, 2, 3].all(x -> x > 0)", "true"),
            ("[1, 2, 3].all(x -> x > 1)", "false"),
            ("[5, 7, 9].find(x -> x > 6)", "1"),
            ("[5, 7, 9].find(x -> x > 10) == #none", "true"),
            ("{\"x\" -> 1, \"y\" -> 5, \"z\" -> 7}.find(v -> v > 2)", "y"),
            // `elem` and `elemIndex` of the inventory, as compositions.
            ("[5, 7, 9].any(x -> x == 7)", "true"),
            ("[5, 7, 9].find(x -> x == 9)", "2"),
        ],
    );
}

/// Steps L3.2 and L3.3: the folds `count`, `sum`, product, `max`, `min`, `.reduce`, `.foldl`,
/// `.foldr`; `max` over a level that may be empty is `#empty`, `sum` gets 0 from its identity.
#[test]
fn folds_collapse_one_level() {
    prints(
        "folds",
        &[
            ("[3, 1, 4].count", "3"),
            ("[3, 1, 4].sum", "8"),
            ("[3, 1, 4] >< (*)", "12"),
            ("[3, 1, 4] >< max", "4"),
            ("[3, 1, 4] >< min", "1"),
            ("[3, 1, 4].reduce(+)", "8"),
            ("[3, 1, 4].where(x -> x > 9).sum", "0"),
            ("([3, 1, 4].where(x -> x > 9) >< max) == #empty", "true"),
            ("[1, 2, 3].foldl(0, (a, x) -> a * 10 + x)", "123"),
            ("[1, 2, 3].foldr((x, a) -> a * 10 + x, 0)", "321"),
            (
                "{\"b\" -> 2, \"a\" -> 1}.foldl(0, (a, x) -> a * 10 + x)",
                "12",
            ),
        ],
    );
}

/// sec:reduction: a non-associative operator on an ordered level is rejected.
#[test]
fn a_fold_by_a_non_associative_operator_is_rejected() {
    rejected("folds", &["[1, 2, 3, 4] >< (-)"]);
}

/// Step L3.2: `split` keeps every piece; `lines` ends a line at `\n`, `\r\n` and a lone `\r`
/// and keeps no empty line after the last line end; `concat` with no separator (the part of
/// `concat` that every answer to QUESTIONS A105 shares).
#[test]
fn split_lines_and_concat() {
    prints(
        "strings",
        &[
            ("\"\".split(\" \") == [\"\"]", "true"),
            ("\"a  b\".split(\" \") == [\"a\", \"\", \"b\"]", "true"),
            ("\"a,b,\".split(\",\") == [\"a\", \"b\", \"\"]", "true"),
            ("\"a\\rb\".lines == [\"a\", \"b\"]", "true"),
            ("\"a\\r\\nb\".lines == [\"a\", \"b\"]", "true"),
            ("\"a\\n\\rb\".lines == [\"a\", \"\", \"b\"]", "true"),
            ("\"a\\r\\r\\n\".lines == [\"a\", \"\"]", "true"),
            ("\"\".lines == []", "true"),
            ("\"\\n\".lines == [\"\"]", "true"),
            ("\"a\\n\".lines == [\"a\"]", "true"),
            ("\"a\\n\".split(\"\\n\") == [\"a\", \"\"]", "true"),
            ("concat([\"a\", \"\", \"bc\"])", "abc"),
            ("concat(\"x,y\".split(\",\"))", "xy"),
        ],
    );
}

/// Step L5.1: `sort` with `asc` / `desc` keys, `.orderedValues`, `.take`, `.drop`, `.slice`,
/// `.takeWhile`, `.first`, `.last`, `.minBy`, `.maxBy` (ties kept).
#[test]
fn order_and_positional_selection() {
    prints(
        "order",
        &[
            ("[1, 0, 1].takeWhile(v -> v > 0) == [1]", "true"),
            ("[1, 0, 1].where(v -> v > 0) == {0 -> 1, 2 -> 1}", "true"),
            ("[3, 1, 4].sort(desc x -> x) == [4, 3, 1]", "true"),
            ("[3, 1, 4].sort(desc) == [4, 3, 1]", "true"),
            ("[3, 1, 4].sort(asc) == [1, 3, 4]", "true"),
            (
                "[3, 1, 4].where(x -> x > 2).sort(desc x -> x) == {0 -> {2 -> 4}, 1 -> {0 -> 3}}",
                "true",
            ),
            (
                "[3, 1, 4].where(x -> x > 2).sort(desc x -> x).orderedValues == [4, 3]",
                "true",
            ),
            ("[5, 6, 7, 8].take(2) == [5, 6]", "true"),
            ("[5, 6, 7, 8].drop(2) == {2 -> 7, 3 -> 8}", "true"),
            ("[5, 6, 7, 8].slice(1..<3) == {1 -> 6, 2 -> 7}", "true"),
            ("[3, 1, 4].first", "3"),
            ("[3, 1, 4].last", "4"),
            ("[3, 1, 4].where(x -> x > 9).first == #none", "true"),
            ("[3, 9, 9].maxBy(x -> x) == {9 -> {1 -> 9, 2 -> 9}}", "true"),
            ("[3, 9, 3].minBy(x -> x) == {3 -> {0 -> 3, 2 -> 3}}", "true"),
        ],
    );
}

/// Step L5.1c: a consumer of the reverse of the delivered order reads it with no sort; `take(3)`
/// over the reverse of 10 entries gives the last three in reverse order.
#[test]
fn reverse_order_take_gives_the_last_entries() {
    prints(
        "reverse",
        &[(
            "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9].sort(desc).take(3) == [9, 8, 7]",
            "true",
        )],
    );
}

/// Step L5.2: `++` is offset concatenation on rank keys; `zip` is the equality join on ranks,
/// and its two projections give back both operands. Unequal keyspaces are rejected.
#[test]
fn concatenation_zip_and_its_law() {
    prints(
        "zip",
        &[
            ("[1, 2] ++ [3] == [1, 2, 3]", "true"),
            ("[1, 2].zip([10, 20]) == [(1, 10), (2, 20)]", "true"),
            (
                "[1, 2].zip([10, 20]).map(p -> p[0] + p[1]) == [11, 22]",
                "true",
            ),
            (
                "[1, 2, 3].zip([4, 5, 6]).map(p -> p[0]) == [1, 2, 3] && \
                 [1, 2, 3].zip([4, 5, 6]).map(p -> p[1]) == [4, 5, 6]",
                "true",
            ),
        ],
    );
    rejected("zip", &["[1, 2].zip([1])"]);
}

/// Step L5.3: `scan` is the family of prefix folds, and its last entry is the fold; `.chunkBy`
/// groups runs of equal key, each run under its index, the entries keeping their keys.
#[test]
fn scan_and_chunk_by() {
    prints(
        "scan",
        &[
            ("[1, 2, 3].scan((+)) == [1, 3, 6]", "true"),
            ("[4, 1, 7, 2].scan((+)).last == [4, 1, 7, 2] >< (+)", "true"),
            ("[4, 1, 7, 2].scan(max).last == [4, 1, 7, 2] >< max", "true"),
            (
                "[1, 1, 2, 1].chunkBy(x -> x) == {0 -> {0 -> 1, 1 -> 1}, 1 -> {2 -> 2}, 2 -> {3 -> 1}}",
                "true",
            ),
        ],
    );
}

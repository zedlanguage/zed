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

/// Each program must be rejected at compile time, its message holding the given text.
#[track_caller]
fn saying(group: &str, cases: &[(&str, &str)]) {
    let wrong: Vec<String> = cases
        .iter()
        .enumerate()
        .filter_map(|(i, &(expr, text))| {
            let src = format!("main(m: MainArgs) {{\n  m.stdout <- \"${{{expr}}}\";\n}}\n");
            let out = run(&format!("fp_ops/{group}_say_{i}"), &src, "", &[]);
            (out.status == 0 || !out.stdout.is_empty() || !out.stderr.contains(text)).then(|| {
                format!(
                    "{expr}\n  want a message saying {text}\n  status {}, printed {}\n  {}",
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
            // `find` may give `#none`, which no port writes, so each key is compared.
            ("[5, 7, 9].find(x -> x > 6) == 1", "true"),
            ("[5, 7, 9].find(x -> x > 10) == #none", "true"),
            (
                "{\"x\" -> 1, \"y\" -> 5, \"z\" -> 7}.find(v -> v > 2) == \"y\"",
                "true",
            ),
            // `elem` and `elemIndex` of the inventory, as compositions.
            ("[5, 7, 9].any(x -> x == 7)", "true"),
            ("[5, 7, 9].find(x -> x == 9) == 2", "true"),
        ],
    );
}

/// Step L3.15a: the walk stops at the deciding entry, so a failure of `p` past it is never
/// met, and a failure before it is the result. Each result may be the failure, so each is
/// compared with `==`.
#[test]
fn quantifiers_stop_at_the_deciding_entry() {
    prints(
        "quantifiers_stop",
        &[
            ("[1, 0].any(x -> ({1 -> true})[x]) == true", "true"),
            ("[1, 0].all(x -> ({1 -> false})[x]) == false", "true"),
            ("[1, 0].find(x -> ({1 -> true})[x]) == 0", "true"),
            ("[0, 1].any(x -> ({1 -> true})[x]) == #notFound", "true"),
            ("[2, 0].all(x -> ({2 -> true})[x]) == #notFound", "true"),
            ("[1, 2].find(x -> x > 5) == #none", "true"),
            ("{}.any(x -> x > 0)", "false"),
            ("{}.find(x -> x > 0) == #none", "true"),
        ],
    );
}

/// The quantifiers' misuses, each named in the program's own words.
#[test]
fn a_misused_quantifier_is_rejected_in_plain_words() {
    saying(
        "quantifiers",
        &[
            (
                "[1, 2].any(x -> x + 1)",
                "`any` asks its function of each entry",
            ),
            ("[1, 2].all(3)", "`all` takes a function"),
            ("[1, 2].find()", "`find` takes one function"),
            ("(3).any(x -> x > 0)", "`any` reads the entries of a family"),
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
            ("[3, 1, 4].reduce((+))", "8"),
            ("[3, 1, 4].where(x -> x > 9).sum", "0"),
            ("([3, 1, 4].where(x -> x > 9) >< max) == #empty", "true"),
            ("[1, 2, 3].foldl(0, (a, x) -> a * 10 + x)", "123"),
            ("[1, 2, 3].foldr((x, a) -> a * 10 + x, 0)", "321"),
            (
                "{\"b\" -> 2, \"a\" -> 1}.foldl(0, (a, x) -> a * 10 + x)",
                "12",
            ),
            // A keyed level folds in key order, from either end.
            (
                "{\"b\" -> 2, \"a\" -> 1}.foldr((x, a) -> a * 10 + x, 0)",
                "21",
            ),
            ("{}.foldl(7, (a, x) -> a + x)", "7"),
            (
                "[1, 2, 3].where(x -> x > 1).foldl(0, (a, x) -> a * 10 + x)",
                "23",
            ),
            ("[3, 1, 4].reduce(max)", "4"),
            ("[3, 1, 4].reduce((*))", "12"),
            ("{\"b\" -> 2, \"a\" -> 5}.sum", "7"),
            ("{\"b\" -> 2, \"a\" -> 5}.count", "2"),
            ("{}.count", "0"),
            ("[1.5, 2.5].sum", "4.0"),
            ("[true, false].reduce((||))", "true"),
        ],
    );
}

/// sec:reduction: a non-associative operator on an ordered level is rejected.
#[test]
fn a_fold_by_a_non_associative_operator_is_rejected() {
    rejected(
        "folds",
        &["[1, 2, 3, 4] >< (-)", "[1, 2, 3, 4].reduce((-))"],
    );
}

/// sec:corner_cases: `first` and `last` are lexicographic, the leaf at the least and greatest
/// keypath; a level that may be empty adds `#none`.
#[test]
fn first_and_last_are_the_ends_in_key_order() {
    prints(
        "ends",
        &[
            ("[3, 1, 4].first", "3"),
            ("[3, 1, 4].last", "4"),
            ("[3, 1, 4].where(x -> x > 9).first == #none", "true"),
            ("{\"b\" -> 2, \"a\" -> 5}.first", "5"),
            ("{\"b\" -> 2, \"a\" -> 5}.last", "2"),
            ("[[1, 2], [3]].last", "3"),
            (
                "{1 -> {\"y\" -> 3, \"x\" -> 4}, 0 -> {\"q\" -> 5}}.first",
                "5",
            ),
        ],
    );
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

/// Step L5.3: a scan keeps the keys of its family, in key order; each entry is the fold of
/// its prefix by the operator; an empty family is its own scan.
#[test]
fn a_scan_keeps_the_keys_and_folds_each_prefix() {
    prints(
        "scan_more",
        &[
            ("[3, 1, 4, 1, 5].scan(min) == [3, 1, 1, 1, 1]", "true"),
            ("[3, 1, 4, 1, 5].scan(max) == [3, 3, 4, 4, 5]", "true"),
            ("[1, 2, 3, 4].scan((*)) == [1, 2, 6, 24]", "true"),
            (
                "[true, true, false, true].scan((&&)) == [true, true, false, false]",
                "true",
            ),
            (
                "[false, true, false].scan((||)) == [false, true, true]",
                "true",
            ),
            (
                "{\"b\" -> 2, \"a\" -> 5, \"c\" -> 7}.scan((+)) == {\"a\" -> 5, \"b\" -> 7, \"c\" -> 14}",
                "true",
            ),
            ("[7].scan((+)) == [7]", "true"),
            ("{}.scan((+)).count", "0"),
            ("{}.scan(max).count", "0"),
            ("[1, 2].where(x -> x > 5).scan((+)).count", "0"),
            ("[1, 2, 3, 4, 5, 6, 7].scan((+)).last", "28"),
            ("[2, 4, 6].reduce((+)) == [2, 4, 6].scan((+)).last", "true"),
            (
                "[5, 7, 9].where(x -> x > 5).scan((+)) == {1 -> 7, 2 -> 16}",
                "true",
            ),
        ],
    );
}

/// sec:reduction item 1: a float scan's entry `i` is the canonical-tree fold of entries
/// `0..=i`, the grouping `x >< (+)` uses, and not the left fold. On `[1e16, 1, 1, 1]` the tree
/// of all four is `(1e16 + 1) + (1 + 1)`, which is `1e16 + 2`, while the left fold adds each
/// `1` to `1e16` alone and rounds it away each time, giving `1e16`; the tree of the first
/// three, `(1e16 + 1) + 1`, is the left fold's grouping, so those agree.
#[test]
fn a_float_scan_rounds_each_prefix_as_its_fold_does() {
    let x = "[10000000000000000.0, 1.0, 1.0, 1.0]";
    let three = "[10000000000000000.0, 1.0, 1.0]";
    let left = "foldl(0.0, (a, v) -> a + v)";
    prints(
        "scan_float",
        &[
            (&format!("{x}.scan((+))[3] == {x} >< (+)"), "true"),
            (&format!("{x}.scan((+))[3] == {x}.{left}"), "false"),
            (&format!("{x}.scan((+))[2] == {three} >< (+)"), "true"),
            (&format!("{x}.scan((+))[2] == {three}.{left}"), "true"),
            ("[1.5, 2.5, 3.0].scan((+)) == [1.5, 4.0, 7.0]", "true"),
        ],
    );
}

/// The canonical tree of DESIGN.md sec:reduction item 1, written from its words, apart from
/// the elaborator's stack of power-of-two blocks: one element is itself; a power of two `n`
/// combines its halves; any other `n`, with `p` the largest power of two dividing it,
/// combines the first `n - p` with the last `p`.
fn canonical_sum(xs: &[f64]) -> f64 {
    let n = xs.len();
    if n == 1 {
        return xs[0];
    }
    let cut = match n.is_power_of_two() {
        true => n / 2,
        false => n - (1 << n.trailing_zeros()),
    };
    canonical_sum(&xs[..cut]) + canonical_sum(&xs[cut..])
}

/// `v` as a Zed float literal: Rust's `Display` writes the shortest digits that read back to
/// `v`, in fixed notation, and a Zed decimal literal is correctly rounded, so the literal is
/// `v` bit for bit.
fn float_lit(v: f64) -> String {
    let s = format!("{v}");
    match s.contains('.') {
        true => s,
        false => format!("{s}.0"),
    }
}

/// Plan row TEST-scan-float-long-chunk-ranks: at lengths past 4, each entry `i` of a float
/// scan is the canonical-tree sum of entries `0..=i` (DESIGN.md sec:reduction item 1: "Entry
/// `i` of a scan is the canonical-tree reduction of elements `0..=i`"), bit for bit, and its
/// last entry is the fold `x >< (+)`. The entries are `1e16` and `-1e16` every 16 places and
/// `1.0` elsewhere, so a `1.0` added to `1e16` alone rounds away while a sum of 1s added
/// first does not: every length here has a prefix whose tree sum differs from the left fold's,
/// which the test asserts, so a scan that grouped from the left fails it. The lengths cover
/// one block past a power of two (5, 9, 17), a power of two (8) and many blocks (100, 1000).
#[test]
fn a_long_float_scan_gives_each_prefix_its_canonical_tree_sum() {
    for n in [5usize, 8, 9, 17, 100, 1000] {
        let xs: Vec<f64> = (0..n)
            .map(|i| match (i % 16, (i / 16) % 2) {
                (0, 0) => 1e16,
                (0, _) => -1e16,
                _ => 1.0,
            })
            .collect();
        let tree: Vec<f64> = (1..=n).map(|i| canonical_sum(&xs[..i])).collect();
        let left: Vec<f64> = (xs.iter())
            .scan(0.0, |a, v| {
                *a += v;
                Some(*a)
            })
            .collect();
        assert!(
            tree.iter()
                .zip(&left)
                .any(|(t, l)| t.to_bits() != l.to_bits()),
            "at n = {n} no prefix's tree sum differs from the left fold's, so the test would \
             not tell them apart"
        );
        let list = |v: &[f64]| {
            let items: Vec<String> = v.iter().map(|&e| float_lit(e)).collect();
            format!("[{}]", items.join(", "))
        };
        let (x, tree, left) = (list(&xs), list(&tree), list(&left));
        prints(
            &format!("scan_float_long_{n}"),
            &[
                (&format!("{x}.scan((+)) == {tree}"), "true"),
                (&format!("{x}.scan((+)).last == {x} >< (+)"), "true"),
                (&format!("{x}.scan((+)) == {left}"), "false"),
            ],
        );
    }
}

/// Step L5.3: `chunkBy` splits where `f`'s value changes, the last run included; a run
/// keeps the keys of its entries; an empty family has no runs.
#[test]
fn chunk_by_splits_where_the_value_changes() {
    prints(
        "chunk",
        &[
            (
                "[1, 2, 3].chunkBy(x -> 0) == {0 -> {0 -> 1, 1 -> 2, 2 -> 3}}",
                "true",
            ),
            (
                "[1, 2, 3].chunkBy(x -> x) == {0 -> {0 -> 1}, 1 -> {1 -> 2}, 2 -> {2 -> 3}}",
                "true",
            ),
            (
                "[1, 3, 6, 4, 5].chunkBy(x -> x > 3) == {0 -> {0 -> 1, 1 -> 3}, 1 -> {2 -> 6, 3 -> 4, 4 -> 5}}",
                "true",
            ),
            (
                "[1, 3, 6, 2, 5].chunkBy(x -> x > 3) == {0 -> {0 -> 1, 1 -> 3}, 1 -> {2 -> 6}, 2 -> {3 -> 2}, 3 -> {4 -> 5}}",
                "true",
            ),
            (
                "{\"c\" -> 1, \"a\" -> 1, \"b\" -> 2}.chunkBy(x -> x) == {0 -> {\"a\" -> 1}, 1 -> {\"b\" -> 2}, 2 -> {\"c\" -> 1}}",
                "true",
            ),
            ("[1, 2].where(x -> x > 5).chunkBy(x -> x).count", "0"),
            ("{}.chunkBy(x -> x).count", "0"),
            // An atom `f` gives is compared as data, as `group`'s keys are.
            (
                "[1, 2, 3].chunkBy(x -> ({1 -> 0})[x]) == {0 -> {0 -> 1}, 1 -> {1 -> 2, 2 -> 3}}",
                "true",
            ),
            ("[4, 4, 5].chunkBy(x -> x).count", "2"),
            ("[4, 4, 5].chunkBy(x -> x)[0] == {0 -> 4, 1 -> 4}", "true"),
            ("[4, 4, 5].chunkBy(x -> x)[2] == #outOfBounds", "true"),
            (
                "[4, 4, 5].chunkBy(x -> x > 4).map(r -> r.sum) == [8, 5]",
                "true",
            ),
        ],
    );
}

/// Plan row TEST-scan-float-long-chunk-ranks: the outer level of `chunkBy` is the run index
/// from 0, every index present, a list (`Dense::Ranks`), so `flatMap` takes a `chunkBy` as
/// the list its function gives, and a read past the last run, or before the first, gives
/// `#outOfBounds`, as on a list; a run keeps its entries' own keys, so it is no list: a
/// missing key in it gives `#notFound`, and `flatMap` does not take a run as a list.
#[test]
fn chunk_by_runs_are_ranked_from_zero() {
    prints(
        "chunk_ranks",
        &[
            (
                "[1, 1, 2].chunkBy(x -> x).flatMap(r -> [r.count, r.sum]) == [[2, 2], [1, 2]]",
                "true",
            ),
            (
                "[[1, 1, 2], [3]].flatMap(v -> v.chunkBy(x -> x)) == [[{0 -> 1, 1 -> 1}, {2 -> 2}], [{0 -> 3}]]",
                "true",
            ),
            (
                "[[1, 1, 2], [3]].flatMap(v -> v.chunkBy(x -> x)).map(rs -> rs.count) == [2, 1]",
                "true",
            ),
            ("[4, 4, 5].chunkBy(x -> x)[5] == #outOfBounds", "true"),
            ("[4, 4, 5].chunkBy(x -> x)[-1] == #outOfBounds", "true"),
            ("{}.chunkBy(x -> x)[0] == #outOfBounds", "true"),
            ("[4, 4, 5].chunkBy(x -> x)[1][0] == #notFound", "true"),
            ("[4, 4, 5].chunkBy(x -> x)[1][2] == 5", "true"),
        ],
    );
    saying(
        "chunk_ranks",
        &[(
            "[4, 4, 5].chunkBy(x -> x).flatMap(r -> r)",
            "`flatMap` adjoins the list its function gives for each entry as a rank level",
        )],
    );
}

/// The misuses of `scan` and `chunkBy`, each named in the program's own words.
#[test]
fn a_misused_scan_or_chunk_by_is_rejected_in_plain_words() {
    saying(
        "scan",
        &[
            ("[1, 2].scan()", "`scan` takes one operator"),
            (
                "[1, 2].scan((-))",
                "`.scan` folds in any grouping, and `-` is not associative",
            ),
            (
                "[1, 2].scan((a, b) -> a)",
                "a scan `.scan` by a function other than",
            ),
            // A scan gives a family of running results, so its repair is a scan, never the
            // left fold `.reduce` is offered, which gives one value.
            (
                "[1, 2].scan((a, b) -> a)",
                "repair: scan by an operator section, `max` or `min` that combines two entries as the function does, as `[1, 2].scan((+))`",
            ),
            (
                "[1, 2].scan(1)",
                "`scan` takes a function, and this value is 1",
            ),
            ("(3).scan((+))", "`.scan` reads the entries of a family"),
            ("[1, 2].chunkBy()", "`chunkBy` takes one function"),
            ("[1, 2].chunkBy(3)", "`chunkBy` takes a function"),
            (
                "[1, 2].chunkBy((a, b) -> a)",
                "`chunkBy` calls its function with one argument",
            ),
            (
                "(3).chunkBy(x -> x)",
                "`chunkBy` reads the entries of a family",
            ),
        ],
    );
}

/// Step L3.2: `split` keeps every piece; `lines` ends a line at `\n`, `\r\n` and a lone `\r`
/// and keeps no empty line after the last line end; `concat(pieces, sep: s)` on strings, `sep`
/// `""` when not given, with the join law `concat(s.split(sep), sep: sep) == s` (QUESTIONS
/// A105, answered B); `concat` of a family of families is rejected, its repair `xss >< (++)`.
#[test]
fn split_lines_and_concat() {
    prints(
        "strings",
        &[
            ("\"\".split(\" \") == [\"\"]", "true"),
            ("\"a  b\".split(\" \") == [\"a\", \"\", \"b\"]", "true"),
            ("\"a,b,\".split(\",\") == [\"a\", \"b\", \"\"]", "true"),
            ("\"hé€\".split(\"é\") == [\"h\", \"€\"]", "true"),
            ("\"a,b\".split(\",\")[1] else \"none\"", "b"),
            ("\"a,b\".split(\",\")[2] else \"none\"", "none"),
            ("\"a\\nb\".lines[-1] else \"none\"", "none"),
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
            ("concat([\"a\", \"b\"], sep: \", \")", "a, b"),
            ("concat([\"a\", \"\", \"b\"], sep: \",\")", "a,,b"),
            ("concat([\"a\"], sep: \",\")", "a"),
            ("concat([]) == \"\"", "true"),
            ("concat([], sep: \",\") == \"\"", "true"),
            (
                "concat(\"a,,b,\".split(\",\"), sep: \",\") == \"a,,b,\"",
                "true",
            ),
            ("concat(\"\".split(\",\"), sep: \",\") == \"\"", "true"),
            // The repairs offered below, each run.
            ("[\"a\", \"b\"].concat", "ab"),
            ("[\"a\", \"b\"].concat(sep: \"-\")", "a-b"),
            ("[\"a\", \"b\"].concat(sep: \"\")", "ab"),
        ],
    );
    saying(
        "strings",
        &[
            ("concat([[1], [2]])", ">< (++)"),
            ("concat([1, 2])", "concat([1, 2].map(x -> String(x)))"),
            ("[1, 2].split(\",\")", "`split` reads strings"),
            ("\"a\".split()", "`split` takes"),
            ("concat([\"a\"], by: \",\")", "`concat` takes"),
        ],
    );
}

/// `program` run by `zedc run`: what it prints, or with status not 0 its error output.
fn ran(name: &str, program: &str) -> (u8, String) {
    let out = run(&format!("fp_ops/{name}"), program, "", &[]);
    match out.status {
        0 => (0, out.stdout),
        s => (s, out.stderr),
    }
}

/// An empty separator has no answer (DESIGN L3.2, author decision P314, plan row
/// FP-ops-split-empty-separator): `s.split("")` always fails, so it is rejected, and its message
/// names the views that read the characters of `s`; a separator that may be empty gives
/// `#emptySeparator` at `""`, and the atom is in the type of the call; a separator the checker
/// proves nonempty adds no atom.
#[test]
fn an_empty_separator_is_a_failure() {
    saying(
        "split_empty",
        &[
            (
                "\"ab\".split(\"\")",
                "`\"ab\".split(\"\")` always fails with `#emptySeparator`",
            ),
            ("\"ab\".split(\"\")", "repair: write `\"ab\"::codepoints`"),
            ("\"ab\".split(\"\")", "repair: write `\"ab\"::chars`"),
            ("\"ab\".split(\"\")", "repair: write `\"ab\"::u8`"),
            ("\"ab\".split(\"\")", "repair: write `\"ab\".split(sep)`"),
            ("split(\"\", \"\")", "`split(\"\", \"\")` always fails"),
            ("split(\"\", \"\")", "repair: write `split(\"\", sep)`"),
            ("split(\"\", \"\")", "repair: write `\"\"::codepoints`"),
        ],
    );
    // `d` may be empty: the call gives `#emptySeparator` there and the pieces elsewhere. The
    // parameters are `String`, the one string type this zedc defines; DESIGN's `d: Utf8String`
    // waits for plan row STR-types.
    let parts = "parts(s: String, d: String) = s.split(d);\n";
    let src = format!(
        "{parts}main(m: MainArgs) {{\n  m.stdout <- \"${{parts(s: \"a,b\", d: \"\") == \
         #emptySeparator}} ${{parts(s: \"a,b\", d: \",\") == [\"a\", \"b\"]}}\";\n}}\n"
    );
    assert_eq!(ran("split_empty_param", &src), (0, "true true\n".into()));
    // The atom is in the type: the joined pieces may be `#emptySeparator`, which is no text.
    let src = format!(
        "{parts}main(m: MainArgs) {{\n  m.stdout <- concat(parts(s: \"a,b\", d: \",\"));\n}}\n"
    );
    let (status, err) = ran("split_empty_param_type", &src);
    assert!(
        status != 0 && err.contains("#emptySeparator"),
        "{status}\n{err}"
    );
    // A literal separator that is not empty, and a name bound to one: the checker proves the
    // separator nonempty from its type, so there is no atom and the joined pieces go to
    // `m.stdout` as they are. A parameter `d: "," | ";"` or `d: String where d != ""` would show
    // the same, but this zedc compiles neither form yet (plan row L10.1; the two tests wait in
    // its deferred tests). A test `if d == "" { … } else { s.split(d) }` proves nothing of a
    // `String` `d`: a test `x != v` takes `v` out of a listed type only (DESIGN L1.39), and
    // `String` is not listed.
    let src = "main(m: MainArgs) {\n  m.stdout <- concat(\"a,b\".split(\",\"), sep: \"+\");\n}\n";
    assert_eq!(ran("split_nonempty_literal", src), (0, "a+b\n".into()));
    let src = "main(m: MainArgs) {\n  d = \",\";\n  m.stdout <- concat(\"a,b\".split(d), sep: \"+\");\n}\n";
    assert_eq!(ran("split_nonempty_bound", src), (0, "a+b\n".into()));
}

/// A call of `split`, `lines` or `concat` of the wrong shape is repaired with the operands the
/// program wrote, in its own style, method or function; a missing operand is named by its
/// parameter, as DESIGN step L3.2 writes it, and no separator the program did not write is
/// offered (plan row FAIL-l01-37a-split-snapshot).
#[test]
fn a_misshapen_string_call_is_repaired_with_the_programs_operands() {
    saying(
        "strings_repair",
        &[
            (
                "[\"a\", \"b\"].concat(\"-\")",
                "repair: write `[\"a\", \"b\"].concat(sep: \"-\")`",
            ),
            (
                "[\"a\", \"b\"].concat(\"\")",
                "repair: write `[\"a\", \"b\"].concat`",
            ),
            (
                "[\"a\", \"b\"].concat(\"\")",
                "repair: write `[\"a\", \"b\"].concat(sep: \"\")`",
            ),
            (
                "concat([\"a\"], \",\")",
                "repair: write `concat([\"a\"], sep: \",\")`",
            ),
            (
                "concat([\"a\"], by: \",\")",
                "repair: write `concat([\"a\"], sep: \",\")`",
            ),
            ("\"a\".split()", "repair: write `\"a\".split(sep)`"),
            ("split(\"a\")", "repair: write `split(\"a\", sep)`"),
            // `"a".split("")` always fails (DESIGN L3.2, P314), so it is never the repair; the
            // views that read the characters are, as in the message for `"a".split("")`.
            ("\"a\".split(sep: \"\")", "repair: write `\"a\".split(sep)`"),
            (
                "\"a\".split(sep: \"\")",
                "repair: write `\"a\"::codepoints`",
            ),
            ("\"a\".split(sep: \"\")", "repair: write `\"a\"::chars`"),
            ("\"a\".split(sep: \"\")", "repair: write `\"a\"::u8`"),
            (
                "split(\"a\", by: \"\")",
                "repair: write `\"a\"::codepoints`",
            ),
            (
                "\"a\".split(\",\", \";\")",
                "repair: write `\"a\".split(\",\")`",
            ),
            ("\"a\".lines(1)", "repair: write `\"a\".lines`"),
        ],
    );
}

/// `split` and `concat` on a line of `m.stdin` in a function passed to `map`, whose type is
/// generic there, are checked where `map` applies the function to the lines (plan row
/// FP-ops-generic-strings, as corpus 09-canonical-equal does at 11:13).
#[test]
fn split_and_concat_on_a_line_of_standard_input_run() {
    let src = "main(m: MainArgs) {\n  m.stdout <- m.stdin.map(l -> concat(l.split(\",\")));\n}\n";
    let out = run("fp_ops/strings_generic_run", src, "a,b\nc\n", &[]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "ab\nc\n"), "{}", out.stderr);
}

/// `program` run by `zedc run` must be rejected, its error output holding each of `texts`.
#[track_caller]
fn rejected_saying(name: &str, program: &str, texts: &[&str]) {
    let (status, err) = ran(name, program);
    let missing: Vec<&&str> = texts.iter().filter(|t| !err.contains(**t)).collect();
    assert!(
        status != 0 && missing.is_empty(),
        "status {status}, missing {missing:?}\n{err}"
    );
}

/// `split`, `lines` and `concat` in a generic function: each operand whose type is generic is
/// checked at each call, on the type the call gives it, and every operand at once, so whether
/// `split`'s separator may be `""` is read from its whole type there (P314): `""` at a call is
/// rejected as at `s.split("")`, and a separator that may be `""` gives `#emptySeparator`. The
/// parts that are not generic are checked at the definition, once (plan row
/// FP-ops-generic-strings).
#[test]
fn a_string_word_in_a_generic_function_is_checked_at_each_call() {
    let main = |body: &str| format!("main(m: MainArgs) {{\n  m.stdout <- \"{body}\";\n}}\n");
    let p = "p(positional s, positional d) = s.split(d);\n";
    // Two calls, of two separators; a generic function calling another.
    let src = format!(
        "{p}p2(positional s) = p(s, \",\");\n{}",
        main("${p(\"a,b\", \",\") == [\"a\", \"b\"]} ${p(\"x y z\", \" \").count} ${p2(\"a,b,c\").count}")
    );
    assert_eq!(ran("strings_generic_split", &src), (0, "true 3 3\n".into()));
    // `lines`, and `concat` of generic pieces, of a generic separator and of generic entries.
    let src = format!(
        "ls(positional s) = s.lines.count;\nj(positional xs) = concat(xs, sep: \"-\");\n\
         k(positional s) = concat([\"a\", \"b\"], sep: s);\n\
         two(positional x) = concat([x, x], sep: \",\");\n{}",
        main("${ls(\"a\\nb\")} ${j([\"a\", \"b\"])} ${j(\"x;y\".split(\";\"))} ${k(\"+\")} ${two(\"a\")}")
    );
    assert_eq!(
        ran("strings_generic_others", &src),
        (0, "2 a-b x-y a+b a,a\n".into())
    );
    // A separator that may be `""` at the call gives `#emptySeparator` there, and the atom is
    // in the type of the call.
    let q = format!("{p}q(d: String) = p(\"a,b\", d);\n");
    let src = format!(
        "{q}{}",
        main("${q(d: \"\") == #emptySeparator} ${q(d: \",\") == [\"a\", \"b\"]}")
    );
    assert_eq!(ran("strings_generic_maybe_empty", &src), (0, "true true\n".into()));
    let src = format!("{q}main(m: MainArgs) {{\n  m.stdout <- concat(q(d: \",\"));\n}}\n");
    rejected_saying("strings_generic_maybe_empty_type", &src, &["#emptySeparator"]);
    // A call whose separator is always `""` always fails, and one that passes no string is
    // rejected, each in the word's own message, at the call.
    let src = format!("{p}{}", main("${p(\"ab\", \"\").count}"));
    rejected_saying(
        "strings_generic_empty",
        &src,
        &["always fails with `#emptySeparator`"],
    );
    let src = format!("{p}{}", main("${p(1, \",\").count}"));
    rejected_saying(
        "strings_generic_not_string",
        &src,
        &["`split` reads strings, and this value is 1"],
    );
    let src = format!(
        "j(positional xs) = concat(xs, sep: \"-\");\n{}",
        main("${j([1, 2])}")
    );
    rejected_saying(
        "strings_generic_not_strings",
        &src,
        &["`concat` joins strings, and an entry of this family is"],
    );
    let src = format!(
        "two(positional x) = concat([x, x], sep: \",\");\n{}",
        main("${two(1)}")
    );
    rejected_saying(
        "strings_generic_entry",
        &src,
        &["`concat` joins strings, and an entry of this family is 1"],
    );
    // A part that is not generic is rejected at the definition, and once, not again at the
    // call; `split("")` on a line of `m.stdin` is rejected as on any string.
    let src = format!(
        "z(positional d) = concat([1], sep: d);\n{}",
        main("${z(\",\")}")
    );
    let (status, err) = ran("strings_generic_definition", &src);
    let said = err.matches("an entry of this family is 1").count();
    assert!(status != 0 && said == 1, "status {status}, said {said} times\n{err}");
    let src = "main(m: MainArgs) {\n  m.stdout <- m.stdin.map(l -> concat(l.split(\"\")));\n}\n";
    rejected_saying(
        "strings_generic_line_empty",
        src,
        &[
            "always fails with `#emptySeparator`",
            "repair: write `l::codepoints`",
        ],
    );
}

/// A parameter of a lambda given to `map` on a receiver of known type is generic while the
/// lambda's body is checked; the note on it says so and names what it ranges over, the entries
/// of the receiver as the program wrote it, never `_`, which in Zed is the type of every value
/// (author A92; plan row MSG-generic-operand-wording).
#[test]
fn a_generic_operand_is_not_shown_as_every_value() {
    let src = "main(m: MainArgs) {\n  m.stdout <- m.stdin.map(l -> concat(l.split(\",\")));\n}\n";
    let out = run("fp_ops/strings_generic_note", src, "", &[]);
    assert!(out.status != 0, "{}", out.stderr);
    assert!(!out.stderr.contains("`l` is _ here"), "{}", out.stderr);
    let want = "`l` has a generic type here, and `map` gives it each entry of `m.stdin`, \
                whose type is String";
    assert!(out.stderr.contains(want), "{}", out.stderr);
    // An `else` that reads the result lets loose atoms pass beside the variable, which also
    // printed as `_`; the note is the same (zed/corpus/09-canonical-equal.zed has this form).
    let src =
        "main(m: MainArgs) {\n  m.stdout <- m.stdin.map(l -> l.split(\" | \")[0] else \"\");\n}\n";
    let out = run("fp_ops/strings_generic_note_else", src, "", &[]);
    assert!(out.status != 0, "{}", out.stderr);
    assert!(!out.stderr.contains("`l` is _ here"), "{}", out.stderr);
    assert!(out.stderr.contains(want), "{}", out.stderr);
}

/// A built-in word on a parameter whose type is not written is not compiled yet; the message
/// names the operand by its code and calls its type generic, as the string words do, not a
/// type parameter, which the program does not write (plan row MSG-generic-operand-wording).
#[test]
fn a_word_on_an_untyped_parameter_names_the_parameter() {
    let src = "f(positional xs) = concat(xs);\nmain(m: MainArgs) {\n  m.stdout <- f([\"a\"]);\n}\n";
    let out = run("fp_ops/generic_levels", src, "", &[]);
    let want = "`concat` on `xs`, whose type is generic here, is part of";
    assert!(
        out.status != 0 && out.stderr.contains(want) && !out.stderr.contains("type parameter"),
        "status {}\n{}",
        out.status,
        out.stderr
    );
}

/// Each repair and headline of a misused fold, level word, string word or `++` writes the
/// operands as the program wrote them where they are on one line, not invented names such as
/// `xs` (plan row MSG-example-repairs).
#[test]
fn repairs_write_the_operands_as_the_program_wrote_them() {
    saying(
        "operand_repairs",
        &[
            ("[1, 2].sum(1)", "repair: write `[1, 2].sum`"),
            ("[1, 2].map()", "as `[1, 2].map(f)`"),
            ("[1, 2].map()", "repair: write `[1, 2].map(x -> …)`"),
            (
                "[1, 2].where(x -> x > 1, 2)",
                "repair: write `[1, 2].where(x -> …)`",
            ),
            (
                "[1, 2].foldl(0)",
                "repair: write `[1, 2].foldl(init, (a, x) -> a + x)`",
            ),
            (
                "[1, 2].foldr(0)",
                "repair: write `[1, 2].foldr((x, a) -> x + a, init)`",
            ),
            (
                "[1, 2].flatMap()",
                "repair: write `[1, 2].flatMap(x -> [x, x + 1])`",
            ),
            ("[1, 2].group()", "repair: write `[1, 2].group(x -> …)`"),
            ("[1, 2].count(1)", "repair: write `[1, 2].count`"),
            ("[1, 2].first(1)", "repair: write `[1, 2].first`"),
            ("[1, 2].reduce()", "repair: write `[1, 2].reduce((+))`"),
            ("[1, 2].scan()", "repair: write `[1, 2].scan((+))`"),
            (
                "[1, 2].chunkBy()",
                "repair: write `[1, 2].chunkBy(x -> x.id)`",
            ),
            ("[1, 2].any()", "repair: write `[1, 2].any(x -> x > 0)`"),
            ("[1, 2].zip()", "repair: write `[1, 2].zip(ys)`"),
            // A receiver that is not a name or a display is put in parentheses.
            (
                "([1] ++ [2]).count(1)",
                "repair: write `([1] ++ [2]).count`",
            ),
            ("[1, 2].scan(1)", "as `[1, 2].scan((+))`"),
            (
                "[1, 2] >< ((a, b) -> a)",
                "repair: fold left to right, which owes no law, as `[1, 2].foldl(init, (a, b) -> a)`",
            ),
            (
                "[1, 2].reduce((-))",
                "repair: fold left to right, as `[1, 2].foldl(init, (a, x) -> a - x)`",
            ),
            (
                "[1, 2].reduce((-))",
                "repair: fold right to left, as `[1, 2].foldr((x, a) -> x - a, init)`",
            ),
            (
                "[1, 2] >< (-)",
                "repair: fold left to right, as `[1, 2].foldl(init, (a, x) -> a - x)`",
            ),
            ("concat([[1], [2]])", "as `[[1], [2]] >< (++)`"),
            (
                "concat([\"a\"], sep: 1)",
                "as `concat([\"a\"], sep: \", \")`",
            ),
            ("[\"a\"].concat(sep: 1)", "as `[\"a\"].concat(sep: \", \")`"),
            ("\"a\".split(1)", "as `\"a\".split(\",\")`"),
            ("split(\"a\", 1)", "as `split(\"a\", \",\")`"),
            ("split([1, 2], \";\")", "as `split(\"a,b\", \";\")`"),
            // A written separator that is empty is not copied: the repair would be rejected.
            ("split(1, \"\")", "as `split(\"a,b\", \",\")`"),
            ("(1).split(\"\")", "as `\"a,b\".split(\",\")`"),
            ("1 ++ [2]", "as `[1] ++ [2]`"),
            ("[2] ++ 1", "as `[2] ++ [1]`"),
        ],
    );
}

/// The folds' and ends' misuses, each named in the program's own words.
#[test]
fn a_misused_fold_or_end_is_rejected_in_plain_words() {
    saying(
        "folds",
        &[
            ("[1, 2].count(1)", "`count` takes no arguments"),
            ("[1, 2].last(0)", "`last` takes no arguments"),
            ("[1, 2].reduce()", "`reduce` takes one operator"),
            ("(3).first", "`first` reads the entries of a family"),
            (
                "[1, 2].reduce((-))",
                "`.reduce` folds in any grouping, and `-` is not associative",
            ),
            (
                "[1, 2].reduce((a, b) -> a)",
                "a fold `.reduce` by a function other than",
            ),
            (
                "[1, 2].reduce((a, b) -> a)",
                "repair: fold left to right, which owes no law, as `[1, 2].foldl(init, (a, b) -> a)`",
            ),
            (
                "[1, 2].reduce(1)",
                "`reduce` takes a function, and this value is 1",
            ),
        ],
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

/// Step L5.2: `++` on lists of any entries, nested lists (an empty entry kept), ranges from 0,
/// the empty family `{}`, and chains; on two strings it still joins the strings.
#[test]
fn concatenation_joins_lists_in_order() {
    prints(
        "concat",
        &[
            ("[[1]] ++ [[], [2]] == [[1], [], [2]]", "true"),
            ("([[1]] ++ [[], [2]]).count", "3"),
            ("(0 ..< 3) ++ [7] == [0, 1, 2, 7]", "true"),
            ("{} ++ [1] == [1]", "true"),
            ("[1] ++ {} == [1]", "true"),
            ("({} ++ {}).count", "0"),
            ("([1] ++ [2]) ++ ([3] ++ [4]) == [1, 2, 3, 4]", "true"),
            ("[1] ++ ([2] ++ [3]) == ([1] ++ [2]) ++ [3]", "true"),
            ("([\"a\"] ++ [\"b\"]).last", "b"),
            ("\"ab\" ++ \"c\"", "abc"),
        ],
    );
}

/// Step L5.2: `zip` after `++`, of keyed families with equal keys, of empty families, and
/// nested.
#[test]
fn zip_pairs_equal_keys() {
    prints(
        "zip_more",
        &[
            ("[1, 2].zip([1] ++ [2]) == [(1, 1), (2, 2)]", "true"),
            ("([1] ++ [2]).zip([3, 4]) == [(1, 3), (2, 4)]", "true"),
            (
                "{\"a\" -> 1}.zip({\"a\" -> 2}) == {\"a\" -> (1, 2)}",
                "true",
            ),
            ("{}.zip({}).count", "0"),
            ("[1].zip([2]).zip([3]) == [((1, 2), 3)]", "true"),
        ],
    );
}

/// Plan row RANGE-literal-keys: a range whose two ends the text fixes holds exactly the keys
/// between them, so `zip` and `++` read its keys as they read a list display's: zips of equal
/// ranges, a range beside a list, `..=`, negative, folded and empty ends, and `++` of ranges.
#[test]
fn a_range_with_literal_ends_has_exact_keys() {
    prints(
        "range_keys",
        &[
            ("(0 ..< 3).zip(0 ..< 3) == [(0, 0), (1, 1), (2, 2)]", "true"),
            ("(0 ..< 3).zip(0 ..< 3).count", "3"),
            (
                "(0 ..= 2).zip([5, 6, 7]) == [(0, 5), (1, 6), (2, 7)]",
                "true",
            ),
            ("[5, 6, 7].zip(0 ..< 3) == [(5, 0), (6, 1), (7, 2)]", "true"),
            ("(2 ..< 5).zip(2 ..= 4).map(p -> p[0] * p[1]).sum", "29"),
            ("(-2 ..< 1).zip(-2 ..= 0).count", "3"),
            ("(1 + 1 ..< 2 * 3).zip(2 ..< 6).count", "4"),
            ("(3 ..< 3).zip(5 ..< 5).count", "0"),
            ("(3 ..< 3).zip({}).count", "0"),
            (
                "((0 ..< 3) ++ [3]).zip([1, 2, 3, 4]) == [(0, 1), (1, 2), (2, 3), (3, 4)]",
                "true",
            ),
            (
                "([9] ++ (0 ..< 2)).zip(0 ..< 3) == [(9, 0), (0, 1), (1, 2)]",
                "true",
            ),
            ("((0 ..< 2) ++ (0 ..< 2)).zip(0 ..< 4).count", "4"),
            ("(0 ..< 3).zip(0 ..< 3).zip([7, 8, 9]).count", "3"),
            ("(3 ..< 3) ++ [1] == [1]", "true"),
            ("((3 ..< 3) ++ [1]).zip([5]).count", "1"),
            // Ends past 64 bits, kept as two ends at check time and at run time.
            (
                "(2 ^ 70 ..< 2 ^ 70 + 2).zip(2 ^ 70 ..= 2 ^ 70 + 1).count",
                "2",
            ),
        ],
    );
}

/// Plan row RANGE-literal-keys: ranges of literal ends whose keys differ are still rejected,
/// naming a key on one side only; a range with an end the text does not fix is unchanged.
#[test]
fn a_zip_of_ranges_with_unequal_keys_is_rejected() {
    saying(
        "range_keys",
        &[
            ("(0 ..< 3).zip(0 ..< 4)", "key 3 is in"),
            ("(0 ..< 3).zip([1, 2])", "key 2 is in"),
            ("(1 ..< 4).zip(0 ..< 3)", "key 3 is in"),
            ("(0 ..< 0).zip([1])", "key 0 is in"),
            // An end past 64 bits is two ends, not 10^20 listed keys.
            ("(0 ..< 3).zip(0 ..< 100000000000000000000)", "key 3 is in"),
            (
                "(0 ..< [1, 2].where(x -> x > 1).count).zip(0 ..< 1)",
                "nothing shows that each key of",
            ),
            (
                "(0 ..< 2) ++ (1 ..< 3)",
                "`++` joins lists, whose keys are the ranks",
            ),
        ],
    );
}

/// Plan row RANGE-literal-reads (DESIGN.md sec:type_language, the `m[k]` row): a read of a
/// range with exact keys at a key whose ints are known is `V` with no miss where each of them
/// is a key, so it prints with no `else`, and a static error where none is, its message
/// printing the keys as a type the program can write, `int[2..=4]`. A key whose ints the
/// checker does not know keeps the miss, as does one with a key on each side.
#[test]
fn a_read_of_exact_keys_at_a_known_key_has_no_miss() {
    prints(
        "range_reads",
        &[
            ("(2 ..< 5)[2]", "2"),
            ("(2 ..< 5)[4]", "4"),
            ("(2 ..= 4)[3]", "3"),
            ("(0 ..< 3)[(1)]", "1"),
            ("(-3 ..< 0)[-2]", "-2"),
            ("(0 ..< 3).zip([7, 8, 9])[1][1]", "8"),
            ("(2 ..< 5).zip(2 ..= 4)[3][1]", "3"),
            // A key past 64 bits, 2 ^ 70 + 1 written as a literal: `2 ^ 70 + 1` written as an
            // operation on bare literals is any number kind (row RANGE-read-literal-operation).
            (
                "(2 ^ 70 ..< 2 ^ 70 + 2)[1180591620717411303425] - 2 ^ 70",
                "1",
            ),
        ],
    );
    saying(
        "range_reads",
        &[
            ("(2 ..< 5)[7]", "the map's keys are `int[2..=4]`"),
            ("(2 ..< 5)[5]", "the map's keys are `int[2..=4]`"),
            ("(2 ..< 5)[1]", "the map's keys are `int[2..=4]`"),
            ("(2 ..< 5)[-1]", "the map's keys are `int[2..=4]`"),
            ("(5 ..< 2)[3]", "the map's keys are `Never`"),
            (
                "(2 ..< 5).zip(2 ..= 4)[5]",
                "the map's keys are `int[2..=4]`",
            ),
        ],
    );
    let main = |binds: &str, read: &str| {
        format!("main(m: MainArgs) {{\n{binds}  r = {read};\n  m.stdout <- \"${{r}}\";\n}}\n")
    };
    let accepted = [
        (main("  n = 4;\n", "(0 ..< n)[n - 1]"), "3\n"),
        (main("  k = 1 + 1;\n", "(2 ..< 5)[k]"), "2\n"),
        (main("  n = 1;\n", "(2 ..< 5)[n + 1]"), "2\n"),
        // Each of the key's ints, 2 and 4, is a key, whichever the run takes.
        (
            main("", "(2 ..< 5)[if m.args.count > 0 { 4 } else { 2 }]"),
            "2\n",
        ),
    ];
    for (i, (src, want)) in accepted.iter().enumerate() {
        assert_eq!(
            ran(&format!("range_read_known_{i}"), src),
            (0, want.to_string()),
            "{src}"
        );
    }
    let refused = [
        (
            main("  n = 4;\n", "(0 ..< n)[n]"),
            "`int[0..=3]`, which hold no `4`",
        ),
        (main("", "(2 ..< 5)[m.args.count]"), "String | #outOfBounds"),
        (
            main("", "(2 ..< 5)[if m.args.count > 0 { 5 } else { 2 }]"),
            "String | #outOfBounds",
        ),
    ];
    for (i, (src, text)) in refused.iter().enumerate() {
        let (status, said) = ran(&format!("range_read_unknown_{i}"), src);
        assert!(status != 0 && said.contains(text), "{src}\n{said}");
    }
}

/// The misuses of `++` and `zip`, each named in the program's own words: unequal keys, with
/// the key that is on one side only; a family whose keys are not ranks; a string beside a
/// list; a wrong argument list.
#[test]
fn a_misused_concatenation_or_zip_is_rejected_in_plain_words() {
    saying(
        "zip",
        &[
            (
                "[1, 2].zip([1])",
                "`zip` pairs the entries at equal keys, and key 1 is in `[1, 2]` but not in `[1]`",
            ),
            ("[1].zip([1, 2])", "key 1 is in `[1, 2]` but not in `[1]`"),
            (
                "{\"a\" -> 1}.zip({\"b\" -> 2})",
                "key \"a\" is in `{\"a\" -> 1}` but not in `{\"b\" -> 2}`",
            ),
            (
                "[1, 2].zip([3])",
                "`(0 ..< min([1, 2].count, [3].count)).map(i -> ([1, 2][i], [3][i]))`",
            ),
            (
                "[1, 2].where(x -> x > 1) ++ [1]",
                "`++` joins lists, whose keys are the ranks",
            ),
            // Keys 2, 3, 4: one interval, but not the ranks.
            (
                "(2 ..< 5) ++ [1]",
                "`++` joins lists, whose keys are the ranks",
            ),
            ("\"a\" ++ [1]", "`++` joins two lists or two strings"),
            ("[1, 2].zip()", "`zip` takes one family, passed by position"),
            ("(3).zip([1])", "`zip` reads the entries of a family"),
        ],
    );
}

/// Step L5.2 on a `Lines` input, whose count is known only at run time: `++` gives the lines
/// and then the list; a `zip` with it is rejected, since nothing shows the counts equal, and
/// the offered repair, the ranks both hold, compiles and runs.
#[test]
fn concatenation_and_zip_on_input_lines() {
    let cases = [
        ("m.stdout <- m.stdin ++ [\"z\"];", "a\nb\nz\n", 0),
        ("m.stdout <- \"${(m.stdin ++ [\"z\"]).count}\";", "3\n", 0),
        ("m.stdout <- m.stdin.zip([\"q\"]).map(p -> p[0]);", "", 1),
        (
            "m.stdout <- \"${(0 ..< min(m.stdin.count, [\"q\"].count)).map(i -> \
             (m.stdin[i], [\"q\"][i]))}\";",
            "{0 -> (\"a\", \"q\")}\n",
            0,
        ),
    ];
    for (i, (body, want, status)) in cases.iter().enumerate() {
        let src = format!("main(m: MainArgs) {{\n  {body}\n}}\n");
        let out = run(&format!("fp_ops/lines_{i}"), &src, "a\nb\n", &[]);
        assert_eq!(
            (out.status, out.stdout.as_str()),
            (*status, *want),
            "{body}\n{}",
            out.stderr
        );
    }
}

/// Plan row PROOF-range-end-known-values: a range's end gets a known value, and the range
/// exact keys, only where every run gives the end that value (the proof at `Ck::known`).
/// Each program is whole, `n` an end; each accepted one prints the count the run gives, and
/// each other one is rejected since nothing shows the keys equal, never with a wrong key.
#[test]
fn a_range_end_is_known_only_where_every_run_gives_it() {
    let zip = |n: &str, other: &str| format!("(0 ..< {n}).zip(0 ..< {other}).count");
    let main = |body: &str, shown: &str| {
        format!("main(m: MainArgs) {{\n{body}  m.stdout <- \"${{{shown}}}\";\n}}\n")
    };
    let accepted = [
        // A name bound once to literals, read inside a lambda: the closure holds that value.
        (
            main(
                "  n = 3;\n  g = k -> (0 ..< n).zip(0 ..< 3).count + k;\n",
                "g(1)",
            ),
            "4",
        ),
        // A block that binds names and returns one value.
        (
            main("  n = { a = 2; return a + 1; };\n", &zip("n", "3")),
            "3",
        ),
        // A block whose bindings read the input, returning a literal.
        (
            main(
                "  a = m.args.count;\n  n = { b = a; return 3; };\n",
                &zip("n", "3"),
            ),
            "3",
        ),
        // The prelude's bit words, called and as a method, folded by the kernel.
        (main("  n = bitAnd(7, 3);\n", &zip("n", "3")), "3"),
        (main("  n = 7.bitAnd(3);\n", &zip("n", "3")), "3"),
        // Integer division and remainder round toward minus infinity, as the run does.
        (
            main("  n = -7 div 2;\n", "(n ..< 0).zip(-4 ..< 0).count"),
            "4",
        ),
        (main("  n = -7 mod 2;\n", &zip("n", "1")), "1"),
        // Ends past 64 bits.
        (
            main(
                "  n = 2 ^ 63 - 1;\n",
                "(n ..< n + 2).zip(n ..= n + 1).count",
            ),
            "2",
        ),
    ];
    for (i, (src, want)) in accepted.iter().enumerate() {
        assert_eq!(
            ran(&format!("range_end_known_{i}"), src),
            (0, format!("{want}\n")),
            "{src}"
        );
    }
    let nothing = "nothing shows that";
    let refused = [
        // An end the run decides: a branch, a port's value, a call's result, a parameter
        // (ranged to one value or not), a lambda's parameter, `else`, `/`.
        main(
            "  c = m.args.count > 0;\n  n = if c { 3 } else { 4 };\n",
            &zip("n", "3"),
        ),
        main("  n = if true { 3 } else { 4 };\n", &zip("n", "3")),
        main(
            "  c = m.args.count > 0;\n  r = if c { 0 ..< 3 } else { 0 ..< 4 };\n",
            "r.zip(0 ..< 3).count",
        ),
        main("  n = m.args.count;\n", &zip("n", "0")),
        format!("three() = 3;\n{}", main("  n = three();\n", &zip("n", "3"))),
        format!(
            "f(n: int[3..=3]) = {};\n{}",
            zip("n", "3"),
            main("", "f(n: 3)")
        ),
        main("  g = k -> (0 ..< k).zip(0 ..< 3).count;\n", "g(3)"),
        main("  n = 3 else 4;\n", &zip("n", "3")),
        // A function or lambda of the program named after a bit word is not the bit word.
        main(
            "  bitAnd = (a, b) -> 5;\n  n = bitAnd(7, 3);\n",
            &zip("n", "5"),
        ),
    ];
    for (i, src) in refused.iter().enumerate() {
        let (status, said) = ran(&format!("range_end_unknown_{i}"), src);
        assert!(status != 0 && said.contains(nothing), "{src}\n{said}");
    }
}

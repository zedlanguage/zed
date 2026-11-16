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
                "repair: scan by an operator section, `max` or `min` that combines two entries as the function does, as `xs.scan((+))`",
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
            ("\"ab\".split(\"\") == [\"a\", \"b\"]", "true"),
            ("\"\".split(\"\") == [\"\"]", "true"),
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
                "repair: fold left to right, which owes no law, as `xs.foldl(init, (a, x) -> f(a, x))`",
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

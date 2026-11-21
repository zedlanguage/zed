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
/// want of a form this zedc does not support (that rejection says nothing about the rule).
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
                || out.stderr.contains("not supported by this version of zedc"))
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

/// Plan row FAIL-flatmap-entries-typed-as-families: `flatMap` keeps the list each entry's
/// function gives as a level (DESIGN.md sec:grouping: "`flatMap` on `K -> V0` with body
/// `V0 -> Seq(V)` yields `K -> rank -> V`"), and a word after it acts at the level it is
/// written on (sec:reduction: "`.map(f)` acts *at the level it is written on*"), so `map`,
/// `where` and a second `flatMap` are each given one of the lists, not the entries of the
/// lists; the checker and the run agree on that. Flattening is a separate remap (DOCS-TODO
/// 198), so `[[1, 2], [3]].flatMap(p -> p)` is not `[1, 2, 3]`, and a function that takes
/// one number is rejected after it.
#[test]
fn a_word_after_flat_map_is_given_each_list() {
    prints(
        "flat_map_then",
        &[
            ("[[1, 2], [3]].flatMap(p -> p) == [[1, 2], [3]]", "true"),
            ("[[1, 2], [3]].flatMap(p -> p) == [1, 2, 3]", "false"),
            (
                "[[1, 2], [3]].flatMap(p -> p).map(w -> w.count) == [2, 1]",
                "true",
            ),
            (
                "[[1, 2], [3]].flatMap(p -> p).map(w -> w.map(v -> v + 1)) == [[2, 3], [4]]",
                "true",
            ),
            (
                "[\"a,b\", \"c\"].flatMap(l -> l.split(\",\")) == [[\"a\", \"b\"], [\"c\"]]",
                "true",
            ),
            (
                "[\"a,b\", \"c\"].flatMap(l -> l.split(\",\")).map(ws -> ws.map(w -> w ++ \"!\")) == [[\"a!\", \"b!\"], [\"c!\"]]",
                "true",
            ),
            (
                "[[1, 2], [3]].flatMap(p -> p).where(w -> w.count > 1) == {0 -> [1, 2]}",
                "true",
            ),
            (
                "[[1, 2], [3]].flatMap(p -> p).where(w -> w.count > 1).count",
                "1",
            ),
            // A second `flatMap` is given each list too, and adjoins its own level.
            (
                "[[1, 2], [3]].flatMap(p -> p).flatMap(w -> [w.count, w.sum]) == [[2, 3], [1, 3]]",
                "true",
            ),
            (
                "[1, 2].flatMap(v -> [v, v * 10]).flatMap(w -> w.map(x -> [x])) == [[[1], [10]], [[2], [20]]]",
                "true",
            ),
        ],
    );
    saying(
        "flat_map_then",
        &[
            (
                "[[1, 2], [3]].flatMap(p -> p).map(w -> w + 1)",
                "the function given to `map` does not take (((0 | 1) -> 1 | 2) | (0 -> 3))",
            ),
            (
                "[[1, 2], [3]].flatMap(p -> p).where(w -> w > 1).count",
                "the function given to `where` does not take",
            ),
        ],
    );
    // A port's lines: each line's pieces are one list, so `map` is given the list.
    let src = "main(m: MainArgs) {\n  m.stdout <- m.stdin.flatMap(l -> l.split(\",\")).map(ws -> \"${ws.count}\");\n}\n";
    let out = run("fp_ops/flat_map_then_lines", src, "a,b\nc\n", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "2\n1\n"),
        "{}",
        out.stderr
    );
    // Generic functions: the function and the receiver are parameters, or the lambda's
    // parameter is generic; each call is checked on the lists it gives.
    let src = "h(positional f, positional m) = m.flatMap(f).map(w -> w.count);\n\
               g(positional m) = m.flatMap(v -> [v, v]).map(w -> w.sum);\n\
               main(m: MainArgs) {\n  m.stdout <- [\"${h(v -> [v, v * 10, 0], [1, 2]) == [3, 3]}\", \
               \"${g([1, 2]) == [2, 4]}\"];\n}\n";
    let out = run("fp_ops/flat_map_then_generic", src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "true\ntrue\n"),
        "{}",
        out.stderr
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
            ("\"a,b\".split(\",\")[1] else #outOfBounds -> \"none\"", "b"),
            (
                "\"a,b\".split(\",\")[2] else #outOfBounds -> \"none\"",
                "none",
            ),
            ("\"a\\nb\".lines[-1] else #outOfBounds -> \"none\"", "none"),
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
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "ab\nc\n"),
        "{}",
        out.stderr
    );
    // On a parameter whose type is not written, checked at the call.
    let src = "f(positional xs) = concat(xs);\nmain(m: MainArgs) {\n  m.stdout <- f([\"a\"]);\n}\n";
    let out = run("fp_ops/strings_generic_param", src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "a\n"),
        "{}",
        out.stderr
    );
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
        main(
            "${p(\"a,b\", \",\") == [\"a\", \"b\"]} ${p(\"x y z\", \" \").count} ${p2(\"a,b,c\").count}"
        )
    );
    assert_eq!(ran("strings_generic_split", &src), (0, "true 3 3\n".into()));
    // `lines`, and `concat` of generic pieces, of a generic separator and of generic entries.
    let src = format!(
        "ls(positional s) = s.lines.count;\nj(positional xs) = concat(xs, sep: \"-\");\n\
         k(positional s) = concat([\"a\", \"b\"], sep: s);\n\
         two(positional x) = concat([x, x], sep: \",\");\n{}",
        main(
            "${ls(\"a\\nb\")} ${j([\"a\", \"b\"])} ${j(\"x;y\".split(\";\"))} ${k(\"+\")} ${two(\"a\")}"
        )
    );
    assert_eq!(
        ran("strings_generic_others", &src),
        (0, "2 a-b x-y a+b a,a\n".into())
    );
    // A type variable the signature writes is checked at each call, as a parameter with no
    // type is.
    let src = format!(
        "g(x: T, y: T) = concat([x, y], sep: \"/\");\n{}",
        main("${g(x: \"a\", y: \"b\")}")
    );
    assert_eq!(
        ran("strings_generic_type_variable", &src),
        (0, "a/b\n".into())
    );
    // A separator that may be `""` at the call gives `#emptySeparator` there, and the atom is
    // in the type of the call.
    let q = format!("{p}q(d: String) = p(\"a,b\", d);\n");
    let src = format!(
        "{q}{}",
        main("${q(d: \"\") == #emptySeparator} ${q(d: \",\") == [\"a\", \"b\"]}")
    );
    assert_eq!(
        ran("strings_generic_maybe_empty", &src),
        (0, "true true\n".into())
    );
    let src = format!("{q}main(m: MainArgs) {{\n  m.stdout <- concat(q(d: \",\"));\n}}\n");
    rejected_saying(
        "strings_generic_maybe_empty_type",
        &src,
        &["#emptySeparator"],
    );
    // A call whose separator is always `""` always fails, and one that passes no string is
    // rejected, each in the word's own message, at the call.
    // Its repairs name no `s`, which is not in scope at the call; each marks the argument that
    // gives the operand and names its parameter, and rewrites that argument in the call (plan
    // row MSG-generic-call-repair-code).
    let src = format!("{p}{}", main("${p(\"ab\", \"\").count}"));
    rejected_saying(
        "strings_generic_empty",
        &src,
        &[
            "`p(\"ab\", \"\")` always fails with `#emptySeparator`",
            "this argument, passed as `d`, is the separator, which is always the empty string",
            "repair: write `p(\"ab\", \",\")`",
        ],
    );
    let (_, err) = ran("strings_generic_empty_names", &src);
    assert!(!err.contains("`s::codepoints`"), "{err}");
    let src = format!("{p}{}", main("${p(1, \",\").count}"));
    rejected_saying(
        "strings_generic_not_string",
        &src,
        &[
            "`split` reads strings, and this value, passed as `s`, is 1",
            "repair: write `p(\"a,b\", \",\")`",
        ],
    );
    let src = format!(
        "j(positional xs) = concat(xs, sep: \"-\");\n{}",
        main("${j([1, 2])}")
    );
    rejected_saying(
        "strings_generic_not_strings",
        &src,
        &[
            "`concat` joins strings, and this family, passed as `xs`, has an entry that is",
            "repair: write `j([\"a\", \"b\"])`",
        ],
    );
    let src = format!(
        "two(positional x) = concat([x, x], sep: \",\");\n{}",
        main("${two(1)}")
    );
    rejected_saying(
        "strings_generic_entry",
        &src,
        &[
            "`concat` joins strings, and this value, passed as `x`, is an entry of the family \
             it joins and is 1",
            "repair: write `two(\"a\")`",
        ],
    );
    // A part that is not generic is rejected at the definition, and once, not again at the
    // call; `split("")` on a line of `m.stdin` is rejected as on any string.
    let src = format!(
        "z(positional d) = concat([1], sep: d);\n{}",
        main("${z(\",\")}")
    );
    let (status, err) = ran("strings_generic_definition", &src);
    let said = err.matches("an entry of this family is 1").count();
    assert!(
        status != 0 && said == 1,
        "status {status}, said {said} times\n{err}"
    );
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

/// A rejection at a call of a generic function writes its repair as the call, with the
/// argument that gives the rejected operand replaced (plan row MSG-generic-call-repair-code).
#[test]
fn a_repair_at_a_generic_call_is_written_as_the_call() {
    let main = |body: &str| format!("main(m: MainArgs) {{\n  m.stdout <- \"{body}\";\n}}\n");
    let p = "p(positional s, positional d) = s.split(d);\n";
    let src = format!("{p}{}", main("${p(\"ab\", \"\").count}"));
    rejected_saying(
        "generic_call_repair_split",
        &src,
        &["repair: write `p(\"ab\", \",\")`"],
    );
    let src = format!(
        "two(positional x) = concat([x, x], sep: \",\");\n{}",
        main("${two(1)}")
    );
    rejected_saying(
        "generic_call_repair_concat",
        &src,
        &["repair: write `two(\"a\")`"],
    );
    // A call over two lines is not rewritten, since a repair is one line of code; the
    // argument is still marked and named, and the repair is said in words.
    let src = format!(
        "{p}main(m: MainArgs) {{\n  m.stdout <- concat(p(\"ab\",\n    \"\"), sep: \"-\");\n}}\n"
    );
    rejected_saying(
        "generic_call_repair_two_lines",
        &src,
        &[
            "this call always fails with `#emptySeparator`",
            "this argument, passed as `d`, is the separator",
            "repair: pass a separator that is not empty to this call",
        ],
    );
}

/// A fold written as the call `sum(x)` is named as the program wrote it, not as `.sum`
/// (plan row MSG-sum-function-form-headline).
#[test]
fn a_sum_written_as_a_call_is_named_as_a_call() {
    let src = "main(m: MainArgs) {\n  m.stdout <- \"${sum([\"a\", \"b\"])}\";\n}\n";
    let out = run("fp_ops/sum_call_headline", src, "", &[]);
    assert!(out.status != 0, "{}", out.stderr);
    assert!(!out.stderr.contains("`.sum`"), "{}", out.stderr);
    assert!(
        out.stderr.contains("`sum([\"a\", \"b\"])`"),
        "{}",
        out.stderr
    );
}

/// `split` on a line of `m.stdin` in a function passed to `map`, with an `else` that reads the
/// result and so lets loose atoms pass beside the line's generic type, is checked where `map`
/// applies the function to the lines (plan row FP-ops-generic-strings; the form of
/// zed/corpus/09-canonical-equal.zed at 11:13). Before that row this was refused, and plan row
/// MSG-generic-operand-wording tested its note on `l` here.
#[test]
fn split_with_else_on_a_line_of_standard_input_runs() {
    let src = "main(m: MainArgs) {\n  m.stdout <- m.stdin.map(l -> l.split(\" | \")[0] else #outOfBounds -> \"\");\n}\n";
    let out = run("fp_ops/strings_generic_else", src, "a | b\nc\n", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "a\nc\n"),
        "{}",
        out.stderr
    );
}

/// A built-in word on a parameter whose type is not written was not compiled; its message named
/// the operand by its code and called its type generic, not a type parameter, which the program
/// does not write (plan row MSG-generic-operand-wording). `concat(xs)` was the example until
/// plan row FP-ops-generic-strings compiled it, and `xs ++ ["a"]` until plan row
/// FP-ops-concat-fold-acc compiled that: the word is now met at each call, here on `["b"]`.
#[test]
fn a_word_on_an_untyped_parameter_names_the_parameter() {
    let src = "f(positional xs) = xs ++ [\"a\"];\nmain(m: MainArgs) {\n  m.stdout <- concat(f([\"b\"]));\n}\n";
    let out = run("fp_ops/generic_levels", src, "", &[]);
    assert!(
        out.status == 0 && out.stdout.trim_end() == "ba",
        "status {}\n{}{}",
        out.status,
        out.stdout,
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
            // The other operand keeps its place, and parentheses only where `++` needs them:
            // none on the left, since `++` groups from the left; on the right, a `++`.
            ("[2] ++ [3] ++ 1", "as `[2] ++ [3] ++ [1]`"),
            ("1 ++ ([2] ++ [3])", "as `[1] ++ ([2] ++ [3])`"),
            (
                "1 ++ ([\")\"] ++ [\"(\"])",
                "as `[1] ++ ([\")\"] ++ [\"(\"])`",
            ),
            ("1 ++ [[2]][0]", "as `[1] ++ [[2]][0]`"),
            // Fragments `in_parens` must read as tokens (plan row
            // TEST-msg-repair-parens-and-entries): nested brackets and parentheses, a comment
            // holding a parenthesis, a string holding a quote and a parenthesis, a hole.
            (
                "1 ++ (([2]) ++ [[3], [(4)]][0])",
                "as `[1] ++ (([2]) ++ [[3], [(4)]][0])`",
            ),
            (
                "1 ++ ([2] ++ /* ) */ [3])",
                "as `[1] ++ ([2] ++ /* ) */ [3])`",
            ),
            (
                "1 ++ ([\"\\\")\"] ++ [\"(\"])",
                "as `[1] ++ ([\"\\\")\"] ++ [\"(\"])`",
            ),
            (
                "1 ++ ([\"${(2)}\"] ++ [\")\"])",
                "as `[1] ++ ([\"${(2)}\"] ++ [\")\"])`",
            ),
            ("([2]) ++ ([3]) ++ 1", "as `([2]) ++ ([3]) ++ [1]`"),
        ],
    );
}

/// The `++` repair the checker prints is Zed that runs and means what the program meant: each
/// faulty expression is run, the form after "as" in its repair is cut out and run in turn,
/// and it must equal the list written by hand (plan row TEST-msg-repair-parens-and-entries).
#[test]
fn a_concat_repair_runs_and_gives_the_list_meant() {
    let cases = [
        ("1 ++ [2]", "[1, 2]"),
        ("[2] ++ [3] ++ 1", "[2, 3, 1]"),
        ("1 ++ ([2] ++ [3])", "[1, 2, 3]"),
        ("1 ++ (([2]) ++ [[3], [(4)]][0])", "[1, 2, 3]"),
        ("1 ++ ([2] ++ /* ) */ [3])", "[1, 2, 3]"),
        (
            "\"a\" ++ ([\"\\\")\"] ++ [\"(\"])",
            "[\"a\", \"\\\")\", \"(\"]",
        ),
        (
            "\"a\" ++ ([\"${(2)}\"] ++ [\")\"])",
            "[\"a\", \"2\", \")\"]",
        ),
        ("([2]) ++ ([3]) ++ 1", "[2, 3, 1]"),
    ];
    let mut wrong = Vec::new();
    for (i, (expr, meant)) in cases.into_iter().enumerate() {
        let src = format!("main(m: MainArgs) {{\n  m.stdout <- \"${{{expr}}}\";\n}}\n");
        let out = run(&format!("fp_ops/concat_repair_{i}"), &src, "", &[]);
        let Some(form) = (out.stderr.split_once("put the value in a list, as `"))
            .and_then(|(_, rest)| rest.split_once('`'))
            .map(|(form, _)| form.to_string())
        else {
            wrong.push(format!("{expr}: no repair\n  {}", out.stderr.trim_end()));
            continue;
        };
        let src = format!("main(m: MainArgs) {{\n  m.stdout <- \"${{{form} == {meant}}}\";\n}}\n");
        let ran = run(&format!("fp_ops/concat_repair_ran_{i}"), &src, "", &[]);
        if ran.status != 0 || ran.stdout.trim_end() != "true" {
            wrong.push(format!(
                "{expr}: the repair `{form}` is not {meant}\n  status {}, printed {}\n  {}",
                ran.status,
                ran.stdout.trim_end(),
                ran.stderr.trim_end()
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// `zip` on a lambda parameter that stays generic is checked on the entries the word gives it,
/// and the error names their type, never `_`, the type of every value (A92; plan rows
/// MSG-generic-operand-wording, TEST-msg-repair-parens-and-entries, ZIP-generic-operands).
/// One case per word that gives a lambda its entries (`map`, `flatMap`, `where`, `group`) and
/// per kind of receiver: a port's lines, the result of a word, entries that are families, and
/// a receiver over two lines. Before ZIP-generic-operands `zip` was refused on a generic
/// operand, and this test checked the note on the parameter that refusal carried.
#[test]
fn a_generic_lambda_parameter_is_noted_with_the_entries_it_is_given() {
    let string = "`zip` reads the entries of a family, and this value is String";
    let cases = [
        ("m.stdout <- m.stdin.map(l -> \"${l.zip([1])}\");", string),
        (
            "m.stdout <- m.stdin.flatMap(l -> [\"${l.zip([1])}\"]);",
            string,
        ),
        // Not `m.stdin.map(…)`, whose entries may be `#ioError`, which `where` does not take
        // yet (plan row WHERE-loose-atoms).
        (
            "m.stdout <- [\"a\", \" b\"].map(l -> l.trim).where(l -> \"${l.zip([1])}\" == \"\");",
            string,
        ),
        (
            "m.stdout <- \"${m.stdin.group(l -> l.zip([1])).count}\";",
            string,
        ),
        // A list of strings is a family; `[1]` may lack its keys.
        (
            "m.stdout <- m.stdin.map(l -> l.split(\",\")).map(p -> \"${p.zip([1])}\");",
            "nothing shows that each key of the family before `.zip` is in the argument of `zip`",
        ),
        (
            "m.stdout <- m.stdin.map(l ->\n    l.trim).map(l -> \"${l.zip([1])}\");",
            string,
        ),
    ];
    let mut wrong = Vec::new();
    for (i, (stmt, want)) in cases.into_iter().enumerate() {
        let src = format!("main(m: MainArgs) {{\n  {stmt}\n}}\n");
        let out = run(&format!("fp_ops/entry_note_{i}"), &src, "", &[]);
        // The placeholder note, as it read before and after row MSG-untyped-note-placeholder.
        let placeholder =
            out.stderr.contains(" is _ here") || out.stderr.contains(" has no type yet here");
        if out.status == 0 || !out.stderr.contains(want) || placeholder {
            wrong.push(format!(
                "{stmt}\n  want {want}\n  {}",
                out.stderr.trim_end()
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A list's type prints as DESIGN writes it, `[String]`, not as the arrow `int ->? String`,
/// which says keys may be missing (plan row MSG-list-type-printed-by-arrows). The pieces of
/// `l.split(",")` are such a list; `trim`, a word on strings, is refused on one.
#[test]
fn a_list_type_prints_as_a_list() {
    let src = "main(m: MainArgs) {\n  m.stdout <- m.stdin.map(l -> l.split(\",\")).map(p -> p.trim);\n}\n";
    let out = run("fp_ops/list_type_print", src, "", &[]);
    assert!(
        out.status != 0 && out.stderr.contains("([String])") && !out.stderr.contains("->?"),
        "{}",
        out.stderr
    );
}

/// Where the type of the entries a word gives a lambda parameter is not known in the body, as
/// those of a parameter of no written type, `zip` on it is checked at each call on what the
/// call gives, which the error names, never `_`, the type of every value (A92; plan rows
/// MSG-generic-param-entry-note-every-value, ZIP-generic-operands).
#[test]
fn an_entry_of_a_generic_parameter_is_not_shown_as_every_value() {
    let src = "f(positional xs) = xs.map(l -> \"${l.zip([1])}\");\nmain(m: MainArgs) {\n  m.stdout <- f([\"a\"]);\n}\n";
    let out = run("fp_ops/entry_note_generic_param", src, "", &[]);
    assert!(out.status != 0, "{}", out.stderr);
    assert!(!out.stderr.contains("`l` is _ here"), "{}", out.stderr);
    assert!(
        !out.stderr.contains("`l` has no type yet here"),
        "{}",
        out.stderr
    );
    assert!(
        out.stderr
            .contains("`zip` reads the entries of a family, and this value is \"a\""),
        "{}",
        out.stderr
    );
}

/// The note on a lambda parameter that stays generic names what the word gives it (plan rows
/// MSG-generic-operand-wording, MSG-generic-param-entry-note-every-value and
/// MSG-generic-lambda-note-unreached). Since ZIP-generic-operands no test above reaches it,
/// since `zip`, `++` and the level words on such a parameter each make a need, whose refusal
/// is at the use. A tuple holding the parameter, refused by `+` in the body, still is: one
/// case per word that gives a lambda its entries (`map`, `flatMap`, `where`, `group`), per
/// kind of receiver (a port's lines, the result of a word, entries that are families, a
/// receiver over two lines), and the parameter of a function of no written type, whose
/// entries' type is not known and is not written.
#[test]
fn a_generic_lambda_parameter_in_a_refused_tuple_is_noted_with_its_entries() {
    let note = |name: &str, word: &str, of: &str| {
        format!("`{name}` has a generic type here, and `{word}` gives it each entry of {of}")
    };
    let stdin = |word: &str| note("l", word, "`m.stdin`, whose type is String");
    let main = |stmt: &str| format!("main(m: MainArgs) {{\n  {stmt}\n}}\n");
    let cases = [
        (
            main("m.stdout <- m.stdin.map(l -> \"${(l, 1) + 1}\");"),
            stdin("map"),
        ),
        (
            main("m.stdout <- m.stdin.flatMap(l -> [\"${(l, 1) + 1}\"]);"),
            stdin("flatMap"),
        ),
        // Not `m.stdin.map(…)`, whose entries may be `#ioError`, which `where` does not take
        // yet (plan row WHERE-loose-atoms).
        (
            main(
                "m.stdout <- [\"a\", \" b\"].map(l -> l.trim).where(l -> \"${(l, 1) + 1}\" == \"\");",
            ),
            note(
                "l",
                "where",
                "`[\"a\", \" b\"].map(l -> l.trim)`, whose type is String",
            ),
        ),
        (
            main("m.stdout <- \"${m.stdin.group(l -> (l, 1) + 1).count}\";"),
            stdin("group"),
        ),
        (
            main("m.stdout <- m.stdin.map(l -> l.split(\",\")).map(p -> \"${(p, 1) + 1}\");"),
            note(
                "p",
                "map",
                "`m.stdin.map(l -> l.split(\",\"))`, whose type is [String]",
            ),
        ),
        (
            main("m.stdout <- m.stdin.map(l ->\n    l.trim).map(l -> \"${(l, 1) + 1}\");"),
            note("l", "map", "the family before `.map`, whose type is String"),
        ),
        (
            format!(
                "f(positional xs) = xs.map(l -> (l, 1) + 1);\n{}",
                main("m.stdout <- \"${f([1])}\";")
            ),
            note("l", "map", "`xs`\n"),
        ),
    ];
    let mut wrong = Vec::new();
    for (i, (src, want)) in cases.into_iter().enumerate() {
        let out = run(&format!("fp_ops/entry_note_tuple_{i}"), &src, "", &[]);
        // The placeholder note, as it read before and after row MSG-untyped-note-placeholder.
        let placeholder =
            out.stderr.contains(" is _ here") || out.stderr.contains(" has no type yet here");
        if out.status == 0 || !out.stderr.contains(&want) || placeholder {
            wrong.push(format!("{src}\n  want {want}\n  {}", out.stderr.trim_end()));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A list type written in a program, `[T]`, resolves and checks as the type the checker prints
/// for a list (plan row LIST-type-written): a parameter of type `[String]`, a list of lists,
/// and a list inside a tuple. The row's test named the function `count`, which `ps.count`
/// would call, so the body recursed; the function is `size` here.
#[test]
fn a_written_list_type_is_checked() {
    let src = "size(ps: [String]) = ps.count;\n\
               main(m: MainArgs) {\n  m.stdout <- \"${size(ps: \"a,b\".split(\",\"))}\";\n}\n";
    let out = run("fp_ops/list_type_written", src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "2\n"),
        "{}",
        out.stderr
    );
    let src = "firsts(rows: [[String]]) = rows.map(r -> r[0] else #outOfBounds -> \"\");\n\
               total(xs: [int]) = xs.count;\n\
               pairs(p: ([int], String)) = p[0].count;\n\
               main(m: MainArgs) {\n  m.stdout <- \"${firsts(rows: [\"a,b\".split(\",\"), \
               \"c\".split(\",\")])} ${total(xs: [1, 2, 3])} ${pairs(p: ([4], \"x\"))}\";\n}\n";
    let out = run("fp_ops/list_type_written_nested", src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "{0 -> \"a\", 1 -> \"c\"} 3 1\n"),
        "{}",
        out.stderr
    );
    // A value that is not such a list is refused, and the refusal prints the type as written.
    let src = "size(ps: [String]) = ps.count;\n\
               main(m: MainArgs) {\n  m.stdout <- \"${size(ps: [1, 2])}\";\n}\n";
    let out = run("fp_ops/list_type_written_refused", src, "", &[]);
    assert!(
        out.status != 0 && out.stderr.contains("[String]") && !out.stderr.contains("->?"),
        "{}",
        out.stderr
    );
    // The kernel has no list type, so the check that a bound's guarantee is within its
    // permission cannot read one: a list type there is refused, never passed unchecked (this
    // guarantee is not within its permission).
    let src = "g(f: ([#a | #c] .. [#a | #b] -> int)) = 1;\n\
               main(m: MainArgs) {\n  m.stdout <- \"${g(f: x -> 1)}\";\n}\n";
    let out = run("fp_ops/list_type_written_in_a_bound", src, "", &[]);
    assert!(
        out.status != 0
            && out.stderr.contains(
                "a list type `[T]` inside a function type `L .. U -> V` is part of the Zed \
                 language but is not supported by this version of zedc"
            ),
        "{}",
        out.stderr
    );
}

/// The function given to `flatMap` is named as given to `flatMap`, not `map`, and the repair
/// for a value that is not a function is a function `flatMap` takes, one that gives a list
/// (plan row MSG-flatmap-labeled-map).
#[test]
fn the_function_given_to_flat_map_is_named_so() {
    for (i, (expr, want)) in [
        (
            "[1, 2].flatMap(x -> [x.trim])",
            "the function given to `flatMap` does not take",
        ),
        (
            "[1, 2].flatMap(5)",
            "repair: pass a function of one parameter, as `x -> [x]`",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let src = format!("main(m: MainArgs) {{\n  m.stdout <- \"${{{expr}}}\";\n}}\n");
        let out = run(&format!("fp_ops/flat_map_label_{i}"), &src, "", &[]);
        assert!(out.status != 0, "{expr}: {}", out.stderr);
        assert!(out.stderr.contains(want), "{expr}: {}", out.stderr);
        assert!(!out.stderr.contains("`map`"), "{expr}: {}", out.stderr);
    }
}

/// `flatMap` on a parameter of no written type demands a list of each entry at the call, as it
/// does on a family written at the use (plan row FLATMAP-generic-demand): before, the need met
/// at the call checked it as `map`, and `h(x: [1, 2])` ran and printed `{0 -> 2, 1 -> 3}`.
#[test]
fn flat_map_on_a_generic_parameter_demands_a_list_of_each_entry() {
    let src = "h(x) = x.flatMap(e -> e + 1);\n\
               main(m: MainArgs) {\n  m.stdout <- \"${h(x: [1, 2])}\";\n}\n";
    let out = run("fp_ops/flat_map_generic_demand", src, "", &[]);
    assert!(
        out.status != 0
            && out.stderr.contains(
                "`flatMap` adjoins the list its function gives for each entry as a rank level"
            )
            && out.stderr.contains("`h` needs this of its argument here"),
        "{}\n{}",
        out.stdout,
        out.stderr
    );
    // A function that gives a list is taken, and the lists are the inner level.
    let src = "h(x) = x.flatMap(e -> [e, e]);\n\
               main(m: MainArgs) {\n  m.stdout <- \"${h(x: [1, 2])}\";\n}\n";
    let out = run("fp_ops/flat_map_generic_lists", src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "{0 -> {0 -> 1, 1 -> 1}, 1 -> {0 -> 2, 1 -> 2}}\n"),
        "{}",
        out.stderr
    );
}

/// A family whose entries hold a lambda's generic parameter is printed with that parameter's
/// type by what it ranges over, never `_`, the type of every value (A92): `l` is a line of
/// `m.stdin`, a String (plan row MSG-generic-entry-shown-as-every-value).
#[test]
fn a_generic_entry_of_a_family_is_not_shown_as_every_value() {
    let src = "main(m: MainArgs) {\n  m.stdout <- m.stdin.map(l -> concat([l, 1]));\n}\n";
    let out = run("fp_ops/strings_generic_entry_note", src, "a\n", &[]);
    assert!(out.status != 0, "{}", out.stderr);
    assert!(
        out.stderr.contains("`concat` joins strings"),
        "{}",
        out.stderr
    );
    assert!(!out.stderr.contains("-> _"), "{}", out.stderr);
    let want = "this expression is (0 | 1) -> 1 | String";
    assert!(out.stderr.contains(want), "{}", out.stderr);
}

/// `++` on a lambda's generic parameter says what the parameter is (plan row
/// MSG-concat-generic-lambda-param-no-note). Since FP-ops-concat-fold-acc the `++` takes a
/// need, met where `map` gives the lambda each entry of `m.stdin`: the refusal names the
/// entry's type, String, and the `++` that needs a list, and never calls the type generic.
#[test]
fn concat_on_a_generic_lambda_parameter_notes_what_it_is() {
    let src = "main(m: MainArgs) {\n  m.stdout <- m.stdin.map(l -> \"${l ++ [1]}\");\n}\n";
    let out = run("fp_ops/concat_generic_note", src, "", &[]);
    assert!(out.status != 0, "{}", out.stderr);
    for want in [
        "this value is String, beside a list",
        "the function given to `map` needs this of its argument here",
    ] {
        assert!(out.stderr.contains(want), "{}", out.stderr);
    }
    assert!(!out.stderr.contains("generic here"), "{}", out.stderr);
}

/// `flatMap` keeps each list its function gives as a level (DESIGN.md sec:grouping, "`flatMap`
/// on `K -> V0` with body `V0 -> Seq(V)` yields `K -> rank -> V`"), which a reader from Scala or
/// Haskell does not expect (DOCS-TODO 198): a word after it whose function would take the
/// entries of those lists is told so, and `map` is given the repair as code, which runs (plan
/// row MSG-flatmap-kept-level-repair).
#[test]
fn a_function_after_flat_map_that_takes_the_lists_entries_is_told_of_the_level() {
    saying(
        "flat_map_level_note",
        &[
            (
                "[[1, 2], [3]].flatMap(p -> p).map(w -> w + 1)",
                "`flatMap` keeps each list",
            ),
            (
                "[[1, 2], [3]].flatMap(p -> p).map(w -> w + 1)",
                "repair: write `[[1, 2], [3]].flatMap(p -> p).map(w -> w.map(v -> v + 1))`",
            ),
            (
                "[[1, 2], [3]].flatMap(p -> p).where(w -> w > 1).count",
                "`flatMap` keeps each list",
            ),
            // The inner parameter takes a name the body does not write.
            (
                "[[1, 2], [3]].flatMap(p -> p).map(v -> v + 1)",
                "repair: write `[[1, 2], [3]].flatMap(p -> p).map(v -> v.map(u -> u + 1))`",
            ),
        ],
    );
    let src = "main(m: MainArgs) {\n  m.stdout <- \"${[[1, 2], [3]].flatMap(p -> p).map(w -> \
               w.map(v -> v + 1)).count}\";\n}\n";
    let out = run("fp_ops/flat_map_level_repair_runs", src, "", &[]);
    assert!(out.status == 0, "{}", out.stderr);
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
            // A key past 64 bits, written as a literal and as an operation on bare integer
            // literals, which is read as the `int` it folds to (row
            // RANGE-read-literal-operation).
            (
                "(2 ^ 70 ..< 2 ^ 70 + 2)[1180591620717411303425] - 2 ^ 70",
                "1",
            ),
            ("(2 ..< 5)[1 + 1]", "2"),
            ("(2 ^ 70 ..< 2 ^ 70 + 2)[2 ^ 70 + 1] - 2 ^ 70", "1"),
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
        // Row RANGE-read-key-intervals: the ints a test bounds a computed key to, and those
        // of a ranged parameter, lie in the keys; and the call form reads as the bracket does.
        (
            main(
                "  k = m.args.count + 3;\n",
                "if k >= 2 && k < 5 { (2 ..< 5)[k] } else { 0 }",
            ),
            "3\n",
        ),
        (
            format!("f(k: int[2..=4]) = (2 ..< 5)[k];\n{}", main("", "f(k: 4)")),
            "4\n",
        ),
        (main("", "(2 ..< 5)(3)"), "3\n"),
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
        // A test that bounds the key to ints outside the keys, a parameter whose range is
        // outside them, and the call form at a key outside them: each is the static error.
        (
            main(
                "  k = m.args.count;\n",
                "if k >= 5 { (2 ..< 5)[k] } else { 0 }",
            ),
            "the map's keys are `int[2..=4]`",
        ),
        (
            format!("f(k: int[5..=9]) = (2 ..< 5)[k];\n{}", main("", "f(k: 6)")),
            "the map's keys are `int[2..=4]`",
        ),
        (main("", "(2 ..< 5)(9)"), "the map's keys are `int[2..=4]`"),
        // A test that bounds the key to ints on each side of the keys keeps the miss.
        (
            main(
                "  k = m.args.count;\n",
                "if k >= 3 { (2 ..< 5)[k] } else { 0 }",
            ),
            "String | #outOfBounds",
        ),
        // An operation on integer literals outside the keys is the static error; one with a
        // decimal literal runs as the `f64` `2.0`, which is no key, and keeps the miss.
        (
            main("", "(2 ..< 5)[2 + 5]"),
            "the map's keys are `int[2..=4]`",
        ),
        (main("", "(2 ..< 5)[1.5 + 0.5]"), "String | #outOfBounds"),
    ];
    for (i, (src, text)) in refused.iter().enumerate() {
        let (status, said) = ran(&format!("range_read_unknown_{i}"), src);
        assert!(status != 0 && said.contains(text), "{src}\n{said}");
    }
}

/// Plan row RANGE-param-exact-keys: a range whose exact keys lie in a parameter's key range is
/// passed, as a range of those keys is a family keyed by them; one with a key outside it is
/// still rejected, naming the parameter's keys. So is the empty range, which has no key.
#[test]
fn a_range_with_exactly_a_parameters_keys_is_passed() {
    let text = |r: &str| {
        format!(
            "f(r: int[2..=4] ->? int) = r(3) else #notFound -> 0;\n\
             main(m: MainArgs) {{\n  m.stdout <- \"${{f(r: {r})}}\";\n}}\n"
        )
    };
    assert_eq!(
        ran("param_exact_keys", &text("2 ..< 5")),
        (0, "3\n".to_string())
    );
    assert_eq!(
        ran("param_inner_keys", &text("3 ..= 4")),
        (0, "3\n".to_string())
    );
    assert_eq!(
        ran("param_no_keys", &text("5 ..< 2")),
        (0, "0\n".to_string())
    );
    for (i, r) in ["0 ..< 9", "2 ..= 5", "1 ..< 3"].into_iter().enumerate() {
        let (status, err) = ran(&format!("param_wider_keys_{i}"), &text(r));
        assert_ne!(status, 0, "{r}: {err}");
        assert!(
            err.contains("`f` takes `r` with keys in int[2..=4]"),
            "{r}: {err}"
        );
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
        main(
            "  n = (if m.args.count > 0 { 3 } else { #a }) else #a -> 3;\n",
            &zip("n", "3"),
        ),
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

/// Step L5.2: `++` on a fold's accumulator, from either side (row FP-ops-concat-fold-acc).
#[test]
fn concatenation_on_a_fold_accumulator_builds_the_list() {
    prints(
        "concat_fold",
        &[
            (
                "[1, 2, 3].foldl([], (a, x) -> a ++ [x]) == [1, 2, 3]",
                "true",
            ),
            (
                "[1, 2, 3].foldl([], (a, x) -> [x] ++ a) == [3, 2, 1]",
                "true",
            ),
            (
                "[1, 2, 3].foldr((x, a) -> [x] ++ a, []) == [1, 2, 3]",
                "true",
            ),
        ],
    );
}

/// Step L5.2: `++` on an operand whose type is generic, beside a list, is the list join on
/// each type the operand is given: an accumulator that starts with entries, a range, the list
/// printed, and a generic function's parameter, called with a list, a range and `[]` (row
/// FP-ops-concat-fold-acc). On two generic operands it is the string join, as on two strings.
/// A string given where a list is joined is rejected at the call.
#[test]
fn concatenation_on_a_generic_operand() {
    prints(
        "concat_generic",
        &[
            ("[1, 2].foldl([0], (a, x) -> a ++ [x]) == [0, 1, 2]", "true"),
            (
                "(0 ..< 3).foldl([], (a, x) -> a ++ [x * 2]) == [0, 2, 4]",
                "true",
            ),
            // Printed as the literal `[1, 2, 3]` is.
            (
                "[1, 2, 3].foldl([], (a, x) -> a ++ [x])",
                "{0 -> 1, 1 -> 2, 2 -> 3}",
            ),
            ("[1, 2, 3].foldl([], (a, x) -> a ++ [x]).count", "3"),
            ("[\"a\", \"b\"].foldl(\"\", (a, x) -> a ++ x)", "ab"),
        ],
    );
    let main = |body: &str| format!("main(m: MainArgs) {{\n  m.stdout <- \"{body}\";\n}}\n");
    let defs = "app(positional a) = a ++ [1];\npre(positional a) = [9] ++ a;\n";
    let src = format!(
        "{defs}{}",
        main("${app([0]) == [0, 1]} ${app(0 ..< 2) == [0, 1, 1]} ${app([]).count} ${pre([1])}")
    );
    assert_eq!(
        ran("concat_generic_fn", &src),
        (0, "true true 1 {0 -> 9, 1 -> 1}\n".into())
    );
    let src = format!("{defs}{}", main("${app(\"s\")}"));
    let (status, said) = ran("concat_generic_fn_string", &src);
    assert!(
        status != 0 && said.contains("`++` joins two lists or two strings"),
        "{said}"
    );
}

/// Plan row MSG-concat-need-repair-template: a `++` on a parameter of no written type is
/// checked at each call, where the operand has no text of its own; the repair is the call
/// with its argument in a list, also where the argument is passed on through another call,
/// and the repair runs.
#[test]
fn concat_checked_at_a_call_repairs_the_call() {
    let src = "app(positional a) = a ++ [1];\n\
               main(m: MainArgs) {\n  m.stdout <- \"${app(\"s\")}\";\n}\n";
    let (status, said) = ran("concat_need_repair", src);
    assert!(status != 0, "{said}");
    assert!(
        said.contains("repair: put the value in a list, as `app([\"s\"])`"),
        "{said}"
    );
    assert!(!said.contains("`[x] ++ xs`"), "{said}");
    // The repair checks and runs.
    let fixed = "app(positional a) = a ++ [1];\n\
                 main(m: MainArgs) {\n  m.stdout <- \"${app([\"s\"]).count}\";\n}\n";
    assert_eq!(ran("concat_need_repair_fixed", fixed), (0, "2\n".into()));
    // Passed on: the argument written in the program is that of the outer call.
    let src = "app(positional a) = a ++ [1];\nwrap(positional x) = app(x);\n\
               main(m: MainArgs) {\n  m.stdout <- \"${wrap(\"s\")}\";\n}\n";
    rejected_saying(
        "concat_need_repair_wrap",
        src,
        &["repair: put the value in a list, as `wrap([\"s\"])`"],
    );
    // Plan row MSG-concat-need-repair-literal-op: an argument that is an operation on
    // literals gets the call with it in a list too, not the template, and the repair runs.
    let src = "app(positional a) = [1] ++ a;\n\
               main(m: MainArgs) {\n  m.stdout <- \"${app(3 + 4)}\";\n}\n";
    let (status, said) = ran("concat_need_repair_op", src);
    assert!(status != 0, "{said}");
    assert!(
        said.contains("repair: put the value in a list, as `app([3 + 4])`"),
        "{said}"
    );
    assert!(!said.contains("`xs ++ [x]`"), "{said}");
    let fixed = "app(positional a) = [1] ++ a;\n\
                 main(m: MainArgs) {\n  m.stdout <- \"${app([3 + 4])}\";\n}\n";
    assert_eq!(
        ran("concat_need_repair_op_fixed", fixed),
        (0, "{0 -> 1, 1 -> 7}\n".into())
    );
    // Two `++` needs of one call, each on the class of its own argument: the repair puts the
    // argument of the operand refused in a list, never the other one.
    let two = |args: &str| {
        format!(
            "two(positional a, positional b) = ([1] ++ a) ++ ([2] ++ b);\n\
             main(m: MainArgs) {{\n  m.stdout <- \"${{two({args})}}\";\n}}\n"
        )
    };
    for (i, (args, repair)) in [
        ("3 + 4, [5]", "two([3 + 4], [5])"),
        ("[3], 5 + 6", "two([3], [5 + 6])"),
    ]
    .into_iter()
    .enumerate()
    {
        let repair = format!("repair: put the value in a list, as `{repair}`");
        rejected_saying(
            &format!("concat_need_repair_two_{i}"),
            &two(args),
            &[&repair],
        );
    }
    // Both at once, of two types, so each error is told apart by its type.
    let (status, said) = ran("concat_need_repair_two_ops", &two("3 + 4, 0.5 + 1.0"));
    assert!(status != 0, "{said}");
    let errors: Vec<&str> = said.split("prog.zed:").skip(1).collect();
    for (ty, repair) in [
        ("int", "`two([3 + 4], 0.5 + 1.0)`"),
        ("f64", "`two(3 + 4, [0.5 + 1.0])`"),
    ] {
        let e = errors
            .iter()
            .find(|e| e.contains(&format!("this value is {ty}, beside a list")))
            .unwrap_or_else(|| panic!("no error for {ty}:\n{said}"));
        assert!(
            e.contains(&format!("repair: put the value in a list, as {repair}")),
            "{ty}: {e}\n{said}"
        );
    }
}

/// Plan row ZIP-generic-operands: a `zip` of two parameters of no written type is checked at
/// each call, as `++` is: arguments that share their keys pass (two reads of one port, lists
/// whose keys the text fixes alike), and arguments whose keys may differ are refused at the
/// call, with the need's `zip` named.
#[test]
fn a_zip_of_generic_parameters_is_checked_at_each_call() {
    let pair_up = "pairUp(positional a, positional b) = a.zip(b);\n";
    let main =
        |body: &str| format!("{pair_up}main(m: MainArgs) {{\n  m.stdout <- \"${{{body}}}\";\n}}\n");
    assert_eq!(
        ran_on_input("zip_generic_ports", &main("pairUp(m.stdin, m.stdin).count")),
        (0, "2\n".into())
    );
    assert_eq!(
        ran_on_input("zip_generic_lists", &main("pairUp([1, 2], [3, 4])")),
        (0, "{0 -> (1, 3), 1 -> (2, 4)}\n".into())
    );
    // One value given to both parameters through a lambda, whose application shows no
    // argument: the need made at `pairUp(l, l)` keeps that its operands are one value.
    assert_eq!(
        ran_on_input(
            "zip_generic_lambda",
            &main("[[1, 2], [3]].map(l -> pairUp(l, l))")
        ),
        (
            0,
            "{0 -> {0 -> (1, 1), 1 -> (2, 2)}, 1 -> {0 -> (3, 3)}}\n".into()
        )
    );
    // Through a generic function between, whose parameters the need passes on to.
    let twice = "twice(positional p, positional q) = pairUp(p, q);\n";
    let through = |body: &str| main(body).replacen("main(", &format!("{twice}main("), 1);
    assert_eq!(
        ran_on_input(
            "zip_generic_between",
            &through("twice(m.stdin, m.stdin).count")
        ),
        (0, "2\n".into())
    );
    let (status, said) = ran_on_input(
        "zip_generic_between_ports",
        &through("twice(m.stdin, m.args).count"),
    );
    assert!(status != 0, "{said}");
    assert!(said.contains("twice(m.stdin, m.args)"), "{said}");
    assert!(
        said.contains("pairUp(p, q)") && said.contains("a.zip(b)"),
        "{said}"
    );
    let (status, said) = ran_on_input(
        "zip_generic_two_ports",
        &main("pairUp(m.stdin, m.args).count"),
    );
    assert!(status != 0, "{said}");
    assert!(!said.contains("generic here"), "{said}");
    assert!(said.contains("pairUp(m.stdin, m.args)"), "{said}");
    assert!(said.contains("a.zip(b)"), "{said}");
    let (status, said) = ran_on_input("zip_generic_lists_differ", &main("pairUp([1, 2], [3])"));
    assert!(status != 0, "{said}");
    assert!(!said.contains("generic here"), "{said}");
    assert!(said.contains("key 1 is in"), "{said}");
}

/// `program` run by `zedc run` with the lines `a` and `b` on its input and the arguments `x`
/// and `y`: what it prints, or with status not 0 its error output.
fn ran_on_input(name: &str, program: &str) -> (u8, String) {
    let out = run(
        &format!("fp_ops/{name}"),
        program,
        "a\nb\n",
        &["--", "x", "y"],
    );
    match out.status {
        0 => (0, out.stdout),
        s => (s, out.stderr),
    }
}

/// Step L5.2, plan row ZIP-count-facts (DESIGN sec:joins): a `zip` whose operands' keys
/// come from one place is accepted though the count is known only at run time, and prints the
/// pairs at every key; operands whose keys may differ are rejected. A function whose body
/// zips two parameters needs their arguments to share their keys at each call, also through
/// a call that passes them on; passing such a function as a value is not supported yet.
#[test]
fn a_zip_of_keys_from_one_place_is_accepted() {
    let main = |defs: &str, body: &str| {
        format!(
            "{defs}main(m: MainArgs) {{\n  xs = (0 ..< m.args.count).map(i -> i * 2);\n{body}}}\n"
        )
    };
    let shown = |e: &str| format!("  m.stdout <- \"${{{e}}}\";\n");
    let pair_up = "pairUp(positional a: Lines, positional b: Lines) = a.zip(b);\n";
    let accepted = [
        // Each read of one port is the same lines.
        (main("", &shown("m.stdin.zip(m.stdin).count")), "2"),
        (
            main(
                "",
                &shown("m.stdin.zip(m.stdin.map(l -> 1)).map(p -> p[1])"),
            ),
            "{0 -> 1, 1 -> 1}",
        ),
        // `map` keeps its operand's keys, through a name.
        (
            main(
                "",
                &format!("  ys = xs.map(x -> x + 1);\n{}", shown("xs.zip(ys)")),
            ),
            "{0 -> (0, 1), 1 -> (2, 3)}",
        ),
        // An `if` whose branches share their keys.
        (
            main(
                "",
                &format!(
                    "  c = m.args.count > 1;\n  ys = if c {{ xs }} else {{ xs.map(x -> x + 1) }};\n{}",
                    shown("xs.zip(ys).count")
                ),
            ),
            "2",
        ),
        // Ranges with the same ends; `0 ..< xs.count` and `xs`.
        (
            main(
                "",
                &shown("(0 ..< m.args.count).zip(0 ..< m.args.count).count"),
            ),
            "2",
        ),
        (
            main("", &shown("xs.zip(0 ..< xs.count)")),
            "{0 -> (0, 0), 1 -> (2, 1)}",
        ),
        // A function's result that keeps its parameter's keys.
        (
            main(
                "twice(positional a) = a.map(x -> x * 2);\n",
                &shown("xs.zip(twice(xs))"),
            ),
            "{0 -> (0, 0), 1 -> (2, 4)}",
        ),
        // A need met at each call, and passed on through `outer`.
        (main(pair_up, &shown("pairUp(m.stdin, m.stdin).count")), "2"),
        (
            main(
                &format!(
                    "{pair_up}outer(positional p: Lines, positional q: Lines) = pairUp(p, q);\n"
                ),
                &shown("outer(m.stdin, m.stdin).count"),
            ),
            "2",
        ),
    ];
    for (i, (src, want)) in accepted.iter().enumerate() {
        assert_eq!(
            ran_on_input(&format!("zip_keys_{i}"), src),
            (0, format!("{want}\n")),
            "{src}"
        );
    }
    let nothing = "nothing shows that each key of";
    let refused = [
        // Two calls that may read different counts.
        (
            main(
                "read(n: int) = (0 ..< n).map(i -> i * 2);\n",
                &format!(
                    "  ys = read(n: m.args.count);\n  zs = read(n: m.args.count + 1);\n{}",
                    shown("ys.zip(zs).count")
                ),
            ),
            nothing,
        ),
        // `where` drops keys.
        (
            main("", &shown("xs.zip(xs.where(x -> x > 0)).count")),
            nothing,
        ),
        // An `if` whose branches may differ in their keys.
        (
            main(
                "",
                &format!(
                    "  ys = (0 ..< m.args.count + 1).map(i -> i);\n  c = m.args.count > 1;\n  \
                     zs = if c {{ xs }} else {{ ys }};\n{}",
                    shown("xs.zip(zs).count")
                ),
            ),
            nothing,
        ),
        // Two ports.
        (
            main(pair_up, &shown("pairUp(m.stdin, m.args).count")),
            "`pairUp` zips its parameters `a` and `b`, so their arguments must have the same \
             keys, and nothing shows that `m.stdin` and `m.args` do",
        ),
        (
            main(
                &format!(
                    "{pair_up}outer(positional p: Lines, positional q: Lines) = pairUp(p, q);\n"
                ),
                &shown("outer(m.stdin, m.args).count"),
            ),
            "`outer` zips its parameters `p` and `q`",
        ),
        (
            main(
                pair_up,
                "  f = pairUp;\n  m.stdout <- \"${f(m.stdin, m.stdin).count}\";\n",
            ),
            "passing `pairUp`, whose body zips its parameters `a` and `b`, as a value",
        ),
        // Literal keys that differ.
        (
            main("", &shown("[1, 2].zip([1])")),
            "key 1 is in `[1, 2]` but not in `[1]`",
        ),
    ];
    for (i, (src, text)) in refused.iter().enumerate() {
        let (status, said) = ran_on_input(&format!("zip_keys_refused_{i}"), src);
        assert!(status != 0 && said.contains(text), "{src}\n{said}");
    }
}

/// Plan row ZIP-count-facts (DESIGN sec:joins): inside `0 ..< e`, where `e` is `x.count` or a
/// `min` with `x.count` as an operand, a read `x[i]` has no `#outOfBounds`, so the repair
/// offered for a `zip` of unequal keys has no failure member; a read at another key, or of
/// another list, keeps it. Each type is shown by pushing the value to `m.stdout`, which
/// rejects it and names its type.
#[test]
fn a_read_within_a_lists_count_has_no_miss() {
    let main = |e: &str| {
        format!(
            "main(m: MainArgs) {{\n  xs = (0 ..< m.args.count).map(i -> i * 2);\n  \
             ys = (0 ..< m.args.count + 1).map(i -> i);\n  m.stdout <- {e};\n}}\n"
        )
    };
    let cases = [
        (
            "(0 ..< xs.count).map(i -> xs[i])",
            "this call gives [int]\n",
        ),
        (
            "(0 ..< min(xs.count, ys.count)).map(i -> (xs[i], ys[i]))",
            "this call gives [(int, int)]\n",
        ),
        (
            "(0 ..< min(xs.count, ys.count)).map(i -> (xs[i], ys[i + 1]))",
            "this call gives [(int, int | #outOfBounds)]\n",
        ),
        (
            "(0 ..< ys.count).map(i -> xs[i])",
            "this call gives [int | #outOfBounds]\n",
        ),
    ];
    for (i, (e, text)) in cases.iter().enumerate() {
        let src = main(e);
        let (status, said) = ran_on_input(&format!("within_count_{i}"), &src);
        assert!(status != 0 && said.contains(text), "{src}\n{said}");
    }
    // The repair runs, and the read of a port's lines within its count prints them.
    let src = "main(m: MainArgs) {\n  m.stdout <- (0 ..< m.stdin.count).map(i -> m.stdin[i]);\n}\n";
    assert_eq!(
        ran_on_input("within_count_lines", src),
        (0, "a\nb\n".into())
    );
}

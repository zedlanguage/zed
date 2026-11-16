//! Each case is an expression a program writes with `${…}`, and the kernel term the spec
//! defines it by, run on the M0 reference evaluator: the program's output must be the value the
//! model gives. `map(m, f)` is `reindex(m, k -> k, f)` (DESIGN.md sec:keypaths), `m.where(p)` is
//! `discard(m, (k, v) -> p(v))` on one level, and `m >< (op)` is `fold(m, op)` with the
//! operator's identity (sec:reduction). The interpreter runs each case as a program of its own;
//! one executable runs them all.

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::{Family, Pattern, Prim, Term, Value, eval};
use zed_tests::kernel::*;
use zed_tests::step_helpers::l01_36a_executables::{built, dir, executable};

use super::{program, run};

fn i(n: i64) -> Value {
    Value::Int(n)
}

/// A one-level family from its entries.
fn family(entries: Vec<(Value, Value)>) -> Term {
    lit(Value::Family(Family::of(entries)))
}

/// `[x0, x1, …]`: keyed by position from 0.
fn list(xs: &[i64]) -> Term {
    family(
        (xs.iter().enumerate())
            .map(|(k, &x)| (i(k as i64), i(x)))
            .collect(),
    )
}

/// `[[…], […]]`: a list of lists.
fn lists(rows: &[&[i64]]) -> Term {
    let leaves = (rows.iter().enumerate())
        .flat_map(|(r, row)| {
            (row.iter().enumerate()).map(move |(k, &x)| (vec![i(r as i64), i(k as i64)], i(x)))
        })
        .collect::<Vec<_>>();
    lit(Value::Family(Family::from_leaves(leaves).unwrap()))
}

/// `map(m, f) = reindex(m, k -> k, f)`, with `f` given as a function of the entry.
fn map(m: Term, f: impl Fn(Term) -> Term) -> Term {
    reindex(m, func(|[p, _]| p), func(|[_, v]| f(v)))
}

/// `m.map(f)` over a family of families: `f` applies to each top-level entry, a row, which
/// `reindex` cannot express, since it moves leaves (sec:kernel); `fam` over the top-level keys
/// does (the term zedc elaborates `map` to).
fn map_rows(m: Term, f: impl Fn(Term) -> Term) -> Term {
    fam(m.clone(), "$k", f(get(m, var("$k"))))
}

/// `m.where(p)` on a one-level `m`: `discard` keeping the entries `p` holds for.
fn where_(m: Term, p: impl Fn(Term) -> Term) -> Term {
    discard(m, func(|[_, v]| p(v)))
}

/// `m >< (op)` with `identity` as the fold of an empty family.
fn reduce(m: Term, op: Prim, identity: Option<Value>) -> Term {
    fold(m, func(|[a, b]| bin(op, a, b)), identity.map(lit))
}

/// `e else d` for a value `e` that may be the bare atom `#atom`.
fn or(e: Term, atom: &str, d: i64) -> Term {
    let arms = vec![
        (Pattern::Atom(atom.into(), vec![]), lit(d)),
        (Pattern::Wild, var("$e")),
    ];
    let_("$e", e, Term::Match(rc(var("$e")), arms))
}

/// The cases: a name, the expression a program writes, and its model.
fn cases() -> Vec<(&'static str, &'static str, Term)> {
    let kv = || family(vec![(i(0), i(1)), (i(1), i(2))]);
    let named = || family(vec![(s("x"), i(1)), (s("y"), i(2))]);
    let xs = || list(&[10, 20, 30]);
    let f = |x: Term| mul(x, lit(2));
    let g = |x: Term| add(x, lit(1));
    vec![
        (
            "map_keeps_the_keys",
            "${{0 -> 1, 1 -> 2}.map(x -> x + 1)}",
            map(kv(), |v| add(v, lit(1))),
        ),
        (
            "map_of_an_array",
            "${[10, 20, 30].map(x -> x * 2)}",
            map(xs(), f),
        ),
        (
            "map_of_a_string_keyed_map",
            "${{\"x\" -> 1, \"y\" -> 2}.map(x -> x * 10)}",
            map(named(), |v| mul(v, lit(10))),
        ),
        (
            "map_of_each_level",
            "${[[1, 2], [3, 4, 5]].map(r -> r.map(x -> x * x))}",
            map(lists(&[&[1, 2], &[3, 4, 5]]), |v| mul(v.clone(), v)),
        ),
        (
            // A loose atom passes through `f` as through any call (rule 6).
            "map_passes_a_loose_atom_through",
            "${{0 -> 1, 1 -> #oops}.map(x -> x + 1)}",
            map(
                family(vec![(i(0), i(1)), (i(1), Value::atom("oops"))]),
                |v| {
                    let arms = vec![
                        (Pattern::Atom("oops".into(), vec![]), var("$v")),
                        (Pattern::Wild, add(var("$v"), lit(1))),
                    ];
                    let_("$v", v, Term::Match(rc(var("$v")), arms))
                },
            ),
        ),
        (
            "map_then_map",
            "${[10, 20, 30].map(x -> x * 2).map(x -> x + 1)}",
            map(map(xs(), f), g),
        ),
        (
            "map_of_the_composite",
            "${[10, 20, 30].map(x -> x * 2 + 1)}",
            map(xs(), |v| g(f(v))),
        ),
        (
            "where_keeps_the_keys_of_the_entries_it_keeps",
            "${[10, 20, 30, 40].where(x -> x > 15)}",
            where_(list(&[10, 20, 30, 40]), |v| bin(Prim::Gt, v, lit(15))),
        ),
        (
            "where_of_a_string_keyed_map",
            "${{\"x\" -> 1, \"y\" -> 2, \"z\" -> 3}.where(v -> v != 2)}",
            where_(
                family(vec![(s("x"), i(1)), (s("y"), i(2)), (s("z"), i(3))]),
                |v| bin(Prim::Ne, v, lit(2)),
            ),
        ),
        (
            "map_then_where_then_sum",
            "${[10, 20, 30, 40].map(x -> x + 1).where(x -> x > 20) >< (+)}",
            reduce(
                where_(map(list(&[10, 20, 30, 40]), g), |v| {
                    bin(Prim::Gt, v, lit(20))
                }),
                Prim::Add,
                Some(i(0)),
            ),
        ),
        (
            "where_then_a_missed_read",
            "${([10, 20, 30, 40].where(x -> x > 15)[0]) else -1}",
            or(
                get(
                    where_(list(&[10, 20, 30, 40]), |v| bin(Prim::Gt, v, lit(15))),
                    lit(0),
                ),
                "notFound",
                -1,
            ),
        ),
        (
            "sum",
            "${[10, 20, 30] >< (+)}",
            reduce(xs(), Prim::Add, Some(i(0))),
        ),
        (
            "product",
            "${{0 -> 2, 1 -> 3}.map(x -> x + 1) >< (*)}",
            reduce(
                map(family(vec![(i(0), i(2)), (i(1), i(3))]), g),
                Prim::Mul,
                Some(i(1)),
            ),
        ),
        (
            "all_of_bools",
            "${[1, 2, 3].map(x -> x > 0) >< (&&)}",
            reduce(
                map(list(&[1, 2, 3]), |v| bin(Prim::Gt, v, lit(0))),
                Prim::And,
                Some(Value::Bool(true)),
            ),
        ),
        (
            "sum_of_each_row",
            "${[[1, 2], [3, 4, 5]].map(r -> r >< (+))}",
            map_rows(lists(&[&[1, 2], &[3, 4, 5]]), |r| {
                reduce(r, Prim::Add, None)
            }),
        ),
        (
            "sum_of_an_empty_row_is_zero",
            "${{0 -> [1], 1 -> []}.map(r -> r >< (+))}",
            family(vec![
                (i(0), i(1)),
                (
                    i(1),
                    eval(&reduce(list(&[]), Prim::Add, Some(i(0)))).unwrap(),
                ),
            ]),
        ),
        (
            "fold_of_an_empty_display_is_empty",
            "${([] >< (+)) else -1}",
            or(reduce(list(&[]), Prim::Add, None), "empty", -1),
        ),
        // `k in m` tests the keys of `m` (DESIGN.md sec:grammar, `k in m::domain`; a set is a
        // self-map, so `x in s` tests its elements): the model reads each key and tests for a
        // miss.
        (
            "a_set_display",
            "${{3, 1, 2}}",
            family(vec![(i(1), i(1)), (i(2), i(2)), (i(3), i(3))]),
        ),
        (
            "in_of_a_set_tests_an_element",
            "${2 in {3, 1, 2}}",
            found(get(
                family(vec![(i(1), i(1)), (i(2), i(2)), (i(3), i(3))]),
                lit(2),
            )),
        ),
        (
            "in_tests_a_key",
            "${1 in [5, 6]}",
            found(get(list(&[5, 6]), lit(1))),
        ),
        (
            "in_of_a_missing_key",
            "${5 in [5, 6]}",
            found(get(list(&[5, 6]), lit(5))),
        ),
        (
            "not_in",
            "${\"z\" not in {\"x\" -> 1}}",
            prim(
                Prim::Not,
                vec![found(get(family(vec![(s("x"), i(1))]), lit(s("z"))))],
            ),
        ),
        (
            "in_of_each_row",
            "${[[1, 2], [3, 4, 5]].map(r -> 2 in r)}",
            map_rows(lists(&[&[1, 2], &[3, 4, 5]]), |r| found(get(r, lit(2)))),
        ),
        // Plan row MAP-run-rest. `><` by `max` and `min`, which have no identity at `int`, so
        // an empty level folds to `#empty` (DESIGN.md sec:reduction, "Identity as data").
        (
            "max_of_a_list",
            "${[3, 9, 4] >< max}",
            reduce(list(&[3, 9, 4]), Prim::Max, None),
        ),
        (
            "min_of_a_string_keyed_map",
            "${{\"a\" -> 3, \"b\" -> 7} >< min}",
            reduce(
                family(vec![(s("a"), i(3)), (s("b"), i(7))]),
                Prim::Min,
                None,
            ),
        ),
        (
            "max_of_each_row",
            "${[[1, 5], [7, 2]].map(r -> r >< max)}",
            map_rows(lists(&[&[1, 5], &[7, 2]]), |r| reduce(r, Prim::Max, None)),
        ),
        (
            "max_of_an_empty_display_is_empty",
            "${([] >< max) else -1}",
            or(reduce(list(&[]), Prim::Max, None), "empty", -1),
        ),
        // A float fold goes round the canonical tree of sec:reduction item 1:
        // `((x0 + x1) + (x2 + x3)) + (x4 + x5)` for six entries, which the kernel `fold` walks.
        (
            "a_float_sum_on_the_canonical_tree",
            "${[0.1, 0.2, 0.3, 0.4, 0.5, 0.6] >< (+)}",
            reduce(
                floats(&[0.1, 0.2, 0.3, 0.4, 0.5, 0.6]),
                Prim::Add,
                Some(Value::float(-0.0)),
            ),
        ),
        (
            "a_float_max",
            "${[1.5, -2.5, 0.5] >< max}",
            reduce(floats(&[1.5, -2.5, 0.5]), Prim::Max, None),
        ),
        // `.foldl(init, op)` and `.foldr(op, init)` over a rank: the definedness fix of the
        // accumulators (zed_tests::kernel::foldl), against the `gen` zedc elaborates them to.
        (
            "foldl_reads_left_to_right",
            "${[1, 2, 3, 4].foldl(0, (a, x) -> a * 10 + x)}",
            foldl(
                list(&[1, 2, 3, 4]),
                lit(0),
                func(|[a, x]| add(mul(a, lit(10)), x)),
            ),
        ),
        (
            "foldr_reads_right_to_left",
            "${[1, 2, 3, 4].foldr((x, a) -> a * 10 + x, 0)}",
            foldr(
                list(&[1, 2, 3, 4]),
                func(|[x, a]| add(mul(a, lit(10)), x)),
                lit(0),
            ),
        ),
        (
            "foldl_by_a_non_associative_section",
            "${[10, 2, 3].foldl(100, (-))}",
            foldl(list(&[10, 2, 3]), lit(100), func(|[a, b]| sub(a, b))),
        ),
        (
            "foldr_by_a_non_associative_section",
            "${[10, 2, 3].foldr((-), 0)}",
            foldr(list(&[10, 2, 3]), func(|[a, b]| sub(a, b)), lit(0)),
        ),
        (
            "foldl_of_an_empty_list_is_its_start",
            "${[].foldl(5, (a, x) -> a + x)}",
            foldl(list(&[]), lit(5), func(|[a, x]| add(a, x))),
        ),
        (
            "foldl_whose_accumulator_is_another_type",
            "${[1, -2, 3].foldl(true, (b, x) -> b && x > 0)}",
            foldl(
                list(&[1, -2, 3]),
                lit(true),
                func(|[b, x]| and(b, bin(Prim::Gt, x, lit(0)))),
            ),
        ),
        (
            "foldl_of_each_row",
            "${[[1, 2], [3, 4, 5]].map(r -> r.foldl(0, (+)))}",
            map_rows(lists(&[&[1, 2], &[3, 4, 5]]), |r| {
                foldl(r, lit(0), func(|[a, b]| add(a, b)))
            }),
        ),
        // `a ..< b` is the set of the integers from `a` up to `b`, `b` left out, and `a ..= b`
        // takes `b` in (DESIGN.md sec:syntax_tour); the model writes that set out, apart from
        // the kernel's `range`.
        ("a_range_from_0", "${0 ..< 4}", range(0, 4)),
        ("a_range_through_its_end", "${1 ..= 3}", range(1, 4)),
        ("a_range_from_a_negative_end", "${-2 ..< 1}", range(-2, 1)),
        ("an_empty_range", "${5 ..< 3}", range(5, 3)),
        (
            "a_range_with_computed_ends",
            "${2 - 1 ..< 2 + 1}",
            range(1, 3),
        ),
        (
            "a_range_at_the_ends_of_i64",
            "${9223372036854775806 ..= 9223372036854775807}",
            lit(Value::Family(Family::set([i64::MAX - 1, i64::MAX]))),
        ),
        ("in_a_range", "${2 in 0 ..< 5}", lit(true)),
        ("past_a_range", "${5 in 0 ..< 5}", lit(false)),
        (
            "a_range_mapped",
            "${(2 ..< 5).map(x -> x * x)}",
            map(range(2, 5), |v| mul(v.clone(), v)),
        ),
        (
            "a_range_reduced",
            "${(1 ..< 5) >< (*)}",
            reduce(range(1, 5), Prim::Mul, Some(i(1))),
        ),
        (
            "a_range_from_0_folded_left",
            "${(0 ..< 4).foldl(0, (a, x) -> a * 10 + x)}",
            foldl(range(0, 4), lit(0), func(|[a, x]| add(mul(a, lit(10)), x))),
        ),
        (
            "a_range_filtered",
            "${(0 ..< 6).where(x -> x mod 2 == 0)}",
            where_(range(0, 6), |v| {
                bin(Prim::Eq, bin(Prim::Mod, v, lit(2)), lit(0))
            }),
        ),
        // A range is `int ->? int`: a read may miss, and since its keys are one integer
        // interval, every key present, the miss is `#outOfBounds` whatever its low end
        // (DESIGN.md sec:type_language, the `m[k]` row, `lst : int[a..<b]`).
        ("a_read_in_a_range", "${(0 ..< 3)[1] else -1}", lit(1)),
        (
            "a_read_past_a_range_from_0",
            "${(0 ..< 3)[3] is #outOfBounds}",
            lit(true),
        ),
        (
            "a_read_in_a_range_from_2",
            "${(2 ..< 5)[3] else -1}",
            lit(3),
        ),
        (
            "a_read_past_a_range_from_2",
            "${(2 ..< 5)[5] is #outOfBounds}",
            lit(true),
        ),
        (
            "a_read_below_a_range_from_2",
            "${(2 ..< 5)[1] is #outOfBounds}",
            lit(true),
        ),
        (
            "a_read_past_a_range_from_a_negative_end",
            "${(-2 ..= 1)[2] is #outOfBounds}",
            lit(true),
        ),
        (
            "a_read_past_a_range_with_computed_ends",
            "${(2 - 1 ..< 2 + 1)[0] is #outOfBounds}",
            lit(true),
        ),
        // `map` keeps the keys, so a mapped range still misses with `#outOfBounds`; `where`
        // may drop any key, so a filtered one misses with `#notFound`.
        (
            "a_read_past_a_mapped_range_from_2",
            "${(2 ..< 5).map(x -> x * x)[5] is #outOfBounds}",
            lit(true),
        ),
        (
            "a_read_past_a_filtered_range_from_2",
            "${(2 ..< 5).where(x -> x > 2)[2] is #notFound}",
            lit(true),
        ),
        // Plan row RANGE-lazy: a range is kept as its two ends, and read, counted and tested
        // at its ends without its entries being made, so a range of 10^12 entries is read here
        // in O(1) by the interpreter and by the executable alike.
        ("a_range_counted", "${(3 ..< 10).count}", lit(7)),
        (
            "the_first_of_a_negative_range",
            "${(-5 ..= -2).first else 0}",
            lit(-5),
        ),
        (
            "the_last_of_a_negative_range",
            "${(-5 ..= -2).last else 0}",
            lit(-2),
        ),
        (
            "reads_at_both_ends_of_a_negative_range",
            "${[(-5 ..= -2)[-5] else 0, (-5 ..= -2)[-2] else 0, (-5 ..= -2)[-1] else 0]}",
            list(&[-5, -2, 0]),
        ),
        (
            "a_range_of_a_trillion_entries_read_at_its_end",
            "${(0 ..< 1000000000000)[999999999999] else -1}",
            lit(999_999_999_999),
        ),
        (
            "a_range_of_a_trillion_entries_counted",
            "${(0 ..< 1000000000000).count}",
            lit(1_000_000_000_000),
        ),
        (
            "in_a_range_of_a_trillion_entries",
            "${[999999999999 in 0 ..< 1000000000000, 1000000000000 in 0 ..< 1000000000000]}",
            family(vec![(i(0), Value::Bool(true)), (i(1), Value::Bool(false))]),
        ),
        (
            "every_64_bit_integer_counted",
            "${(-9223372036854775807 - 1 ..= 9223372036854775807).count}",
            lit(Value::int(num_bigint::BigInt::from(u64::MAX) + 1)),
        ),
        (
            "a_range_equal_to_the_set_of_its_integers",
            "${[(1 ..< 4) == {1, 2, 3}, (1 ..< 4) == {1, 2}, (1 ..< 4) == (1 ..= 3)]}",
            family(vec![
                (i(0), Value::Bool(true)),
                (i(1), Value::Bool(false)),
                (i(2), Value::Bool(true)),
            ]),
        ),
    ]
}

/// `a ..< b`: the set of the integers `k` with `a <= k < b`.
fn range(a: i64, b: i64) -> Term {
    lit(Value::Family(Family::set(a..b)))
}

/// `[x0, x1, …]` of floats.
fn floats(xs: &[f64]) -> Term {
    family(
        (xs.iter().enumerate())
            .map(|(k, &x)| (i(k as i64), Value::float(x)))
            .collect(),
    )
}

/// The output the model gives for a case.
fn expected(model: &Term) -> String {
    match eval(model) {
        Ok(v) => format!("{v}\n"),
        Err(e) => panic!("the model failed: {e:?}"),
    }
}

#[test]
fn each_case_run_by_the_interpreter_gives_the_models_value() {
    for (name, body, model) in cases() {
        let ran = run(name, body);
        assert_eq!(ran.stderr, "", "{name}");
        assert_eq!(ran.status, 0, "{name}");
        assert_eq!(ran.stdout, expected(&model), "{name}: {body}");
    }
}

#[test]
fn map_then_map_is_map_of_the_composite() {
    let ran = |name, body| run(name, body).stdout;
    let two = ran(
        "composite_two",
        "${[3, 1, 4, 1, 5].map(x -> x * 2).map(x -> x - 7)}",
    );
    let one = ran("composite_one", "${[3, 1, 4, 1, 5].map(x -> x * 2 - 7)}");
    assert_eq!(two, one);
    assert_eq!(two, "{0 -> -1, 1 -> -5, 2 -> 1, 3 -> -5, 4 -> 3}\n");
}

#[test]
fn reads_that_miss_give_the_miss_atoms() {
    // Keys of a type that overlaps the family's keys: R11 makes the read
    // `V | #notFound`, and `#outOfBounds` for an array.
    let src = program(
        "misses",
        "${a[ks[1]] else -1} ${a[ks[0]] else -1} ${b[ks[1]] else -2} ${c[ss[1]] else -3} \
         ${c[ss[0]] else -3} ${a[ks[1]] is #notFound} ${b[ks[1]] is #outOfBounds}",
    );
    let text = std::fs::read_to_string(&src).unwrap().replace(
        "main(m: MainArgs) {\n",
        "main(m: MainArgs) {\n    a = {0 -> 1, 1 -> 2}.map(x -> x + 1);\n    b = [10, 20];\n    \
         c = {\"x\" -> 1, \"y\" -> 2}.map(x -> x * 10);\n    ks = [0, 5];\n    \
         ss = [\"y\", \"z\"];\n",
    );
    std::fs::write(&src, text).unwrap();
    let ran = zed_tests::step_helpers::l01_36a_executables::interpreter(&src, &[], &[]);
    assert_eq!(ran.stderr, "");
    // The model: the reads of the kernel, `Get` on the mapped families.
    let a = map(family(vec![(i(0), i(1)), (i(1), i(2))]), |v| add(v, lit(1)));
    let c = map(family(vec![(s("x"), i(1)), (s("y"), i(2))]), |v| {
        mul(v, lit(10))
    });
    let parts = [
        expected(&or(get(a.clone(), lit(5)), "notFound", -1)),
        expected(&or(get(a, lit(0)), "notFound", -1)),
        "-2".to_string(),
        expected(&or(get(c.clone(), lit(s("z"))), "notFound", -3)),
        expected(&or(get(c, lit(s("y"))), "notFound", -3)),
        "true".to_string(),
        "true".to_string(),
    ];
    assert_eq!(
        ran.stdout,
        format!("{}\n", parts.join(" ").replace('\n', ""))
    );
}

#[test]
fn an_executable_gives_each_cases_value() {
    let cases = cases();
    let body = (cases.iter().map(|(_, b, _)| *b))
        .collect::<Vec<_>>()
        .join("\\n");
    let src = program("native", &body);
    let exe = dir("l03_02_map_run/native").join("native");
    built(&src, &exe);
    let ran = executable(&exe, &[], &[]);
    assert_eq!(ran.stderr, "");
    assert_eq!(ran.status, 0);
    let want = (cases.iter().map(|(_, _, m)| expected(m))).collect::<Vec<_>>();
    // The program pushes one text, and `stdout` ends it with a newline as it does each push.
    assert_eq!(ran.stdout, want.concat());
}

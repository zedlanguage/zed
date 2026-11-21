//! Each case is an expression a program writes with `${…}`, and the kernel term the spec
//! defines it by, run on the M0 reference evaluator: the program's output must be the value the
//! model gives. `map(m, f)` is `reindex(m, k -> k, f)` (DESIGN.md sec:keypaths), `m.where(p)` is
//! `discard(m, (k, v) -> p(v))` on one level, and `m >< (op)` is `fold(m, op)` with the
//! operator's identity (sec:reduction). The interpreter runs each case as a program of its own;
//! one executable runs them all.

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::{Family, Pattern, Prim, Term, Value, eval};
use zed_tests::kernel::*;
use zed_tests::step_helpers::l01_36a_executables::{built, dir, executable, interpreter};

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
            "${([10, 20, 30, 40].where(x -> x > 15)[0]) else #notFound -> -1}",
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
            "${([] >< (+)) else #empty -> -1}",
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
            "${([] >< max) else #empty -> -1}",
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
        // (DESIGN.md sec:type_language, the `m[k]` row, `lst : int[a..<b]`). A read of a range
        // with literal ends at a key known to be outside it is a static error (row
        // RANGE-literal-reads, `l03_15a_fp_ops_run::cases`), so a miss here reads a key the
        // checker cannot know, `if m.args.count > 0 { a key } else { the key read }`, one arm
        // in the keys and one not; these runs pass no argument, so the run reads the second.
        ("a_read_in_a_range", "${(0 ..< 3)[1]}", lit(1)),
        (
            "a_read_past_a_range_from_0",
            "${(0 ..< 3)[if m.args.count > 0 { 0 } else { 3 }] is #outOfBounds}",
            lit(true),
        ),
        ("a_read_in_a_range_from_2", "${(2 ..< 5)[3]}", lit(3)),
        (
            "a_read_past_a_range_from_2",
            "${(2 ..< 5)[if m.args.count > 0 { 2 } else { 5 }] is #outOfBounds}",
            lit(true),
        ),
        (
            "a_read_below_a_range_from_2",
            "${(2 ..< 5)[if m.args.count > 0 { 2 } else { 1 }] is #outOfBounds}",
            lit(true),
        ),
        (
            "a_read_past_a_range_from_a_negative_end",
            "${(-2 ..= 1)[if m.args.count > 0 { 0 } else { 2 }] is #outOfBounds}",
            lit(true),
        ),
        (
            "a_read_past_a_range_with_computed_ends",
            "${(2 - 1 ..< 2 + 1)[if m.args.count > 0 { 1 } else { 0 }] is #outOfBounds}",
            lit(true),
        ),
        // `map` keeps the keys, so a mapped range still misses with `#outOfBounds`; `where`
        // may drop any key, so a filtered one misses with `#notFound`.
        (
            "a_read_past_a_mapped_range_from_2",
            "${(2 ..< 5).map(x -> x * x)[if m.args.count > 0 { 2 } else { 5 }] \
             is #outOfBounds}",
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
            "${(-5 ..= -2).first else #none -> 0}",
            lit(-5),
        ),
        (
            "the_last_of_a_negative_range",
            "${(-5 ..= -2).last else #none -> 0}",
            lit(-2),
        ),
        (
            "reads_at_both_ends_of_a_negative_range",
            "${[(-5 ..= -2)[-5], (-5 ..= -2)[-2], \
             (-5 ..= -2)[if m.args.count > 0 { -2 } else { -1 }] else #outOfBounds -> 0]}",
            list(&[-5, -2, 0]),
        ),
        (
            "a_range_of_a_trillion_entries_read_at_its_end",
            "${(0 ..< 1000000000000)[999999999999]}",
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
        // Plan row RANGE-open: `a ..` is kept as its low end, `rangeFrom(a)`, and read by a
        // key, by `in` and by `.first` in O(1), never walked; a key below `a` misses with
        // `#outOfBounds`, since the keys are one interval with every key present.
        (
            "in_a_range_with_no_upper_end",
            "${[3 in 3 .., 2 in 3 .., 1000000000000 in 3 .., -1 in -5 .., 3.5 in 3 ..]}",
            family(
                [
                    has(lit(3), from(3)),
                    has(lit(2), from(3)),
                    has(lit(1_000_000_000_000_i64), from(3)),
                    has(lit(-1), from(-5)),
                    has(lit(Value::float(3.5)), from(3)),
                ]
                .into_iter()
                .enumerate()
                .map(|(k, t)| (i(k as i64), eval(&t).unwrap()))
                .collect(),
            ),
        ),
        (
            "a_read_far_into_a_range_with_no_upper_end",
            "${(3 ..)[1000000000000] else #outOfBounds -> -1}",
            or(at(from(3), lit(1_000_000_000_000_i64)), "outOfBounds", -1),
        ),
        (
            "a_read_below_a_range_with_no_upper_end",
            "${(3 ..)[2] is #outOfBounds}",
            lit(eval(&at(from(3), lit(2))).unwrap() == Value::atom("outOfBounds")),
        ),
        (
            "the_first_of_a_negative_range_with_no_upper_end",
            "${(-7 ..).first else #none -> 0}",
            or(prim(Prim::First, vec![from(-7)]), "none", 0),
        ),
        (
            "a_range_with_no_upper_end_past_64_bits",
            "${[100000000000000000000000 in 99999999999999999999999 .., \
             (99999999999999999999999 ..)[100000000000000000000000] else #outOfBounds -> 0]}",
            {
                let big = |s: &str| lit(Value::int(s.parse::<num_bigint::BigInt>().unwrap()));
                let lo = || prim(Prim::RangeFrom, vec![big("99999999999999999999999")]);
                let k = || big("100000000000000000000000");
                let models = [has(k(), lo()), or(at(lo(), k()), "outOfBounds", 0)];
                family(
                    (models.iter().enumerate())
                        .map(|(n, t)| (i(n as i64), eval(t).unwrap()))
                        .collect(),
                )
            },
        ),
        // Plan row RANGE-open-walk: `.map` and `.where` over `a ..` give a stream that `.first`,
        // `.find`, `.any` and `.all` read entry by entry up to the deciding one. The read gives
        // what it gives on any bounded range `a ..< b` that holds the deciding entry, since it
        // reads no entry past it, so the model is the kernel terms of `map`, `where` and the
        // read on such a range: `.first` and `.find` the first entry `where` keeps (`.find`
        // gives the key, which is the value when no `.map` comes first), `.any(p)` whether
        // `where(p)` keeps one, `.all(p)` whether `where(!p)` keeps none.
        (
            "the_first_of_a_stream_with_no_upper_end",
            "${(-10 ..).where(x -> x mod 7 == 3).first else #none -> 0}",
            or(
                prim(
                    Prim::First,
                    vec![where_(range(-10, 10), |v| eq(modulo(v, lit(7)), lit(3)))],
                ),
                "none",
                0,
            ),
        ),
        (
            "a_stream_mapped_then_kept",
            "${(5 ..).map(x -> x * x).where(x -> x > 50).first else #none -> 0}",
            or(
                prim(
                    Prim::First,
                    vec![where_(map(range(5, 20), |v| mul(v.clone(), v)), |v| {
                        lt(lit(50), v)
                    })],
                ),
                "none",
                0,
            ),
        ),
        (
            "a_stream_kept_twice_then_mapped",
            "${(-10 ..).where(x -> x mod 2 == 0).where(x -> x > 3).map(x -> x - 1).first else #none -> 0}",
            or(
                prim(
                    Prim::First,
                    vec![map(
                        where_(
                            where_(range(-10, 10), |v| eq(modulo(v, lit(2)), lit(0))),
                            |v| lt(lit(3), v),
                        ),
                        |v| sub(v, lit(1)),
                    )],
                ),
                "none",
                0,
            ),
        ),
        (
            "any_and_all_over_a_range_with_no_upper_end",
            "${[(1 ..).any(x -> x * x > 1000), (0 ..).all(x -> x < 1000), \
             (1 ..).map(x -> x * 2).any(x -> x == 64), \
             (1 ..).where(x -> x > 5).all(x -> x < 9)]}",
            {
                let some = |m: Term| not(eq(count(m), lit(0)));
                let none = |m: Term| eq(count(m), lit(0));
                family(
                    [
                        some(where_(range(1, 40), |v| lt(lit(1000), mul(v.clone(), v)))),
                        none(where_(range(0, 1001), |v| not(lt(v, lit(1000))))),
                        some(where_(map(range(1, 40), |v| mul(v, lit(2))), |v| {
                            eq(v, lit(64))
                        })),
                        none(where_(where_(range(1, 10), |v| lt(lit(5), v)), |v| {
                            not(lt(v, lit(9)))
                        })),
                    ]
                    .iter()
                    .enumerate()
                    .map(|(k, t)| (i(k as i64), eval(t).unwrap()))
                    .collect(),
                )
            },
        ),
        (
            "find_over_a_range_with_no_upper_end",
            "${[(3 ..).map(x -> x * 3).find(x -> x mod 7 == 0) else #none -> -1, \
             (3 ..).find(x -> x > 10) else #none -> -1]}",
            family(
                [
                    or(
                        prim(
                            Prim::First,
                            vec![where_(range(3, 30), |v| {
                                eq(modulo(mul(v, lit(3)), lit(7)), lit(0))
                            })],
                        ),
                        "none",
                        -1,
                    ),
                    or(
                        prim(Prim::First, vec![where_(range(3, 30), |v| lt(lit(10), v))]),
                        "none",
                        -1,
                    ),
                ]
                .iter()
                .enumerate()
                .map(|(k, t)| (i(k as i64), eval(t).unwrap()))
                .collect(),
            ),
        ),
        (
            "a_stream_past_64_bits",
            "${(9223372036854775800 ..).where(x -> x mod 1000 == 7).first else #none -> 0}",
            {
                let lo = num_bigint::BigInt::from(9223372036854775800i64);
                let keys = (0..2000).map(|d| &lo + d).collect::<Vec<_>>();
                or(
                    prim(
                        Prim::First,
                        vec![where_(ints(&keys), |v| eq(modulo(v, lit(1000)), lit(7)))],
                    ),
                    "none",
                    0,
                )
            },
        ),
        // Plan row RANGE-lazy-wide: a range with an end past `i64` is kept as its two ends too,
        // read, counted, tested and taken at its ends from them. The models are the integers
        // themselves, not a range. Just past `i64::MAX`, just below `i64::MIN`, across either
        // 64-bit edge, and a range of 10^30 entries, which no memory holds.
        (
            "reads_of_a_range_just_past_64_bits",
            "${[(9223372036854775808 ..< 9223372036854775811)[9223372036854775808], \
             (9223372036854775808 ..< 9223372036854775811)[9223372036854775810], \
             (9223372036854775808 ..< 9223372036854775811)\
             [if m.args.count > 0 { 9223372036854775808 } else { 9223372036854775811 }] else #outOfBounds -> 0, \
             (9223372036854775808 ..< 9223372036854775811)\
             [if m.args.count > 0 { 9223372036854775808 } else { 9223372036854775807 }] else #outOfBounds -> 0]}",
            ints(&[wide(0, 0), wide(0, 2), 0.into(), 0.into()]),
        ),
        (
            "a_range_across_the_top_64_bit_edge",
            "${[(9223372036854775806 ..= 9223372036854775809).count, \
             9223372036854775807 in 9223372036854775806 ..= 9223372036854775809, \
             9223372036854775808 in 9223372036854775806 ..= 9223372036854775809, \
             9223372036854775810 in 9223372036854775806 ..= 9223372036854775809, \
             (9223372036854775806 ..= 9223372036854775809).first else #none -> 0, \
             (9223372036854775806 ..= 9223372036854775809).last else #none -> 0]}",
            family(vec![
                (i(0), Value::Int(4)),
                (i(1), Value::Bool(true)),
                (i(2), Value::Bool(true)),
                (i(3), Value::Bool(false)),
                (i(4), Value::int(wide(0, -2))),
                (i(5), Value::int(wide(0, 1))),
            ]),
        ),
        (
            "a_range_across_the_bottom_64_bit_edge",
            "${[(-9223372036854775810 ..< -9223372036854775806).count, \
             -9223372036854775809 in -9223372036854775810 ..< -9223372036854775806, \
             -9223372036854775808 in -9223372036854775810 ..< -9223372036854775806, \
             -9223372036854775806 in -9223372036854775810 ..< -9223372036854775806, \
             (-9223372036854775810 ..< -9223372036854775806).first else #none -> 0, \
             (-9223372036854775810 ..< -9223372036854775806).last else #none -> 0]}",
            family(vec![
                (i(0), Value::Int(4)),
                (i(1), Value::Bool(true)),
                (i(2), Value::Bool(true)),
                (i(3), Value::Bool(false)),
                (i(4), Value::int(wide(1, -1))),
                (i(5), Value::int(wide(1, 2))),
            ]),
        ),
        (
            "a_range_just_below_64_bits_equal_to_the_set_of_its_integers",
            "${[(-9223372036854775811 ..= -9223372036854775809) == \
             {-9223372036854775811, -9223372036854775810, -9223372036854775809}, \
             (-9223372036854775811 ..= -9223372036854775809) == \
             {-9223372036854775811, -9223372036854775810}]}",
            family(vec![(i(0), Value::Bool(true)), (i(1), Value::Bool(false))]),
        ),
        // `<`, `min` and `max` of two ranges are refused by the checker (they take numbers,
        // strings and booleans), so their order from the ends is tested in the kernel
        // (`two_ranges_of_any_width_are_ordered_by_their_ends_as_their_sets_are`) and in
        // `bench::two_ranges_are_ordered_from_their_ends_in_constant_time`.
        (
            "a_range_of_10_to_the_30_entries_read_counted_and_tested",
            "${[(0 ..< 1000000000000000000000000000000)[999999999999999999999999999999], \
             (0 ..< 1000000000000000000000000000000).count, \
             1000000000000000000000000000000 in 0 ..< 1000000000000000000000000000000, \
             (0 ..< 1000000000000000000000000000000).last else #none -> -1]}",
            {
                let e30 = num_bigint::BigInt::from(10).pow(30u32);
                family(vec![
                    (i(0), Value::int(&e30 - 1)),
                    (i(1), Value::int(e30.clone())),
                    (i(2), Value::Bool(false)),
                    (i(3), Value::int(&e30 - 1)),
                ])
            },
        ),
    ]
}

/// The integer `d` past `i64::MAX + 1` (`below` 0), or past `i64::MIN - 1` (`below` 1).
fn wide(below: u8, d: i64) -> num_bigint::BigInt {
    match below {
        0 => num_bigint::BigInt::from(i64::MAX) + 1 + d,
        _ => num_bigint::BigInt::from(i64::MIN) - 1 + d,
    }
}

/// `[x0, x1, …]` of integers of any width.
fn ints(xs: &[num_bigint::BigInt]) -> Term {
    family(
        (xs.iter().enumerate())
            .map(|(k, x)| (i(k as i64), Value::int(x.clone())))
            .collect(),
    )
}

/// `a ..`: `rangeFrom(a)`, the integers from `a` up.
fn from(a: i64) -> Term {
    prim(Prim::RangeFrom, vec![lit(a)])
}

/// `k in m`.
fn has(k: Term, m: Term) -> Term {
    prim(Prim::Has, vec![k, m])
}

/// `m[k]`.
fn at(m: Term, k: Term) -> Term {
    prim(Prim::At, vec![m, k])
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
        "${a[ks[1]] else #notFound -> -1} ${a[ks[0]] else #notFound -> -1} ${b[ks[1]] else #outOfBounds -> -2} ${c[ss[1]] else #notFound -> -3} \
         ${c[ss[0]] else #notFound -> -3} ${a[ks[1]] is #notFound} ${b[ks[1]] is #outOfBounds}",
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
fn a_range_with_no_upper_end_read_at_keys_from_stdin() {
    // Plan row RANGE-open: with keys known only at run time, the reads do not fold at compile
    // time, so `rangeFrom` itself runs, in the interpreter and in the executable, against the
    // M0 model. `3 ..` and `0 ..< 10^12` are build-stage: the build keeps each as the call that
    // makes it (`zedc_stage` `built_value`), since as a literal one has no last entry and the
    // other 10^12 entries to write.
    let body = "${[n in 3 .., (3 ..)[n] else #outOfBounds -> -1, (n ..).first else #none -> 0, (n ..)[n + 5] else #outOfBounds -> 0, \
                4 in n .., (0 ..< 1000000000000)[n] else #outOfBounds -> -1]}";
    let src = dir("l03_02_map_run/open_stdin").join("open_stdin.zed");
    let text = format!(
        "main(m: MainArgs) {{\n    n = int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0;\n    m.stdout <- \"{body}\";\n}}\n"
    );
    std::fs::write(&src, text).unwrap();
    let exe = dir("l03_02_map_run/open_stdin").join("open_stdin");
    built(&src, &exe);
    for n in ["2", "3", "7", "-4", "1000000000000000000000"] {
        let k = || lit(Value::int(n.parse::<num_bigint::BigInt>().unwrap()));
        let from_k = || prim(Prim::RangeFrom, vec![k()]);
        let models = [
            has(k(), from(3)),
            or(at(from(3), k()), "outOfBounds", -1),
            or(prim(Prim::First, vec![from_k()]), "none", 0),
            or(at(from_k(), bin(Prim::Add, k(), lit(5))), "outOfBounds", 0),
            has(lit(4), from_k()),
            or(
                at(
                    prim(Prim::Range, vec![lit(0), lit(1_000_000_000_000i64)]),
                    k(),
                ),
                "outOfBounds",
                -1,
            ),
        ];
        let want = expected(&family(
            (models.iter().enumerate())
                .map(|(j, t)| (i(j as i64), eval(t).unwrap()))
                .collect(),
        ));
        let stdin = format!("{n}\n");
        let ran = interpreter(&src, &[], stdin.as_bytes());
        assert_eq!(
            (ran.stderr.as_str(), ran.status),
            ("", 0),
            "zedc run at {n}"
        );
        assert_eq!(ran.stdout, want, "zedc run at {n}");
        let ran = executable(&exe, &[], stdin.as_bytes());
        assert_eq!(
            (ran.stderr.as_str(), ran.status),
            ("", 0),
            "executable at {n}"
        );
        assert_eq!(ran.stdout, want, "executable at {n}");
    }
}

#[test]
fn the_first_prime_from_n_read_from_stdin() {
    // Plan row RANGE-open-walk, the gallery's `(n ..).where(isPrime).first` (DESIGN.md
    // sec:grammar, rule Range; there written with `for`, plan row FOR-one-generator), with `n`
    // known only at run time, so the walk runs in the interpreter and in the executable, and
    // `.find`, `.any` and `.all` of the same stream. The model is trial division in Rust; the
    // walk stops at the first prime, `n` itself when `n` is prime.
    let body = "${[(n ..).where(isPrime).first else #none -> 0, (n ..).find(isPrime) else #none -> 0, \
                (n ..).map(x -> x * x).where(x -> x mod 10 == 9).any(x -> x > 100), \
                (n ..).where(isPrime).all(x -> x < n + 3)]}";
    let src = dir("l03_02_map_run/prime_stdin").join("prime_stdin.zed");
    let text = format!(
        "isPrime(positional k) = k >= 2 && (2 ..< k).where(d -> d * d <= k && k mod d == 0)\
         .count == 0;\n\
         main(m: MainArgs) {{\n    n = int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0;\n    m.stdout <- \"{body}\";\n}}\n"
    );
    std::fs::write(&src, text).unwrap();
    let exe = dir("l03_02_map_run/prime_stdin").join("prime_stdin");
    built(&src, &exe);
    // The `.any` stops at the first square past 100 that ends in 9, which always comes, so it
    // gives `true`; the `.all` stops at the first prime from `n + 3` on, which always comes, so
    // it gives `false`.
    let prime = |k: i64| k >= 2 && (2..k).all(|d| d * d > k || k % d != 0);
    for n in [-5i64, 0, 2, 14, 24, 89, 90, 1000] {
        let p = (n..).find(|&k| prime(k)).unwrap();
        let want = expected(&family(vec![
            (i(0), i(p)),
            (i(1), i(p)),
            (i(2), Value::Bool(true)),
            (i(3), Value::Bool(false)),
        ]));
        let stdin = format!("{n}\n");
        let ran = interpreter(&src, &[], stdin.as_bytes());
        assert_eq!(
            (ran.stderr.as_str(), ran.status),
            ("", 0),
            "zedc run at {n}"
        );
        assert_eq!(ran.stdout, want, "zedc run at {n}");
        let ran = executable(&exe, &[], stdin.as_bytes());
        assert_eq!(
            (ran.stderr.as_str(), ran.status),
            ("", 0),
            "executable at {n}"
        );
        assert_eq!(ran.stdout, want, "executable at {n}");
    }
}

#[test]
fn a_family_read_by_key_at_keys_from_stdin() {
    // Cross-review XR-lazy-families round 3 (seat Sol; DESIGN.md sec:arenas, "A family read by
    // key", and sec:kernel, reference semantics (j)), with `n` known only at run time:
    // - a `where` over `n ..` then a `.find`, which reads the stream up to the deciding entry
    //   and so evaluates the selector at no key past it (`nextEven`);
    // - `sq(n)` and `sq[n]`, one read in two spellings, which agree inside and outside the
    //   domain `0 ..< 10`, and `sq[n]` misses with `#outOfBounds` outside it (`sameRead`);
    // - `.count` of a family whose entries are all `#none`, read off its domain (`headOnly`).
    // The call spelling `sq(n)` misses with `#notFound` today, not the `#outOfBounds` of an
    // integer-interval level; that half of `sameRead` waits for plan row KERNEL-family-call.
    // The model is Rust arithmetic on `n`.
    let body = "${[(n ..).where(x -> x mod 2 == 0).find(x -> x >= n) else #none -> -1, \
                sq(n) else #notFound -> -1, sq[n] else #outOfBounds -> -1, sq[n] is #outOfBounds, q.count]}";
    let src = dir("l03_02_map_run/family_by_key").join("family_by_key.zed");
    let text = format!(
        "main(m: MainArgs) {{\n    n = int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0;\n    \
         sq = (0 ..< 10).map(j -> j * j);\n    q = (0 ..< n).map(k -> #none);\n    \
         m.stdout <- \"{body}\";\n}}\n"
    );
    std::fs::write(&src, text).unwrap();
    let exe = dir("l03_02_map_run/family_by_key").join("family_by_key");
    built(&src, &exe);
    for n in [-1i64, 0, 1, 3, 9, 10] {
        let inside = (0..10).contains(&n);
        let square = if inside { n * n } else { -1 };
        let want = expected(&family(vec![
            (i(0), i(if n % 2 == 0 { n } else { n + 1 })),
            (i(1), i(square)),
            (i(2), i(square)),
            (i(3), Value::Bool(!inside)),
            (i(4), i(n.max(0))),
        ]));
        let stdin = format!("{n}\n");
        let ran = interpreter(&src, &[], stdin.as_bytes());
        assert_eq!(
            (ran.stderr.as_str(), ran.status),
            ("", 0),
            "zedc run at {n}"
        );
        assert_eq!(ran.stdout, want, "zedc run at {n}");
        let ran = executable(&exe, &[], stdin.as_bytes());
        assert_eq!(
            (ran.stderr.as_str(), ran.status),
            ("", 0),
            "executable at {n}"
        );
        assert_eq!(ran.stdout, want, "executable at {n}");
    }
}

#[test]
fn a_family_of_stdin_lines_with_no_proved_bound_still_builds() {
    // Cross-review XR-lazy-families round 3 (test R3-T3; DESIGN.md step M0.6): a family over
    // standard input has no proved size, and a normal build still accepts it and runs it, so
    // the feasibility rule of plan row COST-limit-capacity must not refuse every plan whose
    // footprint has no proved bound. The model is the number of lines given.
    let src = dir("l03_02_map_run/stdin_lines_unbounded").join("stdin_lines_unbounded.zed");
    std::fs::write(
        &src,
        "main(m: MainArgs) {\n    m.stdout <- \"${m.stdin.map(l -> l else #ioError -> \"\").count}\";\n}\n",
    )
    .unwrap();
    let exe = dir("l03_02_map_run/stdin_lines_unbounded").join("stdin_lines_unbounded");
    built(&src, &exe);
    for lines in [0usize, 1, 3, 50] {
        let stdin: String = (0..lines).map(|k| format!("line{k}\n")).collect();
        let want = expected(&lit(lines as i64));
        let ran = interpreter(&src, &[], stdin.as_bytes());
        assert_eq!(
            (ran.stderr.as_str(), ran.status),
            ("", 0),
            "zedc run at {lines}"
        );
        assert_eq!(ran.stdout, want, "zedc run at {lines}");
        let ran = executable(&exe, &[], stdin.as_bytes());
        assert_eq!(
            (ran.stderr.as_str(), ran.status),
            ("", 0),
            "executable at {lines}"
        );
        assert_eq!(ran.stdout, want, "executable at {lines}");
    }
}

#[test]
fn a_wide_range_made_from_ends_read_from_stdin() {
    // Plan row RANGE-lazy-wide: with the low end `n` known only at run time, the kernel prim
    // `Range` itself runs, in the interpreter and in the executable, on a range of 10^24
    // entries from `n`, whose high end is past `i64` for every `n` here; `n` past `i64` at
    // either end and across either 64-bit edge. The model is the integers themselves. The last
    // entry reads `2^63 ..< 10^24`, which is build-stage: the build keeps it as the call that
    // makes it (`zedc_stage` `built_value`, from `term::build::made_by`), since as a literal it
    // has about 10^24 entries to write.
    let body = "${[(n ..< n + 1000000000000000000000000)[n + 999999999999999999999999] else #outOfBounds -> 0, \
                (n ..< n + 1000000000000000000000000).count, \
                n - 1 in n ..< n + 1000000000000000000000000, \
                n + 5 in n ..< n + 1000000000000000000000000, \
                (n ..< n + 1000000000000000000000000).first else #none -> 0, \
                (n ..= n + 1000000000000000000000000).last else #none -> 0, \
                (9223372036854775808 ..< 1000000000000000000000000)[n] else #outOfBounds -> -1]}";
    let src = dir("l03_02_map_run/wide_stdin").join("wide_stdin.zed");
    let text = format!(
        "main(m: MainArgs) {{\n    n = int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0;\n    m.stdout <- \"{body}\";\n}}\n"
    );
    std::fs::write(&src, text).unwrap();
    let exe = dir("l03_02_map_run/wide_stdin").join("wide_stdin");
    built(&src, &exe);
    let e24 = num_bigint::BigInt::from(10).pow(24u32);
    for n in [
        wide(0, 0),
        wide(0, -3),
        wide(1, 0),
        wide(1, 2),
        num_bigint::BigInt::from(0),
        -&e24 - 3,
    ] {
        let want = expected(&family(vec![
            (i(0), Value::int(&n + &e24 - 1)),
            (i(1), Value::int(e24.clone())),
            (i(2), Value::Bool(false)),
            (i(3), Value::Bool(true)),
            (i(4), Value::int(n.clone())),
            (i(5), Value::int(&n + &e24)),
            (
                i(6),
                eval(&or(
                    at(
                        prim(
                            Prim::Range,
                            vec![
                                lit(Value::int(num_bigint::BigInt::from(1u64 << 63))),
                                lit(Value::int(e24.clone())),
                            ],
                        ),
                        lit(Value::int(n.clone())),
                    ),
                    "outOfBounds",
                    -1,
                ))
                .unwrap(),
            ),
        ]));
        let stdin = format!("{n}\n");
        let ran = interpreter(&src, &[], stdin.as_bytes());
        assert_eq!(
            (ran.stderr.as_str(), ran.status),
            ("", 0),
            "zedc run at {n}"
        );
        assert_eq!(ran.stdout, want, "zedc run at {n}");
        let ran = executable(&exe, &[], stdin.as_bytes());
        assert_eq!(
            (ran.stderr.as_str(), ran.status),
            ("", 0),
            "executable at {n}"
        );
        assert_eq!(ran.stdout, want, "executable at {n}");
    }
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

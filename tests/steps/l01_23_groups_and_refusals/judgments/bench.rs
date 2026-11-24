//! The benchmarks of `judgments.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `judgments.rs`.

use super::*;

/// A ring of `n` definitions, each a morphism type into a pair of the next and `int`, decided
/// in time linear in `n`. Neither ring is decided before the check: a group makes its canonical
/// form on first use and keeps it, so the first run of each size makes it, and the check holds
/// those first runs to the limit, both cold. Deciding the smaller ring once before (as this test
/// did until GROUP-decide-bytes) left the first larger run alone to make its form, and the
/// first runs then compared 1,504,930 bytes with 17,071,066, 11.3 times, where cold against
/// cold they are 2,141,806 and 17,071,066, 8.0 times.
#[test]
fn deciding_a_group_scales() {
    // TEST-bench-move-l0123, author P169: n 256 before, now 32768; 1x 0.20 s by `ns`, load 33.
    // The rings are built by `check_order_inputs`, only at the sizes each process runs: built
    // at both sizes before the first run, they took the whole first phase where each run is
    // counted under DynamoRIO in a new process that builds its input again; it stopped at its
    // limit on hm4 (job f25 on main b43e6d8bb, 42 s against 26 s), and with no limit counted
    // 8.09 times the instructions at 8n in 41 s (job f27; BENCH-main-43-pieces-v5e4).
    let n = 32768;
    let run = |g: &Group| {
        Type::forget_emptiness();
        let types = g.instance(vec![]);
        assert!(types.iter().all(|t| !t.is_empty()));
    };
    scaling::check_order_inputs("deciding a ring of definitions", n, 1, pair_ring, run);
}

/// The canonical form of one component of `n` members, each its own class, is made in
/// O(n log n): each group is new, so no table holds its form.
#[test]
fn the_canonical_form_of_a_component_scales() {
    // TEST-bench-move-l0123, author P169: n 2048 before, now 65536; 1x 0.31 s by `ns`, load 36.
    // Each group is built before its run's timing starts, one held at a time (MEM-l0126-40gb),
    // and released inside the run, as it was.
    let n = 65536;
    let form = |m: usize, g: Group| {
        let types = g.instance(vec![]);
        assert_eq!(types.len(), m);
    };
    let what = "the canonical form of a ring of definitions";
    scaling::check_order_fresh(what, n, 1, |m, _| marked_ring(m), form);
}

#[test]
fn a_nest_of_key_types_is_decided_in_one_search() {
    // TEST-bench-move-l0123, author P169: n 128 before, now 40_000; 1x 0.47 s by `ns`, load 36.
    let n = 40_000;
    let nests = scaling::inputs(n, key_nest);
    scaling::check("the verdict of a nest of n key types", n, |m| {
        Type::forget_emptiness();
        let verdict = if m % 2 == 0 {
            Verdict::Empty
        } else {
            Verdict::Inhabited
        };
        assert_eq!(nests[&m].verdict(), verdict);
    });
}

/// `order_free` over many seeds: the correctness test runs one new seed each run, so a corpus
/// on which an answer depends on the queries before it is found only now and then (FAIL row
/// FAIL-judgments-query-order-seed was one such seed). Each test sweeps 50 seeds.
fn order_free_sweep(from: u64) {
    for seed in from..from + 50 {
        order_free(seed);
    }
}

#[test]
fn subtype_answers_do_not_depend_on_the_queries_before_them_seeds_0_to_49() {
    order_free_sweep(0);
}

#[test]
fn subtype_answers_do_not_depend_on_the_queries_before_them_seeds_50_to_99() {
    order_free_sweep(50);
}

#[test]
fn subtype_answers_do_not_depend_on_the_queries_before_them_seeds_100_to_149() {
    order_free_sweep(100);
}

#[test]
fn subtype_answers_do_not_depend_on_the_queries_before_them_seeds_150_to_199() {
    order_free_sweep(150);
}

/// A union of `n` functions met with a union of `n` others, each of the one side taking the
/// parameters of one of the other, is `n` functions, made in time linear in `n`: each is paired
/// only with the functions that take its parameters (FAIL-types-meet-function-union, COMPLEXITY.md
/// F200). Small instance: `a_meet_with_a_union_of_functions_keeps_both_sides`.
#[test]
fn a_meet_of_unions_of_functions_scales() {
    use zedc::check::read::parse_type;
    use zedc::check::ty::Ty;
    let union = |m: usize, result: &str| {
        let text = (0..m)
            .map(|i| format!("((x{i}: int) -> {result})"))
            .collect::<Vec<_>>()
            .join(" | ");
        parse_type(&text).expect("a union of functions")
    };
    // n 8192 since TEST-split-chkbub1-long, 16384 before: at 16384 the test took 72.5 s alone
    // at load 66 (killed at its limit at load 39 in main-watch's run of 2026-11-21), while its
    // runs took 2.2 s at n and 15.7 s at 8n; the rest was building the inputs, both sizes in
    // each of its two processes (`scaling::inputs`, `scaling::compare_by`). At 8192 the run at n
    // is near the 1 s per run at n the benchmarks are sized to (author P169), and the building
    // halves with it. The case is the same.
    // Since BENCH-main-43-pieces-v5e4 the sides are built by `check_inputs`, only at the sizes
    // each process runs: built at both (`scaling::inputs`), the test stopped at its 20 s limit
    // in its first phase on hm4 (job f25 on main b43e6d8bb), and with no limit counted 8.00
    // times the instructions at 8n in 53 s (job f27).
    let n = 8192;
    let sides = |m| (m, union(m, "int | #a"), union(m, "int | #b"));
    scaling::check_inputs(
        "the meet of two unions of n functions",
        n,
        sides,
        |(m, a, b): &(usize, Ty, Ty)| {
            assert_eq!(a.meet(b).fns.len(), *m);
        },
    );
}

/// An overload of `n` exact arrows met with an overload of `n` partial arrows over the same
/// keys, one atom each, is one function of `n` exact arrows, each partial arrow joined to the
/// exact arrow over its key, made in time near linear in `n`: each side's guarantee and
/// permission are made once and compared once, each partial arrow is met with the other
/// side's permission once, and the arrows are joined through one hash map
/// (FAIL-types-meet-exact-arrows-differing-domains, COMPLEXITY.md F222). Small instances:
/// `a_meet_of_functions_meets_their_domains`,
/// `a_meet_of_an_exact_and_a_partial_arrow_over_one_domain_is_one_arrow`.
#[test]
fn a_meet_of_overloads_meets_their_domains_in_time_near_linear() {
    use zedc::check::read::parse_type;
    use zedc::check::ty::Ty;
    let overload = |m: usize, arrow: &str| {
        let text = (0..m)
            .map(|i| format!("(#k{i} {arrow})"))
            .collect::<Vec<_>>()
            .join(" & ");
        parse_type(&text).expect("an overload")
    };
    let n = 4096;
    let sides = scaling::inputs(n, |m| (overload(m, "-> int"), overload(m, "->? int | #a")));
    scaling::check("the meet of two overloads of n arrows", n, |m| {
        let (a, b): &(Ty, Ty) = &sides[&m];
        let met = a.meet(b);
        assert_eq!(met.fns.len(), 1);
        assert_eq!(met.fns[0].arrows.len(), m);
        assert!(met.fns[0].arrows.iter().all(|a| !a.partial));
    });
}

/// An overload of `n` exact arrows, each over the functions `#ki -> int`, met with an overload
/// of `n` arrows over the functions `#ji -> int` is empty, and met with one of `n` partial
/// arrows over the same functions as its own is one function of `n` arrows; an overload of `n`
/// exact arrows over `#box(#ki -> int)`, met with one over `#box(#ji)`, is empty. Each is made
/// in time near linear in `n`: the domains of the functions built at the parameter are joined
/// into one kernel type and compared once with the other side's parameter types joined, and a
/// function in a payload is read as every function (FAIL-types-meet-fn-fn-domains,
/// COMPLEXITY.md F234). Small instance:
/// `a_meet_of_functions_over_function_domains_that_differ_is_empty`.
#[test]
fn a_meet_of_overloads_over_function_domains_scales() {
    use zedc::check::read::parse_type;
    use zedc::check::ty::Ty;
    let overload = |m: usize, arrow: &dyn Fn(usize) -> String| {
        let text = (0..m).map(arrow).collect::<Vec<_>>().join(" & ");
        parse_type(&text).expect("an overload")
    };
    let n = 2048;
    let sides = scaling::inputs(n, |m| {
        [
            overload(m, &|i| format!("((#k{i} -> int) -> int)")),
            overload(m, &|i| format!("((#j{i} -> int) -> int)")),
            overload(m, &|i| format!("((#k{i} -> int) ->? int | #a)")),
            overload(m, &|i| format!("(#box(#k{i} -> int) -> int)")),
            overload(m, &|i| format!("(#box(#j{i}) -> int)")),
        ]
    });
    scaling::check(
        "the meets of an overload of n arrows over function domains",
        n,
        |m| {
            let [a, apart, same, boxed, data]: &[Ty; 5] = &sides[&m];
            assert!(a.meet(apart).fns.is_empty());
            let met = a.meet(same);
            assert_eq!(met.fns.len(), 1);
            assert_eq!(met.fns[0].arrows.len(), m);
            assert!(boxed.meet(data).fns.is_empty());
        },
    );
}

/// An overload of `n` exact arrows over the data `#pair(#ki, _)`, and one over `#box(#ki ->
/// int)`, each met with an overload of `n` arrows over the functions `#ji -> int`, are empty,
/// made in time near linear in `n`: what each parameter type of an exact arrow holds is proved
/// once for each function from its reading from below, which the meet makes anyway, by one
/// kernel verdict (`Domains::witness`, FAIL-types-meet-fn-fn-domains, COMPLEXITY.md F234).
/// Small instance: `a_meet_of_a_data_domain_holding_the_unknown_with_function_domains_is_empty`.
#[test]
fn a_meet_of_overloads_over_data_holding_the_unknown_with_function_domains_scales() {
    use zedc::check::read::parse_type;
    use zedc::check::ty::Ty;
    let overload = |m: usize, arrow: &dyn Fn(usize) -> String| {
        let text = (0..m).map(arrow).collect::<Vec<_>>().join(" & ");
        parse_type(&text).expect("an overload")
    };
    let n = 2048;
    let sides = scaling::inputs(n, |m| {
        [
            overload(m, &|i| format!("(#pair(#k{i}, _) -> int)")),
            overload(m, &|i| format!("(#box(#k{i} -> int) -> int)")),
            overload(m, &|i| format!("((#j{i} -> int) ->? int)")),
        ]
    });
    scaling::check(
        "the meets of an overload of n arrows over data holding the unknown or a function",
        n,
        |m| {
            let [unknown, boxed, fns]: &[Ty; 3] = &sides[&m];
            assert!(unknown.meet(fns).fns.is_empty());
            assert!(boxed.meet(fns).fns.is_empty());
        },
    );
}

/// An overload of `n` exact arrows over the functions `int -> #ki` met with one of `n` partial
/// arrows over `int -> #ji` is empty, the results sharing no value, made in time near linear
/// in `n`: the results of the built functions and those of the other side's function types
/// are each joined into one kernel type and compared once (`Domains::fns_apart`,
/// FAIL-types-meet-fn-fn-domains, COMPLEXITY.md F234). Small instance:
/// `a_meet_of_functions_over_function_domains_that_differ_is_empty`.
#[test]
fn a_meet_of_overloads_over_functions_of_results_sharing_no_value_scales() {
    use zedc::check::read::parse_type;
    use zedc::check::ty::Ty;
    let overload = |m: usize, arrow: &dyn Fn(usize) -> String| {
        let text = (0..m).map(arrow).collect::<Vec<_>>().join(" & ");
        parse_type(&text).expect("an overload")
    };
    let n = 2048;
    let sides = scaling::inputs(n, |m| {
        [
            overload(m, &|i| format!("((int -> #k{i}) -> int)")),
            overload(m, &|i| format!("((int -> #j{i}) ->? int)")),
        ]
    });
    scaling::check(
        "the meet of overloads of n arrows over functions of results sharing no value",
        n,
        |m| {
            let [exact, partial]: &[Ty; 2] = &sides[&m];
            assert!(exact.meet(partial).fns.is_empty());
        },
    );
}

/// The paths added for FAIL-types-meet-fn-kept-not-within (COMPLEXITY.md F234), each in time
/// near linear in `n`: an overload of `n` exact arrows `#ki -> #vi | #w` met with one of `n`
/// partial arrows `#ki ->? #vi` is one function of `n` exact arrows, each value type met once
/// with the union of the other side's (`Domains::meet`); an overload of `n` arrows over the
/// functions `#ki .. (#ki | #ji) -> int`, two arrows each, met with one over `#ji -> int` is
/// empty, the domain of each function built from both arrows (`Domains::fns_apart`); one of
/// `n` arrows over pairs `(#ki -> int, #ki)` met with one over triples is empty, the shapes
/// read from above compared once (`Domains::shapes_apart`); a function over functions nested
/// `n` deep over `int` met with the same over `()` is empty, one meet of parameter types at
/// each level (`Domains::keys_apart`); a partial arrow over a union of `2n` functions met with
/// an exact arrow over `n` of them, and `n` arrows over function values met with `n` others,
/// are kept, the unions not paired (`Domains::keys_apart`, `Domains::results_apart`); and
/// `Never ->? Never` met with a function over a function curried `n` deep is empty, the curried
/// function proved to exist on a work list (`Domains::inhabited_fn`). Small instances:
/// `judgments::a_meet_of_functions_kept_before_is_within_each_side`.
///
/// One test for each check (TEST-split-chkbub1-long). Until then the nine checks were one test,
/// which took 110 s at load 42 and 55.5 s at load 13 in main-watch's runs of 2026-11-21, and
/// 154.8 s alone at load 45, while its nine measured runs (at n and at 8n) added up to 18.5 s.
/// The rest was the replays of `scaling::compare_by`: on a count of instructions the run at 8n
/// of check `k` runs in a new process of the test binary, which runs the test from its start
/// and replays each earlier check `j < k` at both sizes, unmeasured, before it measures; and
/// each process built the inputs of all three families at both sizes. So a test of `c` checks
/// runs check `j`'s two sizes `c - j` times, about `c²/2` runs where `c` would do. As tests of
/// one check each, no check is replayed and each process builds only its own check's inputs;
/// the checks, their inputs, sizes and limits are as before.
mod meets_of_many_arrows_narrow_values_in_linear_time {
    use super::*;
    use zedc::check::read::parse_type;
    use zedc::check::ty::Ty;

    /// The overload of the `m` arrows `arrow(0) & .. & arrow(m - 1)`.
    fn overload(m: usize, arrow: &dyn Fn(usize) -> String) -> Ty {
        let text = (0..m).map(arrow).collect::<Vec<_>>().join(" & ");
        parse_type(&text).expect("an overload")
    }

    /// `(#{key}0 -> int) | .. | (#{key}(m-1) -> int)`, in parentheses.
    fn union(m: usize, key: &str) -> String {
        let u = (0..m)
            .map(|i| format!("(#{key}{i} -> int)"))
            .collect::<Vec<_>>()
            .join(" | ");
        format!("({u})")
    }

    /// `((... ((key -> String) -> int) ...) -> int)`, `m` levels over the key.
    fn deep(m: usize, key: &str) -> Ty {
        let mut text = format!("{key} -> String");
        for _ in 0..m {
            text = format!("({text}) -> int");
        }
        parse_type(&text).expect("a function over functions")
    }

    /// `(int -> .. -> int) -> Never`, a function over a function curried `m` deep.
    fn curried(m: usize) -> Ty {
        let nest = vec!["int"; m + 1].join(" -> ");
        parse_type(&format!("({nest}) -> Never")).expect("a curried function")
    }

    #[test]
    fn narrowing_values() {
        let n = 2048;
        let sides = scaling::inputs(n, |m| {
            [
                overload(m, &|i| format!("(#k{i} -> #v{i} | #w)")),
                overload(m, &|i| format!("(#k{i} ->? #v{i})")),
            ]
        });
        scaling::check("meets of n arrows narrowing values", n, |m| {
            let [exact, partial]: &[Ty; 2] = &sides[&m];
            let met = exact.meet(partial);
            assert_eq!(met.fns.len(), 1);
            assert_eq!(met.fns[0].arrows.len(), m);
            assert!(met.fns[0].arrows.iter().all(|a| !a.partial));
        });
    }

    #[test]
    fn over_two_bound_domains() {
        let n = 2048;
        let sides = scaling::inputs(n, |m| {
            [
                overload(m, &|i| {
                    format!("((#k{i} .. (#k{i} | #j{i}) -> int) -> int)")
                }),
                overload(m, &|i| format!("((#j{i} -> int) -> int)")),
            ]
        });
        scaling::check("meets of n arrows over two-bound domains", n, |m| {
            let [bounded, apart]: &[Ty; 2] = &sides[&m];
            assert!(bounded.meet(apart).fns.is_empty());
        });
    }

    #[test]
    fn over_tuples_holding_functions() {
        let n = 2048;
        let sides = scaling::inputs(n, |m| {
            [
                overload(m, &|i| format!("(((#k{i} -> int, #k{i})) -> int)")),
                overload(m, &|i| format!("(((#k{i} -> int, #k{i}, ())) -> int)")),
            ]
        });
        scaling::check("meets of n arrows over tuples holding functions", n, |m| {
            let [pairs, triples]: &[Ty; 2] = &sides[&m];
            assert!(pairs.meet(triples).fns.is_empty());
        });
    }

    // Unions of many function types on both sides of a meet, alone and as the parameter or
    // value types `Domains::meet` meets (the next four tests): only the pairs whose domains are
    // not proved apart are tried (`Pairs::fns_met`). Before (TYPES-meet-fns-indexed), each pair
    // was tried: the meet of the two unions took 84 ms to 3.46 s from m = 32 to 256, and the
    // meets of parameter and value types were skipped, which made them 0.33 s to 6.5 s and
    // 0.19 s to 5.1 s.

    #[test]
    fn two_unions_of_functions_apart() {
        let n = 1024;
        let unions = scaling::inputs(n, |m| {
            [
                parse_type(&union(m, "k")).expect("a union"),
                parse_type(&union(m, "j")).expect("a union"),
            ]
        });
        scaling::check("a meet of two unions of n functions apart", n, |m| {
            let [ks, js]: &[Ty; 2] = &unions[&m];
            assert!(ks.meet(js).fns.is_empty());
        });
    }

    #[test]
    fn arrows_over_unions_of_functions() {
        let n = 1024;
        let unions = scaling::inputs(n, |m| {
            [
                parse_type(&format!("{} ->? int", union(2 * m, "k"))).expect("an arrow"),
                parse_type(&format!("{} -> int", union(m, "k"))).expect("an arrow"),
            ]
        });
        scaling::check("a meet of arrows over unions of n functions", n, |m| {
            let [wide, narrow]: &[Ty; 2] = &unions[&m];
            assert_eq!(wide.meet(narrow).fns.len(), 1);
        });
    }

    #[test]
    fn partial_arrows_over_unions_of_functions() {
        let n = 1024;
        let unions = scaling::inputs(n, |m| {
            [
                parse_type(&format!("{} ->? int", union(2 * m, "k"))).expect("an arrow"),
                parse_type(&format!("{} ->? int", union(m, "j"))).expect("an arrow"),
            ]
        });
        scaling::check(
            "a meet of partial arrows over unions of n functions",
            n,
            |m| {
                // The parameter types `#ki -> int` and `#ji -> int` share no function.
                let [wide, other]: &[Ty; 2] = &unions[&m];
                assert!(wide.meet(other).fns.len() <= 1);
            },
        );
    }

    #[test]
    fn arrows_over_functions_as_values() {
        let n = 1024;
        let unions = scaling::inputs(n, |m| {
            [
                overload(m, &|i| format!("(#k{i} -> (#k{i} -> int))")),
                overload(m, &|i| format!("(#k{i} -> (#j{i} -> int))")),
            ]
        });
        scaling::check("a meet of n arrows over functions as values", n, |m| {
            // The values' domains differ, so no function is of both.
            let [own, other]: &[Ty; 2] = &unions[&m];
            assert!(own.meet(other).fns.is_empty());
        });
    }

    // Nested types are read and met on frames of their own, but kept smaller, as the texts
    // grow with the depth (the next two tests).

    #[test]
    fn functions_over_functions_nested_deep() {
        let depth = 128;
        let nests = scaling::inputs(depth, |m| [deep(m, "int"), deep(m, "()")]);
        scaling::check(
            "a meet of functions over functions nested n deep",
            depth,
            |m| {
                let [ints, units]: &[Ty; 2] = &nests[&m];
                assert!(ints.meet(units).fns.is_empty());
            },
        );
    }

    #[test]
    fn a_function_curried_deep() {
        let depth = 128;
        let nests = scaling::inputs(depth, |m| {
            [curried(m), parse_type("Never ->? Never").expect("no key")]
        });
        scaling::check("a meet with a function curried n deep", depth, |m| {
            let [nest, none]: &[Ty; 2] = &nests[&m];
            assert!(nest.meet(none).fns.is_empty());
        });
    }
}

/// A tuple nested `n` deep with a function at each depth is a subtype of the same tuple with
/// another function of the same type at each depth, decided in time linear in `n`: each
/// function is compared with the one at its depth (FAIL-types-tuple-subtype, COMPLEXITY.md
/// F201). Small instance: `tuples_equal_part_by_part_are_subtypes_both_ways`.
#[test]
fn a_nest_of_tuples_holding_functions_is_compared_depth_by_depth() {
    use zedc::check::read::parse_type;
    use zedc::check::ty::Ty;
    let nest = |m: usize, f: &str| {
        let text = (0..m).fold("int".to_string(), |inner, _| format!("({f}, {inner})"));
        parse_type(&text).expect("a nest of tuples")
    };
    let n = 2048;
    let sides = scaling::inputs(n, |m| {
        let a = nest(m, "(_ -> int) & (_ -> int | #a)");
        (a, nest(m, "_ -> int"))
    });
    scaling::check(
        "comparing two nests of n tuples, each holding a function",
        n,
        |m| {
            let (a, b): &(Ty, Ty) = &sides[&m];
            assert!(a.subtype(b) && b.subtype(a));
        },
    );
}

/// `n` rows of functions equal on both sides at one place, none compared there, decided in time
/// linear in `n` when the forms are built a second time with the skipped pairs merged
/// (FAIL-types-equal-functions-subset-no, COMPLEXITY.md F124): with a tag the right side lacks
/// the answer is a definite no, and without it a refusal. The functions take a tuple,
/// `(x_i: (int, int)) -> int`, so they have no domain key and stay in one part (`domain_key` in
/// ty.rs). Taking `int`, as here until 3189a1922 (PERF-types-loose-pairing-dense), each `i` is a
/// part of its own, the rows are paired and the case without the tag is a definite yes (`f_i`
/// fits `h_i`, so `(f_i, #a_i)` and `(h_i, #b_i)` are both held by `(h_i, #a_i | #b_i)`): that
/// case is checked too (FAIL-bench-equal-functions-domain-key; bisected, the bench passed at
/// 197c7de2b and failed at 3189a1922). Each row `(h_i, #b_i)`
/// meets both right rows of its `i`, and `(h_i, #a_i | #b_i)` both left rows, so the pairs of
/// rows that meet form no stars, and the pairs of rows the search finds outnumber the functions,
/// so the
/// equal functions are skipped ([`PlaceFns::starred`] in `crates/zedc-types/src/ty.rs`; since
/// FAIL-types-loose-pairing-non-star the count alone decides that); until
/// FAIL-types-loose-pairing-decided the right side was
/// `(h_i, #a_i) | (f_i, #b_i) | (h_i, #b_i)`, whose rows meet one by one and are now paired,
/// `functions_at_one_place_meeting_one_by_one_are_paired_in_linear_time`. Small instances:
/// `equal_functions_on_the_right_all_held_on_the_left_are_no_definite_no` and
/// `random_unions_of_tuples_with_functions_agree_with_pairing_every_function`.
#[test]
fn functions_equal_at_one_place_are_decided_a_second_time_in_linear_time() {
    // n 256: 1x 0.15 to 0.21 s by `ns`, load 27 to 42; 8.30 times the instructions at 256 and
    // 2048 (1.16 G and 9.66 G), three runs at ae23e9509 (PERF-equal-functions-forms-ratio).
    // Before, 8.80 there (1.65 G and 14.50 G) and 9.15 at dc060f8b9 (1.58 G and 14.47 G): the
    // unions of tuple types were joined in pairs, remaking each merged set's nodes at each
    // level, and the rows taken away from a union were taken one at a time; both are now made
    // at once (`Type::union_all`, `Bdd::zip_chain`), and at dc060f8b9 the set nodes made fell
    // from 300 k and 3.26 M to 33 k and 258 k.
    use zedc::check::read::parse_type;
    use zedc::check::ty::Ty;
    let sides = |m: usize, d: &str, extra: &str| {
        let f = |i: usize| format!("((x{i}: {d}) -> int)");
        let h = |i: usize| format!("((x{i}: {d}) -> int | #z)");
        let left: Vec<String> = (0..m)
            .flat_map(|i| [format!("({}, #a{i})", f(i)), format!("({}, #b{i})", h(i))])
            .chain([extra.to_string()].into_iter().filter(|e| !e.is_empty()))
            .collect();
        let right: Vec<String> = (0..m)
            .flat_map(|i| {
                let (f, h) = (f(i), h(i));
                [
                    format!("({h}, #a{i} | #b{i})"),
                    format!("({f}, #b{i} | #c{i})"),
                ]
            })
            .collect();
        let parse = |rows: Vec<String>| parse_type(&rows.join(" | ")).expect("a union of tuples");
        (parse(left), parse(right))
    };
    let n = 256;
    let pair = "(int, int)";
    let no = scaling::inputs(n, |m| sides(m, pair, "(((int, int)) -> int, #c)"));
    let refused = scaling::inputs(n, |m| sides(m, pair, ""));
    let yes = scaling::inputs(n, |m| sides(m, "int", ""));
    scaling::check(
        "n rows of functions equal on both sides at one place, decided twice",
        n,
        |m| {
            let (a, b): &(Ty, Ty) = &no[&m];
            assert!(!a.subtype(b) && a.refused(b).is_empty());
            let (a, b): &(Ty, Ty) = &refused[&m];
            assert!(!a.refused(b).is_empty());
            let (a, b): &(Ty, Ty) = &yes[&m];
            assert!(a.subtype(b));
        },
    );
}

/// `n` rows of functions at one place whose rows meet one by one or in stars, decided in time
/// linear in `n` by comparing exactly the pairs of functions whose rows meet
/// (FAIL-types-loose-pairing-decided, COMPLEXITY.md F124): the left row `(h_i, #b_i)` meets the
/// right rows `(f_i, #b_i)` and `(h_i, #b_i)`, and `(f_i, #a_i)` meets only `(h_i, #a_i)`, so
/// each `i` is a star and the answer is a definite yes. Small instance:
/// `functions_at_one_place_are_decided_by_their_pairing`.
#[test]
fn functions_at_one_place_meeting_one_by_one_are_paired_in_linear_time() {
    use zedc::check::read::parse_type;
    use zedc::check::ty::Ty;
    let sides = |m: usize| {
        let f = |i: usize| format!("((x{i}: int) -> int)");
        let h = |i: usize| format!("((x{i}: int) -> int | #z)");
        let left: Vec<String> = (0..m)
            .flat_map(|i| [format!("({}, #a{i})", f(i)), format!("({}, #b{i})", h(i))])
            .collect();
        let right: Vec<String> = (0..m)
            .flat_map(|i| {
                let (f, h) = (f(i), h(i));
                [
                    format!("({h}, #a{i})"),
                    format!("({f}, #b{i})"),
                    format!("({h}, #b{i})"),
                ]
            })
            .collect();
        let parse = |rows: Vec<String>| parse_type(&rows.join(" | ")).expect("a union of tuples");
        (parse(left), parse(right))
    };
    // n 1024: 1x about 0.33 s by `ns` (0.083 s at n 256, load 53).
    let n = 1024;
    let yes = scaling::inputs(n, sides);
    scaling::check(
        "n rows of functions at one place meeting one by one, paired",
        n,
        |m| {
            let (a, b): &(Ty, Ty) = &yes[&m];
            assert!(a.subtype(b) && a.refused(b).is_empty());
        },
    );
}

/// `n` rows of functions at one place whose rows all meet, `((i) -> 1, i)` against
/// `((i) -> int, int)`, decided in time linear in `n` (PERF-types-loose-pairing-dense,
/// COMPLEXITY.md F124, "Parts by domain"): `n^2` pairs of rows meet, but a function fits only
/// one of its own domain, so the functions are split by domain and each part holds one row a
/// side. Before, the spot was refused after counting the near pairs past the functions, which
/// cost 41.7 M instructions at n = 20 and 2,522 M at n = 160, 60.5 times; with every pair
/// compared it would be `n^2` comparisons. The right side with one domain changed is a definite
/// no. Small instance: `functions_at_one_place_whose_tuples_all_meet_are_decided`.
#[test]
fn functions_at_one_place_whose_rows_all_meet_are_split_by_domain_in_linear_time() {
    use zedc::check::read::parse_type;
    use zedc::check::ty::Ty;
    let sides = |m: usize| {
        let left: Vec<String> = (0..m).map(|i| format!("(({i}) -> 1, {i})")).collect();
        let right = |last: usize| -> Vec<String> {
            (0..m)
                .map(|i| format!("(({}) -> int, int)", if i + 1 == m { last } else { i }))
                .collect()
        };
        let parse = |rows: Vec<String>| parse_type(&rows.join(" | ")).expect("a union of tuples");
        (parse(left), parse(right(m - 1)), parse(right(m)))
    };
    let n = 256;
    let pairs = scaling::inputs(n, sides);
    scaling::check(
        "n rows of functions at one place, every row meeting every other, split by domain",
        n,
        |m| {
            let (a, yes, no): &(Ty, Ty, Ty) = &pairs[&m];
            assert!(a.subtype(yes) && a.refused(yes).is_empty());
            assert!(!a.subtype(no) && a.refused(no).is_empty());
        },
    );
}

/// The forms of a union of `n` rows, each with its own set of every atom nested beside a
/// function, cut the marks from each nested set once (FAIL-forms-nested-marks): linear in `n`.
#[test]
fn nested_sets_of_every_atom_are_cut_in_linear_time() {
    let n = 256;
    let pairs = scaling::inputs(n, nested_cut_rows);
    scaling::check(
        "the forms of n rows with a nested set of every atom",
        n,
        |m| {
            let (left, right) = &pairs[&m];
            assert!(left.subtype(right));
        },
    );
}

/// `nested_sets_of_every_atom_are_cut_in_linear_time` with the rows as the result of a
/// function: the `n` functions the rows hold are read as variables inside the comparison of the
/// two function types and replaced by their functions for the forms
/// (TEST-nested-marks-struct-parts), one walk of each result: linear in `n`.
#[test]
fn nested_sets_of_every_atom_in_results_are_cut_in_linear_time() {
    let n = 256;
    let pairs = scaling::inputs(n, nested_cut_results);
    scaling::check(
        "the forms of a result of n rows with a nested set of every atom",
        n,
        |m| {
            let (left, right) = &pairs[&m];
            assert!(left.subtype(right));
        },
    );
}

/// The results of `late_variable_results(n)` are compared at each of their `n` levels with a
/// function with no variable in the comparison's state, and the first variable that is no
/// such function, `T`, lies at the bottom, last in the walk of each level
/// (BENCH-closed-form-late-variable): `closed_binds` must not walk the whole level below at
/// each level.
#[test]
fn results_with_a_variable_late_beside_closed_functions_are_compared_in_linear_time() {
    let n = 256;
    let pairs = scaling::inputs(n, late_variable_results);
    scaling::check(
        "results of n levels with a variable last, beside functions with no variable",
        n,
        |m| {
            let (left, right) = &pairs[&m];
            assert!(left.subtype(right));
        },
    );
}

/// A nest of `n` function types, each result holding the next, compared both ways
/// (BENCH-closed-form-late-variable, `nested_function_results`): the false one searches for a
/// cover after each failed fit, which compares the same results again, and the verdict kept by
/// `Cx::fitted_written` keeps it linear. With that memo off, the false judgment at n 64 did not
/// end in 60 s (negative control, 2026-11-15); with it, 8.0 times at 8n both ways.
#[test]
fn nested_function_results_are_compared_in_linear_time() {
    let n = 64;
    let pairs = scaling::inputs(n, |n| {
        (
            nested_function_results(n, "1"),
            nested_function_results(n, "int"),
        )
    });
    scaling::check("a nest of n function types, left within right", n, |m| {
        let (left, right) = &pairs[&m];
        assert!(left.subtype(right));
    });
    scaling::check(
        "a nest of n function types, right not within left",
        n,
        |m| {
            let (left, right) = &pairs[&m];
            assert!(!right.subtype(left));
        },
    );
}

/// `nested_function_results_beside_a_row` compared both ways (PERF-types-shared-row-each-level):
/// the shared row must be read and compared once, not at each of the n levels.
#[test]
fn nested_function_results_beside_a_shared_row_are_compared_in_linear_time() {
    let n = 16;
    let pairs = scaling::inputs(n, |n| {
        let left = nested_function_results_beside_a_row(n, "1");
        (left, nested_function_results_beside_a_row(n, "int"))
    });
    scaling::check(
        "a nest of n function types beside a shared row, left within right",
        n,
        |m| {
            let (left, right) = &pairs[&m];
            assert!(left.subtype(right));
        },
    );
    scaling::check(
        "a nest of n function types beside a shared row, right not within left",
        n,
        |m| {
            let (left, right) = &pairs[&m];
            assert!(!right.subtype(left));
        },
    );
}

/// One generic arrow over `n` atoms, `((#k0 | … | #k(n-1), T) -> int for T in int)`, against
/// `n` arrows `((#ki, int) -> int)` (FAIL-types-generic-arrow-overload-cover): the cover of
/// each binds `T` to `int`, and each instance, the same one, is outside that arrow alone and
/// within all of them, which is compared once for the comparison, not once per arrow of `q`.
/// With one more atom on the left, `#kn`, no arrow takes it, and the answer is no.
#[test]
fn a_generic_arrow_covering_many_arrows_is_compared_in_linear_time() {
    use zedc::check::read::parse_type;
    let n = 64;
    let atoms = |n: usize| {
        (0..n)
            .map(|i| format!("#k{i}"))
            .collect::<Vec<_>>()
            .join(" | ")
    };
    let pairs = scaling::inputs(n, |n| {
        let q: Vec<String> = (0..n).map(|i| format!("((#k{i}, int) -> int)")).collect();
        let q = parse_type(&q.join(" & ")).unwrap();
        let s = parse_type(&format!("(({}, T) -> int for T in int)", atoms(n))).unwrap();
        let wider = parse_type(&format!("(({}, T) -> int for T in int)", atoms(n + 1))).unwrap();
        (s, wider, q)
    });
    scaling::check("a generic arrow over n atoms within n arrows", n, |m| {
        let (s, _, q) = &pairs[&m];
        assert!(s.subtype(q));
    });
    scaling::check(
        "a generic arrow over n + 1 atoms not within n arrows",
        n,
        |m| {
            let (_, wider, q) = &pairs[&m];
            assert!(!wider.subtype(q));
        },
    );
}

/// `nested_sets_of_every_atom_are_cut_in_linear_time` against the union of the one shape and
/// `(1, 2)` (PERF-types-cut-rows-union-scaling): the kernel splits the first components into
/// the class of the `n` nested sets and that of `1`, and decides the class of the nested sets
/// on the component as it was, not on the union of its `n + 1` cells, which each test of a
/// cell would read: linear in `n`. Before, 46.7 times the instructions from n 16 to 128.
#[test]
fn nested_sets_of_every_atom_against_a_union_are_cut_in_linear_time() {
    let n = 256;
    let pairs = scaling::inputs(n, |n| nested_cut_rows_beside_a_pair(n, "(int -> int)"));
    scaling::check(
        "n rows with a nested set of every atom against a union of two shapes",
        n,
        |m| {
            let (left, right) = &pairs[&m];
            assert!(left.subtype(right));
        },
    );
}

/// A first component that is a large union beside a small class
/// (TEST-split-classes-uncut-bench): two rows with a nested set of every atom against
/// `((#_, int), 1) | (1, 2)` and `n` rows `((#b, i), _)`. The `n` rows make the first
/// component of the box a union of `n` cells; the class of the nested sets is small. The kernel
/// keeps that component whole on the class's piece (PERF-types-cut-rows-union-scaling), so each
/// test of a cell reads the `n` cells where the cut component would hold only the class: linear
/// in `n` all the same. Before that change, 24.0 times the instructions from n 128 to 1024.
#[test]
fn a_large_first_component_beside_a_small_class_is_decided_in_linear_time() {
    let n = 128;
    let pairs = scaling::inputs(n, |m| nested_rows_against_cut_rows(2, m, "(#b, {i})"));
    scaling::check(
        "two nested sets against a union whose first component has n cells",
        n,
        |m| {
            let (left, right) = &pairs[&m];
            assert!(left.subtype(right));
        },
    );
}

/// The mirror of `a_large_first_component_beside_a_small_class_is_decided_in_linear_time`:
/// `n` rows with a nested set of every atom against the same union with two rows
/// `((i, i), _)`, a small first component and a class of `n + 1` cells. Before
/// PERF-types-cut-rows-union-scaling, 61.4 times the instructions from n 128 to 1024.
#[test]
fn n_nested_sets_against_a_small_first_component_are_decided_in_linear_time() {
    let n = 128;
    let pairs = scaling::inputs(n, |m| nested_rows_against_cut_rows(m, 2, "({i}, {i})"));
    scaling::check(
        "n nested sets against a union whose first component has two cells",
        n,
        |m| {
            let (left, right) = &pairs[&m];
            assert!(left.subtype(right));
        },
    );
}

/// `n` nested sets of every atom against the one shape `((#_, int), 1 | 2)`, whose second
/// component is wider than the rows' `1` (PERF-types-nested-rows-wider-second): linear in `n`.
/// Before, 38.8 and 59.2 times the instructions from n 16 to 128 and from 128 to 1024.
#[test]
fn nested_sets_against_a_wider_second_component_are_decided_in_linear_time() {
    let n = 128;
    let pairs = scaling::inputs(n, nested_rows_wider_second);
    scaling::check(
        "n nested sets against one shape with a wider second component",
        n,
        |m| {
            let (left, right) = &pairs[&m];
            assert!(left.subtype(right));
        },
    );
}

/// `n` nested sets of every atom against the two shapes `((#_, int), 1 | 2)` and
/// `((#_, int), 2 | 3)`, which cross on the second component (TEST-may-cover-piece-removal):
/// the pieces of the second component are taken out one at a time (`take_out_piece`) and the
/// box left is narrowed, linear in `n`. The split into the meet with each open tuple type,
/// which crossing cells left such a box to before, makes a piece per row.
#[test]
fn crossing_sets_against_a_wider_second_component_are_decided_in_linear_time() {
    let n = 128;
    let pairs = scaling::inputs(n, crossing_rows_wider_second);
    scaling::check(
        "n nested sets against two shapes crossing on the second component",
        n,
        |m| {
            let (left, right) = &pairs[&m];
            assert!(left.subtype(right));
        },
    );
}

/// One row `(#_, 0 | … | m)` against `m` shapes `(q_i, i | i + 1)`, with `q_i` = `#_` for the
/// first and last shape and `#_ \ #c_i` between: every piece `take_out_piece` can take rests on
/// a fork (PERF-take-out-forked-scan). Before, 11.9M and 878M instructions at `m` 16 and 128,
/// 73.7 times.
fn forked_pairs(m: usize) -> (zedc::check::ty::Ty, zedc::check::ty::Ty) {
    use zedc::check::read::parse_type;
    let values: Vec<String> = (0..=m).map(|v| v.to_string()).collect();
    let left = format!("(#_, {})", values.join(" | "));
    let right: Vec<String> = (0..m)
        .map(|i| {
            let q = if i == 0 || i + 1 == m {
                "#_".to_string()
            } else {
                format!("(#_ \\ #c{i})")
            };
            format!("({q}, {i} | {})", i + 1)
        })
        .collect();
    (
        parse_type(&left).unwrap(),
        parse_type(&right.join(" | ")).unwrap(),
    )
}

#[test]
fn a_row_against_shapes_whose_pieces_all_rest_on_forks_is_decided_in_linear_time() {
    let n = 16;
    let pairs = scaling::inputs(n, forked_pairs);
    scaling::check("a row against forked shapes", n, |m| {
        let (left, right) = &pairs[&m];
        assert!(left.subtype(right));
    });
}

/// A bounded overload over `n` atoms, `((#k0 | … | #k(n-1)) ->? B) & ((#k0 | … | #k(n-1)) ->
/// int | f64 | bool) for B in int | f64`, against `n` arrows `(#ki -> int)`
/// (FAIL-types-met-bindable-partial-narrow): each arrow of `q` is covered by the meet of the
/// exact arrow with the partial arrow at `B = int`. The partial arrows are read at each carrier
/// of `B` once for the comparison (`Cx::open`, `Narrowing`), not once per arrow of `q`. With
/// `-> bool` in place of `-> int` in `q`, no binding narrows to it, and the answer is no.
#[test]
fn a_bounded_partial_arrow_narrowing_many_arrows_is_compared_in_linear_time() {
    use zedc::check::read::parse_type;
    let n = 64;
    let pairs = scaling::inputs(n, |n| {
        let atoms = (0..n)
            .map(|i| format!("#k{i}"))
            .collect::<Vec<_>>()
            .join(" | ");
        let s = format!("(({atoms}) ->? B) & (({atoms}) -> int | f64 | bool) for B in int | f64");
        let q = |r: &str| {
            let q: Vec<String> = (0..n).map(|i| format!("(#k{i} -> {r})")).collect();
            parse_type(&q.join(" & ")).unwrap()
        };
        (parse_type(&s).unwrap(), q("int"), q("bool"))
    });
    scaling::check("a bounded partial arrow narrowing n arrows", n, |m| {
        let (s, q, _) = &pairs[&m];
        assert!(s.subtype(q));
    });
    scaling::check(
        "a bounded partial arrow narrowing none of n arrows",
        n,
        |m| {
            let (s, _, bool_q) = &pairs[&m];
            assert!(!s.subtype(bool_q));
        },
    );
}

/// `m` rows `((#_, i) \ (#a, i), 0)` against `m` shapes `((#_, int), i | i + 1)`: the rows are
/// split into disjoint disjuncts (K80) and each is narrowed against every shape
/// (PERF-disjoint-rows-shared-shapes, PERF-nested-cover-narrow-per-piece). At 8eb436214, 1.15G
/// and 285G instructions at m 32 and 256; after wt/kern-empty, 50.2M and 630M, 12.56 times.
fn chain(m: usize) -> (zedc::check::ty::Ty, zedc::check::ty::Ty) {
    use zedc::check::read::parse_type;
    let left: Vec<String> = (0..m)
        .map(|i| format!("((#_, {i}) \\ (#a, {i}), 0)"))
        .collect();
    let right: Vec<String> = (0..m)
        .map(|i| format!("((#_, int), {i} | {})", i + 1))
        .collect();
    (
        parse_type(&left.join(" | ")).unwrap(),
        parse_type(&right.join(" | ")).unwrap(),
    )
}

#[test]
fn rows_against_a_chain_of_shapes_are_decided_in_linear_time() {
    let n = 32;
    let pairs = scaling::inputs(n, chain);
    scaling::check("m rows against m chained shapes", n, |m| {
        let (left, right) = &pairs[&m];
        assert!(left.subtype(right));
    });
}

/// PERF-kernel-box-union-search: the meet of the overloads `(#box(#k_0) -> int) & … &
/// (#box(#k_{m-1}) -> int)` and the same with `#j_i`, empty, as no two of their domains
/// share a value. `Domains::outside` (`zedc-types`) compares the union of the `m` one-tuples
/// `(#box(#k_i),)` with that of the `(#box(#j_i),)`, which the kernel now does by their
/// components ([`Type::subtype_verdict`], `one_tuple_column`). Before, the simulation made
/// `m²` pairs and the search on the difference was quadratic too: 56, 207, 781 and 3277 ms at
/// `m` 64, 128, 256 and 512 on a Colab VM (2026-11-22), 4.2 times per doubling.
fn box_overloads_meet_scale(n: usize) {
    use zedc::check::read::parse_type;
    let overload = |m: usize, k: &str| {
        let text = (0..m)
            .map(|i| format!("(#box(#{k}{i}) -> int)"))
            .collect::<Vec<_>>()
            .join(" & ");
        parse_type(&text).expect("an overload")
    };
    let built = |m: usize| (overload(m, "k"), overload(m, "j"));
    let (small, large) = (built(n), built(scaling::FACTOR * n));
    scaling::check("the meet of two overloads on distinct boxes", n, |m| {
        let (b, c) = if m == n { &small } else { &large };
        assert!(b.meet(c).fns.is_empty());
    });
}

/// Size (PERF-kernel-box-union-search): n 2048, about 1 s at 1x on a Colab VM. Red before the
/// change, at n 64 (2026-11-22): 334M and 16,928M instructions at 64 and 512, 50.75 times,
/// failed. After it, at n 4096: 3,336M and 28,993M, 8.69 times, bytes 8.3 times, 1x 2.94 s.
#[test]
fn the_meet_of_two_overloads_on_distinct_boxes_scales() {
    box_overloads_meet_scale(2048);
}

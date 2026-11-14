//! The benchmarks of `refusals.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `refusals.rs`.

use super::*;

#[test]
fn a_residues_refusal_is_reached_in_the_size_of_the_classes() {
    // Θ(n) groups of periods. Measured on c881d28c: 10.0M instructions at n = 4, 81.9M at 32.
    refusal_scales(
        "Residues, by n copies of the classes",
        4,
        Refusal::Residues,
        erdos_cover_repeated,
    );
}

#[test]
fn a_tuple_split_refusal_is_reached_in_the_size_of_the_boxes() {
    // Θ(n) boxes. Measured on c881d28c: 4.4M instructions at n = 1, 159M at 32.
    refusal_scales(
        "TupleSplit, by n box covers",
        4,
        Refusal::TupleSplit,
        |n, _| box_covers(n),
    );
}

#[test]
fn a_morphism_split_refusal_is_reached_in_the_size_of_the_union() {
    // Θ(n) morphism types. Measured on c881d28c: 0.42M instructions at n = 1, 4.9M at 32.
    refusal_scales(
        "MorphismSplit, by n results",
        8,
        Refusal::MorphismSplit,
        |n, _| morphism_split_by(n),
    );
}

#[test]
fn a_no_witness_refusal_is_reached_in_the_size_of_the_keys() {
    // Θ(n) required keys. Measured on c881d28c: 87K instructions at n = 1, 302K at 32. Round 10
    // (the keys also hold a list type, X45): 2.21M at n = 8, 2.88M at 64.
    refusal_scales(
        "NoWitness, by n required keys",
        8,
        Refusal::NoWitness,
        |n, _| morphism_between_by(n),
    );
}

#[test]
fn a_fork_refusal_is_reached_in_the_size_of_the_pairs() {
    // Θ(n) excluded pairs. Measured on c881d28c, before REFUSAL-fork-linear: 63M, 221M, 805M and
    // 3209M instructions at n 8, 16, 32 and 64, order n^2: the search for a value before the
    // refusal narrowed the box into each excluded pair and tested every other pair there. Now
    // (REFUSAL-fork-linear) 30.2M and 255.9M instructions at n 8 and 64, 8.5 times.
    refusal_scales("Fork, by n excluded pairs", 8, Refusal::Fork, fork_by);
}

#[test]
fn a_difference_of_forked_unions_is_refused_in_its_size() {
    // The union of `n` pairs minus the union of `n` pairs that hold them, one each. Measured on
    // 8874023a, before REFUSAL-narrow-cells: 25.7M, 104M, 470M and 2396M instructions at n 8,
    // 16, 32 and 64, order n^2: each pair was a candidate for a value, whose narrowing tested
    // the `n` cells of its components and took the `n` excluded pairs out one by one, and the
    // search then refined the forked part, `n` searches of the whole part. Now 3.7M, 7.3M, 14.4M
    // and 28.8M (release probe): each pair is inside the pair that holds it, and the part, with
    // no value outside its pairs, is passed over as empty without refining (COMPLEXITY.md K80).
    refusal_scales(
        "Fork, by a difference of unions",
        8,
        Refusal::Fork,
        forked_difference_of_unions,
    );
}

#[test]
fn a_union_of_forked_differences_is_refused_in_its_size() {
    // The union of `n` differences, each a pair minus a pair that holds it. Measured on
    // 8874023a, before REFUSAL-narrow-cells: 64.6M, 264M, 1125M and 5123M instructions at n 8,
    // 16, 32 and 64, order n^2: the value search took all `2n` pairs on one box. Now 4.3M, 8.4M,
    // 16.7M and 33.4M (release probe), one box for each difference (COMPLEXITY.md K80).
    refusal_scales(
        "Fork, by a union of differences",
        8,
        Refusal::Fork,
        forked_union_of_differences,
    );
}

#[test]
fn a_pair_type_met_with_forked_differences_is_refused_in_its_size() {
    // The union of `a_union_of_forked_differences_is_refused_in_its_size` met with the pairs of
    // lists of integers, so the union is not at the top of the part. On the box that the pair
    // type narrows to, the pair type holds every tuple and drops out, and the union is searched
    // one difference at a time. Release probe, instructions at n 8, 16, 32 and 64: on 3c251cd5,
    // which split only a union at the top, 33M to 1694M (its report); with that split and
    // forked parts refined, 75.0M, 342M, 1757M and 10334M; now 11.3M, 22.5M, 44.9M and 89.8M
    // (COMPLEXITY.md K80).
    refusal_scales(
        "Fork, by a pair type met with a union of differences",
        8,
        Refusal::Fork,
        forked_differences_met_with_pairs,
    );
}

#[test]
fn a_union_of_pairs_less_pairs_holding_them_is_empty_in_its_size() {
    // The cells `0 | i` of the first components all share `0`, so they fall in one class, and
    // the part, false outside its tuple types, was split into its `2n` tuple types, each piece
    // deciding the whole part: 9.2M, 37.1M, 149.8M, 601.9M and 2392M instructions at n 8, 16,
    // 32, 64 and 128 on cf4e1fda, order n^2. The differences share no tuple type, so each is
    // now decided on the box alone: 1.27M, 2.45M, 4.77M, 9.56M and 18.8M (COMPLEXITY.md K80).
    big(|| {
        scaling::check(
            "Empty, by a union of n pairs less pairs that hold them",
            8,
            |n| {
                Type::forget_emptiness();
                assert_eq!(
                    pairs_less_holders(n, None).verdict(),
                    Verdict::Empty,
                    "at {n}"
                );
            },
        )
    });
}

#[test]
fn a_list_by_one_place_from_the_front_is_decided_in_its_size() {
    // Two recursive types on no cycle taken out of one tail are no fork: decided at each size,
    // in time linear in `n`.
    for (two, verdict) in [(false, Verdict::Empty), (true, Verdict::Inhabited)] {
        big(move || {
            scaling::check("a 1 at place n from the front, or none", 8, |n| {
                Type::forget_emptiness();
                let tag = format!("_of{n}{two}");
                let t = by_one_place_from_the_front(n, two, &tag);
                assert_eq!(t.verdict(), verdict, "at {n}");
            })
        });
    }
}

#[test]
fn emptiness_of_lists_by_one_place_from_the_front_scales() {
    // The lists by one place from the front have no fork and are proved empty. Until 2026-11-13
    // this check followed the one above in a single test.
    big(|| {
        let tag = AtomicUsize::new(0);
        scaling::check("emptiness, a 1 at one place from the front", 8, |n| {
            Type::forget_emptiness();
            let tag = format!("_if{}", tag.fetch_add(1, Relaxed));
            assert!(
                by_one_place_from_the_front(n, false, &tag).is_empty(),
                "at {n}"
            );
        });
    });
}

#[test]
fn refining_a_box_follows_no_fork_in_its_size() {
    // The search of a value refines the box of these pairs (`Searching::refine`), and the
    // pieces it tries meet the fork of the end family in the second component. Refining
    // followed the fork, the subset construction: on 92e736cd the verdict took 28.5M, 320M and
    // 3.64G instructions at n 1, 2 and 3, `is_empty` 23.1M, 47.4M and 1.58G, and this test did
    // not end within 60 s. Now refining counts a forked piece as inhabited, as the search of a
    // value after a refused decision does: the verdict 22.5M, 27.3M, 39.1M, 62.1M, 110M, 211M
    // and 435M at n 1, 2, 4, 8, 16, 32 and 64 (7.0 times from 8 to 64, order n^0.94),
    // `is_empty` 54.8M and 396M at 8 and 64 (COMPLEXITY.md K35).
    for skip in [false, true] {
        big(move || {
            let tag = AtomicUsize::new(0);
            scaling::check("Fork, refining pairs by the end family", 8, |n| {
                Type::forget_emptiness();
                let tag = format!("_rf{skip}{}", tag.fetch_add(1, Relaxed));
                let t = refined_pairs(n, skip, &tag);
                assert_eq!(t.verdict(), Verdict::Refused(Refusal::Fork), "at {n}");
            });
        });
    }
    big(|| {
        let tag = AtomicUsize::new(0);
        scaling::check("emptiness, refining pairs by the end family", 8, |n| {
            Type::forget_emptiness();
            let tag = format!("_rfe{}", tag.fetch_add(1, Relaxed));
            assert!(!refined_pairs(n, false, &tag).is_empty(), "at {n}");
        });
    });
    // The refusal at n 1 with the end family's one place left out is checked in
    // `refining_a_box_of_pairs_is_refused_at_the_end_family_fork` of refusals.rs
    // (TEST-bench-move-l0123, author P169).
}

#[test]
fn a_union_of_lists_by_the_place_of_a_one_from_the_front_is_decided_in_its_size() {
    big(|| {
        for (case, want) in [
            ("front", Verdict::Empty),
            ("far", Verdict::Inhabited),
            ("tuple", Verdict::Empty),
            ("tuplefar", Verdict::Inhabited),
            ("tupleflip", Verdict::Empty),
            ("tupleflipfar", Verdict::Inhabited),
            ("multi", Verdict::Empty),
            ("multifar", Verdict::Inhabited),
            ("groups", Verdict::Empty),
            ("groupsfar", Verdict::Inhabited),
            ("groupsholes", Verdict::Empty),
            ("groupsholesfar", Verdict::Inhabited),
            ("manyheads", Verdict::Empty),
            ("manyheadsfar", Verdict::Inhabited),
            ("stagger", Verdict::Empty),
            ("staggerfar", Verdict::Inhabited),
            ("chain", Verdict::Empty),
            ("chainfar", Verdict::Inhabited),
        ] {
            let (s_runs, l_runs) = scaling::Meter::new().runs();
            let small: Vec<Type> = (0..s_runs)
                .map(|i| rfx_case(case, 8, &format!("_fs_{case}_8_{i}")))
                .collect();
            let large: Vec<Type> = (0..l_runs)
                .map(|i| rfx_case(case, 64, &format!("_fs_{case}_64_{i}")))
                .collect();
            let (si, li) = (AtomicUsize::new(0), AtomicUsize::new(0));
            scaling::check(&format!("front family {case}"), 8, |n| {
                Type::forget_emptiness();
                let t = if n == 8 {
                    &small[si.fetch_add(1, Relaxed)]
                } else {
                    &large[li.fetch_add(1, Relaxed)]
                };
                assert_eq!(t.verdict(), want, "{case} at {n}");
            });
        }
    });
}

#[test]
fn r3_stress_scale_prebuilt() {
    for (case, want) in [
        ("bool", Verdict::Empty),
        ("boolfar", Verdict::Inhabited),
        ("chain", Verdict::Empty),
        ("chainfar", Verdict::Inhabited),
        ("clmanyheads", Verdict::Empty),
        ("clmanyheadsfar", Verdict::Inhabited),
        ("clstagger", Verdict::Empty),
        ("clstaggerfar", Verdict::Inhabited),
        ("cxstagger", Verdict::Empty),
        ("cxstaggerfar", Verdict::Inhabited),
        ("cxstaggerwide", Verdict::Empty),
        ("cxstaggerwidefar", Verdict::Inhabited),
        ("emitheads", Verdict::Empty),
        ("emitheadsfar", Verdict::Inhabited),
        ("far", Verdict::Inhabited),
        ("front", Verdict::Empty),
        ("groups", Verdict::Empty),
        ("groupsfar", Verdict::Inhabited),
        ("groupsholes", Verdict::Empty),
        ("groupsholesfar", Verdict::Inhabited),
        ("groupssingles", Verdict::Empty),
        ("groupssinglesfar", Verdict::Inhabited),
        ("manyheads", Verdict::Empty),
        ("manyheadsfar", Verdict::Inhabited),
        ("meet", Verdict::Empty),
        ("mlong", Verdict::Inhabited),
        ("mshort", Verdict::Empty),
        ("multi", Verdict::Empty),
        ("multifar", Verdict::Inhabited),
        ("one", Verdict::Empty),
        ("onetwo", Verdict::Inhabited),
        ("pair", Verdict::Empty),
        ("pairfar", Verdict::Inhabited),
        ("skip1", Verdict::Inhabited),
        ("skipmid", Verdict::Inhabited),
        ("split", Verdict::Empty),
        ("splitfar", Verdict::Inhabited),
        ("stagger", Verdict::Empty),
        ("staggerfar", Verdict::Inhabited),
        ("tuple", Verdict::Empty),
        ("tuplefar", Verdict::Inhabited),
        ("tupleflip", Verdict::Empty),
        ("tupleflipfar", Verdict::Inhabited),
    ] {
        big(move || {
            let inputs: Vec<_> = [8, 64]
                .into_iter()
                .map(|n| (n, rfx_case(case, n, &format!("_scale3_{case}_{n}"))))
                .collect();
            scaling::check(case, 8, |n| {
                Type::forget_emptiness();
                let t = &inputs.iter().find(|(k, _)| *k == n).unwrap().1;
                assert_eq!(t.verdict(), want, "{case} n={n}");
            });
        });
    }
}

#[test]
fn r4_diagnostic_routes_and_head_width() {
    big(|| {
        for case in [
            "front",
            "emitheads",
            "emitheadsfar",
            "cxstagger",
            "clcofront",
            "clstaggerholes",
        ] {
            let t = rfx_case(case, 8, &format!("route_{case}"));
            eprintln!("route {case} {:?}", t.sweep_verdict());
        }
        for width in [4, 8, 12, 16] {
            let all = Type::tuple(vec![Type::bool(); width]);
            let mut coords = vec![Type::bool(); width];
            coords[0] = Type::lit(&Value::Bool(true)).unwrap();
            let one = Type::tuple(coords);
            let (l, u) = rfx_family(2, Some(2), 2, &all, &one, false, &format!("width_{width}"));
            let t = &l - &u;
            Type::forget_emptiness();
            let mut got = None;
            let w = scaling::Meter::new().work(|| got = Some(t.verdict()));
            eprintln!(
                "headwidth {width} {:?} units {} bytes {}",
                got, w.units, w.bytes
            );
            assert_eq!(got, Some(Verdict::Inhabited));
        }
    });
}

#[test]
fn a_union_of_lists_by_the_place_of_a_one_from_the_front_is_decided_in_its_size_gemini() {
    big(|| {
        for (case, want) in [
            ("front", Verdict::Empty),
            ("far", Verdict::Inhabited),
            ("tuple", Verdict::Empty),
            ("tuplefar", Verdict::Inhabited),
            ("tupleflip", Verdict::Empty),
            ("tupleflipfar", Verdict::Inhabited),
            ("multi", Verdict::Empty),
            ("multifar", Verdict::Inhabited),
            ("groups", Verdict::Empty),
            ("groupsfar", Verdict::Inhabited),
            ("groupsholes", Verdict::Empty),
            ("groupsholesfar", Verdict::Inhabited),
            ("groupssingles", Verdict::Empty),
            ("groupssinglesfar", Verdict::Inhabited),
            ("cxstagger", Verdict::Empty),
            ("cxstaggerfar", Verdict::Inhabited),
            ("cxstaggerwide", Verdict::Empty),
            ("cxstaggerwidefar", Verdict::Inhabited),
            ("clmanyheads", Verdict::Empty),
            ("clmanyheadsfar", Verdict::Inhabited),
            ("clstagger", Verdict::Empty),
            ("clstaggerfar", Verdict::Inhabited),
            ("clstaggerholes", Verdict::Inhabited),
            ("clstaggerholesin", Verdict::Inhabited),
            ("clcofront", Verdict::Inhabited),
            ("emitheads", Verdict::Empty),
            ("emitheadsfar", Verdict::Inhabited),
            ("manyheads", Verdict::Empty),
            ("manyheadsfar", Verdict::Inhabited),
            ("stagger", Verdict::Empty),
            ("staggerfar", Verdict::Inhabited),
            ("chain", Verdict::Empty),
            ("chainfar", Verdict::Inhabited),
        ] {
            let (s_runs, l_runs) = scaling::Meter::new().runs();
            let small: Vec<Type> = (0..s_runs)
                .map(|i| rfx_case(case, 8, &format!("_fs_{case}_8_{i}")))
                .collect();
            let large: Vec<Type> = (0..l_runs)
                .map(|i| rfx_case(case, 64, &format!("_fs_{case}_64_{i}")))
                .collect();
            let (si, li) = (AtomicUsize::new(0), AtomicUsize::new(0));
            scaling::check(&format!("front family {case}"), 8, |n| {
                Type::forget_emptiness();
                let t = if n == 8 {
                    &small[si.fetch_add(1, Relaxed)]
                } else {
                    &large[li.fetch_add(1, Relaxed)]
                };
                assert_eq!(t.verdict(), want, "{case} at {n}");
            });
        }
    });
}

/// Every formula of one to four clauses of three literals over three variables (162 cases) is
/// decided as `r5_sat` decides it, by the verdict and by each mechanism that answers alone.
/// Other shapes: `r5_sat_run(vec![k, fewest clauses, most clauses, fewest literals, shard,
/// shards])`.
#[test]
fn r5_sat_check() {
    r5_sat_run(vec![3, 1, 4, 3, 0, 1]);
}

/// Round 6: every formula of three clauses over three variables (2,600), as in `r5_sat_check`.
/// Many have clauses of three literals, whose rows have three atoms in the escape solve, so a
/// solve that gave `Empty` from the first two atoms of such a row answers some of them wrongly.
#[test]
fn r6_every_three_clause_formula_on_three_variables_is_decided_correctly() {
    r5_sat_run(vec![3, 3, 3, 0, 0, 1]);
}

#[test]
fn r5_probe_cases_are_decided_in_their_size_1() {
    r5_cases_scale(&[
        ("front", Verdict::Empty),
        ("far", Verdict::Inhabited),
        ("skip1", Verdict::Inhabited),
        ("skipmid", Verdict::Inhabited),
        ("bool", Verdict::Empty),
        ("boolfar", Verdict::Inhabited),
        ("mshort", Verdict::Empty),
        ("mlong", Verdict::Inhabited),
        ("split", Verdict::Empty),
        ("splitfar", Verdict::Inhabited),
        ("meet", Verdict::Empty),
        ("pair", Verdict::Empty),
        ("pairfar", Verdict::Inhabited),
        ("tuple", Verdict::Empty),
        ("tuplefar", Verdict::Inhabited),
        ("tupleflip", Verdict::Empty),
        ("tupleflipfar", Verdict::Inhabited),
        ("multi", Verdict::Empty),
        ("multifar", Verdict::Inhabited),
    ]);
}

#[test]
fn r5_probe_cases_are_decided_in_their_size_2() {
    r5_cases_scale(&[
        ("groups", Verdict::Empty),
        ("groupsfar", Verdict::Inhabited),
        ("groupsholes", Verdict::Empty),
        ("groupsholesfar", Verdict::Inhabited),
        ("groupssingles", Verdict::Empty),
        ("groupssinglesfar", Verdict::Inhabited),
        ("cxstagger", Verdict::Empty),
        ("cxstaggerfar", Verdict::Inhabited),
        ("cxstaggerwide", Verdict::Empty),
        ("cxstaggerwidefar", Verdict::Inhabited),
        ("emitheads", Verdict::Empty),
        ("emitheadsfar", Verdict::Inhabited),
        ("manyheads", Verdict::Empty),
        ("manyheadsfar", Verdict::Inhabited),
        ("stagger", Verdict::Empty),
        ("staggerfar", Verdict::Inhabited),
        ("clmanyheads", Verdict::Empty),
        ("clmanyheadsfar", Verdict::Inhabited),
        ("clstagger", Verdict::Empty),
    ]);
}

#[test]
fn r5_probe_cases_are_decided_in_their_size_3() {
    r5_cases_scale(&[
        ("clstaggerfar", Verdict::Inhabited),
        ("clstaggerholes", Verdict::Inhabited),
        ("clcofront", Verdict::Inhabited),
        ("chain", Verdict::Empty),
        ("chainfar", Verdict::Inhabited),
        ("one", Verdict::Empty),
        ("onetwo", Verdict::Inhabited),
        ("u4cofrontones", Verdict::Empty),
        ("u4cofrontsame", Verdict::Inhabited),
        ("u4cofrontsameones", Verdict::Inhabited),
        ("u4cofrontsameblock", Verdict::Empty),
        ("u4cofrontshared", Verdict::Inhabited),
        ("u4holesin", Verdict::Inhabited),
        ("u4holesout", Verdict::Inhabited),
        ("u4boundaryin", Verdict::Inhabited),
        ("u4boundaryout", Verdict::Empty),
        ("u4width", Verdict::Inhabited),
    ]);
}

#[test]
fn r5_probe_cases_are_decided_in_their_size_4() {
    r5_cases_scale(&[
        ("r5greedy", Verdict::Inhabited),
        ("r5sat1lit", Verdict::Inhabited),
        ("r5sat2lit", Verdict::Inhabited),
        ("r5satk1n", Verdict::Inhabited),
        ("r5satnone", Verdict::Empty),
        ("r5slotsin", Verdict::Inhabited),
        ("r5slotsout", Verdict::Inhabited),
        ("r5remin", Verdict::Inhabited),
        ("r5remout", Verdict::Inhabited),
    ]);
}

#[test]
fn r6_escape_families_are_decided_in_their_size() {
    r5_cases_scale(&[
        ("r6three", Verdict::Inhabited),
        ("r6wide", Verdict::Inhabited),
        ("r6comb", Verdict::Inhabited),
    ]);
}

/// The two families that were quadratic before rows were retired after four cells (round 6:
/// `r6wide` n^1.82, `r6comb` n^1.62 at 1024), at sizes large enough for that to show.
#[test]
fn r6_wide_rows_are_retired_and_decided_in_their_size() {
    cases_scale_from(
        &[
            ("r6wide", Verdict::Inhabited),
            ("r6comb", Verdict::Inhabited),
        ],
        128,
    );
}

/// R7: the round-6 probe cases no other scaling test reads. `r6twowide` and `r6threeun` are
/// outside the chains' class and quadratic on the base search as well, so they are not here;
/// `r6two` and `r6twoun` are in
/// `r7_round6_probe_cases_r6two_and_r6twoun_are_decided_in_their_size`, deferred to plan row
/// SUB-r6two-bytes in wt/scratch/deferred-tests/SUB-r6two-bytes.rs.
#[test]
fn r7_round6_probe_cases_are_decided_in_their_size() {
    r5_cases_scale(&[
        ("r6parity", Verdict::Inhabited),
        ("r6repeat3", Verdict::Inhabited),
        ("r6distinct2", Verdict::Inhabited),
        ("r6distinct3", Verdict::Inhabited),
    ]);
}

#[test]
fn r7_congruence_scales() {
    cases_scale_from(
        &[
            ("r6parity", Verdict::Inhabited),
            ("r7congruencein", Verdict::Inhabited),
            ("r7congruenceout", Verdict::Inhabited),
            ("r7bmmout", Verdict::Inhabited),
        ],
        128,
    );
}

#[test]
fn r7_peer_escape_families_scale() {
    cases_scale_from(
        &[
            ("r6repeat3", Verdict::Inhabited),
            ("r6distinct2", Verdict::Inhabited),
            ("r6distinct3", Verdict::Inhabited),
        ],
        128,
    );
}

/// X38: the suffix-height filter and the reachable-place lower bound must avoid
/// impossible alignments. The committed global-gcd enumerator fails these bounds.
#[test]
fn r8_escape_alignment_reads_scale_with_the_input() {
    big(|| {
        for name in ["r6parity", "r7congruenceout", "r7aperiodic", "r7bmmout"] {
            for n in [128, 1024] {
                Type::forget_emptiness();
                let t = rfx_case(name, n, &format!("_r8reads{name}{n}"));
                let counts = t.escape_cell_counts();
                eprintln!("r8 reads {name} {n} {counts:?}");
                assert!(counts.1 <= 4 * n, "{name} {n}: {counts:?}");
            }
        }
    });
}

#[test]
fn r8_escape_and_width_instruction_scaling() {
    cases_scale_from(
        &[
            ("r7congruenceout", Verdict::Inhabited),
            ("r7aperiodic", Verdict::Inhabited),
        ],
        32,
    );
    big(|| {
        // n counts the quadratic head representation. Width floor(sqrt(n))
        // gives inputs of about n and 8n, with all construction outside timing.
        let inputs = scaling::inputs(256, |n| {
            rfx_case(
                "r5varywidth",
                (n as f64).sqrt() as usize,
                &format!("_r8width{n}"),
            )
        });
        scaling::check("r5varywidth by head representation size", 256, |n| {
            Type::forget_emptiness();
            assert_eq!(inputs[&n].verdict(), Verdict::Inhabited);
        });
    });
}

#[test]
fn r8_residue_boundary_scales() {
    cases_scale_from(
        &[
            ("r7aperiodic", Verdict::Inhabited),
            ("r8residues", Verdict::Inhabited),
            ("r8residuesout", Verdict::Inhabited),
        ],
        // 64 and 512: `r7aperiodic` is Empty at 128 (its closed form).
        64,
    );
}

/// A list type in a tuple or record field gets the verdict of the list alone, at near the list's
/// work (R8, Q5). The prefix chains and the escape solve ran on the query's own types only, so a
/// list in a field was left to the search, which refused `chain`, `r5remin` and `r6twoun` there,
/// at 12 to 530 times the work of the list alone.
#[test]
fn r8_a_list_in_a_field_is_decided_as_the_list_alone() {
    big(|| {
        let n = 64;
        let tag = format!("_r8field{n}");
        for case in ["chain", "r5remin", "r6twoun"] {
            for wrap in ["tup:", "rec:"] {
                Type::forget_emptiness();
                let bare = rfx_case(case, n, &tag);
                let mut v = None;
                let b = scaling::Meter::new().work(|| v = Some(bare.verdict()));
                Type::forget_emptiness();
                let t = rfx_case(&format!("{wrap}{case}"), n, &tag);
                let mut w = None;
                let f = scaling::Meter::new().work(|| w = Some(t.verdict()));
                assert_eq!(
                    w, v,
                    "{wrap}{case} at {n}: the field's verdict is the list's"
                );
                assert!(
                    f.units <= 2 * b.units,
                    "{wrap}{case} at {n}: {} units in a field, {} alone",
                    f.units,
                    b.units
                );
            }
        }
    });
}

/// A list of the front sweep's class in a tuple or record field gets the verdict of the list
/// alone at near the list's work (R9, X41). The front sweep ran on the query type alone, so the
/// search built the field's value itself: `rec:clstaggerholesout` cost 547 times the list alone
/// at 256, `tup:u4cofrontshared` 360 times, `tup:boundaryinside` 129 times. Sizes n and 8n, so a
/// cost that grows faster in a field than alone fails at the larger one.
#[test]
fn r9_a_front_sweep_list_in_a_field_is_decided_as_the_list_alone() {
    big(|| {
        for n in [16, 128] {
            let tag = format!("_r9field{n}");
            for case in [
                "clstaggerholesout",
                "u4holesout",
                "u4cofrontshared",
                "boundaryinside",
                "clcofrontsame",
            ] {
                for wrap in ["tup:", "rec:"] {
                    Type::forget_emptiness();
                    let bare = rfx_case(case, n, &tag);
                    let mut v = None;
                    let b = scaling::Meter::new().work(|| v = Some(bare.verdict()));
                    Type::forget_emptiness();
                    let t = rfx_case(&format!("{wrap}{case}"), n, &tag);
                    let mut w = None;
                    let f = scaling::Meter::new().work(|| w = Some(t.verdict()));
                    assert_eq!(
                        w, v,
                        "{wrap}{case} at {n}: the field's verdict is the list's"
                    );
                    assert!(
                        f.units <= 2 * b.units,
                        "{wrap}{case} at {n}: {} units in a field, {} alone",
                        f.units,
                        b.units
                    );
                }
            }
        }
    });
}

/// A list in a tagged atom's payload, `#wrap((l,))`, alone or in a tuple or record field, gets
/// the verdict of the list alone at near the list's work (R9, X42). The atom was taken for a
/// list outside the prefix chains, so the list in its payload was left to the general search:
/// `#wrap((l,))` with `l` of `r5remout` at 32 was Refused(Fork) at 34 times the list's work.
#[test]
fn r9_a_list_in_an_atom_payload_is_decided_as_the_list_alone() {
    big(|| {
        for n in [16, 128] {
            let tag = format!("_r9atom{n}");
            for case in [
                "r5remout",
                "chain",
                "r6twoun",
                "clstagger",
                "clstaggerholesout",
            ] {
                for wrap in ["atom:", "tup:atom:", "rec:atom:", "atom:tup:"] {
                    Type::forget_emptiness();
                    let bare = rfx_case(case, n, &tag);
                    let mut v = None;
                    let b = scaling::Meter::new().work(|| v = Some(bare.verdict()));
                    Type::forget_emptiness();
                    let t = rfx_case(&format!("{wrap}{case}"), n, &tag);
                    let mut w = None;
                    let f = scaling::Meter::new().work(|| w = Some(t.verdict()));
                    assert_eq!(
                        w, v,
                        "{wrap}{case} at {n}: the payload's verdict is the list's"
                    );
                    assert!(
                        f.units <= 2 * b.units,
                        "{wrap}{case} at {n}: {} units in a payload, {} alone",
                        f.units,
                        b.units
                    );
                }
            }
        }
    });
}

#[test]
fn r8_stage_boundary_scale() {
    cases_scale_from(
        &[
            ("r8stagein", Verdict::Inhabited),
            ("r8stageout", Verdict::Inhabited),
        ],
        128,
    );
}

#[test]
fn r8_varywidth_scales_within_input_size() {
    // Watch item `r5varywidth`: input has Theta(w^2) nodes (`w` boolean columns x `w` clauses),
    // so `w` to `4w` increases input size `N = w^2` by `16x` (`O(N log N)` bound <= `16 * 3 = 48x`).
    big(|| {
        Type::forget_emptiness();
        let small = r5_varying_width(16);
        let large = r5_varying_width(64);
        let mut m = scaling::Meter::new();
        let mut v1 = None;
        let mut v2 = None;
        let w1 = m.work(|| {
            Type::forget_emptiness();
            v1 = Some(small.verdict());
        });
        let w2 = m.work(|| {
            Type::forget_emptiness();
            v2 = Some(large.verdict());
        });
        assert_eq!(v1, Some(Verdict::Inhabited));
        assert_eq!(v2, Some(Verdict::Inhabited));
        assert!(
            w2.units <= w1.units.saturating_mul(48),
            "r5varywidth w=16 ({}) to w=64 ({}) exceeded O(w^2 log w) bound",
            w1.units,
            w2.units
        );
    });
}

#[test]
fn r9_wrapped_witness_cost_scales() {
    big(|| {
        for case in [
            "clstaggerholesout",
            "u4holesout",
            "u4cofrontshared",
            "r5remout",
        ] {
            for wrap in [
                "tup", "rec", "atom", "atom2", "nested", "option", "map", "listhead",
            ] {
                let small = rfx_case(&format!("{wrap}:{case}"), 32, "_r9scale_small");
                let large = rfx_case(&format!("{wrap}:{case}"), 256, "_r9scale_large");
                scaling::check("a checked list witness inside a product", 32, |n| {
                    Type::forget_emptiness();
                    let t = if n == 32 { &small } else { &large };
                    assert_eq!(t.verdict(), Verdict::Inhabited);
                });
            }
        }
    });
}

#[test]
fn r9_active_groups_have_one_entry_across_simultaneous_reentry() {
    big(|| {
        let small = r9_swapping_groups(512, false, "_r9swap_small");
        let large = r9_swapping_groups(4096, false, "_r9swap_large");
        scaling::check(
            "two positive chains re-enter each other's exhausted groups",
            512,
            |n| {
                Type::forget_emptiness();
                assert_eq!(
                    (if n == 512 { &small } else { &large }).chain_verdict(),
                    Some(Verdict::Inhabited)
                );
            },
        );
        // The words held and not held at n 1 to 6 are checked in
        // `chains_that_reenter_each_others_groups_are_inhabited` of refusals.rs
        // (TEST-bench-move-l0123, author P169).
    });
}

/// The escape's cell discovery stays within n log n from 1024 to 8192 on the families where the
/// sweep it replaced grew faster: `r9cosets` (place and head types both of period 7, every cell
/// empty by alignment; the sweep took 595.9M and 33,746M instructions at 8192 and 65,536, 57x for
/// 8x), and the Boolean-product chains `r9bmmlate` (11.9x) and `r10alternating` (10.7x, above the
/// 9.8x of n log n). The windows of block summaries and residue pair listing take 85.1M and 760.2M
/// on `r9cosets` (8.9x), 8.1x and 8.3x on the other two.
#[test]
fn escape_cells_scale_on_the_coset_and_product_chains() {
    big(|| {
        let base = 1024;
        for case in ["r9cosets", "r9bmmlate", "r10alternating"] {
            let (s_runs, l_runs) = scaling::Meter::new().runs();
            let small: Vec<Type> = (0..s_runs)
                .map(|i| rfx_case(case, base, &format!("_esc_{case}_{base}_{i}")))
                .collect();
            let large: Vec<Type> = (0..l_runs)
                .map(|i| rfx_case(case, 8 * base, &format!("_esc_{case}_{}_{i}", 8 * base)))
                .collect();
            let (si, li) = (AtomicUsize::new(0), AtomicUsize::new(0));
            scaling::check(&format!("escape cells of {case}"), base, |n| {
                let t = if n == base {
                    &small[si.fetch_add(1, Relaxed)]
                } else {
                    &large[li.fetch_add(1, Relaxed)]
                };
                std::hint::black_box(t.escape_cell_counts());
            });
        }
    });
}

/// R9-C7 (Codex R9): `decidable` walked a type shared by two components once per path, 2^d
/// visits at depth d. It visits each distinct type once, and still finds a bounded morphism
/// under tuples, atom payloads and recursive groups.
#[test]
fn r9_decidable_shared_dag_scales_and_rejects_bounded_leaves() {
    big(|| {
        let small = r9_shared_tuple_type(16, Type::bool());
        let large = r9_shared_tuple_type(128, Type::bool());
        scaling::check("decidability of a shared tuple DAG", 16, |n| {
            assert!((if n == 16 { &small } else { &large }).decidable());
        });
        // Bounded leaves, the cyclic list and the atom payload are checked in
        // `shared_dags_are_decidable_unless_a_leaf_is_bounded` of refusals.rs
        // (TEST-bench-move-l0123, author P169).
    });
}

#[test]
fn r10_a_boolean_list_tail_scales() {
    big(|| {
        for case in ["clstaggerholesout", "r5remout", "chain"] {
            let small = rfx_case(&format!("listtail:{case}"), 32, "_r10tail_small");
            let large = rfx_case(&format!("listtail:{case}"), 256, "_r10tail_large");
            let want = rfx_case(case, 32, "_r10tail_want").verdict();
            scaling::check("a Boolean list type as a list's tail", 32, |n| {
                Type::forget_emptiness();
                let t = if n == 32 { &small } else { &large };
                assert_eq!(t.verdict(), want);
            });
        }
    });
}

/// The `Value::Big` gap (round 10): one literal outside the 64-bit range in a head no longer
/// sends the list to the general search; the escape decides it, at the bare case's cost.
#[test]
fn r10_a_wide_head_literal_is_decided_by_the_escape() {
    big(|| {
        // The witness and the escape at n 16 and 64 are checked in
        // `a_wide_head_literal_is_decided_by_the_escape_at_small_sizes` of refusals.rs
        // (TEST-bench-move-l0123, author P169).
        let small = r10_big_congruence(32, "_r10big_small");
        let large = r10_big_congruence(256, "_r10big_large");
        scaling::check("a wide head literal", 32, |n| {
            Type::forget_emptiness();
            let t = if n == 32 { &small } else { &large };
            assert_eq!(t.verdict(), Verdict::Inhabited);
        });
    });
}

#[test]
fn r10_boolean_tail_is_decided_and_scales() {
    big(|| {
        for case in ["chain", "r5remout"] {
            let want = if case == "chain" {
                Verdict::Empty
            } else {
                Verdict::Inhabited
            };
            let a = rfx_case(&format!("listtail:{case}"), 32, "_r10tail32");
            let b = rfx_case(&format!("listtail:{case}"), 256, "_r10tail256");
            scaling::check("a written Boolean list tail", 32, |n| {
                Type::forget_emptiness();
                assert_eq!((if n == 32 { &a } else { &b }).verdict(), want);
            });
        }
    });
}

#[test]
fn r10_big_integer_escape_is_a_renaming_and_scales() {
    big(|| {
        let a = r10_big_congruence_cx(32, true, "_r10big32");
        let b = r10_big_congruence_cx(256, true, "_r10big256");
        scaling::check("a wide integer in escape heads", 32, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 32 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
        for n in [16, 64, 256, 1024] {
            let small = r10_big_congruence_cx(n, false, "_r10bigsmall");
            let wide = r10_big_congruence_cx(n, true, "_r10bigwide");
            assert_eq!(wide.escape_cell_counts(), small.escape_cell_counts());
            assert_eq!(wide.verdict(), small.verdict());
        }
    });
}

#[test]
fn r10_shared_product_list_is_swept_and_checked_once() {
    big(|| {
        let a = rfx_case("r10sharedfront", 16, "_r10shared16");
        let b = rfx_case("r10sharedfront", 128, "_r10shared128");
        scaling::check("one list type shared by every tuple component", 16, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 16 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
        // The empty case, a tuple of one empty list type 16 times, is in
        // `a_list_type_shared_by_tuple_components_is_checked_once` of refusals.rs
        // (TEST-bench-move-l0123, author P169).
    });
}

#[test]
fn r10_shared_irrelevant_holes_are_projected_once_and_scale() {
    big(|| {
        let a = r10_padded_congruence(32, "_r10pad32");
        let b = r10_padded_congruence(256, "_r10pad256");
        scaling::check("irrelevant shared holes in integer heads", 32, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 32 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
    });
}

#[test]
fn r10_shared_payload_probe() {
    let sizes = std::env::var("RFX_N").unwrap_or("16,64,256,1024".into());
    big(move || {
        for n in sizes.split(',').map(|s| s.parse::<usize>().unwrap()) {
            Type::forget_emptiness();
            let tag = format!("_shared{n}");
            let t = r10_shared_payloads(n, &tag);
            let mut v = None;
            let mut meter = scaling::Meter::new();
            let w = meter.work(|| v = Some(t.verdict()));
            assert_eq!(v, Some(Verdict::Inhabited));
            assert!(t.contains(&Value::atom_with(
                format!("r10tag0{tag}"),
                vec![Value::Int(0), Value::Int(0)]
            )));
            assert!(!t.contains(&Value::atom_with(
                format!("r10tag0{tag}"),
                vec![Value::Int(0), Value::Int(1)]
            )));
            eprintln!("R10PAYLOAD n {n} {v:?} units {} bytes {}", w.units, w.bytes);
        }
    });
}

#[test]
fn r10_shared_payload_rows_must_scale() {
    big(|| {
        let a = r10_shared_payloads(32, "_payload32");
        let b = r10_shared_payloads(256, "_payload256");
        scaling::check("tags sharing one tuple payload diagram", 32, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 32 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
    });
}

#[test]
fn r11_group_reads_skip_bare_atom_names_and_scale() {
    big(|| {
        let a = r11_failure_prefixes(128);
        let b = r11_failure_prefixes(1024);
        scaling::check(
            "group dependencies of shared failure-atom prefixes",
            128,
            |n| {
                Type::forget_emptiness();
                assert_eq!(
                    (if n == 128 { &a } else { &b }).verdict(),
                    Verdict::Inhabited
                );
            },
        );
    });
}

#[test]
fn r11_failure_prefix_probe() {
    big(|| {
        for n in [16, 64, 256, 1024] {
            let t = r11_failure_prefixes(n);
            Type::forget_emptiness();
            let mut m = scaling::Meter::new();
            let w = m.work(|| assert_eq!(t.verdict(), Verdict::Inhabited));
            eprintln!("R11FAIL n {n} units {} bytes {}", w.units, w.bytes);
        }
    });
}

#[test]
fn r11_tagged_payload_probe() {
    big(|| {
        for n in [16, 64, 256, 1024] {
            let t = r11_tagged_payloads(n);
            Type::forget_emptiness();
            let mut m = scaling::Meter::new();
            let w = m.work(|| assert_eq!(t.verdict(), Verdict::Inhabited));
            eprintln!("R11TAG n {n} units {} bytes {}", w.units, w.bytes);
        }
    });
}

#[test]
fn r11_boolean_tail_behind_literal_prefix_scales() {
    big(|| {
        let make = |n| {
            let mut t = rfx_case("r5remout", 8, "_r11deepscale");
            for _ in 0..n {
                t = cons_of(Type::int(), t);
            }
            t
        };
        let a = make(32);
        let b = make(256);
        scaling::check("Boolean list boundary behind a literal prefix", 32, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 32 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
    });
}

#[test]
fn r11_literal_prefix_probe() {
    big(|| {
        for n in [16, 64, 256, 1024] {
            let mut t = rfx_case("r5remout", 8, "_r11prefixprobe");
            for _ in 0..n {
                t = cons_of(Type::int(), t);
            }
            Type::forget_emptiness();
            let mut m = scaling::Meter::new();
            let w = m.work(|| assert_eq!(t.verdict(), Verdict::Inhabited));
            let mut word = vec![0; n];
            word.extend([5, 1, 1]);
            assert!(t.contains(&r6_colour_list(&word)));
            eprintln!("R11PREFIX n {n} units {} bytes {}", w.units, w.bytes);
        }
    });
}

#[test]
fn r11_payload_name_prefix_probe() {
    big(|| {
        for n in [16, 64, 256, 1024] {
            let t = r11_payload_name_prefixes(n);
            Type::forget_emptiness();
            let mut m = scaling::Meter::new();
            let w = m.work(|| assert_eq!(t.verdict(), Verdict::Inhabited));
            eprintln!("R11NAMES n {n} units {} bytes {}", w.units, w.bytes);
        }
    });
}

/// A ternary-density alignment family: one row class has only the final two
/// coordinates, two classes have every coordinate. Every product entry is 1.
#[test]
fn r11_ternary_alignment_is_inhabited() {
    r11_ternary_alignment(&[16, 64, 256, 1024]);
}

#[test]
fn r11_tuple_fields_within_list_items_scale() {
    big(|| {
        let a = rfx_case("listhead:pairfar", 32, "_r11pairitem32");
        let b = rfx_case("listhead:pairfar", 256, "_r11pairitem256");
        scaling::check("tuple fields within a list item", 32, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 32 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
    });
}

#[test]
fn r11_many_names_probe() {
    let sizes = std::env::var("RFX_N").unwrap_or("16,64,256,1024".into());
    big(move || {
        for n in sizes.split(',').map(|s| s.parse::<usize>().unwrap()) {
            Type::forget_emptiness();
            let t = r11_names_family(n, &format!("_n{n}"));
            let mut v = None;
            let mut meter = scaling::Meter::new();
            let w = meter.work(|| v = Some(t.verdict()));
            assert_eq!(v, Some(Verdict::Inhabited));
            eprintln!("R11NAMES n {n} {v:?} units {} bytes {}", w.units, w.bytes);
        }
    });
}

#[test]
fn r11_many_names_must_scale() {
    big(|| {
        let a = r11_names_family(32, "_s32");
        let b = r11_names_family(256, "_s256");
        scaling::check("types sharing many atom names", 32, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 32 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
    });
}

/// R11 probe for what the R10-C4 memo leaves: n tags sharing one payload diagram whose n rows
/// each hold a component with an atom name, which every tag still reads.
#[test]
fn r11_named_payload_probe() {
    let sizes = std::env::var("RFX_N").unwrap_or("16,64,256,1024".into());
    big(move || {
        for n in sizes.split(',').map(|s| s.parse::<usize>().unwrap()) {
            Type::forget_emptiness();
            let t = r11_named_payloads(n, &format!("_{n}"));
            let mut v = None;
            let mut meter = scaling::Meter::new();
            let w = meter.work(|| v = Some(t.verdict()));
            assert_eq!(v, Some(Verdict::Inhabited));
            eprintln!("R11NAMED n {n} {v:?} units {} bytes {}", w.units, w.bytes);
        }
    });
}

#[test]
fn a_tuple_with_an_empty_component_is_empty_in_either_order() {
    // The fixed cases of a fork beside an empty component, in either order, are in
    // `a_tuple_with_an_empty_component_is_empty_beside_a_fork` of refusals.rs, and small chains in
    // `a_few_distinct_forks_beside_an_empty_component_are_empty` (TEST-bench-move-l0123, author
    // P169). n forked components before the empty one: the second search sets each fork aside
    // once.
    big(|| {
        scaling::check("Empty, n forked components and an empty one", 8, |n| {
            Type::forget_emptiness();
            let mut parts: Vec<Type> = (0..n as i64).map(fork_empty_at).collect();
            parts.push(pair_meet_empty());
            let t = Type::tuple(parts);
            assert_eq!(t.verdict(), Verdict::Empty, "at {n}");
        });
    });
}

/// The second blame search must walk n distinct forked components before the
/// empty component. Both presentations and both public routes are measured;
/// constructing the groups and tuples is outside the counters.
#[test]
fn a_chain_of_forks_before_an_empty_component_scales() {
    let n = 8;
    let inputs = scaling::inputs(n, |k| {
        let mut parts: Vec<Type> = (0..k as i64).map(fork_empty_at).collect();
        parts.push(pair_meet_empty());
        let last = Type::tuple(parts.clone());
        parts.reverse();
        [last, Type::tuple(parts)]
    });
    scaling::check_order(
        "second blame search over distinct forked components",
        n,
        1,
        |k| {
            for t in &inputs[&k] {
                Type::forget_emptiness();
                assert_eq!(t.verdict(), Verdict::Empty);
                Type::forget_emptiness();
                assert!(t.is_empty());
            }
        },
    );
}

#[test]
fn a_chain_of_forks_nested_before_an_empty_component_is_empty_in_its_size() {
    // The search of a verdict ends at the first fork; the second search (`empty_past_forks`)
    // sets the fork in each of the n nested tuples aside once and reaches the empty component.
    big(|| {
        let inputs = scaling::inputs(8, forks_nested_before_empty);
        scaling::check_order(
            "Empty, n forks nested before an empty component",
            8,
            1,
            |n| {
                Type::forget_emptiness();
                assert_eq!(inputs[&n].verdict(), Verdict::Empty, "at {n}");
            },
        );
    });
}

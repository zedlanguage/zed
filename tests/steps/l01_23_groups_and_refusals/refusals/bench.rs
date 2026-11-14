//! The benchmarks of `refusals.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `refusals.rs`.
//!
//! Sizes (TEST-bench-move-l0123, author P169): each check runs its smaller size n in about 0.5 to
//! 1 s and 8n in about 8 s or less, and each `#[test]` ends within about 15 s. A test that made
//! many checks is split into one `#[test]` per check, named after the test it came from and the
//! case it checks. Where a check fails its limit at the sizes that rule asks for, the check stays
//! at its old size and its comment names the finding. Measurements quoted from before the resize
//! were taken at the old sizes.

use super::*;

/// One probe case of `rfx_case` at `n` and `8 * n`, checked as `cases_scale_from` of refusals.rs
/// checks its cases: a fresh copy of the type for each run, built before any run is timed, and
/// the verdict `want` at both sizes. `what` names the check in its `bench` line and `tag` keeps
/// the names of this test's types apart from those of the tests running beside it.
fn case_scales(what: &str, tag: &str, case: &str, n: usize, want: Verdict) {
    big(|| {
        let (s_runs, l_runs) = scaling::Meter::new().runs();
        let copies = |k: usize, runs: usize| -> Vec<Type> {
            (0..runs)
                .map(|i| rfx_case(case, k, &format!("_{tag}_{k}_{i}")))
                .collect()
        };
        let (small, large) = (copies(n, s_runs), copies(8 * n, l_runs));
        let (si, li) = (AtomicUsize::new(0), AtomicUsize::new(0));
        scaling::check(&format!("{what} {case}"), n, |k| {
            Type::forget_emptiness();
            let t = if k == n {
                &small[si.fetch_add(1, Relaxed)]
            } else {
                &large[li.fetch_add(1, Relaxed)]
            };
            assert_eq!(t.verdict(), want, "{case} at {k}");
        });
    });
}

/// One case checked as `cases_scale_from` of refusals.rs checks each of its cases.
fn probe_case_scales(case: &str, n: usize, want: Verdict) {
    cases_scale_from(&[(case, want)], n);
}

/// One `#[test]` per probe case: `name: case, verdict, old n -> new n, 1x ns at load;`. A list
/// headed `probe;` checks each case with `cases_scale_from` of refusals.rs, as the test it came
/// from did; a list headed by a label checks each with [`case_scales`] under that label. The doc
/// of each test gives its sizes and the 1x time measured at the new size (TEST-bench-move-l0123,
/// author P169).
macro_rules! case_benches {
    (@one $name:ident, $case:literal, $old:literal, $n:literal, $ns:literal, $load:literal,
        $body:expr) => {
        #[doc = concat!("`", $case, "` at n ", $n, " and 8n, resized from n ", $old,
            " (TEST-bench-move-l0123, author P169); 1x took ", $ns, " ns at load ", $load, ".")]
        #[test]
        fn $name() {
            $body;
        }
    };
    (probe; $($name:ident: $case:literal, $want:expr, $old:literal -> $n:literal,
        $ns:literal at $load:literal;)*) => {
        $(case_benches!(@one $name, $case, $old, $n, $ns, $load,
            probe_case_scales($case, $n, $want));)*
    };
    ($what:literal; $($name:ident: $case:literal, $want:expr, $old:literal -> $n:literal,
        $ns:literal at $load:literal;)*) => {
        $(case_benches!(@one $name, $case, $old, $n, $ns, $load,
            case_scales($what, stringify!($name), $case, $n, $want));)*
    };
}

#[test]
fn a_residues_refusal_is_reached_in_the_size_of_the_classes() {
    // Θ(n) groups of periods. Measured on c881d28c: 10.0M instructions at n = 4, 81.9M at 32.
    // Finding (TEST-bench-move-l0123, author P169): left at its old n 4, because the check fails
    // its limit at the sizes the resize asks for. The construction `erdos_cover_repeated` is
    // timed with the verdict, and it grows faster than n log n (71 ms at n 128, 710 ms at 512,
    // 3198 ms at 1024, one build each). Bench lines, load about 33: n 4 passes, 8.3 times
    // (16.9M and 140.1M instructions, 1x 9.2 ms); n 16 passes, 10.1 times (68.0M and 685.7M);
    // n 32 fails, 11.9 times (141.2M and 1682.5M instructions, 14.8M and 147.6M bytes); n 64
    // fails, 15.2 times (302.8M and 4598.6M instructions; bytes 11.9 times).
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
    // Resized from n 4 to n 384 (TEST-bench-move-l0123, author P169); 1x took 309928739 ns at
    // load 34.07.
    refusal_scales(
        "TupleSplit, by n box covers",
        384,
        Refusal::TupleSplit,
        |n, _| box_covers(n),
    );
}

#[test]
fn a_morphism_split_refusal_is_reached_in_the_size_of_the_union() {
    // Θ(n) morphism types. Measured on c881d28c: 0.42M instructions at n = 1, 4.9M at 32.
    // Resized from n 8 to n 16384 (TEST-bench-move-l0123, author P169); 1x took 395058297 ns at
    // load 34.07.
    refusal_scales(
        "MorphismSplit, by n results",
        16384,
        Refusal::MorphismSplit,
        |n, _| morphism_split_by(n),
    );
}

#[test]
fn a_no_witness_refusal_is_reached_in_the_size_of_the_keys() {
    // Θ(n) required keys. Measured on c881d28c: 87K instructions at n = 1, 302K at 32. Round 10
    // (the keys also hold a list type, X45): 2.21M at n = 8, 2.88M at 64.
    // Resized from n 8 to n 65536 (TEST-bench-move-l0123, author P169); 1x took 162033710 ns at
    // load 34.07. The verdict takes about the same work at every n (about 1.6M
    // instructions); the work that grows is building the type, which `refusal_scales` times.
    refusal_scales(
        "NoWitness, by n required keys",
        65536,
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
    // TEST-bench-move-l0123 (author P169), finding: at n 384 and 3072 the first runs took 1712.8M
    // and 20,570.9M instructions, 12.0 times (bytes 233.2M and 2092.1M, 9.0 times; 1x took
    // 445625650 ns at load 34.4), above the limit of 10.5, so the test stays at its old size n 8.
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
    // Resized from n 8 to n 1024 (TEST-bench-move-l0123, author P169); 1x took 316545620 ns at load
    // 34.40.
    refusal_scales(
        "Fork, by a difference of unions",
        1024,
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
    // Resized from n 8 to n 1024 (TEST-bench-move-l0123, author P169); 1x took 233029207 ns at load
    // 33.78.
    refusal_scales(
        "Fork, by a union of differences",
        1024,
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
    // Resized from n 8 to n 512 (TEST-bench-move-l0123, author P169); 1x took 214234900 ns at load
    // 34.07.
    refusal_scales(
        "Fork, by a pair type met with a union of differences",
        512,
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
    // Resized from n 8 to n 4096 (TEST-bench-move-l0123, author P169); 1x took 203209988 ns at load
    // 33.78.
    big(|| {
        scaling::check(
            "Empty, by a union of n pairs less pairs that hold them",
            4096,
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

/// Two recursive types on no cycle taken out of one tail are no fork: decided at each size, in
/// time linear in `n`. A list with no 1 at place n from the front is `Empty`, and with one 1 it
/// is `Inhabited`; until the resize both were checked in one test,
/// `a_list_by_one_place_from_the_front_is_decided_in_its_size` (TEST-bench-move-l0123, author
/// P169).
fn one_place_from_the_front_scales(two: bool, verdict: Verdict, n: usize) {
    big(move || {
        scaling::check("a 1 at place n from the front, or none", n, |n| {
            Type::forget_emptiness();
            let tag = format!("_of{n}{two}");
            let t = by_one_place_from_the_front(n, two, &tag);
            assert_eq!(t.verdict(), verdict, "at {n}");
        })
    });
}

#[test]
fn a_list_by_one_place_from_the_front_is_decided_in_its_size_empty() {
    // Resized from n 8 to n 8192 (TEST-bench-move-l0123, author P169); 1x took 403927590 ns at
    // load 34.40.
    one_place_from_the_front_scales(false, Verdict::Empty, 8192);
}

#[test]
fn a_list_by_one_place_from_the_front_is_decided_in_its_size_inhabited() {
    // Resized from n 8 to n 8192 (TEST-bench-move-l0123, author P169); 1x took 515870829 ns at
    // load 34.40.
    one_place_from_the_front_scales(true, Verdict::Inhabited, 8192);
}

#[test]
fn emptiness_of_lists_by_one_place_from_the_front_scales() {
    // The lists by one place from the front have no fork and are proved empty. Until 2026-11-13
    // this check followed the one above in a single test.
    // Resized from n 8 to n 8192 (TEST-bench-move-l0123, author P169); 1x took 180343714 ns
    // at load 20.15.
    big(|| {
        let tag = AtomicUsize::new(0);
        scaling::check("emptiness, a 1 at one place from the front", 8192, |n| {
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
    //
    // Finding (TEST-bench-move-l0123, author P169): left at its old n 8, because all three checks
    // fail their limit at the sizes the resize asks for (1x about 0.5 s would need n near 128).
    // The work per size grows faster than n log n from n 16 on. Bench lines, load about 33,
    // instructions at n and 8n: Fork without the skip at n 8, 16 and 32 passes, 6.8, 8.2 and
    // 10.0 times (43.8M and 296.0M; 77.1M and 633.8M; 146.5M and 1469.1M), and at n 64 fails,
    // 12.6 times (296.4M and 3734.8M; bytes 12.6 times). Fork with the skip: 7.1, 8.5 and 10.2
    // times at 8, 16 and 32, 12.7 times at 64 (292.9M and 3724.7M). `is_empty`: 7.3, 8.6 and 10.4
    // times at 8, 16 and 32, 13.1 times at 64 (269.6M and 3519.9M). A size probe of one verdict
    // took 281M instructions at n 64 and 3595M at 512, 12.8 times.
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

// The cases of `a_union_of_lists_by_the_place_of_a_one_from_the_front_is_decided_in_its_size`,
// one test each (TEST-bench-move-l0123, author P169). All 18 are also among the cases of the
// `_gemini` test below, which checks them with the same code.
case_benches! {
    "front family";
    front_family_front: "front", Verdict::Empty, 8 -> 4096, "212129611" at "33.49";
    front_family_far: "far", Verdict::Inhabited, 8 -> 4096, "214828522" at "33.41";
    front_family_tuple: "tuple", Verdict::Empty, 8 -> 4096, "158081821" at "31.37";
    front_family_tuplefar: "tuplefar", Verdict::Inhabited, 8 -> 4096, "181033883" at "31.37";
    front_family_tupleflip: "tupleflip", Verdict::Empty, 8 -> 4096, "134602674" at "31.28";
    front_family_tupleflipfar: "tupleflipfar", Verdict::Inhabited, 8 -> 4096, "233304960" at "31.28";
    front_family_multi: "multi", Verdict::Empty, 8 -> 2048, "58460611" at "31.64";
    front_family_multifar: "multifar", Verdict::Inhabited, 8 -> 2048, "72948532" at "31.48";
    front_family_groups: "groups", Verdict::Empty, 8 -> 2048, "131484535" at "32.07";
    front_family_groupsfar: "groupsfar", Verdict::Inhabited, 8 -> 2048, "141708007" at "31.92";
    front_family_groupsholes: "groupsholes", Verdict::Empty, 8 -> 2048, "147765486" at "31.92";
    front_family_groupsholesfar: "groupsholesfar", Verdict::Inhabited, 8 -> 2048, "116526314" at "31.73";
    front_family_manyheads: "manyheads", Verdict::Empty, 8 -> 2048, "236832654" at "31.73";
    front_family_manyheadsfar: "manyheadsfar", Verdict::Inhabited, 8 -> 2048, "184856000" at "31.73";
    front_family_stagger: "stagger", Verdict::Empty, 8 -> 4096, "164398114" at "31.48";
    front_family_staggerfar: "staggerfar", Verdict::Inhabited, 8 -> 4096, "238505662" at "31.48";
    front_family_chain: "chain", Verdict::Empty, 8 -> 4096, "224442212" at "33.49";
    front_family_chainfar: "chainfar", Verdict::Inhabited, 8 -> 4096, "251835085" at "33.49";
}

// The cases of `r3_stress_scale_prebuilt`, one test each (TEST-bench-move-l0123, author P169).
// Before the resize each size had one copy of the type, used by every run; each run now has its
// own copy, as `cases_scale_from` of refusals.rs gives.
case_benches! {
    "r3 stress case";
    r3_stress_bool: "bool", Verdict::Empty, 8 -> 4096, "82021296" at "30.39";
    r3_stress_boolfar: "boolfar", Verdict::Inhabited, 8 -> 4096, "105769891" at "30.39";
    r3_stress_chain: "chain", Verdict::Empty, 8 -> 4096, "143706607" at "30.39";
    r3_stress_chainfar: "chainfar", Verdict::Inhabited, 8 -> 4096, "162775782" at "30.39";
    r3_stress_clmanyheads: "clmanyheads", Verdict::Empty, 8 -> 2048, "83009579" at "30.12";
    r3_stress_clmanyheadsfar: "clmanyheadsfar", Verdict::Inhabited, 8 -> 2048, "93191107" at "30.12";
    r3_stress_clstagger: "clstagger", Verdict::Empty, 8 -> 2048, "98067400" at "30.12";
    r3_stress_clstaggerfar: "clstaggerfar", Verdict::Inhabited, 8 -> 2048, "115299053" at "30.12";
    r3_stress_cxstagger: "cxstagger", Verdict::Empty, 8 -> 2048, "67531588" at "29.82";
    r3_stress_cxstaggerfar: "cxstaggerfar", Verdict::Inhabited, 8 -> 2048, "71424539" at "29.82";
    r3_stress_cxstaggerwide: "cxstaggerwide", Verdict::Empty, 8 -> 2048, "63524564" at "29.82";
    r3_stress_cxstaggerwidefar: "cxstaggerwidefar", Verdict::Inhabited, 8 -> 2048, "63597176" at "29.82";
    r3_stress_emitheads: "emitheads", Verdict::Empty, 8 -> 4096, "156931955" at "29.82";
    r3_stress_emitheadsfar: "emitheadsfar", Verdict::Inhabited, 8 -> 4096, "173053662" at "29.82";
    r3_stress_far: "far", Verdict::Inhabited, 8 -> 4096, "111758270" at "29.54";
    r3_stress_front: "front", Verdict::Empty, 8 -> 4096, "241206214" at "29.54";
    r3_stress_groups: "groups", Verdict::Empty, 8 -> 2048, "206085644" at "29.36";
    r3_stress_groupsfar: "groupsfar", Verdict::Inhabited, 8 -> 2048, "204342343" at "29.36";
    r3_stress_groupsholes: "groupsholes", Verdict::Empty, 8 -> 2048, "179833790" at "29.36";
    r3_stress_groupsholesfar: "groupsholesfar", Verdict::Inhabited, 8 -> 2048, "194111624" at "29.83";
    r3_stress_groupssingles: "groupssingles", Verdict::Empty, 8 -> 2048, "188515083" at "29.83";
    r3_stress_groupssinglesfar: "groupssinglesfar", Verdict::Inhabited, 8 -> 2048, "172438107" at "29.83";
    r3_stress_manyheads: "manyheads", Verdict::Empty, 8 -> 2048, "247704656" at "29.86";
    r3_stress_manyheadsfar: "manyheadsfar", Verdict::Inhabited, 8 -> 1024, "66076641" at "20.34";
    r3_stress_meet: "meet", Verdict::Empty, 8 -> 4096, "188357060" at "29.78";
    r3_stress_mlong: "mlong", Verdict::Inhabited, 8 -> 4096, "271767988" at "29.78";
    r3_stress_mshort: "mshort", Verdict::Empty, 8 -> 4096, "96835262" at "29.94";
    r3_stress_multi: "multi", Verdict::Empty, 8 -> 2048, "93421662" at "30.14";
    r3_stress_multifar: "multifar", Verdict::Inhabited, 8 -> 2048, "86727796" at "30.14";
    r3_stress_one: "one", Verdict::Empty, 8 -> 4096, "173818949" at "30.14";
    r3_stress_onetwo: "onetwo", Verdict::Inhabited, 8 -> 4096, "177440724" at "30.14";
    r3_stress_pair: "pair", Verdict::Empty, 8 -> 2048, "84063634" at "30.49";
    r3_stress_pairfar: "pairfar", Verdict::Inhabited, 8 -> 2048, "155006230" at "30.49";
    r3_stress_skip1: "skip1", Verdict::Inhabited, 8 -> 4096, "142387955" at "30.49";
    r3_stress_skipmid: "skipmid", Verdict::Inhabited, 8 -> 4096, "152783509" at "30.71";
    r3_stress_split: "split", Verdict::Empty, 8 -> 4096, "128647375" at "30.71";
    r3_stress_splitfar: "splitfar", Verdict::Inhabited, 8 -> 4096, "132871833" at "30.71";
    r3_stress_stagger: "stagger", Verdict::Empty, 8 -> 4096, "117015713" at "30.65";
    r3_stress_staggerfar: "staggerfar", Verdict::Inhabited, 8 -> 4096, "248475494" at "30.65";
    r3_stress_tuple: "tuple", Verdict::Empty, 8 -> 4096, "193362416" at "30.46";
    r3_stress_tuplefar: "tuplefar", Verdict::Inhabited, 8 -> 4096, "203507723" at "30.46";
    r3_stress_tupleflip: "tupleflip", Verdict::Empty, 8 -> 4096, "78607476" at "30.80";
    r3_stress_tupleflipfar: "tupleflipfar", Verdict::Inhabited, 8 -> 4096, "103389425" at "30.80";
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

// The cases of
// `a_union_of_lists_by_the_place_of_a_one_from_the_front_is_decided_in_its_size_gemini`, one test
// each (TEST-bench-move-l0123, author P169).
case_benches! {
    "front family";
    front_family_gemini_front: "front", Verdict::Empty, 8 -> 4096, "72672675" at "33.45";
    front_family_gemini_far: "far", Verdict::Inhabited, 8 -> 4096, "96118620" at "33.45";
    front_family_gemini_tuple: "tuple", Verdict::Empty, 8 -> 4096, "108592593" at "32.22";
    front_family_gemini_tuplefar: "tuplefar", Verdict::Inhabited, 8 -> 4096, "132733883" at "32.22";
    front_family_gemini_tupleflip: "tupleflip", Verdict::Empty, 8 -> 4096, "127067824" at "32.07";
    front_family_gemini_tupleflipfar: "tupleflipfar", Verdict::Inhabited, 8 -> 4096, "134166656" at "32.07";
    front_family_gemini_multi: "multi", Verdict::Empty, 8 -> 2048, "59412353" at "32.59";
    front_family_gemini_multifar: "multifar", Verdict::Inhabited, 8 -> 2048, "61383708" at "32.44";
    front_family_gemini_groups: "groups", Verdict::Empty, 8 -> 2048, "72427659" at "33.08";
    front_family_gemini_groupsfar: "groupsfar", Verdict::Inhabited, 8 -> 2048, "113377672" at "33.08";
    front_family_gemini_groupsholes: "groupsholes", Verdict::Empty, 8 -> 2048, "89606381" at "33.08";
    front_family_gemini_groupsholesfar: "groupsholesfar", Verdict::Inhabited, 8 -> 2048, "113262629" at "33.08";
    front_family_gemini_groupssingles: "groupssingles", Verdict::Empty, 8 -> 2048, "183505149" at "32.76";
    front_family_gemini_groupssinglesfar: "groupssinglesfar", Verdict::Inhabited, 8 -> 2048, "138015614" at "32.76";
    front_family_gemini_cxstagger: "cxstagger", Verdict::Empty, 8 -> 2048, "121471907" at "33.51";
    front_family_gemini_cxstaggerfar: "cxstaggerfar", Verdict::Inhabited, 8 -> 2048, "99174598" at "33.63";
    front_family_gemini_cxstaggerwide: "cxstaggerwide", Verdict::Empty, 8 -> 2048, "78409976" at "33.63";
    front_family_gemini_cxstaggerwidefar: "cxstaggerwidefar", Verdict::Inhabited, 8 -> 2048, "84629798" at "33.63";
    front_family_gemini_clmanyheads: "clmanyheads", Verdict::Empty, 8 -> 2048, "161998550" at "33.88";
    front_family_gemini_clmanyheadsfar: "clmanyheadsfar", Verdict::Inhabited, 8 -> 2048, "175846635" at "33.88";
    front_family_gemini_clstagger: "clstagger", Verdict::Empty, 8 -> 2048, "114296573" at "33.74";
    front_family_gemini_clstaggerfar: "clstaggerfar", Verdict::Inhabited, 8 -> 2048, "129152931" at "33.74";
    front_family_gemini_clstaggerholes: "clstaggerholes", Verdict::Inhabited, 8 -> 2048, "164070677" at "33.74";
    front_family_gemini_clstaggerholesin: "clstaggerholesin", Verdict::Inhabited, 8 -> 2048, "283970297" at "33.74";
    front_family_gemini_clcofront: "clcofront", Verdict::Inhabited, 8 -> 4096, "184155014" at "33.76";
    front_family_gemini_emitheads: "emitheads", Verdict::Empty, 8 -> 4096, "172318174" at "33.45";
    front_family_gemini_emitheadsfar: "emitheadsfar", Verdict::Inhabited, 8 -> 4096, "163336720" at "33.45";
    front_family_gemini_manyheads: "manyheads", Verdict::Empty, 8 -> 2048, "211836434" at "32.76";
    front_family_gemini_manyheadsfar: "manyheadsfar", Verdict::Inhabited, 8 -> 2048, "248136131" at "32.59";
    front_family_gemini_stagger: "stagger", Verdict::Empty, 8 -> 4096, "199577056" at "32.44";
    front_family_gemini_staggerfar: "staggerfar", Verdict::Inhabited, 8 -> 4096, "161072578" at "32.44";
    front_family_gemini_chain: "chain", Verdict::Empty, 8 -> 4096, "360034550" at "33.49";
    front_family_gemini_chainfar: "chainfar", Verdict::Inhabited, 8 -> 4096, "334192401" at "33.76";
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

// The cases of `r5_probe_cases_are_decided_in_their_size_1` to `_4`, one test each
// (TEST-bench-move-l0123, author P169).
case_benches! {
    probe;
    r5_probe_front: "front", Verdict::Empty, 8 -> 4096, "103586530" at "30.23";
    r5_probe_far: "far", Verdict::Inhabited, 8 -> 4096, "102222728" at "30.23";
    r5_probe_skip1: "skip1", Verdict::Inhabited, 8 -> 4096, "142185821" at "29.68";
    r5_probe_skipmid: "skipmid", Verdict::Inhabited, 8 -> 4096, "108224908" at "29.68";
    r5_probe_bool: "bool", Verdict::Empty, 8 -> 4096, "127340814" at "30.80";
    r5_probe_boolfar: "boolfar", Verdict::Inhabited, 8 -> 4096, "160108909" at "30.80";
    r5_probe_mshort: "mshort", Verdict::Empty, 8 -> 4096, "127861476" at "29.64";
    r5_probe_mlong: "mlong", Verdict::Inhabited, 8 -> 4096, "174526026" at "29.64";
    r5_probe_split: "split", Verdict::Empty, 8 -> 4096, "122950462" at "29.68";
    r5_probe_splitfar: "splitfar", Verdict::Inhabited, 8 -> 4096, "166779756" at "29.61";
    r5_probe_meet: "meet", Verdict::Empty, 8 -> 4096, "123732470" at "29.73";
    r5_probe_pair: "pair", Verdict::Empty, 8 -> 2048, "58507677" at "29.80";
    r5_probe_pairfar: "pairfar", Verdict::Inhabited, 8 -> 2048, "77473170" at "29.80";
    r5_probe_tuple: "tuple", Verdict::Empty, 8 -> 4096, "159831013" at "29.53";
    r5_probe_tuplefar: "tuplefar", Verdict::Inhabited, 8 -> 4096, "180832833" at "29.53";
    r5_probe_tupleflip: "tupleflip", Verdict::Empty, 8 -> 4096, "144193328" at "29.55";
    r5_probe_tupleflipfar: "tupleflipfar", Verdict::Inhabited, 8 -> 4096, "178728384" at "29.55";
    r5_probe_multi: "multi", Verdict::Empty, 8 -> 2048, "63188686" at "29.64";
    r5_probe_multifar: "multifar", Verdict::Inhabited, 8 -> 2048, "103158769" at "29.64";
    r5_probe_groups: "groups", Verdict::Empty, 8 -> 2048, "85485826" at "30.08";
    r5_probe_groupsfar: "groupsfar", Verdict::Inhabited, 8 -> 2048, "90484713" at "30.08";
    r5_probe_groupsholes: "groupsholes", Verdict::Empty, 8 -> 2048, "93073674" at "30.08";
    r5_probe_groupsholesfar: "groupsholesfar", Verdict::Inhabited, 8 -> 2048, "110276135" at "29.95";
    r5_probe_groupssingles: "groupssingles", Verdict::Empty, 8 -> 2048, "110700936" at "29.95";
    r5_probe_groupssinglesfar: "groupssinglesfar", Verdict::Inhabited, 8 -> 2048, "115185100" at "29.95";
    r5_probe_cxstagger: "cxstagger", Verdict::Empty, 8 -> 2048, "105842572" at "30.52";
    r5_probe_cxstaggerfar: "cxstaggerfar", Verdict::Inhabited, 8 -> 2048, "93532765" at "30.42";
    r5_probe_cxstaggerwide: "cxstaggerwide", Verdict::Empty, 8 -> 2048, "60760749" at "30.42";
    r5_probe_cxstaggerwidefar: "cxstaggerwidefar", Verdict::Inhabited, 8 -> 2048, "72548074" at "30.42";
    r5_probe_emitheads: "emitheads", Verdict::Empty, 8 -> 4096, "259123213" at "30.23";
    r5_probe_emitheadsfar: "emitheadsfar", Verdict::Inhabited, 8 -> 4096, "164217376" at "30.23";
    r5_probe_manyheads: "manyheads", Verdict::Empty, 8 -> 2048, "223337767" at "29.73";
    r5_probe_manyheadsfar: "manyheadsfar", Verdict::Inhabited, 8 -> 2048, "228706462" at "29.73";
    r5_probe_stagger: "stagger", Verdict::Empty, 8 -> 4096, "209819690" at "29.61";
    r5_probe_staggerfar: "staggerfar", Verdict::Inhabited, 8 -> 4096, "181482949" at "29.61";
    r5_probe_clmanyheads: "clmanyheads", Verdict::Empty, 8 -> 2048, "165257570" at "30.35";
    r5_probe_clmanyheadsfar: "clmanyheadsfar", Verdict::Inhabited, 8 -> 2048, "197543554" at "30.46";
    r5_probe_clstagger: "clstagger", Verdict::Empty, 8 -> 2048, "187603562" at "30.46";
    r5_probe_clstaggerfar: "clstaggerfar", Verdict::Inhabited, 8 -> 2048, "208172982" at "30.46";
    r5_probe_clstaggerholes: "clstaggerholes", Verdict::Inhabited, 8 -> 2048, "210081897" at "30.52";
    r5_probe_clcofront: "clcofront", Verdict::Inhabited, 8 -> 4096, "263090145" at "30.47";
    r5_probe_chain: "chain", Verdict::Empty, 8 -> 4096, "151294504" at "30.47";
    r5_probe_chainfar: "chainfar", Verdict::Inhabited, 8 -> 4096, "295402029" at "30.47";
    r5_probe_one: "one", Verdict::Empty, 8 -> 4096, "147017754" at "29.80";
    r5_probe_onetwo: "onetwo", Verdict::Inhabited, 8 -> 4096, "145015937" at "29.80";
    r5_probe_u4cofrontones: "u4cofrontones", Verdict::Empty, 8 -> 2048, "195014934" at "29.67";
    r5_probe_u4cofrontsame: "u4cofrontsame", Verdict::Inhabited, 8 -> 4096, "197765939" at "29.67";
    r5_probe_u4cofrontsameones: "u4cofrontsameones", Verdict::Inhabited, 8 -> 4096, "189381143" at "29.66";
    r5_probe_u4cofrontsameblock: "u4cofrontsameblock", Verdict::Empty, 8 -> 4096, "189560928" at "29.67";
    r5_probe_u4cofrontshared: "u4cofrontshared", Verdict::Inhabited, 8 -> 4096, "172915659" at "29.66";
    r5_probe_u4holesin: "u4holesin", Verdict::Inhabited, 8 -> 2048, "299711750" at "29.58";
    r5_probe_u4holesout: "u4holesout", Verdict::Inhabited, 8 -> 2048, "167934852" at "29.58";
    r5_probe_u4boundaryin: "u4boundaryin", Verdict::Inhabited, 8 -> 4096, "166185321" at "29.48";
    r5_probe_u4boundaryout: "u4boundaryout", Verdict::Empty, 8 -> 4096, "158874441" at "29.48";
    r5_probe_u4width: "u4width", Verdict::Inhabited, 8 -> 65536, "322822850" at "29.45";
    // `r5greedy` takes the same work at every n (ratio 1.0), so no n brings it to 0.5 s; it
    // stays at 8.
    r5_probe_r5greedy: "r5greedy", Verdict::Inhabited, 8 -> 8, "461380" at "29.72";
    r5_probe_r5sat1lit: "r5sat1lit", Verdict::Inhabited, 8 -> 2048, "200927923" at "29.72";
    r5_probe_r5sat2lit: "r5sat2lit", Verdict::Inhabited, 8 -> 2048, "326022785" at "29.72";
    r5_probe_r5satk1n: "r5satk1n", Verdict::Inhabited, 8 -> 2048, "275244229" at "29.57";
    r5_probe_r5satnone: "r5satnone", Verdict::Empty, 8 -> 2048, "152592914" at "29.57";
    r5_probe_r5slotsin: "r5slotsin", Verdict::Inhabited, 8 -> 8192, "87368801" at "29.75";
    r5_probe_r5slotsout: "r5slotsout", Verdict::Inhabited, 8 -> 8192, "164908042" at "29.68";
    r5_probe_r5remin: "r5remin", Verdict::Inhabited, 8 -> 2048, "165542707" at "29.72";
    r5_probe_r5remout: "r5remout", Verdict::Inhabited, 8 -> 2048, "132495905" at "29.72";
}

// The cases of `r6_escape_families_are_decided_in_their_size`, one test each
// (TEST-bench-move-l0123, author P169).
case_benches! {
    probe;
    r6_escape_family_r6three: "r6three", Verdict::Inhabited, 8 -> 1024, "112480312" at "20.34";
    r6_escape_family_r6wide: "r6wide", Verdict::Inhabited, 8 -> 2048, "386775643" at "29.40";
    r6_escape_family_r6comb: "r6comb", Verdict::Inhabited, 8 -> 2048, "215265588" at "29.45";
}

// The cases of `r6_wide_rows_are_retired_and_decided_in_their_size`, one test each
// (TEST-bench-move-l0123, author P169): the two families that were quadratic before rows were
// retired after four cells (round 6: `r6wide` n^1.82, `r6comb` n^1.62 at 1024), at sizes large
// enough for that to show.
case_benches! {
    probe;
    r6_wide_rows_r6wide: "r6wide", Verdict::Inhabited, 128 -> 2048, "283894981" at "29.37";
    r6_wide_rows_r6comb: "r6comb", Verdict::Inhabited, 128 -> 2048, "320797033" at "29.32";
}

// The cases of `r7_round6_probe_cases_are_decided_in_their_size`, one test each
// (TEST-bench-move-l0123, author P169). R7: the round-6 probe cases no other scaling test reads.
// `r6twowide` and `r6threeun` are outside the chains' class and quadratic on the base search as
// well, so they are not here; `r6two` and `r6twoun` are in
// `r7_round6_probe_cases_r6two_and_r6twoun_are_decided_in_their_size`, deferred to plan row
// SUB-r6two-bytes in wt/scratch/deferred-tests/SUB-r6two-bytes.rs.
case_benches! {
    probe;
    r7_round6_probe_r6parity: "r6parity", Verdict::Inhabited, 8 -> 4096, "222739773" at "29.78";
    r7_round6_probe_r6repeat3: "r6repeat3", Verdict::Inhabited, 8 -> 1024, "131337804" at "20.34";
    r7_round6_probe_r6distinct2: "r6distinct2", Verdict::Inhabited, 8 -> 4096, "290590927" at "29.88";
    r7_round6_probe_r6distinct3: "r6distinct3", Verdict::Inhabited, 8 -> 4096, "272795791" at "29.83";
}

// The cases of `r7_congruence_scales`, one test each (TEST-bench-move-l0123, author P169).
case_benches! {
    probe;
    r7_congruence_r6parity: "r6parity", Verdict::Inhabited, 128 -> 4096, "233359900" at "29.99";
    r7_congruence_r7congruencein: "r7congruencein", Verdict::Inhabited, 128 -> 4096, "141752191" at "29.94";
    r7_congruence_r7congruenceout: "r7congruenceout", Verdict::Inhabited, 128 -> 4096, "160450898" at "29.93";
    r7_congruence_r7bmmout: "r7bmmout", Verdict::Inhabited, 128 -> 4096, "183488716" at "29.94";
}

// The cases of `r7_peer_escape_families_scale`, one test each (TEST-bench-move-l0123, author
// P169).
case_benches! {
    probe;
    r7_peer_escape_r6repeat3: "r6repeat3", Verdict::Inhabited, 128 -> 1024, "116576556" at "20.34";
    r7_peer_escape_r6distinct2: "r6distinct2", Verdict::Inhabited, 128 -> 4096, "358197786" at "29.93";
    r7_peer_escape_r6distinct3: "r6distinct3", Verdict::Inhabited, 128 -> 4096, "281779191" at "29.88";
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

// The probe cases of `r8_escape_and_width_instruction_scaling`, one test each
// (TEST-bench-move-l0123, author P169). `r7aperiodic` is `Empty` at some sizes (at 2048 and
// 32768 among the powers of two; see `r7_aperiodic` of refusals.rs), so its n is 3072, where it
// is `Inhabited` at n and 8n.
case_benches! {
    probe;
    r8_escape_instructions_r7congruenceout: "r7congruenceout", Verdict::Inhabited, 32 -> 4096, "232305676" at "29.75";
    r8_escape_instructions_r7aperiodic: "r7aperiodic", Verdict::Inhabited, 32 -> 3072, "132466164" at "29.75";
}

/// The width check of `r8_escape_and_width_instruction_scaling` until the resize.
#[test]
fn r8_width_by_head_representation() {
    // Resized from n 256 to n 1048576 (TEST-bench-move-l0123, author P169); 1x took 163007197 ns
    // at load 29.60.
    big(|| {
        // n counts the quadratic head representation. Width floor(sqrt(n))
        // gives inputs of about n and 8n, with all construction outside timing.
        let inputs = scaling::inputs(1048576, |n| {
            rfx_case(
                "r5varywidth",
                (n as f64).sqrt() as usize,
                &format!("_r8width{n}"),
            )
        });
        scaling::check("r5varywidth by head representation size", 1048576, |n| {
            Type::forget_emptiness();
            assert_eq!(inputs[&n].verdict(), Verdict::Inhabited);
        });
    });
}

// The cases of `r8_residue_boundary_scales`, one test each (TEST-bench-move-l0123, author P169).
// Its base was 64 so that `r7aperiodic` was `Inhabited` at 64 and 512 (it is `Empty` at 128, by
// its closed form); its n is now 3072, `Inhabited` at 3072 and 24576.
case_benches! {
    probe;
    r8_residue_boundary_r7aperiodic: "r7aperiodic", Verdict::Inhabited, 64 -> 3072, "155334748" at "29.69";
    r8_residue_boundary_r8residues: "r8residues", Verdict::Inhabited, 64 -> 4096, "209086464" at "29.65";
    r8_residue_boundary_r8residuesout: "r8residuesout", Verdict::Inhabited, 64 -> 4096, "211962730" at "29.65";
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

// The cases of `r8_stage_boundary_scale`, one test each (TEST-bench-move-l0123, author P169).
case_benches! {
    probe;
    r8_stage_boundary_r8stagein: "r8stagein", Verdict::Inhabited, 128 -> 4096, "221513164" at "29.65";
    r8_stage_boundary_r8stageout: "r8stageout", Verdict::Inhabited, 128 -> 4096, "184461728" at "29.60";
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

// The 32 checks of `r9_wrapped_witness_cost_scales`, one test each (TEST-bench-move-l0123,
// author P169). Before the resize each size had one copy of the type, used by every run; each run
// now has its own copy.
case_benches! {
    "a checked list witness inside a product,";
    r9_wrapped_witness_tup_clstaggerholesout: "tup:clstaggerholesout", Verdict::Inhabited, 32 -> 2048, "145863077" at "30.85";
    r9_wrapped_witness_tup_u4holesout: "tup:u4holesout", Verdict::Inhabited, 32 -> 2048, "177416884" at "30.59";
    r9_wrapped_witness_tup_u4cofrontshared: "tup:u4cofrontshared", Verdict::Inhabited, 32 -> 4096, "150133237" at "30.85";
    r9_wrapped_witness_tup_r5remout: "tup:r5remout", Verdict::Inhabited, 32 -> 2048, "162195818" at "30.85";
    r9_wrapped_witness_rec_clstaggerholesout: "rec:clstaggerholesout", Verdict::Inhabited, 32 -> 2048, "137625154" at "31.07";
    r9_wrapped_witness_rec_u4holesout: "rec:u4holesout", Verdict::Inhabited, 32 -> 2048, "173898332" at "30.85";
    r9_wrapped_witness_rec_u4cofrontshared: "rec:u4cofrontshared", Verdict::Inhabited, 32 -> 4096, "176412120" at "31.00";
    r9_wrapped_witness_rec_r5remout: "rec:r5remout", Verdict::Inhabited, 32 -> 4096, "224426432" at "31.07";
    r9_wrapped_witness_atom_clstaggerholesout: "atom:clstaggerholesout", Verdict::Inhabited, 32 -> 2048, "301117823" at "29.77";
    r9_wrapped_witness_atom_u4holesout: "atom:u4holesout", Verdict::Inhabited, 32 -> 2048, "259390088" at "30.06";
    r9_wrapped_witness_atom_u4cofrontshared: "atom:u4cofrontshared", Verdict::Inhabited, 32 -> 4096, "449653442" at "30.06";
    r9_wrapped_witness_atom_r5remout: "atom:r5remout", Verdict::Inhabited, 32 -> 2048, "134675906" at "30.06";
    r9_wrapped_witness_atom2_clstaggerholesout: "atom2:clstaggerholesout", Verdict::Inhabited, 32 -> 2048, "201088477" at "29.55";
    r9_wrapped_witness_atom2_u4holesout: "atom2:u4holesout", Verdict::Inhabited, 32 -> 2048, "221373990" at "29.77";
    r9_wrapped_witness_atom2_u4cofrontshared: "atom2:u4cofrontshared", Verdict::Inhabited, 32 -> 4096, "258283963" at "29.77";
    r9_wrapped_witness_atom2_r5remout: "atom2:r5remout", Verdict::Inhabited, 32 -> 2048, "140304987" at "29.55";
    r9_wrapped_witness_nested_clstaggerholesout: "nested:clstaggerholesout", Verdict::Inhabited, 32 -> 2048, "131887480" at "30.60";
    r9_wrapped_witness_nested_u4holesout: "nested:u4holesout", Verdict::Inhabited, 32 -> 2048, "377124608" at "30.25";
    r9_wrapped_witness_nested_u4cofrontshared: "nested:u4cofrontshared", Verdict::Inhabited, 32 -> 2048, "48633382" at "20.34";
    r9_wrapped_witness_nested_r5remout: "nested:r5remout", Verdict::Inhabited, 32 -> 2048, "110382338" at "30.40";
    r9_wrapped_witness_option_clstaggerholesout: "option:clstaggerholesout", Verdict::Inhabited, 32 -> 2048, "244114962" at "30.25";
    r9_wrapped_witness_option_u4holesout: "option:u4holesout", Verdict::Inhabited, 32 -> 2048, "198565557" at "31.07";
    r9_wrapped_witness_option_u4cofrontshared: "option:u4cofrontshared", Verdict::Inhabited, 32 -> 2048, "94052197" at "31.07";
    r9_wrapped_witness_option_r5remout: "option:r5remout", Verdict::Inhabited, 32 -> 2048, "259242865" at "30.87";
    r9_wrapped_witness_map_clstaggerholesout: "map:clstaggerholesout", Verdict::Inhabited, 32 -> 2048, "146561023" at "30.72";
    r9_wrapped_witness_map_u4holesout: "map:u4holesout", Verdict::Inhabited, 32 -> 2048, "136506748" at "30.60";
    r9_wrapped_witness_map_u4cofrontshared: "map:u4cofrontshared", Verdict::Inhabited, 32 -> 4096, "143607694" at "30.60";
    r9_wrapped_witness_map_r5remout: "map:r5remout", Verdict::Inhabited, 32 -> 2048, "145229972" at "30.72";
    r9_wrapped_witness_listhead_clstaggerholesout: "listhead:clstaggerholesout", Verdict::Inhabited, 32 -> 2048, "304874391" at "30.28";
    r9_wrapped_witness_listhead_u4holesout: "listhead:u4holesout", Verdict::Inhabited, 32 -> 2048, "153468794" at "30.72";
    r9_wrapped_witness_listhead_u4cofrontshared: "listhead:u4cofrontshared", Verdict::Inhabited, 32 -> 4096, "195368614" at "30.72";
    r9_wrapped_witness_listhead_r5remout: "listhead:r5remout", Verdict::Inhabited, 32 -> 2048, "242980805" at "30.28";
}

#[test]
fn r9_active_groups_have_one_entry_across_simultaneous_reentry() {
    // Resized from n 512 to n 8192 (TEST-bench-move-l0123, author P169); 1x took 137372261 ns at
    // load 20.15.
    big(|| {
        let small = r9_swapping_groups(8192, false, "_r9swap_small");
        let large = r9_swapping_groups(8 * 8192, false, "_r9swap_large");
        scaling::check(
            "two positive chains re-enter each other's exhausted groups",
            8192,
            |n| {
                Type::forget_emptiness();
                assert_eq!(
                    (if n == 8192 { &small } else { &large }).chain_verdict(),
                    Some(Verdict::Inhabited)
                );
            },
        );
        // The words held and not held at n 1 to 6 are checked in
        // `chains_that_reenter_each_others_groups_are_inhabited` of refusals.rs
        // (TEST-bench-move-l0123, author P169).
    });
}

/// The escape's cell discovery of `case` at `n` and `8 * n`, a fresh copy of the type for each
/// run. Until the resize the three cases were checked in one test,
/// `escape_cells_scale_on_the_coset_and_product_chains`, at n 1024 (TEST-bench-move-l0123,
/// author P169). The escape's cell discovery stays within n log n from 1024 to 8192 on the
/// families where the sweep it replaced grew faster: `r9cosets` (place and head types both of
/// period 7, every cell empty by alignment; the sweep took 595.9M and 33,746M instructions at
/// 8192 and 65,536, 57x for 8x), and the Boolean-product chains `r9bmmlate` (11.9x) and
/// `r10alternating` (10.7x, above the 9.8x of n log n). The windows of block summaries and residue
/// pair listing take 85.1M and 760.2M on `r9cosets` (8.9x), 8.1x and 8.3x on the other two
/// (measured at n 1024).
fn escape_cells_scale(case: &str, n: usize) {
    big(|| {
        let (s_runs, l_runs) = scaling::Meter::new().runs();
        let copies = |k: usize, runs: usize| -> Vec<Type> {
            (0..runs)
                .map(|i| rfx_case(case, k, &format!("_esc_{case}_{k}_{i}")))
                .collect()
        };
        let (small, large) = (copies(n, s_runs), copies(8 * n, l_runs));
        let (si, li) = (AtomicUsize::new(0), AtomicUsize::new(0));
        scaling::check(&format!("escape cells of {case}"), n, |k| {
            let t = if k == n {
                &small[si.fetch_add(1, Relaxed)]
            } else {
                &large[li.fetch_add(1, Relaxed)]
            };
            std::hint::black_box(t.escape_cell_counts());
        });
    });
}

#[test]
fn escape_cells_of_r9cosets() {
    // Resized from n 1024 to n 8192 (TEST-bench-move-l0123, author P169); 1x took
    // 69354216 ns at load 20.15.
    escape_cells_scale("r9cosets", 8192);
}

#[test]
fn escape_cells_of_r9bmmlate() {
    // Resized from n 1024 to n 4096 (TEST-bench-move-l0123, author P169); 1x took 138470414 ns
    // at load 33.61.
    escape_cells_scale("r9bmmlate", 4096);
}

#[test]
fn escape_cells_of_r10alternating() {
    // Resized from n 1024 to n 4096 (TEST-bench-move-l0123, author P169); 1x took 115349197 ns
    // at load 33.61.
    escape_cells_scale("r10alternating", 4096);
}

/// R9-C7 (Codex R9): `decidable` walked a type shared by two components once per path, 2^d
/// visits at depth d. It visits each distinct type once, and still finds a bounded morphism
/// under tuples, atom payloads and recursive groups.
#[test]
fn r9_decidable_shared_dag_scales_and_rejects_bounded_leaves() {
    // Resized from n 16 to n 65536 (TEST-bench-move-l0123, author P169); 1x took 184554450 ns at
    // load 29.58.
    big(|| {
        let small = r9_shared_tuple_type(65536, Type::bool());
        let large = r9_shared_tuple_type(8 * 65536, Type::bool());
        scaling::check("decidability of a shared tuple DAG", 65536, |n| {
            assert!((if n == 65536 { &small } else { &large }).decidable());
        });
        // Bounded leaves, the cyclic list and the atom payload are checked in
        // `shared_dags_are_decidable_unless_a_leaf_is_bounded` of refusals.rs
        // (TEST-bench-move-l0123, author P169).
    });
}

// The three cases of `r10_a_boolean_list_tail_scales`, one test each (TEST-bench-move-l0123,
// author P169): a Boolean list type as a list's tail gets the verdict of the list alone, taken
// at n 32. Before the resize each size had one copy of the type, used by every run; each run now
// has its own copy.
fn list_tail_scales(case: &str, n: usize) {
    let want = rfx_case(case, 32, "_r10tail_want").verdict();
    case_scales(
        "a Boolean list type as a list's tail,",
        &format!("r10tail_{case}"),
        &format!("listtail:{case}"),
        n,
        want,
    );
}

#[test]
fn r10_list_tail_clstaggerholesout() {
    // Resized from n 32 to n 2048 (TEST-bench-move-l0123, author P169); 1x took 208466349 ns at
    // load 31.19.
    list_tail_scales("clstaggerholesout", 2048);
}

#[test]
fn r10_list_tail_r5remout() {
    // Resized from n 32 to n 2048 (TEST-bench-move-l0123, author P169); 1x took 121033777 ns at
    // load 31.19.
    list_tail_scales("r5remout", 2048);
}

#[test]
fn r10_list_tail_chain() {
    // Resized from n 32 to n 4096 (TEST-bench-move-l0123, author P169); 1x took 164727298 ns
    // at load 31.19.
    list_tail_scales("chain", 4096);
}

/// The `Value::Big` gap (round 10): one literal outside the 64-bit range in a head no longer
/// sends the list to the general search; the escape decides it, at the bare case's cost.
#[test]
fn r10_a_wide_head_literal_is_decided_by_the_escape() {
    // Resized from n 32 to n 4096 (TEST-bench-move-l0123, author P169); 1x took 133860326 ns at
    // load 31.24.
    big(|| {
        // The witness and the escape at n 16 and 64 are checked in
        // `a_wide_head_literal_is_decided_by_the_escape_at_small_sizes` of refusals.rs
        // (TEST-bench-move-l0123, author P169).
        let small = r10_big_congruence(4096, "_r10big_small");
        let large = r10_big_congruence(8 * 4096, "_r10big_large");
        scaling::check("a wide head literal", 4096, |n| {
            Type::forget_emptiness();
            let t = if n == 4096 { &small } else { &large };
            assert_eq!(t.verdict(), Verdict::Inhabited);
        });
    });
}

// The two cases of `r10_boolean_tail_is_decided_and_scales`, one test each
// (TEST-bench-move-l0123, author P169). They check the same types as `r10_list_tail_chain` and
// `r10_list_tail_r5remout` above, with the verdict written out. Before the resize each size had
// one copy of the type, used by every run; each run now has its own copy.
case_benches! {
    "a written Boolean list tail,";
    r10_written_boolean_tail_chain: "listtail:chain", Verdict::Empty, 32 -> 4096, "164855160" at "30.93";
    r10_written_boolean_tail_r5remout: "listtail:r5remout", Verdict::Inhabited, 32 -> 2048, "124821085" at "30.93";
}

#[test]
fn r10_big_integer_escape_is_a_renaming_and_scales() {
    // Resized from n 32 to n 4096 (TEST-bench-move-l0123, author P169); 1x took 113821398 ns at
    // load 31.24. The renaming checks at n 16 to 1024 are as before.
    big(|| {
        let a = r10_big_congruence_cx(4096, true, "_r10big4096");
        let b = r10_big_congruence_cx(8 * 4096, true, "_r10big32768");
        scaling::check("a wide integer in escape heads", 4096, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 4096 { &a } else { &b }).verdict(),
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
    // Resized from n 16 to n 4096 (TEST-bench-move-l0123, author P169); 1x took 78223787 ns
    // at load 30.93.
    big(|| {
        let a = rfx_case("r10sharedfront", 4096, "_r10shared4096");
        let b = rfx_case("r10sharedfront", 8 * 4096, "_r10shared32768");
        scaling::check("one list type shared by every tuple component", 4096, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 4096 { &a } else { &b }).verdict(),
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
    // Finding (TEST-bench-move-l0123, author P169): left at its old n 32, because the check fails
    // its limit at the sizes the resize asks for (1x is 0.9 ms at n 32; 1x about 0.5 s would need
    // n in the thousands). The work grows faster than n log n. Bench lines, load about 34,
    // instructions at n and 8n: n 32 passes, 9.0 times (4.08M and 36.8M; the first runs 8.3
    // times); n 64 fails, 11.0 times (8.00M and 88.4M); n 128 fails, 14.1 times (16.7M and
    // 235.2M). A size probe of one verdict took 62M instructions at n 256, 911M at 2048 (14.6
    // times) and 9.3G at 8192.
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
    // Resized from n 32 to n 16384 (TEST-bench-move-l0123, author P169); 1x took 64063667 ns at
    // load 31.10. Building the types takes most of the test's time (1.2 s at 32768,
    // 5.5 s at 131072), so n is held where the build fits the test's time.
    big(|| {
        let a = r10_shared_payloads(16384, "_payload16384");
        let b = r10_shared_payloads(8 * 16384, "_payload131072");
        scaling::check("tags sharing one tuple payload diagram", 16384, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 16384 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
    });
}

#[test]
fn r11_group_reads_skip_bare_atom_names_and_scale() {
    // Resized from n 128 to n 32768 (TEST-bench-move-l0123, author P169); 1x took 211424228 ns
    // at load 30.93.
    big(|| {
        let a = r11_failure_prefixes(32768);
        let b = r11_failure_prefixes(8 * 32768);
        scaling::check(
            "group dependencies of shared failure-atom prefixes",
            32768,
            |n| {
                Type::forget_emptiness();
                assert_eq!(
                    (if n == 32768 { &a } else { &b }).verdict(),
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
    // Resized from n 32 to n 16384 (TEST-bench-move-l0123, author P169); 1x took 276510878 ns at
    // load 30.93.
    big(|| {
        let make = |n| {
            let mut t = rfx_case("r5remout", 8, "_r11deepscale");
            for _ in 0..n {
                t = cons_of(Type::int(), t);
            }
            t
        };
        let a = make(16384);
        let b = make(8 * 16384);
        scaling::check(
            "Boolean list boundary behind a literal prefix",
            16384,
            |n| {
                Type::forget_emptiness();
                assert_eq!(
                    (if n == 16384 { &a } else { &b }).verdict(),
                    Verdict::Inhabited
                );
            },
        );
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
    // Resized from n 32 to n 4096 (TEST-bench-move-l0123, author P169); 1x took 63271327 ns at
    // load 30.39.
    big(|| {
        let a = rfx_case("listhead:pairfar", 4096, "_r11pairitem4096");
        let b = rfx_case("listhead:pairfar", 8 * 4096, "_r11pairitem32768");
        scaling::check("tuple fields within a list item", 4096, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 4096 { &a } else { &b }).verdict(),
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
    // Resized from n 32 to n 16384 (TEST-bench-move-l0123, author P169); 1x took 16696681 ns at
    // load 30.70. Building the types takes most of the test's time (0.65 s at 16384, 2.5 s
    // at 65536), so n is held where the build fits the test's time.
    big(|| {
        let a = r11_names_family(16384, "_s16384");
        let b = r11_names_family(8 * 16384, "_s131072");
        scaling::check("types sharing many atom names", 16384, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 16384 { &a } else { &b }).verdict(),
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
    //
    // Finding (TEST-bench-move-l0123, author P169): left at its old n 8, because the check fails
    // its limit at the sizes the resize asks for (1x about 0.5 s would need n near 256). Bench
    // lines, load about 34, instructions at n and 8n: n 8 passes, 7.6 times (32.6M and 247.0M);
    // n 32 passes, 8.8 times (122.7M and 1082.8M); n 64 passes, 9.9 times (247.0M and 2446.9M);
    // n 128 fails, 11.9 times (507.9M and 6027.6M; bytes 12.4 times). A size probe of one verdict
    // took 2.07G instructions at n 512 and 14.96G at 2048, 7.2 times for 4 times n.
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
    // Finding (TEST-bench-move-l0123, author P169): left at its old n 8, because the check fails
    // its limit at the sizes the resize asks for (1x about 0.5 s would need n near 128). Bench
    // lines, load about 34, instructions at n and 8n: n 8 passes, 7.6 times (48.6M and 370.1M);
    // n 32 passes, 9.1 times (182.9M and 1672.0M); n 64 fails, 10.55 times (370.0M and 3903.3M).
    // A size probe of one verdict and one `is_empty` on the forks-first order took 3.97G
    // instructions at n 512 and 29.3G at 2048, 7.4 times for 4 times n; the order with the empty
    // component first took 172M and 597M, 3.5 times.
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
    //
    // Finding (TEST-bench-move-l0123, author P169): left at its old n 8, because the check fails
    // its limit at the sizes the resize asks for (1x about 0.5 s would need n near 256). Bench
    // lines, load about 34, instructions at n and 8n: n 8 passes, 7.9 times (24.6M and 195.4M);
    // n 32 passes, 10.3 times (94.6M and 974.3M); n 64 fails, 12.8 times (195.3M and 2494.8M;
    // the first runs' bytes 10.9 times). A size probe of one verdict took 2.61G instructions at
    // n 512 and 23.7G at 2048, 9.1 times for 4 times n.
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

// Moved from refusals.rs (TEST-bench-move-l0123, author P178): each runs at a depth that
// overflowed a 2 MiB thread stack before the fix it guards, on a thread of that stack size.

/// X39: initialize the emptiness tables before the first type, and leave a deep
/// type in them until thread exit. No recursive group or escape solver is needed.
#[test]
fn r8_deep_type_cached_before_queue_initialization_drops_on_small_stack() {
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| {
            Type::forget_emptiness();
            let mut t = Type::int();
            for _ in 0..12000 {
                t = Type::tuple(vec![t]);
            }
            assert_eq!(t.verdict(), Verdict::Inhabited);
            let body = (0..12000).fold(int(), |tail, _| Expr::Tuple(vec![tail]));
            let group = Group::new(vec![def("R8DeepCachedGroup", body)]).unwrap();
            let member = group.instance(vec![]).remove(0);
            assert_eq!(member.verdict(), Verdict::Inhabited);
            eprintln!("r8 deep cached verdict complete");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn r8_x39_deep_type_drop_does_not_overflow_stack() {
    // Negative control on __COMMIT__ and main `f5ecad1d`: a 2 MiB thread that calls
    // `Type::forget_emptiness()` before building a deep nested `cons(int, ...)` chain (25,000
    // links = 50,000 nested `Node::Parts` / `BTreeMap<usize, Part<Row>>` levels, matching `P` in
    // `r6two` at `n = 4096`) initializes `VERDICTS` before `types::FREED`, and an external
    // thread-local initialized first outlives `types::FREED`; both overflow a 2 MiB stack
    // (`SIGSEGV`, `rc = 139`) at thread exit without `hold()` and `ENDING`.
    //
    // The two threads run at once; until TEST-bench-move-l0123 (author P169) the second started
    // after the first ended (1.36 s alone under load). The depth stays at 25,000: nothing shows
    // a smaller chain still overflowed the 2 MiB stack in the code this guards against.
    let run_forget_first = std::thread::Builder::new()
        .name("r8-x39-forget".into())
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            Type::forget_emptiness();
            let mut chain = Type::atom("nil");
            for _ in 0..25_000 {
                chain = cons_of(Type::int(), chain);
            }
            assert_eq!(chain.verdict(), Verdict::Inhabited);
        })
        .unwrap();

    let run_external_tls = std::thread::Builder::new()
        .name("r8-x39-ext-tls".into())
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            thread_local! {
                static EXT: std::cell::RefCell<Option<Type>> = const { std::cell::RefCell::new(None) };
            }
            EXT.with(|slot| *slot.borrow_mut() = None);
            let mut chain = Type::atom("nil");
            for _ in 0..25_000 {
                chain = cons_of(Type::int(), chain);
            }
            EXT.with(|slot| *slot.borrow_mut() = Some(chain));
        })
        .unwrap();
    run_forget_first.join().unwrap();
    run_external_tls.join().unwrap();
}

/// Every seed of `PREFIX_CHAIN_SEEDS`, of which the correctness test
/// `lists_by_the_place_from_the_front_variants_agree_with_the_oracle` asks 20 each run: each
/// family is decided as the oracle finds, or refused with Fork where `PREFIX_CHAIN_FORK_SEEDS`
/// lists it (row REFUSAL-list-front-chain-fork), so that list stays exact for the range the
/// correctness test draws from. Many cases, so a benchmark (author P178): 1024 families in about
/// 0.55 s at load 19.
#[test]
fn every_random_prefix_chain_agrees_with_the_oracle() {
    for chain in PREFIX_CHAIN_SEEDS {
        check_random_prefix_chain(chain, &format!("_prc{chain}"), "every seed");
    }
}

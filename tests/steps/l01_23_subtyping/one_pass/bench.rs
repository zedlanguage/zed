//! The benchmarks of `one_pass.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `one_pass.rs`.

use super::*;

/// Each family of [`families`] is decided by `is_empty` and `verdict` in time linear in the
/// tuple types, 32 against 256. Before the pass, `is_empty` on `tight(c) - x` took 298M and
/// 5,513M instructions at 32 and 128 tuple types (order `c²`).
#[test]
fn exclusive_ors_and_chains_of_overlapping_tuple_types_are_decided_in_one_pass() {
    // TEST-bench-move-l0123, author P169: c 32 before, now 320 (the sizes above are the old
    // ones); 1x 0.36 s by `ns`, load 41.
    let types = scaling::inputs(320, families);
    scaling::check(
        "one pass over exclusive ors and chains, by tuple types",
        320,
        |c| {
            for (t, expected) in &types[&c] {
                Type::forget_emptiness();
                assert_eq!(t.is_empty(), *expected == Verdict::Empty, "{c}");
                Type::forget_emptiness();
                assert_eq!(t.verdict(), *expected, "{c}");
            }
        },
    );
}

/// Two builds of one exclusive or, in two orders, are one node (item CHAIN-zip-size), so they
/// are equal in time linear in the tuple types.
#[test]
fn an_exclusive_or_built_in_two_orders_is_equal_to_itself_in_linear_time() {
    // Left at its old size, 32 (TEST-bench-move-l0123, author P169): the timed work is one
    // comparison of two hash-consed nodes, about 15 µs at either size (ratio 0.998, load 39),
    // so no size brings the 1x run near 0.5 s.
    let types = scaling::inputs(32, |c| (parity(c, false).ty(2), parity(c, true).ty(2)));
    scaling::check(
        "an exclusive or against its reverse build, by tuple types",
        32,
        |c| {
            let (x, y) = &types[&c];
            Type::forget_emptiness();
            assert!(x.equiv(y), "{c}");
        },
    );
}

/// The comparisons of [`comparisons`] are decided in time `O(c log c)`, 32 against 256 tuple
/// types. Before the item, the split into tuple types took 333M, 1,253M and 4,414M
/// instructions at 32, 64 and 128 on the exclusive ors, and 9.5M, 31.0M and 110M on the
/// chains (order `c²`).
#[test]
fn overlapping_exclusive_ors_and_chains_are_compared_in_n_log_n() {
    // TEST-bench-move-l0123, author P169: c 32 before, now 320 (the sizes above are the old
    // ones); 1x 0.43 s by `ns`, load 41.
    let types = scaling::inputs(320, comparisons);
    scaling::check(
        "an exclusive or or a chain against one more and against each other, by tuple types",
        320,
        |c| {
            let (pairs, meet) = &types[&c];
            for (x, y) in pairs {
                Type::forget_emptiness();
                assert!(!x.equiv(y), "{c}");
            }
            Type::forget_emptiness();
            assert_eq!(meet.verdict(), Verdict::Inhabited, "{c}");
        },
    );
}

/// The chain of `c` tuple types less the chain of `c + 1`, empty at even `c` and inhabited at
/// odd, decided in time `O(c log c)`, 32 against 256 (and 33 against 257). The last tuple type
/// of the longer chain is `|` at even `c` and `-` at odd, so both kinds of end are measured.
/// Once the two tuple types the longer chain adds or takes are refused, the two chains are one
/// decision list and its complement, which meet in `false` at once. Before
/// that was seen (`Connect::same_as_not` on lists other than literals), the part stayed an `&`
/// of the two and narrowing refused one tuple type a pass, 6.6M, 24.8M, 97.7M and 394M
/// instructions at 32, 64, 128 and 256 (order `c²`).
#[test]
fn a_chain_less_a_longer_one_is_decided_in_n_log_n() {
    // TEST-bench-move-l0123, author P169: c 32 before, now 3072 (the sizes above are the old
    // ones); 1x 0.14 s by `ns`, load 27; at 4096 the run took 16.5 s, over 15 s.
    let all = Type::tuple(vec![Type::top(), Type::top()]);
    let types = scaling::inputs(3072, |c| {
        [c, c + 1].map(|c| {
            let (l, l1) = (chain(c).ty(2), chain(c + 1).ty(2));
            (&l & &(&all - &l1), c % 2 == 1)
        })
    });
    scaling::check("a chain less one a tuple type longer", 3072, |c| {
        for (t, inhabited) in &types[&c] {
            Type::forget_emptiness();
            let want = if *inhabited {
                Verdict::Inhabited
            } else {
                Verdict::Empty
            };
            assert_eq!(t.verdict(), want, "{c}");
        }
    });
}

/// The meets of [`wide`] are decided in time `O(c log c)`, 30 against 240 tuple types, none
/// refused; `chains_sharing_two_of_four_components_are_met_as_enumeration_meets_them` checks
/// them against the enumeration up to 30 (TEST-bench-move-l0123, author P170).
#[test]
fn chains_sharing_two_of_four_components_are_met_in_n_log_n() {
    // TEST-bench-move-l0123, author P169: c 30 before, now 1600 (the sizes above are the old
    // ones); 1x 0.37 s by `ns`, load 36.
    let types = scaling::inputs(1600, wide);
    let all = Type::tuple(vec![Type::top(); 4]);
    let run = |c: usize| {
        let (x, y) = &types[&c];
        let mut verdicts = Vec::new();
        for t in [x & y, x - y, y - x, &all - &(x | y)] {
            Type::forget_emptiness();
            let v = t.verdict();
            assert!(!matches!(v, Verdict::Refused(_)), "{c}");
            verdicts.push(v);
        }
        verdicts
    };
    scaling::check(
        "chains on three components sharing two, by tuple types",
        1600,
        |c| {
            run(c);
        },
    );
}

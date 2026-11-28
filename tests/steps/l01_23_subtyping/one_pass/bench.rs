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
    // ones); 1x 0.36 s by `ns`, load 41. Now 1000 (SCALE-small-n-rest; DESIGN sec:plan, n log
    // n is under 10.5 only from n = 777), each size's types built in its own process.
    scaling::check_inputs(
        "one pass over exclusive ors and chains, by tuple types",
        1000,
        |c| (c, families(c)),
        |(c, types)| {
            for (t, expected) in types {
                Type::forget_emptiness();
                assert_eq!(t.is_empty(), *expected == Verdict::Empty, "{c}");
                Type::forget_emptiness();
                assert_eq!(t.verdict(), *expected, "{c}");
            }
        },
    );
}

/// An exclusive or built in reverse, beside its build in turn, and compared with it, in time
/// linear in the tuple types.
#[test]
fn an_exclusive_or_built_in_two_orders_is_equal_to_itself_in_linear_time() {
    // FAIL-l0123-exclusive-or-benches-allocate-nothing: until then the timed run was the
    // comparison alone, of two builds made before it, which are one node (item CHAIN-zip-size):
    // about 33,800 instructions and 1,200 bytes at both sizes, and from 3706656c3 (the identity
    // test first in `Type::subtype`) no bytes, so the check of the bytes refused it. The
    // reverse build is now timed, the work that ends at that node; the comparison of the two
    // builds alone is held to constant time in the next test.
    let firsts = scaling::inputs(N_REVERSE, |c| parity(c, false).ty(2));
    scaling::check(
        "an exclusive or built in reverse and compared with its build in turn, by tuple types",
        N_REVERSE,
        |c| {
            Type::forget_emptiness();
            let y = parity(c, true).ty(2);
            assert!(firsts[&c].equiv(&y), "{c}");
        },
    );
}

/// Size of [`an_exclusive_or_built_in_two_orders_is_equal_to_itself_in_linear_time`]: 1x 92 ms
/// at load 25, 643M to 5,671M instructions, 8.82 times; at 1000 it was 9.01 times, over
/// `PREFERRED`, the ratio falling with `c` as one of `c log c` does.
const N_REVERSE: usize = 4096;

/// Two builds of one exclusive or, in two orders, are one node (item CHAIN-zip-size), so
/// `equiv` decides them by the identity test first in `Type::subtype`, in constant time and
/// with no allocation; its small instance asserts the one node.
#[test]
fn two_builds_of_an_exclusive_or_are_compared_in_constant_time() {
    let types = scaling::inputs(32, |c| (parity(c, false).ty(2), parity(c, true).ty(2)));
    scaling::check_instructions_only(
        "an exclusive or against its reverse build, both built before, by tuple types",
        32,
        0,
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
    // ones); 1x 0.43 s by `ns`, load 41. Now 1000 (SCALE-small-n-rest; DESIGN sec:plan, n log
    // n is under 10.5 only from n = 777), each size's types built in its own process.
    scaling::check_inputs(
        "an exclusive or or a chain against one more and against each other, by tuple types",
        1000,
        |c| (c, comparisons(c)),
        |(c, (pairs, meet))| {
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

/// The `|` of `ts`, joined as a balanced tree, so that its depth is `log` of their number.
fn balanced(ts: &[Type]) -> Type {
    if ts.len() == 1 {
        return ts[0].clone();
    }
    let (x, y) = ts.split_at(ts.len() / 2);
    &balanced(x) | &balanced(y)
}

/// A balanced `|` of exclusive ors of two tuple types each, every tuple type on component 0, less
/// the exclusive or of all its `c` tuple types (empty) and less that of all but the last
/// (inhabited), joined by `|` to a part open on components 1 and 2 that the box
/// `(top, 1 | 2 | 3, top)` leaves empty, so that the part is not a product of components and
/// goes to the one pass, at `c` and `8c` tuple types (REFUSAL-one-component-shared-meet): each
/// `|` of two parts that are not both lists or exclusive ors, and each meet, is read cell by
/// cell on component 0 (`OneFn` in zed-kernel `types/empty.rs`), `O(c log^2 c)`. Before the
/// row the meet was refused with `SharedCells(0)` (kept output, 2026-11-22: "assertion `left ==
/// right` failed: 256 left: Refused(SharedCells(0)) right: Empty"). Measured on a Colab VM
/// (v5e2, DynamoRIO instruction counts, 2026-11-22): 1,199M and 9,983M instructions at 256
/// and 2048, 8.32 times; 1x 1.29 s. Small instance:
/// `a_meet_open_on_one_component_only_is_decided_cell_by_cell`.
#[test]
fn meets_on_one_component_scale() {
    let n = 256;
    let b = Type::tuple(vec![
        Type::top(),
        Type::union_all([1, 2, 3].map(lit)),
        Type::top(),
    ]);
    // True at component 1 = 0 only, which the box leaves out.
    let others = F::And(
        Box::new(F::Xor(vec![(1, 0), (1, 1)])),
        Box::new(F::Xor(vec![(1, 0), (1, 2)])),
    )
    .ty(3);
    let types = scaling::inputs(n, |c| {
        let pairs: Vec<Type> = (0..c / 2)
            .map(|i| F::Xor(vec![(0, 1000 + 2 * i), (0, 1001 + 2 * i)]).ty(3))
            .collect();
        let union = balanced(&pairs);
        let xor = |k: usize| F::Xor((0..k).map(|i| (0, 1000 + i)).collect()).ty(3);
        let part = |t: Type| &b & &(&t | &others);
        (part(&union - &xor(c)), part(&union - &xor(c - 1)))
    });
    scaling::check("meets on one component, by tuple types", n, |c| {
        let (empty, inhabited) = &types[&c];
        for (t, expected) in [(empty, Verdict::Empty), (inhabited, Verdict::Inhabited)] {
            Type::forget_emptiness();
            assert_eq!(t.verdict(), expected, "{c}");
            Type::forget_emptiness();
            assert_eq!(t.is_empty(), expected == Verdict::Empty, "{c}");
        }
    });
}

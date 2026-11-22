//! The benchmarks of `setop.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `setop.rs`.

use super::*;

/// Meets of `k` members at `k` and `8k`: with one empty operand the decider settles the meet
/// with no search; with all operands inhabited, in
/// [`meets_of_k_inhabited_members_scale`], only the meet is searched.
///
/// Size (TEST-bench-move-l0123, author P169): n 8 before, now 8192: 1x 93 ms, 8x 1.42 s, the
/// whole test 8.9 s at load 23, most of it building the inputs. At 16384 the test passed the
/// 20 s limit at load 27.
#[test]
fn meets_of_k_members_scale() {
    let n = 8192;
    let empty = scaling::inputs(n, |k| meet_of_k(k, true));
    scaling::check("the verdict on a meet of k members, one empty", n, |k| {
        assert_eq!(verdict_and_searched(&empty[&k]), (Verdict::Empty, 0));
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 8 before, now 8192, for the reason given at
/// [`meets_of_k_members_scale`].
#[test]
fn meets_of_k_inhabited_members_scale() {
    let n = 8192;
    let full = scaling::inputs(n, |k| meet_of_k(k, false));
    scaling::check("the verdict on a meet of k inhabited members", n, |k| {
        assert_eq!(verdict_and_searched(&full[&k]), (Verdict::Inhabited, 1));
    });
}

/// The product of `k` parity lists is inhabited (`[k]` is in it), and the search for a value
/// finds the singleton before following the recursive tuple fork (COMPLEXITY.md K35).
/// Both the verdict and emptiness are checked in the size of the constraints. Small instance
/// `the_product_of_a_few_parity_lists_has_a_singleton`.
///
/// Size (TEST-bench-move-l0123, author P169): n 4 before, now 4096; 1x 873 ms at load 42, each
/// run on an instance of its own ([`Fresh`]; 155 ms at load 21.54 when the runs after the first
/// reused one).
#[test]
fn the_product_of_k_parity_lists_has_a_checked_singleton() {
    let n = 4096;
    let meets = scaling::inputs(n, |k| Fresh::new(parity_meet_group(k), 2 * k + 2));
    scaling::check("emptiness of the product of k parity lists", n, |k| {
        Type::forget_emptiness();
        assert!(!meets[&k].member().is_empty());
    });
}

/// Size (PERF-blame-settlement): n 64 before, now 2048; 1x 1.38 s by `ns` on a Colab VM
/// (v5e2, 2026-11-22). Before the row the instruction ratio grew with n: 8.51 at 64, 13.88 at
/// 512 and 25.93 at 2048 (TEST-bench-move-l0123), while bytes grew 8.0 times. A callgrind
/// profile at 1024 and 4096 found the step: `group_verdicts` dropped the decided members from
/// `DECIDING` with a scan of the `undecided` slice per member, order `m²` here, where every
/// member is refused. Negative control, run once and not committed (the slice scan restored):
/// 1,324M and 23,887M instructions at 2048 and 16384, 18.04 times, failed. With the set:
/// 1,095M and 8,785M, 8.02 times; bytes 8.0 times. COMPLEXITY.md K141.
#[test]
fn canonical_blame_settlement_scales() {
    let n = 2048;
    let groups = scaling::inputs(n, canonical_blame_chain);
    scaling::check_order(
        "canonical blame settlement on m refused chain members",
        n,
        1,
        |m| {
            Type::forget_emptiness();
            let v = groups[&m][0].verdict();
            assert_eq!(v, Verdict::Refused(Refusal::NoWitness));
        },
    );
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 4096; 1x 1.07 s at load 42, each
/// run on an instance of its own ([`Fresh`]; 216 ms at load 22.90 when the runs after the first
/// reused one).
#[test]
fn parity_verdicts_scale_with_the_number_of_constraints() {
    let n = 4096;
    let inputs = scaling::inputs(n, |k| {
        let (group, meet) = parity_variant_group(k, 0, Some("Scale_"), false);
        Fresh::new(group, meet)
    });
    scaling::check_order("parity verdict with a checked singleton", n, 1, |k| {
        Type::forget_emptiness();
        assert_eq!(inputs[&k].member().verdict(), Verdict::Inhabited);
    });
}

/// Bounded parity of `k` with bound `2k`, with `k` excluded when `exclude`, at `n` and `8n`.
/// One test for each.
fn bounded_parity_verdicts(n: usize, exclude: bool) {
    let inputs = scaling::inputs(n, |k| {
        let group = bounded_parity_group(k, 2 * k, exclude.then_some(k), None);
        Fresh::new(group, 2 * k + 3)
    });
    scaling::check_order(
        "bounded parity with a further integer constraint",
        n,
        1,
        |k| {
            Type::forget_emptiness();
            assert_eq!(inputs[&k].member().verdict(), Verdict::Inhabited);
        },
    );
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 4096; 1x 1.20 s at load 42, each
/// run on an instance of its own ([`Fresh`]; 252 ms at load 23.94 when the runs after the first
/// reused one).
#[test]
fn bounded_parity_verdicts_scale() {
    bounded_parity_verdicts(4096, false);
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 4096; 1x 1.21 s at load 42, each
/// run on an instance of its own ([`Fresh`]; 253 ms at load 23.94 when the runs after the first
/// reused one).
#[test]
fn bounded_parity_verdicts_with_an_excluded_integer_scale() {
    bounded_parity_verdicts(4096, true);
}

/// The diagonal parity answer is kept with each instance, so a thread that decided the same
/// group first does not make the first decision on this thread cheaper: here the inputs of size
/// `n` are decided on another thread before the first runs, and the first runs still take
/// work in the size of the constraints (item GSX-unsolved, I6.7). Sizes 10 and 80 are this
/// test's own.
///
/// Size (TEST-bench-move-l0123, author P169): left at n 10: the work does not grow with
/// n (3.7 µs and 4.0 µs, 19,711 and 20,180 instructions, at n and 8n, load 24.28), so no n
/// brings the 1x near 0.5 s.
#[test]
fn bounded_empty_parity_decided_on_another_thread_costs_the_same_here() {
    let n = 10;
    // The type decided there is kept alive, and with it its group, which this thread's inputs
    // share.
    let _decided = std::thread::spawn(move || {
        let t = bounded_parity(n, n - 1, None);
        assert_eq!(t.verdict(), Verdict::Empty);
        t
    })
    .join()
    .unwrap();
    let inputs = scaling::inputs(n, |k| bounded_parity(k, k - 1, None));
    scaling::check_order(
        "diagonal parity decided on another thread first",
        n,
        1,
        |k| {
            Type::forget_emptiness();
            assert_eq!(inputs[&k].verdict(), Verdict::Empty);
        },
    );
}

/// Singleton count equations force every allowed symbol to occur evenly, so
/// the sum cannot be the required odd length. Inputs are built before timing.
///
/// Size (TEST-bench-move-l0123, author P169): left at n 9: the work does not grow with
/// n (5.0 µs and 5.1 µs, 20,629 and 20,823 instructions, at n and 8n, load 23.94), so no n
/// brings the 1x near 0.5 s.
#[test]
fn bounded_empty_parity_is_decided_in_the_size_of_the_constraints() {
    // Each instance keeps its diagonal answer while it lives, as it keeps its group's
    // judgment, so a test that built the same group on another thread cannot have decided
    // these inputs before their first runs.
    let n = 9;
    let inputs = scaling::inputs(n, |k| bounded_parity(k, k - 1, None));
    scaling::check_order("diagonal parity contradiction", n, 1, |k| {
        Type::forget_emptiness();
        assert_eq!(inputs[&k].verdict(), Verdict::Empty);
        assert!(inputs[&k].is_empty());
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 4096; 1x 1.05 s at load 42, each
/// run on an instance of its own ([`Fresh`]; 206 ms at load 23.70 when the runs after the first
/// reused one).
#[test]
fn bounded_parity_with_a_repeated_scalar_field_scales() {
    repeated_integer_field_scale(4096);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 262144; 1x 14 ms at load
/// 21.54. The 1x stays under 0.5 s because building the inputs takes most of the
/// wall time: at 2097152 the test passed the 25 s limit before its first run. The sets of
/// literals are built with `Type::union_all` (FAIL-setop-parity-bench-time): the evens at 8n
/// are joined in 1.46 s, where folding them with `|` took 7.66 s (load 33); the whole test now
/// takes 7 to 10 s at load 40.
#[test]
fn shared_integer_columns_scale_with_their_written_dag() {
    shared_integer_columns_check(262144, false);
}

/// Distinct columns at `n` and `8n`. The check that a further finite field keeps the point the
/// first search checked is in `a_few_shared_integer_columns_are_inhabited`.
///
/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 65536; 1x 48 ms at load
/// 23.33. Not grown past 65536: peak memory there was 4.6 GB (measured), near the 6 GB
/// stop the resize brief sets.
#[test]
fn distinct_integer_columns_reuse_a_checked_point() {
    shared_integer_columns_check(65536, true);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 16384; 1x 56 ms at load
/// 22.11.
#[test]
fn shared_cofinite_boundaries_are_not_enumerated_per_row() {
    cofinite_rows_scale(16384);
}

/// A run of a parity benchmark on a [`Fresh`] leaves nothing that a later run on it finds: a
/// second run at one size does the counted work of the first (PROOF-bench-fresh-instance; the
/// proof is at [`Fresh`]).
#[test]
fn a_second_run_on_a_fresh_instance_does_the_work_of_the_first() {
    check_a_second_run_does_the_work_of_the_first(&|fresh| fresh.member());
}

/// The check of [`a_second_run_on_a_fresh_instance_does_the_work_of_the_first`], with `member`
/// giving each run the member it decides: two runs of the check of
/// [`parity_verdicts_scale_with_the_number_of_constraints`] at one size on one [`Fresh`], each on
/// a new thread, as `scaling::check` runs them, and their instructions and bytes within 1% of
/// each other (PROOF-bench-fresh-instance). One instance kept for both runs gave the second
/// about half the work of the first (FAIL-setop-parity-bench-time), so a memo a run leaves
/// where the next run finds it shows here.
fn check_a_second_run_does_the_work_of_the_first(member: &(dyn Fn(&Fresh) -> Type + Sync)) {
    const STACK: usize = 256 << 20;
    let k = 1024;
    let (group, meet) = parity_variant_group(k, 0, Some("Scale_"), false);
    let fresh = Fresh::new(group, meet);
    let mut meter = scaling::Meter::new();
    let mut run = || {
        meter.work(|| {
            scaling::on_a_thread(STACK, || {
                Type::forget_emptiness();
                assert_eq!(member(&fresh).verdict(), Verdict::Inhabited);
            })
        })
    };
    let (first, second) = (run(), run());
    let unit = meter.unit();
    eprintln!(
        "two runs on a fresh instance at {k}: {} and {} {unit}, {} and {} bytes",
        first.units, second.units, first.bytes, second.bytes
    );
    let within = |a: u64, b: u64| a.abs_diff(b) * 100 <= a.max(b);
    assert!(
        within(first.units, second.units) && within(first.bytes, second.bytes),
        "a second run at {k} differs from the first by more than 1%: {} and {} {unit}, {} and {} \
         bytes",
        first.units,
        second.units,
        first.bytes,
        second.bytes
    );
}

/// The exponent has n+1 decimal digits; the integer has far more than 2^n
/// digits. A checked point must keep those powers instead of expanding them. The types are
/// [`beside_a_large_power`]; small instance, with the check that each holds `(1,)`:
/// `cofinite_integer_points_beside_a_few_large_powers`.
///
/// Size (TEST-bench-move-l0123, author P169): left at n 8: the work does not grow with
/// n (34.6 µs and 36.2 µs, 89,533 and 93,312 instructions, at n and 8n, load 23.33), so no n
/// brings the 1x near 0.5 s.
#[test]
fn cofinite_integer_points_keep_large_powers_symbolic() {
    let n = 8;
    let inputs = scaling::inputs(n, beside_a_large_power);
    scaling::check_order(
        "a cofinite point beyond symbolic integer exclusions",
        n,
        1,
        |k| {
            Type::forget_emptiness();
            assert_eq!(inputs[&k].verdict(), Verdict::Inhabited);
        },
    );
}

/// The verdict on the product of `k` parity lists, at `k` and `8k`: `Inhabited`, found without
/// walking the product of the meet's `2^(k+1)` states (row VERDICT-fork-value). Small instance
/// `the_verdict_on_a_few_parity_lists_is_inhabited`.
#[test]
fn the_verdict_on_k_parity_lists_is_inhabited() {
    let n = 512;
    let meets = scaling::inputs(n, |k| Fresh::new(parity_meet_group(k), 2 * k + 2));
    scaling::check("the verdict on the product of k parity lists", n, |k| {
        Type::forget_emptiness();
        assert_eq!(meets[&k].member().verdict(), Verdict::Inhabited);
    });
}

//! The benchmarks of `x13.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `x13.rs`.

use super::*;

#[test]
fn e4b_scales() {
    // Input Θ(n). Neither of `nth_from_end(n)` and `nth_from_end(n + 1)` contains the other.
    // A chain of plain lists was walked once from each of its definitions, Θ(n²) in all.
    big(|| {
        let tag = AtomicUsize::new(0);
        scaling::check_order("E4b, by n", 64, 1, |n| {
            Type::forget_emptiness();
            let tag = format!("_{}", tag.fetch_add(1, Relaxed) + 1);
            let (a, b) = (nth_from_end_named(n, &tag), nth_from_end_named(n + 1, &tag));
            assert!(!a.subtype(&b) && !b.subtype(&a));
        })
    });
}

#[test]
fn the_union_of_nth_from_end_is_built_in_its_size() {
    // The input is Θ(n²) definitions; the build reads each once.
    big(|| {
        let ((n, m), tag) = (NTH_SIZES, AtomicUsize::new(0));
        let build = |k: usize| {
            black_box(nth_pair(k, &format!("_b{}", tag.fetch_add(1, Relaxed) + 1)));
        };
        let (small, large) = (nth_pair_size(n), nth_pair_size(m));
        assert!((8.0..8.1).contains(&(large as f64 / small as f64)));
        scaling::compare(
            &format!("the nth union built: n {n} and {m}, {small} and {large} definitions"),
            1,
            || build(n),
            || build(m),
        );
    });
}

#[test]
fn the_union_of_nth_from_end_is_decided_in_its_size() {
    // `t <: t | nth_from_end(n + 1)` holds, and the converse does not: a list of `n + 1`
    // integers that starts with 1 is in `nth_from_end(n + 1)` alone. Each run decides a pair
    // built before any run is timed, under its own tag.
    big(|| {
        let (n, m) = NTH_SIZES;
        let (runs_small, runs_large) = scaling::Meter::new().runs();
        let pool = |k: usize, runs: usize| {
            let pairs = (0..runs).map(|i| nth_pair(k, &format!("_{k}_{i}")));
            Mutex::new(pairs.collect::<Vec<_>>())
        };
        let (small_pairs, large_pairs) = (pool(n, runs_small), pool(m, runs_large));
        let decide = |pairs: &Mutex<Vec<(Type, Type)>>| {
            let (t, v) = pairs
                .lock()
                .expect("the pool of pairs")
                .pop()
                .expect("one pair per run");
            Type::forget_emptiness();
            assert!(t.subtype(&v));
            assert!(!v.subtype(&t));
        };
        let (small, large) = (nth_pair_size(n), nth_pair_size(m));
        scaling::compare(
            &format!("the nth union decided: n {n} and {m}, {small} and {large} definitions"),
            1,
            || decide(&small_pairs),
            || decide(&large_pairs),
        );
    });
}

#[test]
fn the_choice_chain_scales() {
    // Input Θ(d²): power 2 in d. The build alone at d = 23 took more than 60 s.
    big(|| {
        scaling::check_order("the choice chain, built and compared, by d", 23, 2, |d| {
            Type::forget_emptiness();
            assert!(mux(d).equiv(&mux2(d)));
        })
    });
}

#[test]
fn the_choice_chain_with_a_choice_swapped_scales() {
    big(|| {
        // The rows fix their column to one of `SHAPES` values, each giving the hash-consed
        // nodes another random shape, so the work at each size is summed over the shapes.
        const SHAPES: i64 = 8;
        scaling::check_order("the choice chain against a swapped one, by d", 4, 2, |d| {
            for v in 1..=SHAPES {
                Type::forget_emptiness();
                assert!(!mux_at(d, v).equiv(&swapped_at(d, v)));
            }
        })
    });
}

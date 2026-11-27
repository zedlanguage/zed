//! Copying, comparing, writing the `Debug` text of, displaying and breaking a deep term are
//! linear in its depth (COMPLEXITY.md K39): the benchmarks of `deep.rs`, run by
//! `tools/run_tests.sh --bench`. What each run asserts, that two builds and a DAG compare equal,
//! is checked 100,000 deep by `stack::a_term_far_deeper_than_the_stack_copies_compares_and_prints`,
//! `stack::equal_dags_compare_once_per_shared_pair` and
//! `stack::a_term_far_deeper_than_the_stack_is_displayed_and_broken`.

use zed_kernel::print::pretty;
use zed_tests::scaling;

use crate::deep::{NESTED, dag, indents, nested, printed};

/// One test for each term of `nested`, each copying, comparing and writing the `Debug` text of
/// it, and one for the DAG (TEST-bench-replay-sweep). Until then the four terms and the DAG were
/// one test of 13 checks, 9.8 s at load 39: on a count of instructions the run at 8n of each
/// check runs in a new process of the test binary, which runs the test from its start and
/// replays each earlier check at both sizes (`scaling::compare_by`; `on_small_stack` keeps the
/// test's thread name, so its checks are replayed too), so 13 checks in one test ran
/// 13 · 14 / 2 = 91 checks' runs where 13 do. Now a test of a term runs 1 + 2 + 3 = 6 and the
/// DAG's test 1, 25 in all. The terms, sizes and checks are as before. Each test builds its own
/// term alone (`crate::deep::NESTED`), in its process and in each process `compare_by` starts:
/// built all four in each, the four tests took 4.5 to 4.9 s each at load 4.2 on the VM of
/// b22-tests6 on 2026-11-22, where the DAG's test, which builds the DAG alone, took 0.7 s.
///
/// Skipping the replay in the child process instead was ruled out: the child would then
/// measure each check after no earlier check had run in its process, where the run at n,
/// measured in the test's own process, comes after them, so state they leave (memo tables,
/// interners, a warmed allocator) would differ between the two runs, which
/// TEST-scaling-cold-shared-memo (2936015a7) removed. Its test
/// `a_fixed_set_up_kept_by_the_process_passes_in_each_check_of_a_test`
/// (tests/src/scaling_tests.rs) fails without the replay: the second check's run at 8n would pay
/// a set-up the first check built, alone.
mod copying_comparing_and_printing_scale_with_size {
    use super::*;

    /// The names of the terms of `NESTED`, in their order: test `k` below times term `k`, and
    /// each test checks `NESTED` still lists exactly these, so a term added there fails until
    /// it is listed here and has a test.
    const TERMS: [&str; 4] = [
        "nested lambdas",
        "a left-nested sum",
        "nested `match` arms",
        "a nested tuple pattern",
    ];

    /// Copies, compares (with a second build) and writes the `Debug` text of term `k` of
    /// [`TERMS`] at depth 20,000 and 8 times that. Nested lambdas are not copied: a lambda
    /// holds its body shared (`Term::Lam(_, Shared)`), so the copy is one node at any depth,
    /// 1.059 times the work at 8n (TEST-bench-replay-sweep), a check of nothing that grows
    /// (BENCH-copy-nested-lambdas-flat). The other three terms hold their children in place,
    /// so their copies visit every level.
    fn case(k: usize) {
        let n = 20_000;
        let names = NESTED.map(|(what, _)| what);
        assert_eq!(names, TERMS, "the terms of NESTED");
        let (what, build) = NESTED[k];
        zed_tests::deep::on_small_stack(|| {
            let built = |m: usize| (build(m), build(m));
            let (small, large) = (built(n), built(scaling::FACTOR * n));
            let at = |m: usize| if m == n { &small } else { &large };
            if what != "nested lambdas" {
                scaling::check(&format!("copying {what}"), n, |m| {
                    drop(std::hint::black_box(at(m).0.clone()));
                });
            }
            scaling::check(&format!("comparing {what}"), n, |m| {
                let (a, b) = at(m);
                assert!(std::hint::black_box(a == b));
            });
            scaling::check(&format!("writing the Debug text of {what}"), n, |m| {
                std::hint::black_box(format!("{:?}", at(m).0));
            });
        });
    }

    #[test]
    fn nested_lambdas() {
        case(0);
    }

    #[test]
    fn a_left_nested_sum() {
        case(1);
    }

    #[test]
    fn nested_match_arms() {
        case(2);
    }

    #[test]
    fn a_nested_tuple_pattern() {
        case(3);
    }

    #[test]
    fn a_dag_of_shared_subterms() {
        let n = 20_000;
        zed_tests::deep::on_small_stack(|| {
            let (small, large) = (
                (dag(n), dag(n)),
                (dag(scaling::FACTOR * n), dag(scaling::FACTOR * n)),
            );
            scaling::check("comparing a DAG of shared subterms", n, |m| {
                let (a, b) = if m == n { &small } else { &large };
                assert!(std::hint::black_box(a == b));
            });
        });
    }
}

/// One test for each term of `nested` and `printed` (TEST-split-chkbub1-long), each displaying
/// and breaking it. Until then the ten terms were one test of 20 checks, which took 36 s at load
/// 39 and 23 s at load 17 in main-watch's runs of 2026-11-21 and 58.6 s alone at load 61, while
/// its 40 measured runs at n and 8n added up to 11.1 s: on a count of instructions the run at 8n
/// of each check runs in a new process of the test binary, which runs the test from its start
/// and replays each earlier check at both sizes (`scaling::compare_by`; `on_small_stack` keeps
/// the test's thread name, so its checks are replayed too), so 20 checks in one test ran
/// 20 · 21 / 2 = 210 checks' runs where 20 do. Now a test runs 3 (its break check replays its
/// display check). The terms, sizes, widths and checks are as before.
mod displaying_and_breaking_scale_with_depth {
    use super::*;

    /// The names of the terms of `nested` then `printed`, in their order: test `k` below times
    /// term `k`, and each test checks the generators still make exactly these, so a term added
    /// there fails until it is listed here and has a test.
    const TERMS: [&str; 11] = [
        "nested lambdas",
        "a left-nested sum",
        "nested `match` arms",
        "a nested tuple pattern",
        "nested `let` bodies",
        "nested `else` branches",
        "calls in head position",
        "nested negations",
        "nested indices",
        "a nested atom pattern",
        "nested rebinding `let`s",
    ];

    /// Displays and breaks term `k` of [`TERMS`] at depth 20,000 and 8 times that.
    fn case(k: usize) {
        let n = 20_000;
        zed_tests::deep::on_small_stack(|| {
            let built = |m: usize| nested(m).into_iter().chain(printed(m)).collect::<Vec<_>>();
            let (small, large) = (built(n), built(scaling::FACTOR * n));
            let names = small.iter().map(|(what, _)| *what).collect::<Vec<_>>();
            assert_eq!(names, TERMS, "the terms of nested and printed");
            let at = |m: usize| if m == n { &small[k].1 } else { &large[k].1 };
            let what = TERMS[k];
            scaling::check(&format!("displaying {what}"), n, |m| {
                std::hint::black_box(at(m).to_string());
            });
            let width = if indents(what) { usize::MAX } else { 80 };
            scaling::check(&format!("breaking {what} to width {width}"), n, |m| {
                std::hint::black_box(pretty(at(m), width));
            });
        });
    }

    #[test]
    fn nested_lambdas() {
        case(0);
    }

    #[test]
    fn a_left_nested_sum() {
        case(1);
    }

    #[test]
    fn nested_match_arms() {
        case(2);
    }

    #[test]
    fn a_nested_tuple_pattern() {
        case(3);
    }

    #[test]
    fn nested_let_bodies() {
        case(4);
    }

    #[test]
    fn nested_else_branches() {
        case(5);
    }

    #[test]
    fn calls_in_head_position() {
        case(6);
    }

    #[test]
    fn nested_negations() {
        case(7);
    }

    #[test]
    fn nested_indices() {
        case(8);
    }

    #[test]
    fn a_nested_atom_pattern() {
        case(9);
    }

    #[test]
    fn nested_rebinding_lets() {
        case(10);
    }
}

//! Copying, comparing, writing the `Debug` text of, displaying and breaking a deep term are
//! linear in its depth (COMPLEXITY.md K39): the benchmarks of `deep.rs`, run by
//! `tools/run_tests.sh --bench`. What each run asserts, that two builds and a DAG compare equal,
//! is checked 100,000 deep by `deep::a_term_far_deeper_than_the_stack_copies_compares_and_prints`,
//! `deep::equal_dags_compare_once_per_shared_pair` and
//! `deep::a_term_far_deeper_than_the_stack_is_displayed_and_broken`.

use zed_kernel::print::pretty;
use zed_tests::scaling;

use crate::deep::{dag, indents, nested, printed};

#[test]
fn copying_comparing_and_printing_scale_with_size() {
    let n = 20_000;
    zed_tests::deep::on_small_stack(|| {
        let built = |k: usize| (nested(k), nested(k));
        let (small, large) = (built(n), built(8 * n));
        let at = |k: usize| if k == n { &small } else { &large };
        for i in 0..small.0.len() {
            let what = small.0[i].0;
            scaling::check(&format!("copying {what}"), n, |k| {
                drop(std::hint::black_box(at(k).0[i].1.clone()));
            });
            scaling::check(&format!("comparing {what}"), n, |k| {
                let (a, b) = at(k);
                assert!(std::hint::black_box(a[i].1 == b[i].1));
            });
            scaling::check(&format!("writing the Debug text of {what}"), n, |k| {
                std::hint::black_box(format!("{:?}", at(k).0[i].1));
            });
        }
        let (small, large) = ((dag(n), dag(n)), (dag(8 * n), dag(8 * n)));
        scaling::check("comparing a DAG of shared subterms", n, |k| {
            let (a, b) = if k == n { &small } else { &large };
            assert!(std::hint::black_box(a == b));
        });
    });
}

#[test]
fn displaying_and_breaking_scale_with_depth() {
    let n = 20_000;
    zed_tests::deep::on_small_stack(|| {
        let built = |k: usize| nested(k).into_iter().chain(printed(k)).collect::<Vec<_>>();
        let (small, large) = (built(n), built(8 * n));
        let at = |k: usize| if k == n { &small } else { &large };
        for (i, (what, _)) in small.iter().enumerate() {
            scaling::check(&format!("displaying {what}"), n, |k| {
                std::hint::black_box(at(k)[i].1.to_string());
            });
            let width = if indents(what) { usize::MAX } else { 80 };
            scaling::check(&format!("breaking {what} to width {width}"), n, |k| {
                std::hint::black_box(pretty(&at(k)[i].1, width));
            });
        }
    });
}

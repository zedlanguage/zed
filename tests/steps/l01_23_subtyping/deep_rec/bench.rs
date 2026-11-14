//! The benchmarks of `deep_rec.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `deep_rec.rs`.

use super::*;

#[test]
fn copying_comparing_writing_and_checking_scale_with_depth() {
    let n = 20_000;
    zed_tests::deep::on_small_stack(|| {
        let (small, large) = (
            (nested(n, int), nested(n, int)),
            (nested(8 * n, int), nested(8 * n, int)),
        );
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
            // The copy is linear, timed above.
            scaling::check(&format!("checking a body of {what}"), n, |k| {
                assert!(Group::new(vec![def(at(k).0[i].1.clone())]).is_ok());
            });
        }
    });
}

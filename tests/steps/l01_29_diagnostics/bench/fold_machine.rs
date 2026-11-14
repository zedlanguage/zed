//! `n` powers folded or refused, at `n` and `8n` (`fold_machine.rs`).

use zed_tests::scaling;

use crate::fold_machine::{built, powers};

#[test]
fn folding_many_powers_scales() {
    let n = 410;
    let inputs = scaling::inputs(n, |k| powers(k, "2^10"));
    scaling::check("n powers within the fold's bound, each folded", n, |k| {
        assert_eq!(built(&inputs[&k]), None);
    });
}

#[test]
fn refusing_many_folds_scales() {
    let n = 260;
    let inputs = scaling::inputs(n, |k| powers(k, "2^40"));
    scaling::check("n powers past the fold's bound, each refused", n, |k| {
        assert!(built(&inputs[&k]).is_some());
    });
}

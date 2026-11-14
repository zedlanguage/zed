//! Rung 2 on a chain of `k` and `8k` bit ands (plan row RUNG2-bit).

use std::sync::Arc;

use zed_tests::scaling;
use zedc::store::preimage::relations;
use zedc::store::presburger::{Entailment, entails};

use super::super::rung2::{chain, signs};

#[test]
fn a_chain_of_bit_ands_is_proved_in_linear_time() {
    // Complexity: each `bitAnd` is one auxiliary variable and one disjunction of four cases
    // (O(1) to translate); the premise fixes every sign, so one case of each is left.
    let n = 600;
    let built = scaling::inputs(n, |k| (signs(k), chain(k)));
    let inputs = scaling::inputs(n, |k| {
        (0..=k)
            .map(|i| Arc::<str>::from(format!("x{i}")))
            .collect::<Vec<_>>()
    });
    let measure = move || {
        scaling::check("a chain of bit ands proved by rung 2", n, |k| {
            let (p, g) = &built[&k];
            let rs = relations(&[p, g], &inputs[&k], true).expect("in the domain");
            assert_eq!(rs[1].bit_ands.len(), k);
            let e = entails(&rs[0], &rs[1]);
            assert!(matches!(e, Entailment::Proved(_)), "{e}");
        });
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

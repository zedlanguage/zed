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
    // This also checks that the renaming tells the chain's atoms apart: where it does not
    // (`Renamed::colored` listing each constraint once, eea76fee4 to the fix of
    // FAIL-rung2-bit-ands-regress-eea76fee4), the formula is tied and settled by
    // `settle_tied`, O(k^2): 65.8 times from 75 to 600 and 67 to 71 GB at 4800. With the
    // second coloring, by each constraint's count of places, 8.36 times at 600 to 4800 (8.40G
    // instructions, 1.70 GB at 4800).
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
    scaling::on_a_stack(8 << 20, measure);
}

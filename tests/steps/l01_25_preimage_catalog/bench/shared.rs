//! The preimage of `n` levels of `if` on `2^n` paths, at `n` and `8n`: each shared level is
//! numbered and transferred once. `shared.rs` checks the same terms at depths up to 10.

use std::collections::HashMap;

use zed_kernel::Shared;
use zed_tests::scaling;
use zedc::store::preimage::{Demand, preimage};

use crate::doms;
use crate::shared::levels;

/// The preimage of a term of `n` levels on `2^n` paths takes time of `n`: each shared level is
/// numbered and transferred once. The terms are built before the timing.
#[test]
fn shared_levels_scale_with_the_distinct_parts() {
    let n = 64;
    let terms: HashMap<usize, Shared> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|d| (d, levels(d, 0)))
        .collect();
    let ds = doms(&[("i", None, None)]);
    scaling::check(
        "the preimage of `n` levels of `if`, each level's branches one shared subterm",
        n,
        |d| {
            preimage(&terms[&d], &ds, &Demand::Bool(true));
        },
    );
}

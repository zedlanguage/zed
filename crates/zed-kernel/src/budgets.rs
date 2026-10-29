//! The verification ladder's budgets and the bounded-model instance (DESIGN.md
//! sec:verification, fixed by step M0.10).
//!
//! The grade an obligation reaches is a function of the source and these constants, the same
//! in every compiler, so each budget is per obligation and counted in a quantity the source
//! determines: bindings, e-graph iterations and e-nodes, never time or memory.

use std::ops::RangeInclusive;

/// Rung 1 (and the enumeration that interval revision and the preimage catalog share,
/// sec:domains): an obligation whose binder domains have at most this many bindings in their
/// product is enumerated in full and its proposition run at each.
pub const ENUMERATION_BUDGET: u64 = 4_096;

/// Rung 6: an integer binder's domain is cut to this interval.
pub const BMC_INT: RangeInclusive<i64> = -8..=8;

/// Rung 6: a sequence binder ranges over the sequences of at most this length.
pub const BMC_SEQ_LEN: usize = 4;

/// Rung 6: a loop or `gen` runs at most this many generations.
pub const BMC_GENERATIONS: usize = 16;

/// Rung 6: a float binder ranges over these values: both zeros, which compare equal under
/// IEEE `==` but are different values, the three decimals whose sum shows double rounding,
/// both infinities, and a NaN.
pub const BMC_FLOATS: [f64; 9] = [
    0.0,
    -0.0,
    1.0,
    0.1,
    0.2,
    0.3,
    f64::INFINITY,
    f64::NEG_INFINITY,
    f64::NAN,
];

/// Rung 6: the most bindings of the cut instance that are run, visited in shortlex order
/// (shorter sequences first, then by the domain order of each binder in turn); an instance
/// with more is checked on that prefix, and the grade records the prefix run.
pub const BMC_BUDGET: u64 = 65_536;

/// Rung 3: the most saturation iterations of the e-graph.
pub const SATURATION_ITERATIONS: u32 = 8;

/// Rung 3: saturation stops before an iteration would leave the e-graph above this many
/// e-nodes, whichever of the two bounds comes first.
pub const SATURATION_NODES: u64 = 10_000;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_float_instance_has_nine_distinct_values() {
        let mut bits: Vec<u64> = BMC_FLOATS.iter().map(|x| x.to_bits()).collect();
        bits.sort();
        bits.dedup();
        assert_eq!(bits.len(), 9);
        assert!(BMC_FLOATS.iter().any(|x| x.is_nan()));
    }

    #[test]
    fn the_cut_instance_fits_the_budgets() {
        let ints = BMC_INT.count() as u64;
        assert_eq!(ints, 17);
        // One sequence binder over the cut integers has 88,741 values, more than the rung 6
        // budget, so its length-4 sequences are visited only in part.
        let seqs: u64 = (0..=BMC_SEQ_LEN as u32).map(|n| ints.pow(n)).sum();
        assert_eq!(seqs, 88_741);
        assert!(seqs > BMC_BUDGET);
        // Three integer binders are enumerated in full at rung 6 but not at rung 1.
        assert!(ints.pow(3) <= BMC_BUDGET && ints.pow(3) > ENUMERATION_BUDGET);
    }
}

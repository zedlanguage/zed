//! A totally ordered set extended by the two infinities, for the ends of intervals and the
//! bounds of a propagation (DRY-ext-ends-2026-11-26, algebra-text-hash.md group A9).
//!
//! The derived order is the order wanted: variants compare by their place in the declaration
//! first, and two `Fin` by their payloads, so `NegInf < Fin(x) < PosInf` for every `x` and
//! `Fin(x) < Fin(y)` exactly when `x < y`. That is a total order when the payload's is, and it is
//! the order of the extended line when the payload's order is the order of its values: an
//! encoding moves onto this type only when its payload is such a plain ordered value. The
//! encodings kept apart, each with its reason, are listed in the row's note in
//! `docs/plan_dag.md`.

/// A value of `T`, or one of the infinities below and above every value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Ext<T> {
    /// Below every value.
    NegInf,
    /// A value.
    Fin(T),
    /// Above every value.
    PosInf,
}

#[cfg(test)]
mod tests {
    use super::Ext::{self, Fin, NegInf, PosInf};

    /// The derived order against the definition, on every pair of a small set of ends.
    #[test]
    fn the_infinities_are_below_and_above_every_value() {
        let ends: Vec<Ext<(i32, i32)>> = [NegInf, PosInf]
            .into_iter()
            .chain((-2..=2).flat_map(|s| (-2..=2).map(move |k| Fin((s, k)))))
            .collect();
        let rank = |e: &Ext<(i32, i32)>| match e {
            NegInf => (0, (0, 0)),
            Fin(v) => (1, *v),
            PosInf => (2, (0, 0)),
        };
        for a in &ends {
            for b in &ends {
                assert_eq!(a.cmp(b), rank(a).cmp(&rank(b)), "{a:?} against {b:?}");
            }
        }
    }
}

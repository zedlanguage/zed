//! The row of a [`crate::hull::Hull`], an integer affine form, as a trait: its own module, so that
//! `hull.rs` and `hull/rows.rs` both read it here and neither imports the other back (test
//! `s_01f_import_graph::no_crate_has_an_import_cycle_but_the_known_ones`).

use std::collections::BTreeMap;
use std::fmt;
use std::hash::Hash;

use zedc_int::int::Int;

/// An integer affine form `Σ c·x + k`, a row of a [`crate::hull::Hull`]: its terms, none of
/// them zero, and its constant. zedc-presburger's `Lin` is one.
pub trait Form: Clone + Default + PartialEq + fmt::Debug {
    /// The variables, the pivots of the rows. A pivot's priority in the treap of rows is a hash
    /// of it, so it is `Hash`.
    type Atom: Ord + Clone + Hash + fmt::Debug;
    /// The coefficients, none zero.
    fn terms(&self) -> &BTreeMap<Self::Atom, Int>;
    /// The constant.
    fn constant(&self) -> &Int;
    /// The coefficients and the constant, to change.
    fn parts_mut(&mut self) -> (&mut BTreeMap<Self::Atom, Int>, &mut Int);
}

#[cfg(test)]
pub(crate) mod tests {
    use std::collections::BTreeMap;
    use std::sync::Arc;

    use zedc_int::int::Int;

    use super::Form;

    /// A form for the tests: terms by name and a constant.
    #[derive(Clone, PartialEq, Eq, Debug, Default)]
    pub(crate) struct Lin {
        pub(crate) terms: BTreeMap<Arc<str>, Int>,
        pub(crate) constant: Int,
    }

    impl Form for Lin {
        type Atom = Arc<str>;
        fn terms(&self) -> &BTreeMap<Arc<str>, Int> {
            &self.terms
        }
        fn constant(&self) -> &Int {
            &self.constant
        }
        fn parts_mut(&mut self) -> (&mut BTreeMap<Arc<str>, Int>, &mut Int) {
            (&mut self.terms, &mut self.constant)
        }
    }
}

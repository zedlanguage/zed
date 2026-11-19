//! A formula of the class of the module above, read into numbers, and the greatest common
//! divisor both its methods use: the join of row sums (the module above) and the polygons of
//! [`super::plane`] read it, so it lies in a file of its own that imports neither, and the
//! imports of the three files form no cycle (S1F-row-sums-plane-cycle).

use super::super::formula::Atom;

/// A row `Σ c·y + k`, `== 0` or `>= 0`, over the atoms' indices.
pub(super) struct Row {
    pub(super) terms: Vec<(usize, i128)>,
    pub(super) k: i128,
    pub(super) eq: bool,
}

/// A formula of the class the module note of `row_sums` names, read into numbers.
pub(in crate::presburger) struct Rows {
    pub(super) atoms: Vec<Atom>,
    /// Each atom's values: sorted ranges, disjoint and not adjacent.
    pub(super) domains: Vec<Vec<(i128, i128)>>,
    pub(super) rows: Vec<Row>,
    /// Some conjunct has no point.
    pub(super) empty: bool,
}

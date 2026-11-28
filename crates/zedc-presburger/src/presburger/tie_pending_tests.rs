//! The swap checks of an equality's tied pivots read the definitions not yet written into the
//! rows (`Omega::pending`), item PRES-tie-symmetry-pending: [`Omega::pending_swaps_onto_itself`]
//! in [`Omega::equality`] and in [`Omega::pivot_swaps`].
//!
//! Each test starts from the rows `x0 >= 0`, `x1 >= 0`, `x2 >= 0`, `x3 >= 0` over four
//! variables of one color, which the swap of `x1` and `x2` maps onto themselves. The
//! variable `x0` is then made pending with a definition: written in, the row `x0 >= 0`
//! becomes that definition `>= 0`, so the swap maps the written rows onto themselves exactly
//! when it maps the definition onto itself.

use super::*;

/// `Σ c·x[v] + k` over the terms `a`.
fn row(a: &[(usize, i64)], k: i64) -> Row {
    let a: Vec<Term> = a.iter().map(|&(v, c)| (v, Int::from(c))).collect();
    Row {
        a: a.into(),
        k: Int::from(k),
    }
}

/// The four rows `x[i] >= 0` and the definitions `defs` pending.
fn omega(defs: &[(usize, Row)]) -> Omega {
    let base: Vec<(Row, Rel)> = (0..4).map(|i| (row(&[(i, 1)], 0), Rel::Ge)).collect();
    let mut o = Omega::new(&[0; 4], &base, true);
    assert!(
        o.sys.swaps_onto_itself(1, 2),
        "the rows are symmetric in x1 and x2"
    );
    o.pending.extend(defs.iter().cloned());
    o
}

/// `x1 + x2 + 2·x3 == 0`, whose pivots `x1` and `x2` tie.
fn tied_equality() -> Row {
    row(&[(1, 1), (2, 1), (3, 2)], 0)
}

#[test]
fn a_definition_that_holds_one_swapped_variable_refuses_the_swap() {
    // `x0 = x1 + 1`: written in, `x1 + 1 >= 0` has no image `x2 + 1 >= 0` among the rows, so
    // the swap is not a symmetry, though the rows held (`x0 >= 0` among them) are symmetric.
    let o = omega(&[(0, row(&[(1, 1)], 1))]);
    assert!(!o.pending_swaps_onto_itself(1, 2));
    assert!(o.pivot_swaps(&tied_equality(), &[1, 2], |_| true).is_none());
}

#[test]
fn two_definitions_that_the_swap_exchanges_refuse_the_swap() {
    // `x0 = x1 + 1` and `x3 = x2 + 1`: the swap maps one onto the other, but it fixes `x0`
    // and `x3`, so it maps neither onto itself.
    let o = omega(&[(0, row(&[(1, 1)], 1)), (3, row(&[(2, 1)], 1))]);
    assert!(!o.pending_swaps_onto_itself(1, 2));
    assert!(o.pivot_swaps(&tied_equality(), &[1, 2], |_| true).is_none());
}

#[test]
fn a_definition_symmetric_in_the_swapped_variables_keeps_the_swap() {
    // `x0 = x1 + x2 - 3`: the swap maps it onto itself, so the written rows too. Before item
    // PRES-tie-symmetry-pending, `pivot_swaps` refused any pivot a pending definition held.
    let o = omega(&[(0, row(&[(1, 1), (2, 1)], -3))]);
    assert!(o.pending_swaps_onto_itself(1, 2));
    assert_eq!(
        o.pivot_swaps(&tied_equality(), &[1, 2], |_| true),
        Some(vec![vec![(1, 2), (2, 1)]])
    );
}

#[test]
fn a_definition_at_different_coefficients_refuses_the_swap() {
    // `x0 = x1 + 2·x2`: both swapped variables, at different coefficients.
    let o = omega(&[(0, row(&[(1, 1), (2, 2)], 0))]);
    assert!(!o.pending_swaps_onto_itself(1, 2));
    assert!(o.pivot_swaps(&tied_equality(), &[1, 2], |_| true).is_none());
}

/// The step [`Omega::equality`] on `x1 + x2 + 2·x3 == 0` among the four rows, with `defs`
/// pending: whether it took the tie of `x1` and `x2` (`Ok`) or refused it.
fn equality_step(defs: &[(usize, Row)]) -> Result<(), Tied> {
    let mut base: Vec<(Row, Rel)> = (0..4).map(|i| (row(&[(i, 1)], 0), Rel::Ge)).collect();
    base.push((tied_equality(), Rel::Eq));
    let mut o = Omega::new(&[0; 4], &base, true);
    assert!(
        o.sys.swaps_onto_itself(1, 2),
        "the rows are symmetric in x1 and x2"
    );
    let s = (o.es.rows.iter())
        .position(Option::is_some)
        .expect("the equality is held");
    o.pending.extend(defs.iter().cloned());
    o.equality(s)
}

#[test]
fn the_equality_step_reads_the_pending_definitions() {
    // The control: with nothing pending the swap maps the system onto itself and the tie is
    // taken. Then `x0 = x1 + 1` pending: the rows and the equalities alone are still
    // symmetric, and before item PRES-tie-symmetry-pending the tie was taken here too.
    assert!(equality_step(&[]).is_ok());
    let t = equality_step(&[(0, row(&[(1, 1)], 1))]).expect_err("the swap changes x0's value");
    assert_eq!(t.vars, [1, 2]);
    assert!(equality_step(&[(0, row(&[(1, 1), (2, 1)], -3))]).is_ok());
}

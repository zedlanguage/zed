//! The benchmarks of `by_halves_against_old`, run by `tools/run_tests.sh --bench` and left out
//! of its default run. Their small instance is
//! `batch_and_single_hulls_are_exact_on_a_chain_of_sums`, which checks the answers.

use super::*;
use crate::scaling;

/// The rows of [`linked_copies`] without its disjunctions: one linked group of `9n` symbols.
fn linked_rows(n: usize) -> (Vec<Con>, Vec<Atom>, Model) {
    let (f, syms) = linked_copies(n);
    let rows: Vec<Con> = (f.conjuncts().iter())
        .filter_map(|c| match c {
            Formula::Con(c) => Some(c.clone()),
            _ => None,
        })
        .collect();
    let model = solve(&rows, true)
        .expect("solve answers")
        .expect("the rows hold");
    (rows, syms, model)
}

/// The hulls of the symbols of one linked group are found by projecting its rows onto all of
/// them together ([`projected_hulls`], FAIL-batch-linked-copies-growth), in work near linear in
/// the number of copies; asking each symbol of the whole group ([`hull_from`]) was quadratic.
#[test]
fn hulls_of_linked_copies_are_projected_in_linear_work() {
    let inputs = scaling::inputs(40, linked_rows);
    scaling::check_order("hulls of linked copies, projected together", 40, 1, |n| {
        let (rows, syms, model) = &inputs[&n];
        let ks: Vec<&Atom> = syms.iter().collect();
        let hulls = projected_hulls(rows.clone(), &ks, model, &KnownSides::new());
        assert_eq!(hulls.len(), 9 * n);
        assert!(hulls.values().all(|h| h.is_ok()));
    });
}

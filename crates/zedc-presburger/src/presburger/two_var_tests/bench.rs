//! The benchmark of `two_var_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run. The correctness test that keeps small instances of it is
//! `chains_of_unit_equalities_project_exactly_in_either_order`.

use super::*;
use crate::scaling;

/// [`two_var_domains`] on [`chain`] with `e` equalities, given in order: each substitution
/// meets the two rows that hold its atom, O(e log e) in all (the work list and the rows that
/// hold each atom, comment at the elimination in `two_var_domains`). Before, each read every
/// row, O(e²).
#[test]
fn a_chain_of_unit_equalities_scales() {
    let inputs = scaling::inputs(N_CHAIN, |e| chain(e, false));
    let sym = [xa(0)];
    scaling::check_order(
        "a chain of unit equalities in two_var_domains",
        N_CHAIN,
        1,
        |e| {
            let (each, _) = two_var_domains(&inputs[&e], &sym).expect("two_var_domains answers");
            assert_eq!(each[0].as_ref().expect("a domain"), &expected(e));
        },
    );
}

/// [`two_var_domains`] on [`chain`] with `e` equalities and every one of its `e + 1` symbols
/// asked, at `e` and `8e` (row PERF-twovar-elim-per-arm: the elimination ran once per arm and
/// symbol, O(s e log e) for `s` symbols). `x_i` takes `e - i..=e - i + 100`.
#[test]
fn a_chain_of_unit_equalities_with_every_symbol_asked_scales() {
    let inputs = scaling::inputs(N_EVERY, |e| chain(e, false));
    scaling::check(
        "a chain of unit equalities, every symbol asked",
        N_EVERY,
        |e| {
            let syms: Vec<Atom> = (0..=e).map(xa).collect();
            let (each, _) = two_var_domains(&inputs[&e], &syms).expect("two_var_domains answers");
            for (i, got) in each.iter().enumerate() {
                let want =
                    IntervalSet::range(End::of((e - i) as i64), End::of((e - i) as i64 + 100));
                assert_eq!(got.as_ref().expect("a domain"), &want, "x{i}");
            }
        },
    );
}

/// The size of [`a_chain_of_unit_equalities_with_every_symbol_asked_scales`].
const N_EVERY: usize = 125;

/// The size of [`a_chain_of_unit_equalities_scales`].
const N_CHAIN: usize = 2_000;

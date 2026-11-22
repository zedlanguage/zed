//! [`two_var_domains`] on formulas that reduce to two atoms by unit equalities (COMPLEXITY.md
//! row XR-l139-neon-r4): its answers on chains of equalities given in either order, and, in
//! [`bench`], its work as the number of equalities grows.

use super::*;

mod bench;

fn xa(i: usize) -> Atom {
    Atom::Sym(format!("x{i:06}").into())
}

fn x(i: usize) -> Lin {
    Lin::atom(xa(i))
}

/// `x_i == x_{i+1} + 1` for `i < e`, then `0 <= x_e <= 100`, with the equalities in reverse
/// order when `reverse`. The projection of `x_0` is `e..=e + 100`.
fn chain(e: usize, reverse: bool) -> Formula {
    let mut eqs: Vec<Formula> = (0..e)
        .map(|i| {
            let row = x(i).minus(&x(i + 1)).minus(&Lin::constant(1));
            Formula::Con(Con::eq(&row, &Lin::default()))
        })
        .collect();
    if reverse {
        eqs.reverse();
    }
    eqs.push(Formula::Con(Con::ge(&x(e), &Lin::default())));
    eqs.push(Formula::Con(Con::ge(
        &Lin::constant(100).minus(&x(e)),
        &Lin::default(),
    )));
    Formula::and(eqs)
}

/// The answer [`chain`] must get: `e..=e + 100`.
fn expected(e: usize) -> IntervalSet {
    IntervalSet::range(End::of(e as i64), End::of(e as i64 + 100))
}

#[test]
fn chains_of_unit_equalities_project_exactly_in_either_order() {
    for e in [1, 2, 5, 40] {
        for reverse in [false, true] {
            let f = chain(e, reverse);
            let (each, _) = two_var_domains(&f, &[xa(0)]).expect("two_var_domains answers");
            assert_eq!(each.len(), 1);
            assert_eq!(
                each[0].as_ref().expect("a domain"),
                &expected(e),
                "e = {e}, reverse = {reverse}"
            );
        }
    }
}

/// A chain whose last value is fixed by an equality of one atom, `2·x_e == 6`, and one with
/// no integer value, `2·x_e == 7`: the single-atom branch gives `x_e` its value or the empty
/// set.
#[test]
fn single_atom_equalities_fix_a_value_or_empty_the_domain() {
    for (k, answer) in [(6, Some(3 + 5)), (7, None)] {
        let mut parts: Vec<Formula> = (0..5)
            .map(|i| {
                let row = x(i).minus(&x(i + 1)).minus(&Lin::constant(1));
                Formula::Con(Con::eq(&row, &Lin::default()))
            })
            .collect();
        let two = x(5).plus(&x(5));
        parts.push(Formula::Con(Con::eq(&two, &Lin::constant(k))));
        parts.push(Formula::Con(Con::ge(&x(5), &Lin::default())));
        let (each, _) =
            two_var_domains(&Formula::and(parts), &[xa(0)]).expect("two_var_domains answers");
        let got = each[0].as_ref().expect("a domain");
        match answer {
            Some(v) => assert_eq!(got, &IntervalSet::single(v)),
            None => assert_eq!(got, &IntervalSet::empty()),
        }
    }
}

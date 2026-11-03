//! The Omega test at the rule of low complexity (DESIGN.md Part G). The solver is one loop, and
//! a step touches only the rows of the variable it removes, so the work follows the rows
//! rather than doubling with each variable: `chain(v, 3)` is solved by the dark shadow after one
//! test of the real shadow, and the empty `chain(v, 0)` and `rising(v)` are shown empty by that
//! test alone. Each formula is built before it is timed.

use std::sync::Arc;

use zed_tests::scaling;
use zedc::store::presburger::{Atom, Con, Formula, Lin, satisfiable};

fn x(i: usize) -> Lin {
    Lin::atom(Atom::Sym(Arc::from(format!("x{i}"))))
}

/// `3·x[i+1] >= 2·x[i] + 1` and `2·x[i] + k >= 3·x[i+1]` for `i < v`: no elimination is
/// exact, the chain has a point when `k >= 1`, and none when `k == 0`.
fn chain(v: usize, k: i128) -> Formula {
    let mut cons = Vec::new();
    for i in 0..v {
        let a = x(i).times(2).unwrap();
        let b = x(i + 1).times(3).unwrap();
        cons.push(Formula::Con(
            Con::ge(&b, &a.plus(&Lin::constant(1)).unwrap()).unwrap(),
        ));
        cons.push(Formula::Con(
            Con::ge(&a.plus(&Lin::constant(k)).unwrap(), &b).unwrap(),
        ));
    }
    Formula::and(cons)
}

/// `3·x[i] + 1 <= 2·x[i+1] <= 3·x[i] + 5` for `i < v`, `x[0] >= 0` and `x[v] <= 0`: empty,
/// since each `x[i+1]` is above `x[i]`, but no single step shows it.
fn rising(v: usize) -> Formula {
    let zero = Lin::constant(0);
    let mut cons = vec![
        Formula::Con(Con::ge(&x(0), &zero).unwrap()),
        Formula::Con(Con::ge(&zero, &x(v)).unwrap()),
    ];
    for i in 0..v {
        let a = x(i).times(3).unwrap();
        let b = x(i + 1).times(2).unwrap();
        cons.push(Formula::Con(
            Con::ge(&b, &a.plus(&Lin::constant(1)).unwrap()).unwrap(),
        ));
        cons.push(Formula::Con(
            Con::ge(&a.plus(&Lin::constant(5)).unwrap(), &b).unwrap(),
        ));
    }
    Formula::and(cons)
}

#[test]
fn chains_of_inexact_eliminations_are_answered() {
    for v in 1..=15 {
        let m = satisfiable(&chain(v, 3)).expect("answered");
        let m = m.unwrap_or_else(|| panic!("the chain of {v} has a point"));
        assert!(chain(v, 3).holds(&m), "{m:?}");
        assert_eq!(
            satisfiable(&chain(v, 0)),
            Ok(None),
            "the chain of {v} is empty"
        );
        assert_eq!(
            satisfiable(&rising(v)),
            Ok(None),
            "the rising chain of {v} is empty"
        );
    }
}

/// Times `satisfiable` on the formulas of `make` at `n` and 8n variables, built first, each
/// first checked to have a point or none as `point` says: a refusal would be quick and wrong.
fn scales(what: &str, n: usize, point: bool, make: impl Fn(usize) -> Formula) {
    let (small, large) = (make(n), make(scaling::FACTOR * n));
    for f in [&small, &large] {
        let found = satisfiable(f).expect("answered");
        assert_eq!(found.is_some(), point, "{what}");
    }
    scaling::check(what, n, |m| {
        let f = if m == n { &small } else { &large };
        drop(satisfiable(f));
    });
}

#[test]
fn a_chain_of_inexact_eliminations_with_a_point_scales() {
    scales("the chain with a point", 32, true, |v| chain(v, 3));
}

#[test]
fn an_empty_chain_scales() {
    scales("the empty chain", 256, false, |v| chain(v, 0));
}

#[test]
fn a_rising_chain_scales() {
    scales("the rising chain", 128, false, rising);
}

// A cost quadratic with a small constant stays below the limit at the sizes above and shows at
// these. Controls, each a patch to `crates/zedc/src/store/presburger.rs`, run on all six tests;
// COMPLEXITY.md, S18, has what each gave.
//
// Rows rescanned, in `System::take`, in place of `std::mem::take(&mut self.vars[j].rows)`:
//     let held = |a: &Coefs| a.binary_search_by_key(&j, |t| t.0).is_ok();
//     let ids: Vec<usize> = (0..self.ids.len())
//         .filter(|&id| self.ids[id].as_ref().is_some_and(held))
//         .collect();
//
// A row looked up by scanning, in `System::add`, in place of `self.rows.get_mut(&r.a)`:
//     if let Some((_, old)) = self.rows.iter_mut().find(|(a, _)| **a == r.a) {
//
// The rows copied at each elimination, as a step that builds its rows anew would, at the start
// of `System::eliminate`:
//     drop(self.rows.iter().map(|(a, r)| (a.to_vec(), r.k.clone())).collect::<Vec<_>>());
//
// Variables rescanned, in `System::best`: `self.exact.iter().rev().last()` for
// `self.exact.first()` and `self.inexact.iter().rev().last()` for `self.inexact.first()`.
//
// The real shadow tested at every inexact step, in `Omega::run`: `if inexact` for
// `if inexact && !dark`.

#[test]
fn a_long_chain_with_a_point_scales() {
    scales("the long chain with a point", 4096, true, |v| chain(v, 3));
}

#[test]
fn a_long_empty_chain_scales() {
    scales("the long empty chain", 2048, false, |v| chain(v, 0));
}

#[test]
fn a_long_rising_chain_scales() {
    scales("the long rising chain", 2048, false, rising);
}

//! The Omega test at the rule of low complexity (DESIGN.md Part G). The solver is one loop, and
//! a step touches only the rows of the variable it removes, so the work follows the rows
//! rather than doubling with each variable: `chain(v, 3)` is solved by the dark shadow after one
//! test of the real shadow, and the empty `chain(v, 0)` and `rising(v)` are shown empty by that
//! test alone. Each formula is built before it is timed.

use std::sync::Arc;

use zed_tests::scaling;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Refusal, decide, satisfiable};

fn x(i: usize) -> Lin {
    Lin::atom(Atom::Sym(Arc::from(format!("x{i}"))))
}

/// `3·x[i+1] >= 2·x[i] + 1` and `2·x[i] + k >= 3·x[i+1]` for `i < v`: no elimination is
/// exact, the chain has a point when `k >= 1`, and none when `k == 0`.
fn chain(v: usize, k: i128) -> Formula {
    let mut cons = Vec::new();
    for i in 0..v {
        let a = x(i).times(2);
        let b = x(i + 1).times(3);
        cons.push(Formula::Con(Con::ge(&b, &a.plus(&Lin::constant(1)))));
        cons.push(Formula::Con(Con::ge(&a.plus(&Lin::constant(k)), &b)));
    }
    Formula::and(cons)
}

/// `3·x[i] + 1 <= 2·x[i+1] <= 3·x[i] + 5` for `i < v`, `x[0] >= 0` and `x[v] <= 0`: empty,
/// since each `x[i+1]` is above `x[i]`, but no single step shows it.
fn rising(v: usize) -> Formula {
    let zero = Lin::constant(0);
    let mut cons = vec![
        Formula::Con(Con::ge(&x(0), &zero)),
        Formula::Con(Con::ge(&zero, &x(v))),
    ];
    for i in 0..v {
        let a = x(i).times(3);
        let b = x(i + 1).times(2);
        cons.push(Formula::Con(Con::ge(&b, &a.plus(&Lin::constant(1)))));
        cons.push(Formula::Con(Con::ge(&a.plus(&Lin::constant(5)), &b)));
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

/// `Σ c·x[i] + k >= 0` over the pairs `(i, c)`, with each `x[i]` moved by `shift(i)` when
/// `shifted`, so that neither the origin nor small values stay points.
fn row(t: &[(usize, i64)], k: i64, shifted: bool) -> Formula {
    let shift = |i: usize| ((i as i64 * 7919 + 13) % 2001) - 1000;
    let k = if shifted {
        k - t.iter().map(|(i, c)| c * shift(*i)).sum::<i64>()
    } else {
        k
    };
    let l = t
        .iter()
        .fold(Lin::constant(k), |l, (i, c)| l.plus(&x(*i).times(*c)));
    Formula::Con(Con::ge(&l, &Lin::constant(0)))
}

/// Three rows of three variables at each `i`, cyclically, shifted: the family on which Bland's
/// rule alone takes about 2^(0.7n) pivots. No elimination keeps the rows, so the answer is the
/// refusal [`Refusal::Growth`], given once the simplex finds the rational vertex and it is not
/// an integer point; the work is the simplex's.
fn sparse(n: usize) -> Formula {
    let mut r = Vec::new();
    for i in 0..n {
        let (a, b, c) = (i, (i + 1) % n, (i + 2) % n);
        r.push(row(&[(a, 2), (b, -3), (c, 1)], 5, true));
        r.push(row(&[(a, -3), (b, 1), (c, -2)], 5, true));
        r.push(row(&[(a, 1), (b, 2), (c, -3)], 5, true));
    }
    Formula::and(r)
}

/// `2n` rows `±x[a] ± x[b] + k >= 0`, shifted, with a point: decided by the parity test.
fn utvpi(n: usize) -> Formula {
    let mut r = Vec::new();
    for i in 0..2 * n {
        let a = (i * 37 + 11) % n;
        let mut b = (i * 53 + 5) % n;
        if a == b {
            b = (b + 1) % n;
        }
        let (ca, cb) = (
            if i % 3 == 0 { -1 } else { 1 },
            if i % 2 == 0 { -1 } else { 1 },
        );
        r.push(row(&[(a, ca), (b, cb)], (i % 4) as i64, true));
    }
    Formula::and(r)
}

/// `x[0] + x[1] == 1` and `x[i] == x[i+1]` around a cycle of `n`: the rational point `1/2`
/// and no integer point, shown by the parity of a zero-weight cycle.
fn odd_cycle(n: usize) -> Formula {
    let mut r = vec![
        row(&[(0, 1), (1, 1)], -1, false),
        row(&[(0, -1), (1, -1)], 1, false),
    ];
    for i in 1..n {
        r.push(row(&[(i, 1), ((i + 1) % n, -1)], 0, false));
        r.push(row(&[((i + 1) % n, 1), (i, -1)], 0, false));
    }
    Formula::and(r)
}

/// `n` disjoint copies of Pugh's example, shifted: each part has two variables and is decided
/// exactly, and each is empty.
fn pugh_pairs(n: usize) -> Formula {
    let mut r = Vec::new();
    for i in 0..n {
        let (a, b) = (2 * i, 2 * i + 1);
        r.push(row(&[(a, 11), (b, 13)], -27, true));
        r.push(row(&[(a, -11), (b, -13)], 45, true));
        r.push(row(&[(a, 7), (b, -9)], 10, true));
        r.push(row(&[(a, -7), (b, 9)], 4, true));
    }
    Formula::and(r)
}

/// Times `decide` on the formulas of `make` at `n` and 8n, built first, each first checked to
/// give `answer`.
fn decides(what: &str, n: usize, answer: Result<bool, Refusal>, make: impl Fn(usize) -> Formula) {
    let (small, large) = (make(n), make(scaling::FACTOR * n));
    for f in [&small, &large] {
        assert_eq!(decide(f), answer, "{what}");
    }
    scaling::check(what, n, |m| {
        let f = if m == n { &small } else { &large };
        let _ = std::hint::black_box(decide(f));
    });
}

#[test]
fn the_shifted_sparse_family_scales() {
    decides(
        "the shifted sparse family",
        128,
        Err(Refusal::Growth),
        sparse,
    );
}

#[test]
fn rows_of_two_unit_coefficients_scale() {
    decides("rows of two unit coefficients", 256, Ok(true), utvpi);
}

#[test]
fn an_odd_cycle_scales() {
    decides("an odd cycle", 256, Ok(false), odd_cycle);
}

#[test]
fn disjoint_two_variable_parts_scale() {
    decides(
        "disjoint copies of Pugh's example",
        256,
        Ok(false),
        pugh_pairs,
    );
}

/// `chain(n, 3)` joined at `x[n]` to a block of three rows of three variables at each of `m`
/// places around a cycle, shifted: the chain's dark eliminations come first, and the block
/// then has no elimination that keeps it, so the question is refused with
/// [`Refusal::Growth`]. The splinters of the chain's eliminations are not searched, since a
/// refused dark shadow leaves the answer refused whatever they hold; searching them ran the
/// test again once per elimination.
fn chain_into_block(n: usize) -> Formula {
    let m = 8;
    let mut r = vec![chain(n, 3)];
    for i in 0..m {
        let (a, b, c) = (n + i, n + (i + 1) % m, n + (i + 2) % m);
        r.push(row(&[(a, 2), (b, -3), (c, 1)], 5, true));
        r.push(row(&[(a, -3), (b, 1), (c, -2)], 5, true));
        r.push(row(&[(a, 1), (b, 2), (c, -3)], 5, true));
    }
    Formula::and(r)
}

#[test]
fn a_chain_into_a_refused_block_scales() {
    decides(
        "a chain into a refused block",
        64,
        Err(Refusal::Growth),
        chain_into_block,
    );
}

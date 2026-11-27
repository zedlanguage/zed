//! What the printer does inside, which its text alone does not show (round 3 of
//! XR-lazy-and-kernel-batch-1, Codex C3 and Gemini C-3, Claude C-4): the updates that pass an env
//! over (`dag::Builder::update`, Codex C6) and the walks of `LetReads` (Codex D3). The tests of
//! the text are in tests/steps/l01_28_staging/print.rs.

use std::cell::RefCell;
use std::collections::HashSet;
use std::sync::Arc;

use super::{Doc, PLAIN, Piece, dag};
use crate::term::build::{lit, var};
use crate::term::{Prim, Shared, Term};

thread_local! {
    /// The `let` each walk of `LetReads::walk` starts from, in order.
    pub(super) static WALKED_FROM: RefCell<Vec<*const Term>> = const { RefCell::new(Vec::new()) };
    /// The env each update passes over, in order (`dag::Builder::update`).
    pub(super) static PASSED: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
    /// The name of each binder an update passes over whose slot it has set already, from an inner
    /// binder of the same name, which it keeps.
    pub(super) static SET_ALREADY: RefCell<Vec<Arc<str>>> = const { RefCell::new(Vec::new()) };
}

fn add(a: Term, b: Term) -> Term {
    Term::Prim(Prim::Add, vec![a, b])
}

fn let_(x: &str, e: Term, body: Shared) -> Term {
    Term::Let(x.into(), Shared::new(e), body)
}

/// No name resolves where these terms are written.
fn none(_: &str) -> bool {
    false
}

/// `c -> { x1 = 0; …; xk = 0; T1 }`, `Tj = { xj = j; (T(j+1), { xj = j + 100; P }) }` for
/// `j < k`, `Tk = { xk = k; P }`, `P = x1 + … + xk` one node: the term `chains` of
/// tests/steps/l01_28_staging/print.rs, whose updates passed one chain of envs k times before
/// the flag `passed` (Claude C-1 of round 2).
fn chains(k: usize) -> Term {
    let x = |i: usize| format!("x{i}");
    let p = Shared::new((2..=k).fold(var(&x(1)), |s, i| add(s, var(&x(i)))));
    let inner = let_(&x(k), lit(k as i64), p.clone());
    let t = (1..k).rev().fold(inner, |below, j| {
        let second = let_(&x(j), lit(j as i64 + 100), p.clone());
        let pair = Term::Prim(Prim::Tuple, vec![below, second]);
        let_(&x(j), lit(j as i64), Shared::new(pair))
    });
    let t = (1..=k).rev().fold(Shared::new(t), |body, j| {
        Shared::new(let_(&x(j), lit(0i64), body))
    });
    Term::Lam(vec!["c".into()], t)
}

/// Codex C6: on `chains(k)` the updates pass envs over, and no env twice: the flag `passed`
/// stops a walk at an env an earlier update passed. Without the flag the envs of one chain were
/// passed at each binder up the chain, Θ(k²) in all. k is 8 and up (Claude C-4 of round 3): for
/// small k, naming `P` need not write fewer nodes, and then no part is named.
#[test]
fn an_update_passes_each_env_over_at_most_once() {
    for k in [8, 16, 32] {
        PASSED.take();
        let form = dag::shared_form(&chains(k), Some(&none), None)
            .unwrap_or_else(|| panic!("k = {k}: no part is named"));
        assert!(form.labels.is_empty());
        let passed = PASSED.take();
        let distinct: HashSet<usize> = passed.iter().copied().collect();
        assert_eq!(distinct.len(), passed.len(), "k = {k}: {passed:?}");
        assert!(!passed.is_empty(), "k = {k}: no env passed over");
    }
}

/// Codex C1/C2 and C6: in `c -> if c { x = 1; y = 2; x = 3; P } else { x = 4; y = 5; P }` the
/// update at the inner `x` passes over the binders above it, each once; at the outer `x` the
/// slot of `x` is set already, by the inner `x`, which the update keeps (the staging test
/// `a_chain_setting_one_slot_twice_keeps_the_inner_binder` checks the value read).
#[test]
fn an_update_passing_a_binder_of_a_slot_it_set_keeps_the_inner_binder() {
    let items = (0..5)
        .map(|i| add(add(var("x"), var("y")), lit(i as i64)))
        .collect();
    let p = Shared::new(Term::Prim(Prim::Tuple, items));
    let inner = let_("x", lit(3i64), p.clone());
    let then = let_(
        "x",
        lit(1i64),
        Shared::new(let_("y", lit(2i64), Shared::new(inner))),
    );
    let other = let_("x", lit(4i64), Shared::new(let_("y", lit(5i64), p)));
    let t = Term::Lam(
        vec!["c".into()],
        Shared::new(Term::If(
            Shared::new(var("c")),
            Shared::new(then),
            Shared::new(other),
        )),
    );
    PASSED.take();
    SET_ALREADY.take();
    dag::shared_form(&t, Some(&none), None).expect("a part is named");
    let passed = PASSED.take();
    let distinct: HashSet<usize> = passed.iter().copied().collect();
    assert_eq!(distinct.len(), passed.len(), "{passed:?}");
    assert!(passed.len() >= 2, "{passed:?}");
    assert_eq!(SET_ALREADY.take(), [Arc::<str>::from("x")]);
}

/// Codex D3: `L = { a = x + 1; { x = 5; a + x } }` held in two places, in the block of `y = 1`
/// in the `then` arm and first of a block in the `else` arm. The walk from `y = 1` reads `L`
/// inside that block; `L` first of a block takes a walk of its own, or its block does not end at
/// `x = 5` (the staging test
/// `a_shared_let_first_of_a_block_at_one_place_and_in_a_block_at_another_reads_back` checks the
/// text).
#[test]
fn a_shared_let_first_of_a_block_at_one_place_takes_a_walk_of_its_own() {
    let sh = Shared::new;
    let inner = let_("x", lit(5i64), sh(add(var("a"), var("x"))));
    let l = sh(let_("a", add(var("x"), lit(1i64)), sh(inner)));
    let then = sh(let_("y", lit(1i64), l.clone()));
    let t = Term::Lam(
        vec!["x".into(), "c".into()],
        sh(Term::If(sh(var("c")), then.clone(), l.clone())),
    );
    WALKED_FROM.take();
    let mut out = String::new();
    Doc::of(Piece::Term(&t), PLAIN, &HashSet::new())
        .write_flat(&mut out)
        .expect("writing to a string does not fail");
    let walked = WALKED_FROM.take();
    let from_l = walked
        .iter()
        .filter(|&&w| w == std::ptr::from_ref(&*l))
        .count();
    assert_eq!(walked.first(), Some(&std::ptr::from_ref(&*then)), "{out}");
    assert_eq!(from_l, 1, "{out}");
    assert_eq!(
        out,
        "(x, c) -> if c { { y = 1; a = (x + 1); { x = 5; (a + x) } } } \
         else { { a = (x + 1); { x = 5; (a + x) } } }"
    );
}

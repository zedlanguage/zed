//! Item STAGE-store-probes (COMPLEXITY.md row F83): what a part held in a node asked of the
//! scope outside it, the part that holds it asks too. Each part used to ask again, when the
//! part it held was stored, every question that part had asked, and to keep them all in its
//! own tree, so `d` nested parts over a body that asks `p` questions asked and kept `d * p`.
//! Now a part keeps one item for each part it holds, the leaf of that part's tree, and asks
//! again only the questions of names bound between the two parts; a walk of a tree is kept
//! by the entries of the names it asks of, so the parts around a part do not walk its tree
//! again under one scope.

use std::collections::BTreeSet;

use zed_kernel::term::build::{app, lam, lit, prim, var};
use zed_kernel::{Prim, Shared, Term};
use zedc::elab::Unit;
use zedc::stage;

use super::cone::{F0, chain, def, left, mixed_text, sites, unit};
use super::dag::distinct;
use super::scaling::deep;

/// `body` under `d` nested `if c >= j`s whose two arms are one part when `shared`, and two
/// copies of it otherwise; each arm first binds `g = (y) -> y` when `lets`.
fn ifs(d: usize, body: Term, shared: bool, lets: bool) -> Term {
    let arm = |t: Shared| match lets {
        true => Shared::new(Term::Let("g".into(), Shared::new(lam(&["y"], var("y"))), t)),
        false => t,
    };
    if d == 0 {
        return body;
    }
    let guard = Shared::new(prim(Prim::Ge, vec![var("c"), lit(d as i64)]));
    match shared {
        true => {
            let t = Shared::new(ifs(d - 1, body, true, lets));
            Term::If(guard, arm(t.clone()), arm(t))
        }
        false => {
            let a = Shared::new(ifs(d - 1, body.clone(), false, lets));
            let b = Shared::new(ifs(d - 1, body, false, lets));
            Term::If(guard, arm(a), arm(b))
        }
    }
}

/// A chain of `n` functions and `main = (c) -> ..` calling each of them once, under `n`
/// nested `if`s.
pub(super) fn family(n: usize, f0: F0, shared: bool, lets: bool) -> Unit {
    let mut defs = chain(n, f0, false);
    defs.push(def("main", lam(&["c"], ifs(n, sites(n), shared, lets))));
    unit(defs)
}

/// The distinct nodes of the mixed `main` of `u`, and the number of calls left to run.
pub(super) fn mixed(u: &Unit) -> (usize, usize) {
    let (out, report) = stage::mix(u, &["main"]);
    let main = out.defs.iter().find(|d| d.name == "main").expect("main");
    (distinct(&main.term), report.left.len())
}

/// What [`mixed`] gives on the shared family of `n`: the calls of a chain whose form shows
/// that it ends are evaluated, to `1 + c`; the others are left to run, each once.
pub(super) fn expected(n: usize, f0: F0) -> (usize, usize) {
    match f0 {
        F0::Ends => (2 * n + 1, 0),
        F0::Loops | F0::Fails => (3 * n + 1, n),
    }
}

/// The shared form mixes to the term the tree form mixes to, leaves each call to run once
/// rather than once per place, and keeps its parts shared (`bench::store` times 400 and 3200
/// calls). The tree form doubles at each level, so the sizes stop at 6 (they went to 8).
#[test]
fn mixing_calls_under_nested_ifs_whose_arms_are_one_part_gives_what_the_tree_gives() {
    deep(|| {
        // The terms, compared as terms: the text of the shared form names its parts.
        let terms = |u: &Unit| {
            let (out, _) = stage::mix(u, &["main"]);
            let defs = out.defs.iter();
            defs.map(|d| (d.name.clone(), (*d.term).clone()))
                .collect::<Vec<_>>()
        };
        let calls = |u: &Unit| {
            let (_, report) = stage::mix(u, &["main"]);
            left(&report).into_iter().collect::<BTreeSet<_>>()
        };
        for f0 in [F0::Ends, F0::Loops, F0::Fails] {
            for lets in [false, true] {
                for n in 1..=6 {
                    let (one, tree) = (family(n, f0, true, lets), family(n, f0, false, lets));
                    let what = format!("n = {n}, lets = {lets}");
                    assert_eq!(terms(&one), terms(&tree), "{what}");
                    assert_eq!(calls(&one), calls(&tree), "{what}");
                    assert_eq!(mixed(&one), expected(n, f0), "{what}");
                }
            }
        }
    });
}

/// One part under three sibling arms that bind `f1` at the same depth, to `y + 1`, `y + 1`
/// and `y + 2`, is mixed under each arm's own `f1`. The second arm reuses the first arm's
/// tree by walking it, and that walk is kept by the stamps of `f1`; a stamp counts entries
/// over the whole run and is never reused, so the third arm, whose `f1` answers otherwise,
/// does not get the second arm's walk.
#[test]
fn a_part_under_sibling_arms_that_bind_a_name_differently_is_mixed_under_each() {
    let part = Shared::new(prim(
        Prim::Add,
        vec![app(var("f1"), vec![lit(0i64)]), var("c")],
    ));
    let arm = |step: i64, shared: bool| {
        let f1 = lam(&["y"], prim(Prim::Add, vec![var("y"), lit(step)]));
        let part = match shared {
            true => part.clone(),
            false => Shared::new((*part).clone()),
        };
        Shared::new(Term::Let("f1".into(), Shared::new(f1), part))
    };
    let main = |shared: bool| {
        let guard = |j: i64| Shared::new(prim(Prim::Ge, vec![var("c"), lit(j)]));
        let inner = Term::If(guard(2), arm(1, shared), arm(2, shared));
        let body = Term::If(guard(1), arm(1, shared), Shared::new(inner));
        unit(vec![def("main", lam(&["c"], body))])
    };
    let text = |u: &Unit| {
        let text = mixed_text(u);
        text[..text.rfind("Report").expect("the report")].to_string()
    };
    let (one, tree) = (text(&main(true)), text(&main(false)));
    assert_eq!(one, tree);
    assert_eq!(one.matches("(1 + c)").count(), 2, "{one}");
    assert_eq!(one.matches("(2 + c)").count(), 1, "{one}");
}

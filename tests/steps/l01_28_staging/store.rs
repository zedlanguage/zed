//! Item STAGE-store-probes (COMPLEXITY.md row F83): what a part held in a node asked of the
//! scope outside it, the part that holds it asks too. Each part used to ask again, when the
//! part it held was stored, every question that part had asked, and to keep them all in its
//! own tree, so `d` nested parts over a body that asks `p` questions asked and kept `d * p`.
//! Now a part keeps one item for each part it holds, the leaf of that part's tree, and asks
//! again only the questions of names bound between the two parts; a walk of a tree is kept
//! by the entries of the names it asks of, so the parts around a part do not walk its tree
//! again under one scope.

use std::collections::BTreeSet;

use zed_kernel::term::build::{lam, lit, prim, var};
use zed_kernel::{Prim, Shared, Term};
use zed_tests::scaling;
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
fn family(n: usize, f0: F0, shared: bool, lets: bool) -> Unit {
    let mut defs = chain(n, f0, false);
    defs.push(def("main", lam(&["c"], ifs(n, sites(n), shared, lets))));
    unit(defs)
}

/// The distinct nodes of the mixed `main` of `u`, and the number of calls left to run.
fn mixed(u: &Unit) -> (usize, usize) {
    let (out, report) = stage::mix(u, &["main"]);
    let main = out.defs.iter().find(|d| d.name == "main").expect("main");
    (distinct(&main.term), report.left.len())
}

/// What [`mixed`] gives on the shared family of `n`: the calls of a chain whose form shows
/// that it ends are evaluated, to `1 + c`; the others are left to run, each once.
fn expected(n: usize, f0: F0) -> (usize, usize) {
    match f0 {
        F0::Ends => (2 * n + 1, 0),
        F0::Loops | F0::Fails => (3 * n + 1, n),
    }
}

fn mixing_scales(what: &'static str, f0: F0, lets: bool) {
    deep(move || {
        let n = 400;
        let units = scaling::inputs(n, |n| family(n, f0, true, lets));
        scaling::check(what, n, |n| {
            assert_eq!(mixed(&units[&n]), expected(n, f0));
        });
    });
}

#[test]
fn mixing_calls_of_a_chain_under_nested_ifs_whose_arms_are_one_part_scales() {
    mixing_scales(
        "stage::mix on n calls of a chain of n functions under n nested ifs whose two arms \
         are one part",
        F0::Ends,
        false,
    );
}

#[test]
fn mixing_calls_left_to_run_under_nested_ifs_whose_arms_are_one_part_scales() {
    mixing_scales(
        "stage::mix on n calls of a chain of n functions whose form does not show it ends, \
         under n nested ifs whose two arms are one part",
        F0::Loops,
        false,
    );
}

#[test]
fn mixing_calls_under_nested_ifs_whose_arms_bind_a_name_over_one_part_scales() {
    mixing_scales(
        "stage::mix on n calls of a chain of n functions under n nested ifs whose two arms \
         each bind g over one part",
        F0::Ends,
        true,
    );
}

/// The shared form mixes to the text the tree form mixes to, leaves each call to run once
/// rather than once per place, and keeps its parts shared.
#[test]
fn mixing_calls_under_nested_ifs_whose_arms_are_one_part_gives_what_the_tree_gives() {
    deep(|| {
        let text = |u: &Unit| {
            let text = mixed_text(u);
            text[..text.rfind("Report").expect("the report")].to_string()
        };
        let calls = |u: &Unit| {
            let (_, report) = stage::mix(u, &["main"]);
            left(&report).into_iter().collect::<BTreeSet<_>>()
        };
        for f0 in [F0::Ends, F0::Loops, F0::Fails] {
            for lets in [false, true] {
                for n in 1..=8 {
                    let (one, tree) = (family(n, f0, true, lets), family(n, f0, false, lets));
                    let what = format!("n = {n}, lets = {lets}");
                    assert_eq!(text(&one), text(&tree), "{what}");
                    assert_eq!(calls(&one), calls(&tree), "{what}");
                    assert_eq!(mixed(&one), expected(n, f0), "{what}");
                }
            }
        }
    });
}

//! A binder spelled as a level, `\0k`, is canonical only at level `k` (row
//! FAIL-kernel-canon-misplaced-level). The rule kept such a binder at whatever level it stood,
//! so `\x. x` and the same term with its binder named `\05` had two addresses: the fault
//! commit 0a516f19c fixed in the ZIR rule. No source text spells such a name (the lexer
//! rejects U+0000), so the terms here are built by hand, as a term that already holds level
//! names would reach the canonicalizer.

use zed_kernel::Shared;
use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::term::{Evidence, FixKind, Pattern, Prim, Term};
use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::canon::{binders, canonicalize};

use super::alpha::{addresses_agree, one_pass_is_stepwise, random};
use super::{addr, def};

/// The name of level `k`, as the canonicalizer writes it.
fn l(k: usize) -> String {
    binders::level_name(k).to_string()
}

/// `spelled` and `written` are one term up to binder names: one address, one normal form, and
/// the rules applied one step at a time reach it from `spelled` too.
fn same(spelled: Term, written: Term) {
    let (a, b) = (def("f", spelled.clone()), def("f", written));
    assert_eq!(canonicalize(&a), canonicalize(&b), "{spelled:?}");
    assert_eq!(addr(&a), addr(&b), "{spelled:?}");
    one_pass_is_stepwise(spelled);
}

#[test]
fn a_binder_named_as_another_level_is_renamed_to_its_own() {
    // The row's cases.
    assert_eq!(
        addr(&def("f", lam(&["\u{0}5"], var("\u{0}5")))),
        addr(&def("f", lam(&["x"], var("x"))))
    );
    assert_eq!(
        addr(&def("f", lam(&["\u{0}1", "\u{0}0"], var("\u{0}1")))),
        addr(&def("f", lam(&["p", "q"], var("p"))))
    );
    // A binder named as its own level is already canonical.
    assert_eq!(
        addr(&def("f", lam(&["\u{0}0"], var("\u{0}0")))),
        addr(&def("f", lam(&["x"], var("x"))))
    );
    // Reading the other parameter is another function.
    assert_ne!(
        addr(&def("f", lam(&["\u{0}1", "\u{0}0"], var("\u{0}1")))),
        addr(&def("f", lam(&["p", "q"], var("q"))))
    );
}

#[test]
fn renaming_a_binder_to_its_level_captures_no_other_binder() {
    let (l0, l1, l2, l3, l5) = (l(0), l(1), l(2), l(3), l(5));
    let add = |a: &str, b: &str| prim(Prim::Add, vec![var(a), var(b)]);
    // Two parameters spelled as each other's levels: renaming the first to `\00` must not
    // let the second, still spelled `\00`, take its uses.
    same(
        lam(&[&l1, &l0], add(&l1, &l0)),
        lam(&["p", "q"], add("p", "q")),
    );
    // Two parameters of one name: the second shadows the first, whatever their spelling.
    same(lam(&[&l0, &l0], var(&l0)), lam(&["p", "q"], var("q")));
    // An inner binder spelled as the level an outer one is renamed to.
    same(
        lam(&[&l5], lam(&["a"], lam(&[&l0], add(&l5, &l0)))),
        lam(&["x"], lam(&["a"], lam(&["b"], add("x", "b")))),
    );
    // An inner binder at its own level, after an outer one renamed: both index rules hold.
    same(
        lam(&[&l5], lam(&[&l1], add(&l5, &l1))),
        lam(&["x"], lam(&["y"], add("x", "y"))),
    );
    // `let`, `fam`, a `match` arm and a fixpoint's `this` and key.
    same(let_(&l3, lit(1), var(&l3)), let_("x", lit(1), var("x")));
    let fam = |x: &str| Term::Fam {
        domain: Shared::new(var("lines")),
        var: x.into(),
        body: Shared::new(var(x)),
    };
    same(fam(&l2), fam("line"));
    let arm = |p: &str, q: &str| {
        let pat = Pattern::Tuple(vec![Pattern::Bind(p.into()), Pattern::Bind(q.into())]);
        Term::Match(Shared::new(var("pair")), vec![(pat, add(p, q))])
    };
    same(arm(&l1, &l0), arm("p", "q"));
    let fix = |this: &str, key: &str| Term::Fix {
        init: Shared::new(var("upTo")),
        step: Shared::new(add(this, key)),
        this: this.into(),
        key: key.into(),
        kind: FixKind::Definedness,
        ev: Evidence::new(),
    };
    same(fix(&l1, &l0), fix("fib", "n"));
}

#[test]
fn the_rule_counts_and_records_a_misplaced_level_as_written() {
    let (l0, l1, l5) = (l(0), l(1), l(5));
    assert_eq!(binders::written(&lam(&[&l0], var(&l0))), 0);
    assert_eq!(binders::written(&lam(&[&l5], var(&l5))), 1);
    assert_eq!(binders::written(&lam(&[&l1, &l0], var(&l1))), 2);
    // The binder renamed is the first misplaced one in preorder, and its index counts the
    // binders before it, whether or not a canonical binder follows it.
    let t = lam(&[&l5], lam(&[&l1], var(&l5)));
    let (t, i, w) = binders::step(&t).unwrap();
    assert_eq!((i, &*w), (0, &*l5));
    assert_eq!(t, lam(&[&l0], lam(&[&l1], var(&l0))));
    assert_eq!(binders::step(&t), None);
    let (_, i, w) = binders::step(&lam(&[&l0], lam(&[&l5], var(&l5)))).unwrap();
    assert_eq!((i, &*w), (1, &*l5));
}

#[test]
fn the_keyed_form_gives_a_misplaced_level_its_own() {
    let none = |_: &str| None;
    let (l0, l5) = (l(0), l(5));
    assert_eq!(
        binders::keyed(&lam(&[&l5], var(&l5)), &none),
        lam(&[&l0], var(&l0))
    );
    assert_eq!(
        binders::keyed(&lam(&[&l0], var(&l0)), &none),
        lam(&[&l0], var(&l0))
    );
}

/// Binder names for random terms: written names and level names, so that a binder often
/// stands at a level other than the one it is spelled as, and sometimes at its own.
const POOL: [&str; 6] = ["a", "x", "\u{0}0", "\u{0}1", "\u{0}2", "\u{0}3"];

#[test]
fn random_terms_with_level_names_agree_with_an_independent_alpha_equivalence_test() {
    let base = zed_tests::seed::seed(
        "random_terms_with_level_names_agree_with_an_independent_alpha_equivalence_test",
    );
    for i in 0..RANDOM_INSTANCES as u64 {
        let seed = base.wrapping_add(i);
        let make = |names: u64| {
            random(
                &mut Rng::new(seed),
                &mut Rng::new(names),
                4,
                &mut Vec::new(),
                &POOL,
            )
        };
        let (s, t) = (make(seed ^ 0x51), make(seed ^ 0x9e));
        addresses_agree(&s, &t);
        if i % 4 == 0 {
            one_pass_is_stepwise(s);
        }
    }
    // A pair built for each outcome, with a binder spelled as level 1 standing at level 0.
    // `\01 -> \01` and `a -> a` both read the innermost binder, index 0, so they are alike;
    // `(\01, a) -> \01` reads index 1 and `(\01, a) -> a` index 0, so they differ.
    let l1 = POOL[3];
    assert!(
        addresses_agree(&lam(&[l1], var(l1)), &lam(&["a"], var("a"))),
        "alike"
    );
    assert!(
        !addresses_agree(&lam(&[l1, "a"], var(l1)), &lam(&[l1, "a"], var("a"))),
        "different"
    );
}

/// `f(match v { _ -> f(… \05. \a. … \a. \05 …) })`: the binder spelled `\05` under `n` calls and
/// `match` arms in turn, with `n` lambdas in its scope. One step renames it, which walks its
/// scope once and rebuilds each call and `match` above it once.
pub(super) fn under_and_over(n: usize) -> Term {
    let l5 = l(5);
    let mut t = var(&l5);
    for _ in 0..n {
        t = lam(&["a"], t);
    }
    t = lam(&[&l5], t);
    for i in 0..n {
        t = if i % 2 == 0 {
            app(var("f"), vec![t])
        } else {
            Term::Match(Shared::new(var("v")), vec![(Pattern::Wild, t)])
        };
    }
    t
}

/// One step of the rule on `t`, an [`under_and_over`] term: the binder `\05` at preorder index 0
/// is the one renamed.
pub(super) fn steps_once(t: &Term) {
    let (_, i, w) = binders::step(t).expect("a binder to rename");
    assert_eq!((i, &*w), (0, &*l(5)));
}

#[test]
fn a_binder_deep_inside_a_term_is_renamed_in_one_step() {
    // The benchmark `bench::stepping_past_a_deep_binder_scales` times this at large sizes.
    let t = under_and_over(20);
    steps_once(&t);
    one_pass_is_stepwise(t);
}

/// `\a. \b. \c. \d. \02` with `\02` free, and the same term reading `c`, the binder at level 2.
fn free_and_bound_level_two() -> (Term, Term) {
    let body = |x: &str| lam(&["a", "b", "c", "d"], var(x));
    (body(&l(2)), body("c"))
}

#[test]
fn a_bound_variable_at_a_level_is_addressed() {
    // The control for the refusals below: the term that reads the binder is canonical.
    let (_, bound) = free_and_bound_level_two();
    let normal = canonicalize(&def("f", bound.clone()));
    assert_eq!(normal.body, lam(&[&l(0), &l(1), &l(2), &l(3)], var(&l(2))));
    addr(&def("f", bound));
}

#[test]
#[should_panic(expected = "is spelled as a binder level")]
fn a_free_name_spelled_as_a_level_is_refused() {
    // Kept, the free `\02` would be written as the bound variable at level 2, and both terms
    // of the pair would have one address (PROOF-sweep-front-end).
    let (free, _) = free_and_bound_level_two();
    addr(&def("f", free));
}

#[test]
#[should_panic(expected = "is spelled as a binder level")]
fn a_free_name_spelled_as_a_level_is_refused_in_a_query_key() {
    let (free, _) = free_and_bound_level_two();
    binders::keyed(&free, &|_| None);
}

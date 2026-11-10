//! The linear-relation domain against the interpreter on random terms over `x` and `y`: the
//! translation of a test holds at exactly the points where the interpreter gives `true`; the
//! Omega test finds a point of the window exactly when one exists, and its model is one; the
//! projection of a relation holds every value a point takes, and all but one of the 60 lie
//! within the hull of those values; and rung 2 proves no entailment the window refutes, and
//! refutes only with a real countermodel.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::instances::Rng;
pub(crate) use zed_tests::step_helpers::l01_38_presburger::bool_term;
use zedc::store::interval::IntervalSet;
use zedc::store::preimage::relations;
use zedc::store::presburger::{
    Atom, Con, Entailment, Formula, Lin, Refusal, Relation, entails, member, project, satisfiable,
};

use super::{holds, point, projections, window};

/// The window every check runs over.
pub(super) const LO: i64 = -5;
pub(super) const HI: i64 = 5;

fn lit(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn prim(p: Prim, args: Vec<Term>) -> Term {
    Term::Prim(p, args)
}

fn names() -> Vec<Arc<str>> {
    vec!["x".into(), "y".into()]
}

/// The window as a formula over `names`.
pub(super) fn boxed(names: &[Arc<str>]) -> Formula {
    Formula::and(
        names
            .iter()
            .map(|n| member(&Atom::Sym(n.clone()), &IntervalSet::of(LO, HI)))
            .collect(),
    )
}

/// The relation's points as a formula: its definitions, its body, and the window.
fn whole(r: &Relation, names: &[Arc<str>]) -> Formula {
    Formula::and(vec![r.defined(), r.body.clone(), boxed(names)])
}

/// The relation holds at each point of the window exactly where `t` does.
fn check_points(r: &Relation, t: &Term, names: &[Arc<str>]) -> Result<(), String> {
    for p in window(names.len(), LO, HI) {
        let at = Formula::and(
            names
                .iter()
                .zip(&p)
                .map(|(n, v)| {
                    let x = Lin::atom(Atom::Sym(n.clone()));
                    Formula::Con(Con::eq(&x, &Lin::constant(*v)))
                })
                .collect(),
        );
        let f = Formula::and(vec![r.defined(), r.body.clone(), at]);
        let sat = satisfiable(&f).map_err(|_| format!("{t}: refused at {p:?}"))?;
        if sat.is_some() != holds(t, names, &p) {
            return Err(format!(
                "{t} at {p:?}: the interpreter gives {}, and the relation {r} {}",
                holds(t, names, &p),
                if sat.is_some() { "holds" } else { "fails" }
            ));
        }
    }
    Ok(())
}

/// The Omega test finds a point of the window exactly when `t` holds at one, and the point
/// it finds is one.
fn check_model(found: Option<Vec<i64>>, t: &Term, names: &[Arc<str>]) -> Result<(), String> {
    let any = window(names.len(), LO, HI)
        .into_iter()
        .find(|p| holds(t, names, p));
    match (found, any) {
        (Some(p), _) if p.iter().all(|v| (LO..=HI).contains(v)) && holds(t, names, &p) => Ok(()),
        (Some(p), _) => Err(format!(
            "{t}: the model {p:?} is no point of it in the window"
        )),
        (None, Some(p)) => Err(format!("{t}: unsatisfiable, but it holds at {p:?}")),
        (None, None) => Ok(()),
    }
}

/// Each claimed projection holds every value the points of `t` take; whether every one also
/// lies within their hull. Past one disjunction a projection is only a set holding the values
/// (presburger.rs, module note), and a bound it cannot show moves stays where it is.
fn check_projection(claimed: &[IntervalSet], t: &Term, names: &[Arc<str>]) -> Result<bool, String> {
    let points: Vec<Vec<i64>> = window(names.len(), LO, HI)
        .into_iter()
        .filter(|p| holds(t, names, p))
        .collect();
    let mut exact = true;
    for ((n, c), want) in names
        .iter()
        .zip(claimed)
        .zip(projections(&points, names.len()))
    {
        let hull = match want.bounds() {
            Some((lo, hi)) => IntervalSet::range(lo.clone(), hi.clone()),
            None => IntervalSet::empty(),
        };
        if !want.is_subset(c) {
            return Err(format!(
                "{t}: `{n}` takes {want}, and the projection is {c}"
            ));
        }
        exact &= c.is_subset(&hull);
    }
    Ok(exact)
}

/// No point of the window refutes a proved entailment from `p` to `g`, and a countermodel
/// is one. A refusal for a search whose order only names would fix (NAME-ties repair 2) is
/// the one refusal a linear question may give.
fn check_entailment(e: &Entailment, p: &Term, g: &Term, names: &[Arc<str>]) -> Result<(), String> {
    let counter = window(names.len(), LO, HI)
        .into_iter()
        .find(|q| holds(p, names, q) && !holds(g, names, q));
    match (e, counter) {
        (Entailment::Proved(_), Some(q)) => {
            Err(format!("{p} to {g}: proved, but {q:?} refutes it"))
        }
        (Entailment::Refuted(m), _) => {
            let q = point(m, names);
            if holds(p, names, &q) && !holds(g, names, &q) {
                Ok(())
            } else {
                Err(format!("{p} to {g}: the countermodel {q:?} is none"))
            }
        }
        (Entailment::Refused(Refusal::Unordered(_)), _) => Ok(()),
        (Entailment::NotProved(_) | Entailment::Refused(_), _) => Err(format!(
            "{p} to {g}: {e}, which a linear question never gives"
        )),
        (Entailment::Proved(_), None) => Ok(()),
    }
}

/// The window as a test over `names`.
fn window_term(names: &[Arc<str>]) -> Term {
    names
        .iter()
        .map(|n| {
            let x = Term::Var(n.clone());
            prim(
                Prim::And,
                vec![
                    prim(Prim::Le, vec![lit(LO), x.clone()]),
                    prim(Prim::Le, vec![x, lit(HI)]),
                ],
            )
        })
        .reduce(|a, b| prim(Prim::And, vec![a, b]))
        .expect("an input")
}

#[test]
fn random_tests_agree_with_the_interpreter() {
    let mut rng = Rng::new(0x1_38);
    let ns = names();
    let (mut checked, mut models, mut entailments, mut wider, mut unordered) = (0, 0, 0, 0, 0);
    while checked < 60 {
        let t = bool_term(&mut rng, 2);
        let Some(rs) = relations(&[&t], &ns, false) else {
            panic!("{t}: outside the domain, though built from its operators")
        };
        let r = &rs[0];
        check_points(r, &t, &ns).unwrap();
        let f = whole(r, &ns);
        let Ok(m) = satisfiable(&f) else {
            continue;
        };
        let inside = prim(Prim::And, vec![t.clone(), window_term(&ns)]);
        check_model(m.as_ref().map(|m| point(m, &ns)), &inside, &ns).unwrap();
        models += usize::from(m.is_some());
        let claimed: Vec<IntervalSet> = ns
            .iter()
            .map(|n| project(&f, &Atom::Sym(n.clone())).expect("answered"))
            .collect();
        wider += usize::from(!check_projection(&claimed, &inside, &ns).unwrap());
        // Rung 2 from the window and this test to a second one.
        let g = bool_term(&mut rng, 1);
        let rs = relations(&[&inside, &g], &ns, false).expect("in the domain");
        let e = entails(&rs[0], &rs[1]);
        check_entailment(&e, &inside, &g, &ns).unwrap();
        entailments += usize::from(matches!(e, Entailment::Proved(_)));
        unordered += usize::from(matches!(e, Entailment::Refused(Refusal::Unordered(_))));
        checked += 1;
    }
    // Option A (STATUS.md, L1.38): one projection of the 60, of `y` on a term with `div`, `mod`,
    // `min` and `if`, is [-4..=5] where the points take [0..=5]. A question it asks of a disjunct
    // is refused, so the bound below stays where no question showed it can move. The linear
    // program before design R decided that question; this count measures that strength, not
    // correctness, which the check above holds for every projection. Since HULL3 (XT3 B4), the
    // only change, that projection is [0..=5]: every projection is the hull of its values. It
    // stays so with `live3` alone, since that stage was removed (HULL3-subsumed).
    assert_eq!(wider, 0, "projections wider than the hull of their values");
    // Since NAME-ties repair 2, one entailment of the 60, from `x != y` in the window to
    // `-x == y - 1`, is refused: `x` and `y` occur alike, and two disjunctions are left that only
    // an order chosen by name would search. Before, it was answered.
    assert_eq!(
        unordered, 1,
        "entailments refused for a search order only names fix"
    );
    // Both answers occur, so neither check passes by never being asked.
    assert!(models > 10 && models < 55, "{models} of 60 satisfiable");
    assert!(
        entailments > 3 && entailments < 57,
        "{entailments} of 60 proved"
    );
}

/// Plan item SOUND-div-exact: `c^0` fails where `c` does (DESIGN.md sec:failure), so `(1 div x)^0 == 1`
/// is `false` at `x == 0`. Rung 1, which does not track failure, translated `c^0` as 1 without
/// reading `c` and gave the relation `1 == 1`, true at `x == 0`; it now gives none, since a
/// quotient by a term does not translate there. Rung 2 meets the relation with the condition
/// that the divisor is not 0.
#[test]
fn a_power_zero_of_a_quotient_by_a_term_fails_where_the_divisor_is_zero() {
    let ns = names();
    let (x, y) = (|| Term::Var("x".into()), || Term::Var("y".into()));
    let pow0 = |t: Term| prim(Prim::Pow, vec![t, lit(0)]);
    for t in [
        prim(
            Prim::Eq,
            vec![pow0(prim(Prim::IntDiv, vec![lit(1), x()])), lit(1)],
        ),
        prim(
            Prim::Ge,
            vec![
                pow0(prim(Prim::Mod, vec![x(), prim(Prim::Sub, vec![x(), y()])])),
                lit(1),
            ],
        ),
    ] {
        assert!(relations(&[&t], &ns, false).is_none(), "{t}: rung 1");
        let rs = relations(&[&t], &ns, true).expect("in the domain");
        check_points(&rs[0], &t, &ns).unwrap();
    }
}

//! The linear-relation domain against the interpreter on random terms over `x` and `y`: the
//! translation of a test holds at exactly the points where the interpreter gives `true`; the
//! Omega test finds a point of the window exactly when one exists, and its model is one; the
//! projection of a relation holds every value a point takes, within the hull of those
//! values; and rung 2 proves no entailment the window refutes, and refutes only with a real
//! countermodel.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::instances::Rng;
use zedc::store::interval::IntervalSet;
use zedc::store::preimage::relations;
use zedc::store::presburger::{
    Atom, Con, Entailment, Formula, Lin, Relation, entails, member, project, satisfiable,
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

/// A random integer term over `x` and `y` that the domain states, of depth at most `d`.
pub(crate) fn int_term(rng: &mut Rng, d: u32) -> Term {
    if d == 0 || rng.below(3) == 0 {
        return match rng.below(5) {
            0 | 1 => Term::Var("x".into()),
            2 | 3 => Term::Var("y".into()),
            _ => lit(rng.int(-6, 6)),
        };
    }
    let sub = |rng: &mut Rng| int_term(rng, d - 1);
    let nonzero = |rng: &mut Rng| {
        let c = rng.int(1, 5);
        lit(if rng.below(3) == 0 { -c } else { c })
    };
    match rng.below(11) {
        0 | 1 => prim(Prim::Add, vec![sub(rng), sub(rng)]),
        2 => prim(Prim::Sub, vec![sub(rng), sub(rng)]),
        3 => prim(Prim::Mul, vec![lit(rng.int(-3, 3)), sub(rng)]),
        4 => prim(Prim::IntDiv, vec![sub(rng), nonzero(rng)]),
        5 => prim(Prim::Mod, vec![sub(rng), nonzero(rng)]),
        6 => prim(Prim::Neg, vec![sub(rng)]),
        7 => prim(Prim::Abs, vec![sub(rng)]),
        8 => prim(rng.pick(&[Prim::Min, Prim::Max]), vec![sub(rng), sub(rng)]),
        _ => Term::If(
            Arc::new(bool_term(rng, d - 1)),
            Arc::new(sub(rng)),
            Arc::new(sub(rng)),
        ),
    }
}

/// A random test over `x` and `y` that the domain states, of depth at most `d`.
pub(crate) fn bool_term(rng: &mut Rng, d: u32) -> Term {
    let cmp = |rng: &mut Rng| {
        let p = rng.pick(&[Prim::Lt, Prim::Le, Prim::Gt, Prim::Ge, Prim::Eq, Prim::Ne]);
        prim(p, vec![int_term(rng, d), int_term(rng, d)])
    };
    if d == 0 || rng.below(2) == 0 {
        return cmp(rng);
    }
    let sub = |rng: &mut Rng| bool_term(rng, d - 1);
    match rng.below(4) {
        0 => prim(Prim::Not, vec![sub(rng)]),
        1 => prim(Prim::And, vec![sub(rng), sub(rng)]),
        2 => prim(Prim::Or, vec![sub(rng), sub(rng)]),
        _ => Term::If(Arc::new(sub(rng)), Arc::new(sub(rng)), Arc::new(sub(rng))),
    }
}

fn names() -> Vec<Arc<str>> {
    vec!["x".into(), "y".into()]
}

/// The window as a formula over `names`.
pub(super) fn boxed(names: &[Arc<str>]) -> Formula {
    Formula::and(
        names
            .iter()
            .map(|n| member(&Atom::Sym(n.clone()), &IntervalSet::of(LO, HI)).expect("in budget"))
            .collect(),
    )
}

/// The relation's points as a formula: its definitions, its body, and the window.
fn whole(r: &Relation, names: &[Arc<str>]) -> Formula {
    Formula::and(vec![r.defined(), r.body.clone(), boxed(names)])
}

/// The relation holds at each point of the window exactly where `t` does.
pub(super) fn check_points(r: &Relation, t: &Term, names: &[Arc<str>]) -> Result<(), String> {
    for p in window(names.len(), LO, HI) {
        let at = Formula::and(
            names
                .iter()
                .zip(&p)
                .map(|(n, v)| {
                    let x = Lin::atom(Atom::Sym(n.clone()));
                    Formula::Con(Con::eq(&x, &Lin::constant((*v).into())).expect("small"))
                })
                .collect(),
        );
        let f = Formula::and(vec![r.defined(), r.body.clone(), at]);
        let sat = satisfiable(&f).map_err(|_| format!("{t}: past the budget at {p:?}"))?;
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
pub(super) fn check_model(
    found: Option<Vec<i64>>,
    t: &Term,
    names: &[Arc<str>],
) -> Result<(), String> {
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

/// Each claimed projection holds every value the points of `t` take, within their hull.
pub(super) fn check_projection(
    claimed: &[IntervalSet],
    t: &Term,
    names: &[Arc<str>],
) -> Result<(), String> {
    let points: Vec<Vec<i64>> = window(names.len(), LO, HI)
        .into_iter()
        .filter(|p| holds(t, names, p))
        .collect();
    for ((n, c), want) in names
        .iter()
        .zip(claimed)
        .zip(projections(&points, names.len()))
    {
        let hull = match want.bounds() {
            Some((lo, hi)) => IntervalSet::range(lo, hi),
            None => IntervalSet::empty(),
        };
        if !want.is_subset(c) || !c.is_subset(&hull) {
            return Err(format!(
                "{t}: `{n}` takes {want}, and the projection is {c}"
            ));
        }
    }
    Ok(())
}

/// No point of the window refutes a proved entailment from `p` to `g`, and a countermodel
/// is one.
pub(super) fn check_entailment(
    e: &Entailment,
    p: &Term,
    g: &Term,
    names: &[Arc<str>],
) -> Result<(), String> {
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
        (Entailment::NotProved(_) | Entailment::Dropped, _) => Err(format!(
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
    let (mut checked, mut models, mut entailments) = (0, 0, 0);
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
            .map(|n| project(&f, &Atom::Sym(n.clone())).expect("in budget"))
            .collect();
        check_projection(&claimed, &inside, &ns).unwrap();
        // Rung 2 from the window and this test to a second one.
        let g = bool_term(&mut rng, 1);
        let rs = relations(&[&inside, &g], &ns, false).expect("in the domain");
        let e = entails(&rs[0], &rs[1]);
        check_entailment(&e, &inside, &g, &ns).unwrap();
        entailments += usize::from(matches!(e, Entailment::Proved(_)));
        checked += 1;
    }
    // Both answers occur, so neither check passes by never being asked.
    assert!(models > 10 && models < 55, "{models} of 60 satisfiable");
    assert!(
        entailments > 3 && entailments < 57,
        "{entailments} of 60 proved"
    );
}

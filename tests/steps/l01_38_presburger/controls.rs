//! Relations of any size and the refused fragment.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zedc::store::interval::IntervalSet;
use zedc::store::preimage::{Demand, preimage};
use zedc::store::presburger::{
    Atom, Con, Entailment, Formula, Lin, Refusal, Relation, entails, satisfiable,
};

fn lit(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}
#[test]
fn a_relation_of_any_size_is_decided() {
    // The sum of 40 symbols: there is no limit on the atoms.
    let sum = Formula::Con(Con {
        lin: (0..40).fold(Lin::constant(-50), |l, i| {
            l.plus(&Lin::atom(Atom::Sym(format!("a{i}").into())))
                .unwrap()
        }),
        rel: zedc::store::presburger::Rel::Ge,
    });
    let m = satisfiable(&sum).unwrap().unwrap();
    assert!(sum.holds(&m));
    let r = Relation::of(sum.clone());
    assert!(matches!(entails(&r, &r), Entailment::Proved(_)));
    // 200 constraints over one symbol, and the last one false with them.
    let x = || Lin::atom(Atom::Sym("x".into()));
    let mut many: Vec<Formula> = (0..200)
        .map(|k| Formula::Con(Con::ge(&x(), &Lin::constant(k)).unwrap()))
        .collect();
    assert!(satisfiable(&Formula::and(many.clone())).unwrap().is_some());
    many.push(Formula::Con(Con::ge(&Lin::constant(198), &x()).unwrap()));
    assert_eq!(satisfiable(&Formula::and(many)), Ok(None));
    // The preimage of a sum of 40 inputs has its relation, and its box.
    let inputs: Vec<Arc<str>> = (0..40).map(|i| format!("a{i}").into()).collect();
    let total = inputs
        .iter()
        .map(|n| Term::Var(n.clone()))
        .reduce(|a, b| Term::Prim(Prim::Add, vec![a, b]))
        .unwrap();
    let t = Term::Prim(Prim::Lt, vec![total, lit(50)]);
    let doms = inputs
        .iter()
        .map(|n| (n.clone(), IntervalSet::of(0, 1000)))
        .collect();
    let p = preimage(&t, &doms, &Demand::Bool(true));
    assert!(p.relation.is_some() && !p.exact);
    assert!(
        p.domains.values().all(|d| *d == IntervalSet::of(0, 49)),
        "{:?}",
        p.domains
    );
}

#[test]
fn a_question_between_the_shadows_is_refused_and_the_written_constraint_kept() {
    // Pugh's example: 27 <= 11x + 13y <= 45, -10 <= 7x - 9y <= 4 has no integer point, its
    // dark shadow is empty and its real shadow is not.
    let l = |a: i128, b: i128, k: i128| {
        Lin::atom(Atom::Sym("x".into()))
            .times(a)
            .unwrap()
            .plus(&Lin::atom(Atom::Sym("y".into())).times(b).unwrap())
            .unwrap()
            .plus(&Lin::constant(k))
            .unwrap()
    };
    let ge0 = |l: Lin| Formula::Con(Con::ge(&l, &Lin::constant(0)).unwrap());
    let pugh = Formula::and(vec![
        ge0(l(11, 13, -27)),
        ge0(l(-11, -13, 45)),
        ge0(l(7, -9, 10)),
        ge0(l(-7, 9, 4)),
    ]);
    assert!(satisfiable(&pugh).is_err());
    let r = Relation::of(pugh);
    let goal = Relation::of(Formula::bottom());
    assert_eq!(entails(&r, &goal), Entailment::Refused(Refusal::Shadows));
    assert_eq!(
        entails(&r, &goal).to_string(),
        "refused: the relation has rational points but no integer point was found or ruled out"
    );
}

//! The completeness pass of step L1.38 (TEST-complete-presburger, COMPLETENESS.md): each way the
//! public operations of the linear-relation domain can be called that no other test of the
//! step reaches, each with the answer the design or the operation's own contract gives:
//! the constant formulas `true` and `false` through every question, conjunctions and
//! disjunctions of none, one and constant operands, negation, forgetting, sets as formulas,
//! the joining of chains, the sharing of conjuncts by `either`, the reduction of a constraint,
//! products of terms, the printed forms, the repairs of a refusal, the box kept for a refused
//! projection, exact elimination and colors, and Zed tests whose operators meet at the
//! domain's edges, checked against the interpreter at every point of a window.

use std::collections::HashSet;
use std::sync::Arc;

use zed_tests::step_helpers::l01_25_preimage_catalog::{function, int_ok};
use zedc::store::int::Int;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::preimage::relations;
use zedc::store::presburger::{
    Atom, Boxed, Con, Entailment, Factor, Formula, Joining, Lin, Model, Refusal, Relation, Split,
    Tie, Written, colors, decide, eliminated, entails, free_names, hull_sides_asked, member,
    names_in, parts_tested, project, project_each, project_each_boxed, row_box, satisfiable,
    with_parts_reversed, within, without_modular_empty_check,
};

use super::scaling::x;
use super::stages::CROSSING;
use super::{holds, window};

fn sym(s: &str) -> Atom {
    Atom::Sym(Arc::from(s))
}

fn var(s: &str) -> Lin {
    Lin::atom(sym(s))
}

/// `Σ c·s + k`.
fn lin(terms: &[(&str, i128)], k: i128) -> Lin {
    terms
        .iter()
        .fold(Lin::constant(k), |l, (s, c)| l.plus(&var(s).times(*c)))
}

/// `Σ c·s + k >= 0`.
fn ge(terms: &[(&str, i128)], k: i128) -> Formula {
    Formula::Con(Con::ge(&lin(terms, k), &Lin::constant(0)))
}

/// `Σ c·s + k == 0`.
fn eq(terms: &[(&str, i128)], k: i128) -> Formula {
    Formula::Con(Con::eq(&lin(terms, k), &Lin::constant(0)))
}

/// The model of the named values.
fn model(values: &[(&str, i128)]) -> Model {
    values
        .iter()
        .map(|(s, v)| (sym(s), Int::from(*v)))
        .collect()
}

/// The set `[lo..=hi]`.
fn range(lo: i128, hi: i128) -> IntervalSet {
    IntervalSet::range(End::Fin(Num::from(lo)), End::Fin(Num::from(hi)))
}

/// Whether `f` and `g` hold at the same points of `x` (and `y`) in `-8..=8`.
fn same_points(f: &Formula, g: &Formula, names: &[&str]) -> bool {
    window(names.len(), -8, 8).iter().all(|p| {
        let m: Model = names
            .iter()
            .zip(p)
            .map(|(n, v)| (sym(n), Int::from(i128::from(*v))))
            .collect();
        f.holds(&m) == g.holds(&m)
    })
}

#[test]
fn true_and_false_answer_every_question() {
    let (t, f) = (Formula::top(), Formula::bottom());
    assert_eq!(satisfiable(&t), Ok(Some(Model::new())));
    assert_eq!(satisfiable(&f), Ok(None));
    assert_eq!(decide(&t), Ok(true));
    assert_eq!(decide(&f), Ok(false));
    // A symbol no constraint mentions takes every value where the formula holds, and none
    // where it holds nowhere.
    assert_eq!(project(&t, &sym("x")), Ok(IntervalSet::top()));
    assert_eq!(project(&f, &sym("x")), Ok(IntervalSet::empty()));
    assert_eq!(row_box(&t, &[sym("x")]), vec![IntervalSet::top()]);
    assert_eq!(row_box(&f, &[sym("x")]), vec![IntervalSet::empty()]);
    // No symbol asked: no set.
    assert_eq!(project_each(&ge(&[("x", 1)], 0), &[]), Ok((vec![], vec![])));
    assert!(row_box(&t, &[]).is_empty());
    // `false` entails everything; `true` entails only `true`.
    let x_pos = Relation::of(ge(&[("x", 1)], -1));
    assert!(matches!(
        entails(&Relation::of(f.clone()), &x_pos),
        Entailment::Proved(_)
    ));
    assert!(matches!(
        entails(&Relation::of(t.clone()), &Relation::of(t.clone())),
        Entailment::Proved(_)
    ));
    assert!(matches!(
        entails(&Relation::of(t.clone()), &Relation::of(f.clone())),
        Entailment::Refuted(_)
    ));
    let Entailment::Refuted(m) = entails(&Relation::of(t), &x_pos) else {
        panic!("`x >= 1` does not hold everywhere")
    };
    assert!(m.get(&sym("x")).is_none_or(|v| *v < Int::ONE), "{m:?}");
}

#[test]
fn conjunctions_and_disjunctions_of_none_one_and_constant_operands() {
    let (a, b, c) = (
        ge(&[("x", 1)], 0),
        ge(&[("y", 1)], 0),
        ge(&[("x", -1), ("y", 1)], 3),
    );
    assert_eq!(Formula::and(vec![]), Formula::top());
    assert_eq!(Formula::or(vec![]), Formula::bottom());
    assert_eq!(Formula::and(vec![a.clone()]), a);
    assert_eq!(Formula::or(vec![a.clone()]), a);
    // `true` is dropped from a conjunction and `false` absorbs it; the other way round in a
    // disjunction.
    assert_eq!(Formula::and(vec![a.clone(), Formula::top()]), a);
    assert_eq!(
        Formula::and(vec![a.clone(), Formula::bottom(), b.clone()]),
        Formula::bottom()
    );
    assert_eq!(Formula::or(vec![a.clone(), Formula::bottom()]), a);
    assert_eq!(
        Formula::or(vec![a.clone(), Formula::top(), b.clone()]),
        Formula::top()
    );
    // Nested conjunctions are flattened, in order.
    assert_eq!(
        Formula::and(vec![Formula::and(vec![a.clone(), b.clone()]), c.clone()]),
        Formula::and(vec![a.clone(), b.clone(), c.clone()])
    );
    assert_eq!(
        Formula::or(vec![a.clone(), Formula::or(vec![b.clone(), c.clone()])]),
        Formula::or(vec![a.clone(), b.clone(), c.clone()])
    );
    // Of two inequalities on one term, the tighter alone; two equations on one term with
    // different constants hold nowhere; one equation twice is one.
    assert_eq!(
        Formula::and(vec![ge(&[("x", 1)], -3), ge(&[("x", 1)], -5)]),
        ge(&[("x", 1)], -5)
    );
    assert_eq!(
        Formula::and(vec![ge(&[("x", 1)], -5), ge(&[("x", 1)], -3)]),
        ge(&[("x", 1)], -5)
    );
    assert_eq!(
        Formula::and(vec![eq(&[("x", 1)], -1), eq(&[("x", 1)], -2)]),
        Formula::bottom()
    );
    assert_eq!(
        Formula::and(vec![eq(&[("x", 1)], -1), eq(&[("x", 1)], -1)]),
        eq(&[("x", 1)], -1)
    );
    // `x >= 0 || x <= -1` holds at every integer, and so does `c || !c`; `x >= 0 || x <= -2`
    // does not (it fails at -1).
    assert_eq!(
        Formula::or(vec![ge(&[("x", 1)], 0), ge(&[("x", -1)], -1)]),
        Formula::top()
    );
    assert_eq!(
        Formula::or(vec![c.clone(), Formula::negate(c.clone())]),
        Formula::top()
    );
    let gap = Formula::or(vec![ge(&[("x", 1)], 0), ge(&[("x", -1)], -2)]);
    assert_ne!(gap, Formula::top());
    assert!(!gap.holds(&model(&[("x", -1)])));
    assert_eq!(decide(&gap), Ok(true));
    // A conjunction kept whole holds where the flat one does, and is shown and compared as it.
    let kept = Formula::and_keeping(
        vec![Formula::and(vec![a.clone(), b.clone()]), c.clone()],
        |i| i == 0,
    );
    let flat = Formula::and(vec![a.clone(), b.clone(), c.clone()]);
    assert_eq!(kept.to_string(), flat.to_string());
    assert_eq!(kept, flat);
    assert!(same_points(&kept, &flat, &["x", "y"]));
    let kept = Formula::or_keeping(
        vec![Formula::or(vec![a.clone(), b.clone()]), c.clone()],
        |i| i == 0,
    );
    let flat = Formula::or(vec![a, b, c]);
    assert_eq!(kept.to_string(), flat.to_string());
    assert!(same_points(&kept, &flat, &["x", "y"]));
}

#[test]
fn negation_removes_double_negations_and_constants() {
    let c = ge(&[("x", 2), ("y", -1)], 1);
    assert_eq!(Formula::negate(Formula::top()), Formula::bottom());
    assert_eq!(Formula::negate(Formula::bottom()), Formula::top());
    assert_eq!(Formula::negate(Formula::negate(c.clone())), c);
    let not_c = Formula::negate(c.clone());
    for p in window(2, -4, 4) {
        let m = model(&[("x", p[0].into()), ("y", p[1].into())]);
        assert_eq!(not_c.holds(&m), !c.holds(&m), "{p:?}");
    }
    // An integer point of `!(2x - y + 1 >= 0)` has `2x - y <= -2`.
    let m = satisfiable(&Formula::and(vec![
        not_c.clone(),
        ge(&[("x", 1)], 0),
        ge(&[("x", -1)], 0),
    ]))
    .unwrap()
    .expect("x = 0, y >= 2");
    assert!(
        m.get(&sym("y")).is_some_and(|y| *y >= Int::from(2i64)),
        "{m:?}"
    );
}

#[test]
fn forgetting_a_symbol_weakens_by_the_parity_of_negations() {
    let x: Arc<str> = Arc::from("x");
    let (xs, ys) = (ge(&[("x", 1)], -1), ge(&[("y", 1)], -2));
    let both = Formula::and(vec![xs.clone(), ys.clone()]);
    assert_eq!(both.forget(&x), ys);
    // Under one negation a constraint on `x` becomes `false`: `!(false && y >= 2)` is `true`.
    assert_eq!(Formula::negate(both.clone()).forget(&x), Formula::top());
    // Under two it is `true` again.
    assert_eq!(
        Formula::negate(Formula::negate(both.clone())).forget(&x),
        ys
    );
    assert_eq!(
        Formula::or(vec![xs.clone(), ys.clone()]).forget(&x),
        Formula::top()
    );
    // A symbol the formula does not mention changes nothing.
    assert_eq!(both.forget(&Arc::from("z")), both);
    // A product that has `x` as a factor mentions `x`.
    let xy = var("x")
        .product(&var("y"))
        .expect("a product of two symbols");
    let with_product = Formula::and(vec![
        Formula::Con(Con::ge(&xy, &Lin::constant(1))),
        ge(&[("y", 1)], 0),
    ]);
    assert_eq!(with_product.forget(&x), ge(&[("y", 1)], 0));
    assert_eq!(with_product.forget(&Arc::from("y")), Formula::top());
}

#[test]
fn a_set_as_a_formula_holds_exactly_at_its_members() {
    let x = sym("x");
    assert_eq!(member(&x, &IntervalSet::empty()), Formula::bottom());
    assert_eq!(member(&x, &IntervalSet::top()), Formula::top());
    let sets = [
        IntervalSet::single(3),
        IntervalSet::of(-2, 2),
        IntervalSet::of(0, 2).join(&IntervalSet::of(5, 7)),
        IntervalSet::range(End::Fin(Num::from(4)), End::PosInf),
        IntervalSet::range(End::NegInf, End::Fin(Num::from(-3))),
        IntervalSet::range(End::NegInf, End::Fin(Num::from(-3)))
            .join(&IntervalSet::range(End::Fin(Num::from(3)), End::PosInf)),
    ];
    for s in &sets {
        let f = member(&x, s);
        for v in -10i64..=10 {
            assert_eq!(
                f.holds(&model(&[("x", v.into())])),
                s.contains(v),
                "{s} at {v}"
            );
        }
        // The projection of the set's formula is the set: over a disjunction of boxes, the
        // union of each box's projection.
        assert_eq!(project(&f, &x).as_ref(), Ok(s), "{f}");
        assert_eq!(decide(&f), Ok(true));
    }
    // The values of a term: `0 <= x + y <= 1`.
    let f = within(&lin(&[("x", 1), ("y", 1)], 0), &IntervalSet::of(0, 1));
    for p in window(2, -3, 3) {
        let m = model(&[("x", p[0].into()), ("y", p[1].into())]);
        assert_eq!(f.holds(&m), (0..=1).contains(&(p[0] + p[1])), "{p:?}");
    }
    assert_eq!(within(&var("x"), &IntervalSet::empty()), Formula::bottom());
}

#[test]
fn a_chain_joined_one_operand_at_a_time_is_the_chain_joined_two_at_a_time() {
    let (a, b, c) = (ge(&[("x", 1)], 0), ge(&[("y", 1)], 0), ge(&[("z", 1)], 0));
    // Empty joinings are `true` and `false`.
    assert_eq!(Joining::new(true).finish(), Formula::top());
    assert_eq!(Joining::new(false).finish(), Formula::bottom());
    // `a && (b && c)`: the inner operand, kept while it is made, is unwrapped by `close`.
    let mut j = Joining::new(true);
    j.operand(a.clone(), false);
    let m = j.mark();
    j.operand(Formula::and(vec![b.clone(), c.clone()]), true);
    j.close(m);
    assert_eq!(
        j.finish(),
        Formula::and(vec![a.clone(), b.clone(), c.clone()])
    );
    // `a && (b || c)`: a disjunction in a conjunction stays one part.
    let mut j = Joining::new(true);
    j.operand(a.clone(), false);
    let m = j.mark();
    j.operand(Formula::or(vec![b.clone(), c.clone()]), true);
    j.close(m);
    assert_eq!(
        j.finish(),
        Formula::and(vec![a.clone(), Formula::or(vec![b.clone(), c.clone()])])
    );
    // `a || (b || c)`.
    let mut j = Joining::new(false);
    j.operand(a.clone(), false);
    let m = j.mark();
    j.operand(Formula::or(vec![b.clone(), c.clone()]), true);
    j.close(m);
    assert_eq!(
        j.finish(),
        Formula::or(vec![a.clone(), b.clone(), c.clone()])
    );
    // A mark with two operands after it closes nothing: `a && (b && c)` with `b` and `c` given
    // apart is already flat.
    let mut j = Joining::new(true);
    let m = j.mark();
    j.operand(a.clone(), false);
    j.operand(b.clone(), false);
    j.close(m);
    assert_eq!(j.finish(), Formula::and(vec![a.clone(), b.clone()]));
    // `false` decides a conjunction and `true` a disjunction; later operands are ignored.
    let mut j = Joining::new(true);
    j.operand(a.clone(), false);
    j.operand(Formula::bottom(), false);
    j.operand(b.clone(), false);
    let m = j.mark();
    j.close(m);
    assert_eq!(j.finish(), Formula::bottom());
    let mut j = Joining::new(false);
    j.operand(Formula::top(), true);
    j.operand(a.clone(), false);
    assert_eq!(j.finish(), Formula::top());
    // The empty one of the joining's own kind is dropped, kept or not.
    let mut j = Joining::new(true);
    j.operand(Formula::top(), true);
    j.operand(a.clone(), false);
    assert_eq!(j.finish(), a);
}

#[test]
fn either_takes_out_the_shared_conjuncts_and_drops_a_complement() {
    let id = |c: &Con| Formula::Con(c.clone());
    let s = ge(&[("z", 1)], 0);
    let (xs, ys) = (ge(&[("x", 1)], -5), ge(&[("y", 1)], -5));
    let a = Formula::and(vec![s.clone(), xs.clone()]);
    let b = Formula::and(vec![s.clone(), ys.clone()]);
    let e = Formula::either(&a, &b, &id);
    assert_eq!(e, Formula::and(vec![s.clone(), Formula::or(vec![xs, ys])]));
    assert!(same_points(
        &e,
        &Formula::or(vec![a.clone(), b.clone()]),
        &["x", "y"]
    ));
    // `rest` maps each constraint of the rest of each side: mapped to `true`, the disjunction is
    // `true` and only the shared part is left.
    assert_eq!(Formula::either(&a, &b, &|_| Formula::top()), s);
    // `x <= 4` and `x >= 5 && x <= 9`: `x <= 4 || x >= 5` is true, so `x >= 5` is dropped and
    // the two join to `x <= 4 || x <= 9`.
    let below = ge(&[("x", -1)], 4);
    let between = Formula::and(vec![ge(&[("x", 1)], -5), ge(&[("x", -1)], 9)]);
    let e = Formula::either(&below, &between, &id);
    assert_eq!(e, Formula::or(vec![below.clone(), ge(&[("x", -1)], 9)]));
    assert!(same_points(&e, &Formula::or(vec![below, between]), &["x"]));
    // Equal sides: the whole is shared, and the disjunction of nothing left is `true`.
    assert_eq!(Formula::either(&a, &a, &id), a);
}

#[test]
fn a_constraint_is_reduced_by_the_gcd_of_its_coefficients() {
    let reduced = |f: Formula| match &f {
        Formula::Con(c) => c.reduced(),
        _ => unreachable!(),
    };
    // `2x - 1 >= 0` is `x - 1 >= 0` at integer points.
    assert_eq!(reduced(ge(&[("x", 2)], -1)), Some(ge(&[("x", 1)], -1)));
    // `3x - 4 >= 0` is `x >= 2`; `-4x + 6 >= 0` is `x <= 1`.
    assert_eq!(reduced(ge(&[("x", 3)], -4)), Some(ge(&[("x", 1)], -2)));
    assert_eq!(reduced(ge(&[("x", -4)], 6)), Some(ge(&[("x", -1)], 1)));
    // `6x + 4y == 10` is `3x + 2y == 5`; `6x + 4y == 9` holds nowhere, nor `2x == 1`.
    assert_eq!(
        reduced(eq(&[("x", 6), ("y", 4)], -10)),
        Some(eq(&[("x", 3), ("y", 2)], -5))
    );
    assert_eq!(
        reduced(eq(&[("x", 6), ("y", 4)], -9)),
        Some(Formula::bottom())
    );
    assert_eq!(reduced(eq(&[("x", 2)], -1)), Some(Formula::bottom()));
    // A gcd of one, or no term, keeps the constraint as written.
    assert_eq!(reduced(ge(&[("x", 2), ("y", 3)], -1)), None);
    assert_eq!(reduced(ge(&[("x", 1)], 7)), None);
    assert_eq!(reduced(ge(&[], 3)), None);
    assert_eq!(reduced(eq(&[], 0)), None);
    // Each reduced form has the same integer points.
    for (f, g) in [
        (ge(&[("x", 3)], -4), ge(&[("x", 1)], -2)),
        (ge(&[("x", -4)], 6), ge(&[("x", -1)], 1)),
        (
            eq(&[("x", 6), ("y", 4)], -10),
            eq(&[("x", 3), ("y", 2)], -5),
        ),
    ] {
        assert!(same_points(&f, &g, &["x", "y"]), "{f} and {g}");
    }
}

#[test]
fn terms_are_added_scaled_and_multiplied() {
    let (x, y) = (var("x"), var("y"));
    assert_eq!(x.times(0), Lin::constant(0));
    assert_eq!(x.minus(&x), Lin::constant(0));
    assert_eq!(x.plus(&y).minus(&y), x);
    // `(x + 1)(y + 2) = x·y + 2x + y + 2`.
    let p = x
        .plus(&Lin::constant(1))
        .product(&y.plus(&Lin::constant(2)))
        .unwrap();
    let xy = x.product(&y).unwrap();
    assert_eq!(p, xy.plus(&x.times(2)).plus(&y).plus(&Lin::constant(2)));
    assert!(!p.is_linear());
    assert!(x.plus(&y).is_linear());
    // A product is the same whichever factor is first.
    assert_eq!(y.product(&x), Some(xy.clone()));
    // A constant scales either side, a product included.
    assert_eq!(
        Lin::constant(3).product(&x.plus(&Lin::constant(1))),
        Some(x.times(3).plus(&Lin::constant(3)))
    );
    assert_eq!(xy.product(&Lin::constant(-2)), Some(xy.times(-2)));
    // A product of a product and a symbol is not a product of two factors.
    assert_eq!(xy.product(&x), None);
    assert_eq!(x.product(&xy), None);
    // `x·x` is a product of one symbol with itself.
    let xx = x.product(&x).unwrap();
    assert!(!xx.is_linear());
    let f = Formula::Con(Con::ge(&xx, &Lin::constant(4)));
    assert!(f.holds(&model(&[("x", -2)])));
    assert!(!f.holds(&model(&[("x", 1)])));
}

#[test]
fn constraints_and_terms_are_printed_with_the_first_atom_positive_on_the_left() {
    let show = |f: Formula| f.to_string();
    assert_eq!(show(ge(&[("x", 1)], -5)), "x >= 5");
    assert_eq!(show(ge(&[("x", -1)], 5)), "x <= 5");
    assert_eq!(show(eq(&[("x", 1)], -5)), "x == 5");
    assert_eq!(show(eq(&[("x", -1)], 5)), "x == 5");
    assert_eq!(show(ge(&[("x", 2), ("y", -3)], 1)), "2 * x >= 3 * y - 1");
    assert_eq!(show(ge(&[("x", 1), ("y", 1)], 0)), "x + y >= 0");
    assert_eq!(show(ge(&[], 3)), "3 >= 0");
    assert_eq!(show(eq(&[], -1)), "-1 == 0");
    assert_eq!(
        lin(&[("x", -1), ("y", 2)], -3).to_string(),
        "-x + 2 * y - 3"
    );
    assert_eq!(Lin::constant(0).to_string(), "0");
    assert_eq!(var("x").product(&var("y")).unwrap().to_string(), "x * y");
    assert_eq!(Lin::atom(Atom::Aux(4)).to_string(), "q4");
}

#[test]
fn each_conclusion_of_rung_2_is_printed() {
    assert_eq!(
        Entailment::Proved(vec![ge(&[("x", 1)], -1)]).to_string(),
        "proved from x >= 1"
    );
    assert_eq!(
        Entailment::Refuted(model(&[("x", 0), ("y", -1)])).to_string(),
        "refuted: countermodel x = 0, y = -1"
    );
    assert_eq!(
        Entailment::NotProved(model(&[("x", 2)])).to_string(),
        "not proved: the linear reading fails at x = 2"
    );
    assert_eq!(
        Entailment::Refused(Refusal::Growth).to_string(),
        format!("refused: {}", Refusal::Growth)
    );
}

/// A relation with one definition numbered `n`.
fn defined_at(n: u32) -> Relation {
    Relation {
        body: ge(&[("x", 1)], 0),
        defs: vec![(n, "x div 2".into(), Formula::top())],
        bit_ands: Vec::new(),
    }
}

#[test]
#[should_panic(expected = "numbered apart")]
fn entailment_between_relations_whose_definitions_share_a_number_panics() {
    entails(&defined_at(0), &defined_at(0));
}

#[test]
fn a_relation_is_printed_and_conjoined_with_its_definitions() {
    let r = Relation {
        body: ge(&[("x", 1)], 0),
        defs: vec![
            (0, "x div 2".into(), eq(&[("x", 1)], 0)),
            (1, "x mod 2".into(), ge(&[("y", 1)], 0)),
        ],
        bit_ands: Vec::new(),
    };
    assert_eq!(r.to_string(), "x >= 0 where q0 = x div 2, q1 = x mod 2");
    assert_eq!(
        r.defined(),
        Formula::and(vec![eq(&[("x", 1)], 0), ge(&[("y", 1)], 0)])
    );
    assert_eq!(Relation::of(Formula::top()).defined(), Formula::top());
    assert_eq!(Relation::of(ge(&[("x", 1)], 0)).to_string(), "x >= 0");
    // Definitions numbered apart are accepted.
    assert!(matches!(
        entails(&defined_at(0), &defined_at(1)),
        Entailment::Proved(_)
    ));
}

#[test]
fn split_names_skip_the_names_a_program_takes() {
    let none = HashSet::new();
    assert_eq!(free_names("ok", &none), ["ok1", "ok2"]);
    assert_eq!(free_names("ok", &HashSet::from(["ok1"])), ["ok2", "ok3"]);
    assert_eq!(free_names("ok", &HashSet::from(["ok2"])), ["ok1", "ok3"]);
    assert_eq!(
        free_names("ok", &HashSet::from(["ok1", "ok2", "ok3"])),
        ["ok4", "ok5"]
    );
    // Other names are no obstacle.
    assert_eq!(
        free_names("ok", &HashSet::from(["ok", "f1"])),
        ["ok1", "ok2"]
    );
}

#[test]
fn the_names_of_a_condition_are_its_variables_once_each_in_order() {
    assert_eq!(
        names_in("a + f(b) mod c <= 10 && d_1 in e && a > 0"),
        ["a", "b", "c", "d_1", "e"]
    );
    assert_eq!(names_in("x div 2 == y mod 3 || not z"), ["x", "y", "z"]);
    assert_eq!(names_in("true && false"), Vec::<&str>::new());
    assert_eq!(names_in(""), Vec::<&str>::new());
    assert_eq!(names_in("g (x) >= x2"), ["x", "x2"]);
    assert_eq!(names_in("3x"), Vec::<&str>::new());
}

#[test]
fn a_refusal_offers_the_repairs_its_data_supports() {
    let split = || {
        Some(Split {
            name: "ok",
            rest: "(a, b) = ",
            into: ["ok1", "ok2"],
        })
    };
    let three = ["a >= 0", "b >= 0", "a + b <= 3"];
    let w = Written {
        what: "`ok`",
        head: "ok(a, b) = ",
        tail: ";",
        split: split(),
        conjuncts: &three,
        names: &["a", "b"],
    };
    let tie = Refusal::Tie(Arc::new(Tie {
        vars: vec!["b".into(), "a".into()],
        rows: vec!["a + b <= 3".into()],
    }));
    let r = tie.repairs(&w);
    assert_eq!(r.len(), 3, "{r:#?}");
    assert_eq!(
        r[0],
        "repair: if `b` is meant to take only one value in `ok`, state that value, and the \
         checker removes `b` from the question: `ok(a, b) = b == 0 && a >= 0 && b >= 0 && a + b \
         <= 3;`, with the value in place of `0`"
    );
    assert_eq!(
        r[1],
        "repair: if `b <= a` is meant to hold in `ok`, state it, and the checker can tell `b` \
         and `a` apart: `ok(a, b) = b <= a && a >= 0 && b >= 0 && a + b <= 3;`"
    );
    // The alike variables go to separate functions: the conditions on `b` without `a` first.
    assert!(
        r[2].ends_with("`ok1(a, b) = b >= 0;` and `ok2(a, b) = a >= 0 && a + b <= 3;`"),
        "{}",
        r[2]
    );
    // A refusal with no alike variables: the first name is fixed, and the conditions halved.
    let r = Refusal::Growth.repairs(&w);
    assert_eq!(r.len(), 2, "{r:#?}");
    assert!(
        r[0].contains("if `a` is meant to take only one value"),
        "{}",
        r[0]
    );
    assert!(
        r[1].ends_with("`ok1(a, b) = a >= 0 && b >= 0;` and `ok2(a, b) = a + b <= 3;`"),
        "{}",
        r[1]
    );
    // Alike variables the program did not write are not offered.
    let made_up = Refusal::Unordered(Arc::new(Tie {
        vars: vec!["t1".into(), "t2".into()],
        rows: vec![],
    }));
    assert_eq!(made_up.repairs(&w).len(), 2);
    // One condition is not split; a test has no function to split; with no name, nothing to fix.
    let one = ["a + b <= 3"];
    let w1 = Written {
        conjuncts: &one,
        split: split(),
        ..w
    };
    assert_eq!(Refusal::Growth.repairs(&w1).len(), 1);
    let test = Written {
        what: "the test",
        head: "",
        tail: "",
        split: None,
        conjuncts: &three,
        names: &["a", "b"],
    };
    let r = Refusal::Shadows.repairs(&test);
    assert_eq!(r.len(), 1);
    assert!(
        r[0].ends_with(
            "`a == 0 && a >= 0 && b >= 0 && a + b <= 3`, with the value in place of `0`"
        ),
        "{}",
        r[0]
    );
    let nameless = Written {
        names: &[],
        split: None,
        ..test
    };
    assert!(Refusal::Growth.repairs(&nameless).is_empty());
}

#[test]
fn each_refusal_reason_ends_with_what_the_checker_kept() {
    let stopped = "The checker stopped there, with no values found and none ruled out";
    let tie = Arc::new(Tie {
        vars: vec!["a".into(), "b".into()],
        rows: vec!["a + b >= 0".into()],
    });
    let all = [
        Refusal::Growth,
        Refusal::Shadows,
        Refusal::Disjuncts,
        Refusal::Tie(tie.clone()),
        Refusal::Unordered(tie.clone()),
    ];
    for r in &all {
        let s = r.to_string();
        assert!(s.ends_with(stopped), "{s}");
        let kept = r.closed_by("It kept `x` in `[0..=3]`.").to_string();
        assert!(kept.ends_with(" It kept `x` in `[0..=3]`."), "{kept}");
        assert!(!kept.contains(stopped), "{kept}");
        // `said` changes only the shadows reason of a program of one variable with moduli.
        assert_eq!(r.said(&["x", "y"], &["3"]), s);
        assert_eq!(r.said(&["x"], &[]), s);
    }
    // The condition and conditions of a tie are counted.
    assert!(
        Refusal::Tie(tie.clone())
            .to_string()
            .contains("share the condition `a + b >= 0`")
    );
    let two = Refusal::Tie(Arc::new(Tie {
        vars: vec!["a".into(), "b".into()],
        rows: vec!["a >= 0".into(), "b >= 0".into()],
    }));
    assert!(
        two.to_string()
            .contains("share the conditions `a >= 0`, `b >= 0`")
    );
    assert!(
        Refusal::Unordered(tie)
            .to_string()
            .contains("the alternative `a + b >= 0` is left")
    );
    let said = Refusal::Shadows.said(&["x"], &["3"]);
    assert!(said.contains("one variable, `x`"), "{said}");
    assert!(said.contains("quotients by 3;"), "{said}");
    assert!(said.ends_with(stopped));
    let said = Refusal::Shadows.said(&["x"], &["2", "3", "5"]);
    assert!(said.contains("quotients by 2, 3 and 5;"), "{said}");
    assert_eq!(
        Refusal::Growth.said(&["x"], &["3"]),
        Refusal::Growth.to_string()
    );
}

#[test]
fn the_first_cause_of_a_wider_set_is_the_whole_question_then_a_symbol_then_a_disjunction() {
    let t = IntervalSet::top();
    let b = |each: Vec<Option<Refusal>>, skipped: Vec<Refusal>, whole: Option<Refusal>| Boxed {
        each: each.into_iter().map(|r| (t.clone(), r)).collect(),
        skipped,
        whole,
    };
    assert_eq!(b(vec![None, None], vec![], None).cause(), None);
    assert_eq!(
        b(
            vec![None, None],
            vec![Refusal::Disjuncts, Refusal::Growth],
            None
        )
        .cause(),
        Some(Refusal::Disjuncts)
    );
    assert_eq!(
        b(
            vec![None, Some(Refusal::Growth), Some(Refusal::Shadows)],
            vec![Refusal::Disjuncts],
            None
        )
        .cause(),
        Some(Refusal::Growth)
    );
    assert_eq!(
        b(
            vec![Some(Refusal::Growth)],
            vec![Refusal::Disjuncts],
            Some(Refusal::Shadows)
        )
        .cause(),
        Some(Refusal::Shadows)
    );
}

/// Four tasks `a`, `b`, `c`, `d`, each in `0..=2`, all different: no point, and the tasks occur
/// alike, so the search through the `!=` disjunctions would be ordered by name
/// (`omega::the_refusals_name_their_cause`).
fn pigeons() -> Formula {
    let tasks = ["a", "b", "c", "d"];
    let mut rows = Vec::new();
    for (i, t) in tasks.iter().enumerate() {
        rows.push(ge(&[(t, 1)], 0));
        rows.push(ge(&[(t, -1)], 2));
        for s in &tasks[..i] {
            rows.push(Formula::or(vec![
                ge(&[(s, 1), (t, -1)], -1),
                ge(&[(t, 1), (s, -1)], -1),
            ]));
        }
    }
    Formula::and(rows)
}

#[test]
fn a_refused_projection_keeps_the_box_of_its_rows() {
    let f = pigeons();
    let syms = [sym("a"), sym("d"), sym("e")];
    let boxed = project_each_boxed(&f, &syms);
    let plain = project_each(&f, &syms);
    match &plain {
        // Answered: each set agrees with the boxed form and is not refused.
        Ok((each, _)) => {
            for (s, (b, r)) in each.iter().zip(&boxed.each) {
                if let Ok(s) = s {
                    assert_eq!((s, r), (b, &None));
                }
            }
        }
        Err(e) => assert_eq!(boxed.whole.as_ref(), Some(e)),
    }
    // Each refused set is the box of the rows: `0..=2` for each task, every value for `e`,
    // which no row mentions.
    let rb = row_box(&f, &syms);
    assert_eq!(rb, vec![range(0, 2), range(0, 2), IntervalSet::top()]);
    for ((s, r), want) in boxed.each.iter().zip(&rb) {
        if r.is_some() {
            assert_eq!(s, want);
        } else {
            assert!(s.is_subset(want), "{s} beyond {want}");
        }
    }
    // No point, yet with six disjunctions left the sets need not be empty: past one disjunction a
    // projection is a set holding the values, not the exact one (`project`, COMPLEXITY.md rows S7
    // and S16). Each one is still within the box.
    assert!(boxed.each.iter().zip(&rb).all(|((s, _), b)| s.is_subset(b)));
    // The rows of `stages::CROSSING` raised by 8, each variable in -4..=4: every elimination
    // adds terms, so the question is refused with Growth (`stages`), and each projection is
    // refused too. Each refused set is then the box of its rows, the refusal is kept beside it,
    // and the cause is the first refused symbol's.
    let mut rows: Vec<Formula> = CROSSING
        .iter()
        .map(|(c, k)| {
            Formula::Con(Con::ge(
                &(0..4).fold(Lin::constant(k + 8), |l, i| l.plus(&x(i).times(c[i]))),
                &Lin::constant(0),
            ))
        })
        .collect();
    for i in 0..4 {
        rows.push(Formula::Con(Con::ge(&x(i), &Lin::constant(-4))));
        rows.push(Formula::Con(Con::ge(&Lin::constant(4), &x(i))));
    }
    let crossing = Formula::and(rows);
    assert_eq!(decide(&crossing), Err(Refusal::Growth));
    let xs: Vec<Atom> = (0..4).map(|i| sym(&format!("x{i}"))).collect();
    let boxed = project_each_boxed(&crossing, &xs);
    let rb = row_box(&crossing, &xs);
    // Each wider row tightens each atom once from the others' box: `2·x0 - 3·x1 - 4·x2 - x3 - 12 >= 0`
    // gives `4·x2 <= 12`, and `2·x0 - 2·x1 + 4·x2 + x3 - 9 >= 0` gives `4·x2 >= -11`, so `x2` is in
    // -2..=3; no row moves the other bounds.
    assert_eq!(
        rb,
        vec![range(-4, 4), range(-4, 4), range(-2, 3), range(-4, 4)]
    );
    assert_eq!(project_each(&crossing, &xs), Err(Refusal::Growth));
    let want = Boxed {
        each: rb.into_iter().map(|s| (s, Some(Refusal::Growth))).collect(),
        skipped: Vec::new(),
        whole: Some(Refusal::Growth),
    };
    assert_eq!(boxed, want);
    assert_eq!(boxed.cause(), Some(Refusal::Growth));
    // An answered question keeps its projections and has no cause.
    let g = Formula::and(vec![
        ge(&[("a", 1)], 0),
        ge(&[("a", -1), ("d", 1)], -1),
        ge(&[("d", -1)], 4),
    ]);
    let boxed = project_each_boxed(&g, &syms);
    assert_eq!(boxed.cause(), None);
    assert_eq!(
        boxed
            .each
            .iter()
            .map(|(s, _)| s.clone())
            .collect::<Vec<_>>(),
        vec![range(0, 3), range(1, 4), IntervalSet::top()]
    );
}

#[test]
fn project_each_answers_a_repeated_and_an_absent_symbol() {
    let f = Formula::and(vec![
        ge(&[("x", 1)], 0),
        ge(&[("x", -1), ("y", -1)], 6),
        ge(&[("y", 1)], -2),
    ]);
    let (each, skipped) = project_each(&f, &[sym("x"), sym("z"), sym("x"), sym("y")]).unwrap();
    assert!(skipped.is_empty());
    assert_eq!(
        each,
        vec![
            Ok(range(0, 4)),
            Ok(IntervalSet::top()),
            Ok(range(0, 4)),
            Ok(range(2, 6))
        ]
    );
    // An equation and the two inequalities it stands for project alike.
    let e = Formula::and(vec![
        eq(&[("x", 1), ("y", -2)], 0),
        ge(&[("y", 1)], 0),
        ge(&[("y", -1)], 3),
    ]);
    let two = Formula::and(vec![
        ge(&[("x", 1), ("y", -2)], 0),
        ge(&[("x", -1), ("y", 2)], 0),
        ge(&[("y", 1)], 0),
        ge(&[("y", -1)], 3),
    ]);
    assert_eq!(project(&e, &sym("x")), project(&two, &sym("x")));
    assert_eq!(project(&e, &sym("x")), Ok(range(0, 6)));
    // An unsatisfiable formula projects every symbol, mentioned or not, to the empty set.
    let none = Formula::and(vec![f, ge(&[("y", -1)], 1)]);
    let (each, _) = project_each(&none, &[sym("x"), sym("z")]).unwrap();
    assert_eq!(
        each,
        vec![Ok(IntervalSet::empty()), Ok(IntervalSet::empty())]
    );
}

#[test]
fn elimination_is_exact_or_declined() {
    let rows = |fs: Vec<Formula>| -> Vec<Con> {
        fs.into_iter()
            .map(|f| match &f {
                Formula::Con(c) => c.clone(),
                _ => unreachable!(),
            })
            .collect()
    };
    let x = sym("x");
    let keep_x = |a: &Atom| *a == x;
    // `x >= y` and `y >= 1`: `x >= 1`.
    let r = rows(vec![ge(&[("x", 1), ("y", -1)], 0), ge(&[("y", 1)], -1)]);
    let out = eliminated(&r, &keep_x).expect("eliminated");
    let f = Formula::and(out.into_iter().map(Formula::Con).collect());
    assert!(same_points(&f, &ge(&[("x", 1)], -1), &["x"]), "{f}");
    // No point: the single row `-1 >= 0`.
    let r = rows(vec![
        ge(&[("y", 1)], -1),
        ge(&[("y", -1)], 0),
        ge(&[("x", 1)], 0),
    ]);
    assert_eq!(
        eliminated(&r, &keep_x),
        Some(vec![Con::ge(&Lin::constant(0), &Lin::constant(1))])
    );
    // Keeping every atom keeps the rows' points.
    let r = rows(vec![ge(&[("x", 1), ("y", -1)], 0), ge(&[("y", 1)], -1)]);
    let out = eliminated(&r, &|_| true).expect("nothing to eliminate");
    let f = Formula::and(out.into_iter().map(Formula::Con).collect());
    let g = Formula::and(r.into_iter().map(Formula::Con).collect());
    assert!(same_points(&f, &g, &["x", "y"]));
    // `x == 2y` leaves `x` even, which no row over `x` alone states: if rows are given, they
    // hold exactly at the even values.
    let r = rows(vec![eq(&[("x", 1), ("y", -2)], 0)]);
    if let Some(out) = eliminated(&r, &keep_x) {
        let f = Formula::and(out.into_iter().map(Formula::Con).collect());
        for v in -6i64..=6 {
            assert_eq!(
                f.holds(&model(&[("x", v.into())])),
                v % 2 == 0,
                "{f} at {v}"
            );
        }
    }
}

#[test]
fn colors_tell_apart_only_what_the_structure_does() {
    let rows = |fs: Vec<Formula>| -> Vec<Con> {
        fs.into_iter()
            .map(|f| match &f {
                Formula::Con(c) => c.clone(),
                _ => unreachable!(),
            })
            .collect()
    };
    // `x + y <= 5`, `x >= 0`, `y >= 0`: `x` and `y` alike.
    let r = rows(vec![
        ge(&[("x", -1), ("y", -1)], 5),
        ge(&[("x", 1)], 0),
        ge(&[("y", 1)], 0),
    ]);
    let (atoms, col) = colors(&r);
    assert_eq!(atoms.len(), 2);
    assert_eq!(col[&sym("x")], col[&sym("y")]);
    // `x + 2y <= 5`: told apart by their coefficients.
    let r = rows(vec![
        ge(&[("x", -1), ("y", -2)], 5),
        ge(&[("x", 1)], 0),
        ge(&[("y", 1)], 0),
    ]);
    let (_, col) = colors(&r);
    assert_ne!(col[&sym("x")], col[&sym("y")]);
    // Renaming changes no color: `u`, `v` in place of `x`, `y`.
    let r2 = rows(vec![
        ge(&[("v", -1), ("u", -2)], 5),
        ge(&[("v", 1)], 0),
        ge(&[("u", 1)], 0),
    ]);
    let (_, col2) = colors(&r2);
    assert_eq!(col[&sym("x")], col2[&sym("v")]);
    assert_eq!(col[&sym("y")], col2[&sym("u")]);
    // No rows: no atoms.
    assert!(colors(&[]).0.is_empty());
}

#[test]
fn the_test_hooks_change_no_answer_and_their_counters_reset() {
    let f = Formula::and(vec![
        pigeons(),
        // A second part over other variables.
        ge(&[("p", 1), ("q", -1)], 0),
        ge(&[("q", 1)], -1),
    ]);
    let g = Formula::and(vec![
        ge(&[("p", 1), ("q", -1)], 0),
        ge(&[("q", 1)], -1),
        ge(&[("r", 1)], 0),
    ]);
    for h in [&f, &g] {
        assert_eq!(with_parts_reversed(|| decide(h)), decide(h));
        assert_eq!(without_modular_empty_check(|| decide(h)), decide(h));
    }
    let _ = satisfiable(&f);
    parts_tested();
    assert_eq!(parts_tested(), 0);
    let _ = project(&g, &sym("p"));
    hull_sides_asked();
    assert_eq!(hull_sides_asked(), 0);
}

/// The relation of the body of `ok` in `src`, over its parameters each declared `int`, holds at
/// each point of the window `-7..=7` exactly where the interpreter's value of the body is
/// `true`; `None` when the body is outside the domain.
fn agrees(src: &str) -> Option<()> {
    let src = int_ok(src);
    let (names, body) = function(&src);
    let r = relations(&[&body], &names, false)?.remove(0);
    for p in window(names.len(), -7, 7) {
        let at = Formula::and(
            names
                .iter()
                .zip(&p)
                .map(|(n, v)| {
                    Formula::Con(Con::eq(
                        &Lin::atom(Atom::Sym(n.clone())),
                        &Lin::constant(*v),
                    ))
                })
                .collect(),
        );
        let f = Formula::and(vec![r.defined(), r.body.clone(), at]);
        let sat = satisfiable(&f).unwrap_or_else(|e| panic!("{src} at {p:?}: refused: {e}"));
        assert_eq!(
            sat.is_some(),
            holds(&body, &names, &p),
            "{src} at {p:?}: the relation is {r}"
        );
    }
    Some(())
}

#[test]
fn tests_at_the_edges_of_the_operators_agree_with_the_interpreter() {
    for src in [
        // Euclidean quotient and remainder by a negative constant, and by one.
        "ok(x) = x mod -3 == 1;",
        "ok(x) = x div -3 >= 1;",
        "ok(x) = x div -1 == -x;",
        "ok(x) = x mod 1 == 0;",
        "ok(x, y) = (x + y) div 4 == y mod 3;",
        // `abs`, `min` and `max`, and an `if` over a test.
        "ok(x, y) = abs(x - y) <= 2;",
        "ok(x, y) = min(x, y) == max(x, 0);",
        "ok(x, y) = (if x > y { x - y } else { y - x }) == 3;",
        // Negation of a conjunction, `!=`, and the constants.
        "ok(x) = !(x >= 2 && x <= 4);",
        "ok(x, y) = x != y;",
        "ok(x) = true;",
        "ok(x) = false;",
        // An equation with no integer point, and one with a coefficient.
        "ok(x) = 2 * x == 7;",
        "ok(x) = 2 * x + 1 == 7;",
        "ok(x, y) = 3 * x - 2 * y >= 1 || x == y;",
        // Powers 0 and 1 of a variable, and a power of a constant.
        "ok(x) = x ^ 0 == 1;",
        "ok(x) = x ^ 1 + 2 ^ 2 == 6;",
        // `&&` beside `||`.
        "ok(x, y) = x >= 0 && y >= 0 || x == -y;",
    ] {
        assert!(agrees(src).is_some(), "{src}: outside the domain");
    }
}

#[test]
fn the_box_of_rows_reads_one_term_rows_equations_and_disjunctions_that_bound_in_every_case() {
    let (x, y) = (sym("x"), sym("y"));
    let within =
        |s: &str, lo: i128, hi: i128| Formula::and(vec![ge(&[(s, 1)], -lo), ge(&[(s, -1)], hi)]);
    let boxes = |f: &Formula| row_box(f, &[x.clone(), y.clone()]);
    // A disjunction every disjunct of which bounds `x` gives it their hull, gaps and all.
    let two = Formula::or(vec![within("x", 0, 2), within("x", 5, 7)]);
    assert_eq!(boxes(&two), vec![range(0, 7), IntervalSet::top()]);
    // A disjunct with no point bounds nothing and is passed over.
    let none = Formula::and(vec![ge(&[("x", 1)], -3), ge(&[("x", -1)], 1)]);
    let one = Formula::or(vec![within("x", 0, 2), none.clone()]);
    assert_eq!(boxes(&one), vec![range(0, 2), IntervalSet::top()]);
    // A disjunct that does not bound `x` leaves it unbounded; one-sided bounds stay one-sided.
    let open = Formula::or(vec![within("x", 0, 2), ge(&[("y", 1)], 0)]);
    assert_eq!(boxes(&open), vec![IntervalSet::top(), IntervalSet::top()]);
    let lower = Formula::or(vec![ge(&[("x", 1)], 0), ge(&[("x", 1)], -5)]);
    assert_eq!(
        boxes(&lower)[0],
        IntervalSet::range(End::Fin(Num::from(0)), End::PosInf)
    );
    // A negation is not read.
    assert_eq!(
        boxes(&Formula::negate(ge(&[("x", 1)], -3)))[0],
        IntervalSet::top()
    );
    // No point: every set is empty, whether the bounds cross or the formula is `false`.
    assert_eq!(
        boxes(&none),
        vec![IntervalSet::empty(), IntervalSet::empty()]
    );
    assert_eq!(
        boxes(&Formula::bottom()),
        vec![IntervalSet::empty(), IntervalSet::empty()]
    );
    // An equation is its two rows, each divided by the gcd: `2·x == 6` fixes `x` at 3, and
    // `2·x - 1 >= 0` is `x >= 1`.
    assert_eq!(boxes(&eq(&[("x", 2)], -6))[0], range(3, 3));
    assert_eq!(
        boxes(&ge(&[("x", 2)], -1))[0],
        IntervalSet::range(End::Fin(Num::from(1)), End::PosInf)
    );
    // A wider row tightens each of its atoms once from the others' bounds:
    // `x + y <= 3` with `y >= 1` gives `x <= 2`.
    let wide = Formula::and(vec![
        ge(&[("x", -1), ("y", -1)], 3),
        within("y", 1, 9),
        ge(&[("x", 1)], 0),
    ]);
    assert_eq!(boxes(&wide), vec![range(0, 2), range(1, 3)]);
}

/// The name a program wrote for a symbol elaboration renamed `x@2`.
fn unversioned(s: &str) -> &str {
    s.split('@').next().unwrap_or(s)
}

#[test]
fn factors_and_formulas_are_written_with_the_names_the_program_wrote() {
    let x: Arc<str> = Arc::from("x");
    assert!(Factor::Sym(x.clone()).is(&x));
    assert!(!Factor::Sym(Arc::from("y")).is(&x));
    assert!(!Factor::Aux(0).is(&x));
    assert_eq!(Factor::Sym(x.clone()).to_string(), "x");
    assert_eq!(Factor::Aux(3).to_string(), "q3");
    assert_eq!(Factor::of(&Atom::Aux(3)), Some(Factor::Aux(3)));
    assert_eq!(Factor::Aux(3).atom(), Atom::Aux(3));
    assert_eq!(
        Factor::of(&Atom::Product(Factor::Aux(1), Factor::Aux(2))),
        None
    );
    let f = Formula::and(vec![ge(&[("x@2", 1)], -1), ge(&[("x@2", -1), ("y", 1)], 0)]);
    assert_eq!(f.written(unversioned), f.to_string().replace("x@2", "x"));
    assert_eq!(
        Formula::top().written(unversioned),
        Formula::top().to_string()
    );
}

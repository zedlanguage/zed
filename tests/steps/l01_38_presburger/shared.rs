//! Formulas that hold a part in more than one place, as the formula of a `let`-bound test
//! holds that test once at each use: an eligibility rule `x >= 1 && y >= 1` checked both in a
//! discount and in a refund condition is one part with two parents. Every question the
//! domain answers about such a formula has the answer it has for the same formula written
//! out, with a separate copy of the part at each place (COMPLEXITY.md S31).

use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use zed_tests::instances::Rng;
use zedc::store::int::Int;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, decide, project, satisfiable};

fn sym(n: &str) -> Lin {
    Lin::atom(Atom::Sym(n.into()))
}

/// `a x + b y + c >= 0`, or `== 0` when `eq`.
fn con(a: i64, b: i64, c: i64, eq: bool) -> Formula {
    let l = sym("x")
        .times(a)
        .plus(&sym("y").times(b))
        .plus(&Lin::constant(c));
    Formula::Con(if eq {
        Con::eq(&l, &Lin::constant(0))
    } else {
        Con::ge(&l, &Lin::constant(0))
    })
}

fn and(fs: Vec<Formula>) -> Formula {
    Formula::And(Arc::new(fs))
}

fn or(fs: Vec<Formula>) -> Formula {
    Formula::Or(Arc::new(fs))
}

fn not(f: Formula) -> Formula {
    Formula::Not(Arc::new(f))
}

/// The formula with a copy of each part at each place that holds it, so that no part has
/// two parents.
fn written_out(f: &Formula) -> Formula {
    match f {
        Formula::Con(c) => Formula::Con(c.clone()),
        Formula::Not(g) => not(written_out(g)),
        Formula::And(gs) => and(gs.iter().map(written_out).collect()),
        Formula::Or(gs) => or(gs.iter().map(written_out).collect()),
    }
}

fn hash(f: &Formula) -> u64 {
    let mut h = DefaultHasher::new();
    f.hash(&mut h);
    h.finish()
}

fn model(x: i64, y: i64) -> Model {
    [("x", x), ("y", y)]
        .into_iter()
        .map(|(n, v)| (Atom::Sym(n.into()), Int::from(v)))
        .collect()
}

/// Panics unless `f` and `written` give the same answer to each question: equal, hashed
/// alike, printed alike, the same atoms and constraints, true at the same points of a window,
/// the same decision, model and projections, and the same after a constraint is forgotten.
fn agree(f: &Formula, written: &Formula, what: &str) {
    assert_eq!(f, written, "{what}");
    assert_eq!(f.cmp(written), Ordering::Equal, "{what}");
    assert_eq!(hash(f), hash(written), "{what}");
    assert_eq!(f.to_string(), written.to_string(), "{what}");
    assert_eq!(format!("{f:?}"), format!("{written:?}"), "{what}");
    assert_eq!(f.atoms(), written.atoms(), "{what}");
    for x in -4..=4 {
        for y in -4..=4 {
            let m = model(x, y);
            assert_eq!(f.holds(&m), written.holds(&m), "{what} at ({x}, {y})");
        }
    }
    assert_eq!(decide(f), decide(written), "{what}");
    let (a, b) = (satisfiable(f), satisfiable(written));
    assert_eq!(a, b, "{what}");
    if let Ok(Some(m)) = &a {
        assert!(written.holds(m), "{what}: the model {m:?} holds");
    }
    for n in ["x", "y"] {
        let s = Atom::Sym(n.into());
        assert_eq!(project(f, &s), project(written, &s), "{what}: {n}");
    }
    let x: Arc<str> = "x".into();
    assert_eq!(f.forget(&x), written.forget(&x), "{what}");
    let flip = |c: &Con| Formula::Con(Con::ge(&Lin::constant(0), &c.lin));
    assert_eq!(f.map_cons(&flip), written.map_cons(&flip), "{what}");
}

/// A random formula built from a pool: each new part takes up to three parts of the pool,
/// which then have two or more parents.
fn random_shared(rng: &mut Rng) -> Formula {
    let mut pool: Vec<Formula> = (0..4)
        .map(|_| {
            con(
                rng.int(-2, 2),
                rng.int(-2, 2),
                rng.int(-3, 3),
                rng.below(5) == 0,
            )
        })
        .collect();
    for _ in 0..8 {
        let pick = |rng: &mut Rng| pool[rng.below(pool.len())].clone();
        let g = match rng.below(5) {
            0 => not(pick(rng)),
            1 | 2 => and((0..rng.below(4)).map(|_| pick(rng)).collect()),
            _ => or((0..rng.below(4)).map(|_| pick(rng)).collect()),
        };
        pool.push(g);
    }
    pool.pop().expect("a formula")
}

#[test]
fn a_formula_with_shared_parts_answers_as_written_out() {
    let mut rng = Rng::new(0x531);
    for i in 0..300 {
        let f = random_shared(&mut rng);
        agree(&f, &written_out(&f), &format!("formula {i}: {f}"));
    }
}

#[test]
fn shared_parts_order_formulas_as_written_out() {
    // Sorting a list of formulas, as the parts of a disjunction are sorted, puts them in the
    // same order whether each part is shared or copied.
    let mut rng = Rng::new(0x532);
    let fs: Vec<Formula> = (0..60).map(|_| random_shared(&mut rng)).collect();
    let ws: Vec<Formula> = fs.iter().map(written_out).collect();
    for (a, wa) in fs.iter().zip(&ws) {
        for (b, wb) in fs.iter().zip(&ws) {
            assert_eq!(a.cmp(b), wa.cmp(wb), "{a} against {b}");
        }
    }
}

#[test]
fn an_empty_conjunction_or_disjunction_shared_is_true_or_false() {
    let yes = Formula::top();
    let no = Formula::bottom();
    let both_true = and(vec![yes.clone(), yes.clone()]);
    let both_false = or(vec![no.clone(), no.clone()]);
    agree(&both_true, &written_out(&both_true), "true && true");
    agree(&both_false, &written_out(&both_false), "false || false");
    assert_eq!(decide(&both_true), Ok(true));
    assert_eq!(decide(&both_false), Ok(false));
    // `!false` held twice is true at every point.
    let never = not(no);
    let twice = and(vec![never.clone(), never]);
    assert_eq!(decide(&twice), Ok(true));
    agree(&twice, &written_out(&twice), "!false && !false");
}

#[test]
fn a_rule_and_its_negation_held_as_one_part_meet_nowhere() {
    // An eligibility rule and a refusal written as its negation: `rule && !rule` has no
    // point, and `rule || !rule` holds everywhere, so its negation has no point.
    let rule = and(vec![con(1, 0, -1, false), con(0, 1, -1, false)]);
    let both = and(vec![rule.clone(), not(rule.clone())]);
    let either = or(vec![rule.clone(), not(rule.clone())]);
    assert_eq!(decide(&both), Ok(false));
    assert_eq!(decide(&not(either.clone())), Ok(false));
    assert_eq!(decide(&either), Ok(true));
    agree(&both, &written_out(&both), "rule && !rule");
    agree(&either, &written_out(&either), "rule || !rule");
}

#[test]
fn a_rule_shared_by_both_arms_of_a_disjunction_bounds_each_arm() {
    // `(rule && x <= 0) || (rule && y <= 0)` with `rule` `x >= 5 || y >= 5`: the first arm
    // forces `y >= 5` beside `x <= 0`, and the second `x >= 5`, so `x` is at most 0 or at
    // least 5, and the point `(0, 0)` meets neither arm.
    let rule = or(vec![con(1, 0, -5, false), con(0, 1, -5, false)]);
    let f = or(vec![
        and(vec![rule.clone(), con(-1, 0, 0, false)]),
        and(vec![rule.clone(), con(0, -1, 0, false)]),
    ]);
    agree(&f, &written_out(&f), "a rule in both arms");
    assert!(!f.holds(&model(0, 0)));
    assert!(f.holds(&model(0, 5)) && f.holds(&model(5, 0)));
    let x = project(&f, &Atom::Sym("x".into())).expect("a projection");
    assert_eq!(x.to_string(), "[..=0, 5..]");
}

#[test]
fn a_part_shared_many_times_over_is_read_once_per_pass() {
    // Each level holds the level below twice, so the formula written out has 2^40 constraints;
    // comparing, hashing, evaluating and listing read each of the 40 distinct parts once.
    let doubled = |depth: i64| {
        let mut f = con(1, 0, 0, false);
        for i in 0..depth {
            f = or(vec![
                and(vec![f.clone(), con(0, 1, -i, false)]),
                and(vec![f, con(1, 0, -i, false)]),
            ]);
        }
        f
    };
    // Two such formulas built apart share no part with each other, and are equal.
    let (f, g) = (doubled(40), doubled(40));
    assert_eq!(f, g);
    assert_eq!(hash(&f), hash(&g));
    assert!(f.holds(&model(100, 100)));
    assert!(!f.holds(&model(-1, 100)));
    assert_eq!(f.atoms().len(), 2);
    // The 80 constraints of the levels, and the first one, a constraint and not a shared node,
    // copied into both parts of the first level.
    assert_eq!(f.cons().len(), 82);
    assert_eq!(decide(&f), Ok(true));
    // A projection takes the union over the disjuncts written out, 2^depth of them, so it is
    // checked at depth 6.
    let small = doubled(6);
    agree(&small, &written_out(&small), "six levels");
    assert_eq!(
        project(&small, &Atom::Sym("x".into())).map(|s| s.to_string()),
        Ok("[0..]".to_string())
    );
}

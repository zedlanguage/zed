//! Formulas that hold a part in more than one place, as the formula of a `let`-bound test
//! holds that test once at each use: an eligibility rule `x >= 1 && y >= 1` checked both in a
//! discount and in a refund condition is one part with two parents. Every question the
//! domain answers about such a formula has the answer it has for the same formula written
//! out, with a separate copy of the part at each place (COMPLEXITY.md S31).

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use zed_tests::instances::Rng;
use zed_tests::scaling;
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

/// The chain of rules `a0 = x >= 0 && y >= 0`, `a1 = x >= 1 <join> a0` and
/// `ai = x >= i <join> a(i-1) <join> a(i-2)`, each a name kept whole where it is used, as the
/// translator keeps the formula of a name used as an operand of `&&` or `||`
/// ([`Formula::and_keeping`]), and `ad` returned. Each rule is one part, held by the two after
/// it, so the chain written out holds `a0` a number of times exponential in `d`.
fn named_chain(d: usize, and: bool) -> Formula {
    let mut rules = vec![Formula::and(vec![con(1, 0, 0, false), con(0, 1, 0, false)])];
    for i in 1..=d as i64 {
        let mut fs = vec![con(1, 0, -i, false)];
        fs.extend(rules.iter().rev().take(2).cloned());
        // Every operand but the first, a constraint, is a name.
        rules.push(if and {
            Formula::and_keeping(fs, |j| j > 0)
        } else {
            Formula::or_keeping(fs, |j| j > 0)
        });
    }
    rules.pop().expect("the last rule")
}

/// `named_chain(d, and)` with `x >= -1` joined after it.
fn extended_chain(d: usize, and: bool) -> Formula {
    let fs = vec![named_chain(d, and), con(1, 0, 1, false)];
    if and {
        Formula::and_keeping(fs, |j| j == 0)
    } else {
        Formula::or_keeping(fs, |j| j == 0)
    }
}

#[test]
fn comparing_a_named_chain_with_one_built_apart_takes_time_near_linear_in_its_length() {
    // Two chains built apart share no part, so each pair of their parts is compared.
    let built: BTreeMap<usize, Vec<[Formula; 3]>> = [30, 240]
        .map(|d| {
            let three = |and| {
                [
                    named_chain(d, and),
                    named_chain(d, and),
                    extended_chain(d, and),
                ]
            };
            (d, vec![three(true), three(false)])
        })
        .into();
    scaling::check(
        "a chain of d names compared with an equal and an extended one built apart",
        30,
        |d| {
            for [a, b, c] in &built[&d] {
                assert!(a == b);
                assert_eq!(a.cmp(c), Ordering::Less);
                std::hint::black_box((a.cmp(b), c.cmp(a)));
            }
        },
    );
}

/// The chain of [`named_chain`] built of nodes made here, with `y >= y0` in `a0`; when
/// `regroup`, each rule `ai` from `a2` on is `(x >= i <join> a(i-1)) <join> a(i-2)`, a node
/// of its own around the first two operands, so that its parts read as flattened are those
/// of the chain but its nodes begin and end at other places.
fn chain(d: usize, join: fn(Vec<Formula>) -> Formula, regroup: bool, y0: i64) -> Formula {
    let mut rules = vec![join(vec![con(1, 0, 0, false), con(0, 1, -y0, false)])];
    for i in 1..=d {
        let x = con(1, 0, -(i as i64), false);
        let a = rules[i - 1].clone();
        rules.push(match i.checked_sub(2).map(|j| rules[j].clone()) {
            Some(b) if regroup => join(vec![join(vec![x, a]), b]),
            Some(b) => join(vec![x, a, b]),
            None => join(vec![x, a]),
        });
    }
    rules.pop().expect("the last rule")
}

/// The constraints of `f`, a conjunction or disjunction of constraints and of parts of its
/// own variant, read as flattened, written out.
fn flat(f: &Formula) -> Vec<Con> {
    let mut out = Vec::new();
    let mut stack = vec![f];
    while let Some(g) = stack.pop() {
        match g {
            Formula::Con(c) => out.push(c.clone()),
            Formula::And(gs) | Formula::Or(gs) => stack.extend(gs.iter().rev()),
            Formula::Not(_) => unreachable!("a chain holds no negation"),
        }
    }
    out
}

#[test]
fn chains_grouped_alike_or_otherwise_compare_as_their_constraints_written_out() {
    for d in 0..=9 {
        for join in [and as fn(Vec<Formula>) -> Formula, or] {
            let extended = join(vec![chain(d, join, false, 0), con(1, 0, 1, false)]);
            let fs = [
                chain(d, join, false, 0),
                chain(d, join, false, 0),
                chain(d, join, true, 0),
                extended,
                chain(d, join, false, 1),
                chain(d, join, true, 1),
            ];
            for p in &fs {
                for q in &fs {
                    let o = flat(p).cmp(&flat(q));
                    assert_eq!(p.cmp(q), o, "d = {d}: {p} against {q}");
                    if o == Ordering::Equal {
                        assert_eq!(hash(p), hash(q), "d = {d}: {p}");
                    }
                }
            }
        }
    }
}

#[test]
fn parts_entered_together_that_end_apart_are_not_taken_as_equal() {
    // `p = [X, c2, X, c3]` and `q = [Y, Y, c4]` with `X = [c1]` and `Y = [c1, c2]`: `X` and
    // `Y` are met at one point and their parts agree until `X` runs out, but they are not
    // equal, so the second pair of them is compared again and `c3` meets `c2`.
    let cs: Vec<Formula> = (1..=4).map(|i| con(1, 0, -i, false)).collect();
    for join in [and as fn(Vec<Formula>) -> Formula, or] {
        for c2 in &cs[1..] {
            for c3 in &cs[1..] {
                for c4 in &cs[1..] {
                    let x = join(vec![cs[0].clone()]);
                    let y = join(vec![cs[0].clone(), c2.clone()]);
                    let p = join(vec![x.clone(), c2.clone(), x, c3.clone()]);
                    let q = join(vec![y.clone(), y, c4.clone()]);
                    assert_eq!(p.cmp(&q), flat(&p).cmp(&flat(&q)), "{p} against {q}");
                    assert_eq!(q.cmp(&p), flat(&q).cmp(&flat(&p)), "{q} against {p}");
                }
            }
        }
    }
}

/// Two chains of `d` levels with the same constraints written out, grouped apart: on one
/// side level `i` is `[[t, t], ci]` and on the other `[[t', t', ci]]`, where `t` and `t'` are
/// the level below, each a part held twice. Each level's outer pair is entered together, and
/// so is its inner pair, which ends at another place on each side; the outer pair still ends
/// at one place on both. With `x` the conjunction or disjunction of a constraint, each side
/// written out holds `2^d` copies of `c0`.
fn split_chains(d: usize, join: fn(Vec<Formula>) -> Formula) -> (Formula, Formula) {
    let c0 = con(0, 1, 0, false);
    let (mut a, mut b) = (join(vec![c0.clone()]), join(vec![c0]));
    for i in 1..=d as i64 {
        let ci = con(1, 0, -i, false);
        a = join(vec![join(vec![a.clone(), a]), ci.clone()]);
        b = join(vec![join(vec![b.clone(), b, ci])]);
    }
    (a, b)
}

#[test]
fn chains_whose_inner_parts_end_apart_compare_in_time_near_linear_in_their_length() {
    let built: BTreeMap<usize, Vec<(Formula, Formula)>> = [30, 240]
        .map(|d| (d, vec![split_chains(d, and), split_chains(d, or)]))
        .into();
    scaling::check(
        "two chains of d levels whose inner parts end at other places on each side",
        30,
        |d| {
            for (a, b) in &built[&d] {
                assert!(a == b);
                std::hint::black_box(b.cmp(a));
            }
        },
    );
    let (a, b) = split_chains(6, and);
    assert_eq!(flat(&a), flat(&b));
    assert_eq!(hash(&a), hash(&b));
}

/// A formula written out with each conjunction directly in a conjunction, and each
/// disjunction directly in a disjunction, flattened into it: the order the derived one gives
/// on it is the order [`Formula::cmp`] must give.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Written {
    Con(Con),
    Not(Box<Written>),
    And(Vec<Written>),
    Or(Vec<Written>),
}

fn written(f: &Formula) -> Written {
    fn parts(gs: &[Formula], and: bool, out: &mut Vec<Written>) {
        for g in gs {
            match g {
                Formula::And(hs) if and => parts(hs, and, out),
                Formula::Or(hs) if !and => parts(hs, and, out),
                g => out.push(written(g)),
            }
        }
    }
    match f {
        Formula::Con(c) => Written::Con(c.clone()),
        Formula::Not(g) => Written::Not(Box::new(written(g))),
        Formula::And(gs) => {
            let mut out = Vec::new();
            parts(gs, true, &mut out);
            Written::And(out)
        }
        Formula::Or(gs) => {
            let mut out = Vec::new();
            parts(gs, false, &mut out);
            Written::Or(out)
        }
    }
}

/// A node of a formula to be built: a constraint, or a variant over earlier nodes.
enum Spec {
    Con(Formula),
    Not(usize),
    And(Vec<usize>),
    Or(Vec<usize>),
}

/// Random specs: constraints, then nodes over earlier ones, conjunctions and disjunctions
/// often of the same variant as some of their parts, some of them empty.
fn random_specs(rng: &mut Rng) -> Vec<Spec> {
    let mut specs: Vec<Spec> = (0..3)
        .map(|_| Spec::Con(con(rng.int(-1, 1), rng.int(-1, 1), rng.int(-2, 2), false)))
        .collect();
    for _ in 0..7 {
        let n = specs.len();
        let kids = |rng: &mut Rng| (0..rng.below(4)).map(|_| rng.below(n)).collect();
        specs.push(match rng.below(6) {
            0 => Spec::Not(rng.below(n)),
            1..=3 => Spec::And(kids(rng)),
            _ => Spec::Or(kids(rng)),
        });
    }
    specs
}

/// Node `i` of `specs` built with the parts of each conjunction and disjunction grouped at
/// random into nodes of its own variant, empty ones among them. Each place that uses a node
/// takes, at random, the one node built for it before (`kept`) or one grouped anew.
fn build(specs: &[Spec], i: usize, rng: &mut Rng, kept: &mut [Option<Formula>]) -> Formula {
    if let Some(f) = &kept[i]
        && rng.below(2) == 0
    {
        return f.clone();
    }
    let f = match &specs[i] {
        Spec::Con(c) => c.clone(),
        Spec::Not(j) => not(build(specs, *j, rng, kept)),
        Spec::And(js) | Spec::Or(js) => {
            let join = if matches!(specs[i], Spec::And(_)) {
                and
            } else {
                or
            };
            let mut parts: Vec<Formula> = js.iter().map(|&j| build(specs, j, rng, kept)).collect();
            // Wrap random runs of the parts, empty runs too, in nodes of the variant.
            for _ in 0..rng.below(3) {
                let at = rng.below(parts.len() + 1);
                let len = rng.below(parts.len() - at + 1);
                let run: Vec<Formula> = parts.drain(at..at + len).collect();
                parts.insert(at, join(run));
            }
            join(parts)
        }
    };
    if kept[i].is_none() {
        kept[i] = Some(f.clone());
    }
    f
}

#[test]
fn formulas_grouped_and_shared_at_random_compare_and_hash_as_written_out() {
    // Each round builds several formulas from one set of specs, so that they share parts at
    // several depths, group the same parts otherwise and often are equal; and one from
    // specs with a constraint changed, so that they differ late.
    let mut rng = Rng::new(0x533);
    for round in 0..400 {
        let mut specs = random_specs(&mut rng);
        let mut kept: Vec<Option<Formula>> = vec![None; specs.len()];
        let top = specs.len() - 1;
        let mut fs: Vec<Formula> = (0..4)
            .map(|_| build(&specs, top, &mut rng, &mut kept))
            .collect();
        fs.push(build(&specs, top - 1, &mut rng, &mut kept));
        specs[rng.below(3)] = Spec::Con(con(1, 1, 3, true));
        let mut fresh: Vec<Option<Formula>> = vec![None; specs.len()];
        fs.push(build(&specs, top, &mut rng, &mut fresh));
        for p in &fs {
            for q in &fs {
                let o = written(p).cmp(&written(q));
                assert_eq!(p.cmp(q), o, "round {round}: {p} against {q}");
                assert_eq!(
                    p == q,
                    o == Ordering::Equal,
                    "round {round}: {p} against {q}"
                );
                if o == Ordering::Equal {
                    assert_eq!(hash(p), hash(q), "round {round}: {p}");
                }
            }
        }
    }
}

/// One sequence of constraints grouped at other places on each side: `t0 = [c]` and
/// `ti = [t(i-1), t(i-1), ci]` on one, and on the other `[c, rd]` with `r0 = []` and
/// `ri = [r(i-1), c, r(i-1), ci]`, so that no node on one side begins and ends where one on
/// the other does. Compare reads it at the cost of the `2^(d+1) - 1` constraints written out
/// (the tradeoff at [`Formula::cmp`], COMPLEXITY.md S31b).
fn shifted_chains(d: usize, join: fn(Vec<Formula>) -> Formula) -> (Formula, Formula) {
    let c = con(0, 1, 0, false);
    let (mut t, mut r) = (join(vec![c.clone()]), join(vec![]));
    for i in 1..=d as i64 {
        let ci = con(1, 0, -i, false);
        t = join(vec![t.clone(), t, ci.clone()]);
        r = join(vec![r.clone(), c.clone(), r, ci]);
    }
    (t, join(vec![c, r]))
}

#[test]
fn one_sequence_grouped_at_other_places_on_each_side_compares_as_written_out() {
    for d in 0..=9 {
        for join in [and as fn(Vec<Formula>) -> Formula, or] {
            let (t, r) = shifted_chains(d, join);
            let (split_a, split_b) = split_chains(d, join);
            let fs = [t, r, split_a, split_b];
            for p in &fs {
                for q in &fs {
                    let o = written(p).cmp(&written(q));
                    assert_eq!(p.cmp(q), o, "d = {d}: {p} against {q}");
                    if o == Ordering::Equal {
                        assert_eq!(hash(p), hash(q), "d = {d}: {p}");
                    }
                }
            }
            assert_eq!(fs[0], fs[1]);
            assert_eq!(fs[2], fs[3]);
        }
    }
}

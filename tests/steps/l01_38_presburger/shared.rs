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
use zedc::store::presburger::{
    Atom, Con, Formula, Lin, Model, Shared, decide, project, satisfiable,
};

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

pub(super) fn and(fs: Vec<Formula>) -> Formula {
    Formula::And(Shared::new(fs))
}

pub(super) fn or(fs: Vec<Formula>) -> Formula {
    Formula::Or(Shared::new(fs))
}

fn not(f: Formula) -> Formula {
    Formula::Not(Shared::new(f))
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

pub(super) fn hash(f: &Formula) -> u64 {
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
pub(super) fn named_chain(d: usize, and: bool) -> Formula {
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
pub(super) fn extended_chain(d: usize, and: bool) -> Formula {
    let fs = vec![named_chain(d, and), con(1, 0, 1, false)];
    if and {
        Formula::and_keeping(fs, |j| j == 0)
    } else {
        Formula::or_keeping(fs, |j| j == 0)
    }
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
pub(super) fn flat(f: &Formula) -> Vec<Con> {
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
pub(super) fn split_chains(d: usize, join: fn(Vec<Formula>) -> Formula) -> (Formula, Formula) {
    let c0 = con(0, 1, 0, false);
    let (mut a, mut b) = (join(vec![c0.clone()]), join(vec![c0]));
    for i in 1..=d as i64 {
        let ci = con(1, 0, -i, false);
        a = join(vec![join(vec![a.clone(), a]), ci.clone()]);
        b = join(vec![join(vec![b.clone(), b, ci])]);
    }
    (a, b)
}

/// A formula written out with each conjunction directly in a conjunction, and each
/// disjunction directly in a disjunction, flattened into it: the order the derived one gives
/// on it is the order [`Formula::cmp`] must give.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) enum Written {
    Con(Con),
    Not(Box<Written>),
    And(Vec<Written>),
    Or(Vec<Written>),
}

pub(super) fn written(f: &Formula) -> Written {
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
/// the other does. Each side holds `2^(d+1) - 1` constraints written out in `2d + 2` distinct
/// parts; compare parses the two sequences ([`Formula::cmp`], COMPLEXITY.md S31b).
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
    for d in 0..=12 {
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

/// [`shifted_chains`] and the same two with one more constraint at the end of each, unequal,
/// so that they differ at the last of their constraints written out.
pub(super) fn shifted_pairs(d: usize) -> Vec<(Formula, Formula, Ordering)> {
    let mut out = Vec::new();
    for join in [and as fn(Vec<Formula>) -> Formula, or] {
        let (t, r) = shifted_chains(d, join);
        let (x, y) = (con(0, 1, -1, false), con(0, 1, -2, false));
        let o = written(&x).cmp(&written(&y));
        out.push((join(vec![t.clone(), x]), join(vec![r.clone(), y]), o));
        out.push((t, r, Ordering::Equal));
    }
    out
}

/// Specs of `depth` levels over three constraints, each level of two or three nodes over the
/// level below and the constraints, so that a node is reached by many paths and its parts,
/// written out, are up to `3^depth` constraints.
fn layered_specs(rng: &mut Rng, depth: usize) -> Vec<Spec> {
    let mut specs: Vec<Spec> = (0..3)
        .map(|_| Spec::Con(con(rng.int(-1, 1), rng.int(-1, 1), rng.int(-2, 2), false)))
        .collect();
    let mut below: Vec<usize> = (0..3).collect();
    for _ in 0..depth {
        let start = specs.len();
        for _ in 0..2 + rng.below(2) {
            let mut from = below.clone();
            from.extend(0..3);
            let kids = |rng: &mut Rng| (0..1 + rng.below(3)).map(|_| rng.pick(&from)).collect();
            specs.push(match rng.below(8) {
                0 => Spec::Not(rng.pick(&below)),
                1 => Spec::Or(kids(rng)),
                _ => Spec::And(kids(rng)),
            });
        }
        below = (start..specs.len()).collect();
    }
    specs
}

#[test]
fn formulas_shared_and_regrouped_at_random_at_several_depths_compare_and_hash_as_written_out() {
    // Each round builds several formulas from one set of layered specs, each node kept or
    // built and grouped anew at random at each place it is used, so that shared parts are
    // met at many places and grouped otherwise on each side; and one with a constraint
    // changed, so that they differ, often late.
    let mut rng = Rng::new(0x5_31b);
    for depth in [2, 4, 6, 8] {
        for round in 0..60 {
            let mut specs = layered_specs(&mut rng, depth);
            let top = specs.len() - 1;
            let mut kept: Vec<Option<Formula>> = vec![None; specs.len()];
            let mut fs: Vec<Formula> = (0..4)
                .map(|_| build(&specs, top, &mut rng, &mut kept))
                .collect();
            specs[rng.below(3)] = Spec::Con(con(1, 1, 3, true));
            let mut fresh: Vec<Option<Formula>> = vec![None; specs.len()];
            fs.push(build(&specs, top, &mut rng, &mut fresh));
            let ws: Vec<Written> = fs.iter().map(written).collect();
            for (p, wp) in fs.iter().zip(&ws) {
                for (q, wq) in fs.iter().zip(&ws) {
                    let o = wp.cmp(wq);
                    assert_eq!(p.cmp(q), o, "depth {depth}, round {round}");
                    assert_eq!(p == q, o == Ordering::Equal, "depth {depth}, round {round}");
                    if o == Ordering::Equal {
                        assert_eq!(hash(p), hash(q), "depth {depth}, round {round}");
                    }
                }
            }
        }
    }
}

/// `d` tops `[ti || x >= -3y - i]`, each `ti` the conjunction `[t(i-1), t(i-1), x >= i]` from
/// `t0 = [y >= 0]`; when `regroup`, each `ti` is grouped as in [`shifted_chains`], `[y >= 0,
/// ri]`, so that the parts of each top read alike but begin and end at other places. The last
/// top's constant has `last` added. Each top holds `2^(i+1) - 1` constraints written out.
fn staircase(d: usize, regroup: bool, last: i64) -> Formula {
    let c = con(0, 1, 0, false);
    let (mut t, mut r) = (and(vec![c.clone()]), and(vec![]));
    let mut tops = Vec::with_capacity(d);
    for i in 1..=d as i64 {
        let ci = con(1, 0, -i, false);
        t = and(vec![t.clone(), t, ci.clone()]);
        r = and(vec![r.clone(), c.clone(), r, ci]);
        let ti = if regroup {
            and(vec![c.clone(), r.clone()])
        } else {
            t.clone()
        };
        let k = i + if i == d as i64 { last } else { 0 };
        tops.push(or(vec![ti, con(3, 1, k, false)]));
    }
    and(tops)
}

/// `d` tops as in [`staircase`], each `ti = [ta, tb, x >= i]` with `ta` and `tb` earlier
/// conjunctions picked at random from `seed`, so that parts are shared at random depths.
fn random_dag(d: usize, seed: u64, last: i64) -> Formula {
    let mut rng = Rng::new(seed);
    let mut ts = vec![and(vec![con(0, 1, 0, false)])];
    let mut tops = Vec::with_capacity(d);
    for i in 1..=d {
        let (a, b) = (rng.below(i), rng.below(i));
        let t = and(vec![
            ts[a].clone(),
            ts[b].clone(),
            con(1, 0, -(i as i64), false),
        ]);
        let k = i as i64 + if i == d { last } else { 0 };
        tops.push(or(vec![t.clone(), con(3, 1, k, false)]));
        ts.push(t);
    }
    and(tops)
}

/// `k` sets of `k` constraints each, picked at random from `seed` among `k^2`, each a chain of
/// conjunctions, and a top `[si && sj] || x >= -3y - (ik + j)` for each pair `i < j`: about
/// `k^2` tops, each holding two of the sets. The last top's constant has `last` added.
pub(super) fn pairs(k: usize, seed: u64, last: i64) -> Formula {
    let mut rng = Rng::new(seed);
    let sets: Vec<Formula> = (0..k)
        .map(|_| {
            (0..k).fold(and(vec![]), |t, _| {
                and(vec![t, con(1, 0, -(rng.below(k * k) as i64), false)])
            })
        })
        .collect();
    let mut tops = Vec::new();
    for i in 0..k {
        for j in i + 1..k {
            let n = (i * k + j) as i64 + if (i, j) == (k - 2, k - 1) { last } else { 0 };
            tops.push(or(vec![
                and(vec![sets[i].clone(), sets[j].clone()]),
                con(3, 1, n, false),
            ]));
        }
    }
    and(tops)
}

/// Pairs equal written out, and pairs that differ only at the last top, each built apart: a
/// staircase against itself and against its regrouping, and a random DAG against itself.
pub(super) fn tops_pairs(d: usize) -> Vec<(Formula, Formula, bool)> {
    let mut out = Vec::new();
    for last in [0, 1] {
        let equal = last == 0;
        out.push((staircase(d, false, 0), staircase(d, false, last), equal));
        out.push((staircase(d, false, 0), staircase(d, true, last), equal));
        out.push((random_dag(d, 7, 0), random_dag(d, 7, last), equal));
    }
    out
}

#[test]
fn tops_sharing_parts_compare_as_written_out() {
    // Equal pairs are one sequence written out, and unequal pairs differ in a constraint that
    // occurs nowhere else, so they are equal or unequal under every answer of Q55; the order of
    // an unequal pair depends on the answer, so only equality, the hash of equal formulas and
    // antisymmetry are asserted.
    for d in 1..=9 {
        for (a, b, equal) in tops_pairs(d) {
            assert_eq!(
                written(&a) == written(&b),
                equal,
                "d = {d}: {a} against {b}"
            );
            assert_eq!(a == b, equal, "d = {d}: {a} against {b}");
            assert_eq!(b.cmp(&a), a.cmp(&b).reverse(), "d = {d}: {b} against {a}");
            if equal {
                assert_eq!(hash(&a), hash(&b), "d = {d}: {a}");
            }
        }
    }
    for k in 2..=6 {
        for last in [0, 1] {
            let (a, b) = (pairs(k, 9, 0), pairs(k, 9, last));
            assert_eq!(written(&a) == written(&b), last == 0, "k = {k}");
            assert_eq!(a == b, last == 0, "k = {k}: {a} against {b}");
            assert_eq!(b.cmp(&a), a.cmp(&b).reverse(), "k = {k}: {b} against {a}");
            if last == 0 {
                assert_eq!(hash(&a), hash(&b), "k = {k}: {a}");
            }
        }
    }
}

#[test]
fn a_deep_chain_of_single_parts_compares_without_running_out_of_stack() {
    // Each level one conjunction around the level below: the depth is the number of parts.
    let deep = |last: i64| {
        (0..200_000).fold(con(0, 1, last, false), |f, i| {
            if i % 2 == 0 {
                and(vec![f])
            } else {
                or(vec![f])
            }
        })
    };
    let (a, b, c) = (deep(0), deep(0), deep(1));
    assert!(a == b);
    assert_eq!(a.cmp(&c), c.cmp(&a).reverse());
    assert_ne!(a, c);
    assert_eq!(hash(&a), hash(&b));
}

/// Small formulas whose runs of `&&` and `||` are empty, of one part, repeated, grouped at
/// other places or in other orders, built anew at each call so that no hash is kept yet.
fn corner_cases() -> Vec<Formula> {
    let (c, c1, c2) = (
        con(0, 1, 0, false),
        con(1, 0, -1, false),
        con(1, 0, -2, false),
    );
    let s = and(vec![c1.clone(), c2.clone()]);
    vec![
        c.clone(),
        and(vec![]),
        or(vec![]),
        and(vec![and(vec![])]),
        or(vec![and(vec![])]),
        and(vec![and(vec![]), c.clone()]),
        and(vec![c.clone(), or(vec![])]),
        and(vec![c.clone()]),
        or(vec![c.clone()]),
        and(vec![and(vec![c.clone()])]),
        or(vec![and(vec![c.clone()])]),
        not(c.clone()),
        not(and(vec![c.clone()])),
        and(vec![not(c.clone())]),
        and(vec![c.clone(), c.clone()]),
        and(vec![and(vec![c.clone()]), c.clone()]),
        and(vec![c1.clone(), c2.clone()]),
        and(vec![c2.clone(), c1.clone()]),
        or(vec![c2.clone(), c1.clone()]),
        and(vec![and(vec![c1.clone()]), c2.clone()]),
        and(vec![c1.clone(), and(vec![c2.clone()])]),
        and(vec![s.clone(), s.clone()]),
        and(vec![c1.clone(), c2.clone(), c1.clone(), c2.clone()]),
        and(vec![
            c1.clone(),
            and(vec![c2.clone(), c1.clone()]),
            c2.clone(),
        ]),
        and(vec![s.clone(), c1.clone()]),
        not(s.clone()),
        not(and(vec![c1, c2])),
    ]
}

#[test]
fn equal_formulas_hash_alike_however_their_runs_are_grouped() {
    // Each pair compared with the hash of neither side kept (single), and all pairs compared
    // after every hash is kept, both ways and in both orders (batch): `==` gives the answer the
    // order written out gives, and the same in each way.
    let n = corner_cases().len();
    let single: Vec<Vec<bool>> = (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    let fs = corner_cases();
                    fs[i] == fs[j]
                })
                .collect()
        })
        .collect();
    let fs = corner_cases();
    for (i, p) in fs.iter().enumerate() {
        for (j, q) in fs.iter().enumerate() {
            let o = written(p).cmp(&written(q));
            assert_eq!(p == q, o == Ordering::Equal, "{p} against {q}");
            assert_eq!(single[i][j], o == Ordering::Equal, "{p} against {q}");
            assert_eq!(p.cmp(q), o, "{p} against {q}");
            if o == Ordering::Equal {
                assert_eq!(hash(p), hash(q), "{p} against {q}");
            }
        }
    }
    for (i, p) in fs.iter().enumerate().rev() {
        for (j, q) in fs.iter().enumerate().rev() {
            assert_eq!(p == q, single[i][j], "{p} against {q}");
        }
    }
    // The corner cases the order written out treats as equal, so that the hash must too.
    let same = |i: usize, j: usize| assert!(single[i][j], "{} against {}", fs[i], fs[j]);
    same(1, 3); // `true` and a conjunction of `true`
    same(5, 7); // an empty run beside a constraint, and a run of one
    same(7, 9); // a run of one in a run of one
    same(14, 15); // a repeat in the top run, regrouped
    same(16, 19);
    same(16, 20);
    same(21, 22); // a shared part twice, and its parts written out twice
    same(25, 26);
    assert!(!single[16][17], "a run in another order");
    assert!(!single[7][8] && !single[0][7] && !single[11][13] && !single[1][2]);
    assert!(!single[7][14], "a repeat is not dropped");
}

/// `sum of k a >= c`, or `== c` when `eq`, over the named atoms.
fn row(terms: &[(&str, i64)], c: i64, eq: bool) -> Formula {
    let l = (terms.iter()).fold(Lin::constant(-c), |l, (n, k)| l.plus(&sym(n).times(*k)));
    Formula::Con(if eq {
        Con::eq(&l, &Lin::constant(0))
    } else {
        Con::ge(&l, &Lin::constant(0))
    })
}

/// A random constraint over one or two of `names`, an equation at times, coefficients up to
/// 3 so that a projection can have holes.
fn random_row(rng: &mut Rng, names: &[&'static str]) -> Formula {
    let a = rng.pick(names);
    let mut terms = vec![(a, [-3, -2, -1, 1, 2, 3][rng.below(6)])];
    if rng.below(2) == 0 {
        let b = rng.pick(names);
        if b != a {
            terms.push((b, rng.int(-2, 2)));
        }
    }
    terms.retain(|(_, k)| *k != 0);
    row(&terms, rng.int(-4, 4), rng.below(5) == 0)
}

/// A random disjunction of 2 to 4 disjuncts each holding one shared part `u` over `a` and
/// `b` (a conjunction, at times holding a disjunction, so that a projection has a gap) beside
/// rows of their own over `c` and `d`; at times a disjunct also reads `a`, or lacks `u`, so
/// that the part may not be taken out. Under a conjunction with rows over all four atoms, at
/// times negated.
fn random_tiers(rng: &mut Rng) -> Formula {
    let mut u: Vec<Formula> = (0..1 + rng.below(3))
        .map(|_| random_row(rng, &["a", "b"]))
        .collect();
    if rng.below(3) == 0 {
        u.push(or(vec![
            random_row(rng, &["a", "b"]),
            random_row(rng, &["a", "b"]),
        ]));
    }
    let u = and(u);
    let ds: Vec<Formula> = (0..2 + rng.below(3))
        .map(|_| {
            let rest: &[&'static str] = if rng.below(6) == 0 {
                &["a", "c", "d"]
            } else {
                &["c", "d"]
            };
            let mut parts: Vec<Formula> = (0..1 + rng.below(2))
                .map(|_| random_row(rng, rest))
                .collect();
            if rng.below(8) != 0 {
                parts.insert(rng.below(parts.len() + 1), u.clone());
            }
            and(parts)
        })
        .collect();
    let mut tiers = or(ds);
    if rng.below(3) == 0 {
        tiers = not(tiers);
    }
    let base: &[&'static str] = if rng.below(4) == 0 {
        &["a", "b", "c", "d"]
    } else {
        &["a", "b"]
    };
    let mut top: Vec<Formula> = (0..rng.below(3)).map(|_| random_row(rng, base)).collect();
    top.push(random_row(rng, &["c", "d"]));
    top.push(tiers);
    and(top)
}

#[test]
fn taking_a_shared_part_out_of_a_disjunction_loses_no_precision() {
    // `presburger::factored` takes a part every disjunct holds out of the disjunction when it
    // is linked to nothing else in the disjuncts (ST-formula-sibling). Each decision and each
    // refusal is the one the formula as written gives, and each projection is the one it
    // gives or within it, and holds every value of a point of the formula in a window.
    use zedc::store::presburger::{UNFACTORED, project_each};
    let names = ["a", "b", "c", "d"];
    let syms: Vec<Atom> = names.map(|n| Atom::Sym(n.into())).into();
    fn as_written<T>(run: impl Fn() -> T) -> T {
        UNFACTORED.with(|u| u.set(true));
        let r = run();
        UNFACTORED.with(|u| u.set(false));
        r
    }
    let mut rng = Rng::new(0x5F5B);
    let (mut same, mut narrower, mut answered) = (0, 0, 0);
    for i in 0..600 {
        let f = random_tiers(&mut rng);
        let what = format!("formula {i}: {f}");
        // A refusal as written may become an answer, never the other way.
        match (decide(&f), as_written(|| decide(&f))) {
            (now, Ok(then)) => assert_eq!(now, Ok(then), "{what}"),
            (Ok(_), Err(_)) => answered += 1,
            (now, then) => assert_eq!(now, then, "{what}"),
        }
        let (now, then) = (
            project_each(&f, &syms),
            as_written(|| project_each(&f, &syms)),
        );
        if now == then {
            same += 1;
            continue;
        }
        narrower += 1;
        let (Ok((now, now_skipped)), Ok((then, _))) = (&now, &then) else {
            panic!("{what}: {now:?} where as written {then:?}");
        };
        assert!(now_skipped.is_empty(), "{what}");
        let now: Vec<_> = now.iter().map(|s| s.clone().expect("a set")).collect();
        for (n, t) in now.iter().zip(then) {
            if let Ok(t) = t {
                assert!(n.is_subset(t), "{what}: {n} not within {t}");
            }
        }
        for p in 0..9i64.pow(4) {
            let v: Vec<i64> = (0..4).map(|k| (p / 9i64.pow(k)) % 9 - 4).collect();
            let m: Model = (syms.iter().cloned())
                .zip(v.iter().map(|&x| Int::from(x)))
                .collect();
            if f.holds(&m) {
                for (k, s) in now.iter().enumerate() {
                    assert!(s.contains(v[k]), "{what}: {} = {} at {v:?}", names[k], v[k]);
                }
            }
        }
    }
    assert!(
        narrower > 0 && same > narrower,
        "{same} the same, {narrower} narrower, {answered} answered"
    );
}

/// Two nodes whose parts are all constraints are compared as their two lists of constraints
/// (ST-walk-orders-left), with no walk: the order must still be that of the formulas written
/// out, for each variant, lists of other lengths, one list a prefix of the other, empty
/// lists, and a node holding a compound part against one that holds none.
#[test]
fn nodes_of_constraints_alone_compare_as_written_out() {
    let cs = [
        con(1, 0, 0, false),
        con(1, 0, 1, false),
        con(0, 1, 0, false),
        con(1, -1, 0, true),
    ];
    let lists: Vec<Vec<Formula>> = vec![
        vec![],
        vec![cs[0].clone()],
        vec![cs[1].clone()],
        vec![cs[0].clone(), cs[1].clone()],
        vec![cs[1].clone(), cs[0].clone()],
        vec![cs[0].clone(), cs[1].clone(), cs[2].clone()],
        vec![cs[3].clone(), cs[2].clone()],
    ];
    let mut fs: Vec<Formula> = Vec::new();
    for l in &lists {
        fs.push(and(l.clone()));
        fs.push(or(l.clone()));
    }
    fs.extend(cs.iter().map(|c| not(c.clone())));
    fs.extend(cs.iter().cloned());
    fs.push(and(vec![cs[0].clone(), or(vec![cs[1].clone()])]));
    fs.push(or(vec![cs[0].clone(), and(vec![])]));
    fs.push(not(and(vec![cs[0].clone(), cs[1].clone()])));
    for p in &fs {
        for q in &fs {
            assert_eq!(p.cmp(q), written(p).cmp(&written(q)), "{p} against {q}");
        }
    }
}

/// Terms compare as their derived order would, the pairs of atom and coefficient in order and
/// then the constant, though the first pairs are read apart from the rest (COMPLEXITY.md row
/// ST-chain-raise-reverse-log): terms with no pairs, one a prefix of another, the same first
/// pair and another second, first atoms or coefficients that differ, symbols against
/// auxiliary variables, and equal pairs with other constants. Each pair of terms is also
/// compared as constraints, which the conjuncts of a relation are kept in the order of.
#[test]
fn terms_compare_as_their_derived_order() {
    fn lin(pairs: &[(Atom, i64)], c: i64) -> Lin {
        Lin {
            terms: pairs
                .iter()
                .map(|(a, k)| (a.clone(), Int::from(*k)))
                .collect(),
            constant: Int::from(c),
        }
    }
    let (x, y, z) = (
        Atom::Sym("x".into()),
        Atom::Sym("y".into()),
        Atom::Sym("z".into()),
    );
    let (a0, a1) = (Atom::Aux(0), Atom::Aux(1));
    let lins = [
        lin(&[], 0),
        lin(&[], -3),
        lin(&[(x.clone(), 1)], 0),
        lin(&[(x.clone(), 1)], 2),
        lin(&[(x.clone(), -1)], 0),
        lin(&[(x.clone(), 1), (y.clone(), -1)], 0),
        lin(&[(x.clone(), 1), (y.clone(), 1)], 0),
        lin(&[(x.clone(), 1), (z.clone(), -1)], 0),
        lin(&[(x.clone(), 1), (y.clone(), -1), (z.clone(), 1)], 0),
        lin(&[(y.clone(), 1), (z.clone(), -1)], 5),
        lin(&[(y.clone(), 1), (a0.clone(), 1)], 0),
        lin(&[(a0.clone(), 2)], 0),
        lin(&[(a1.clone(), 2)], 0),
        lin(&[(x.clone(), 1), (a1.clone(), -1)], 1),
    ];
    fn derived(l: &Lin) -> (Vec<(&Atom, &Int)>, &Int) {
        (l.terms.iter().collect(), &l.constant)
    }
    for p in &lins {
        for q in &lins {
            let want = derived(p).cmp(&derived(q));
            assert_eq!(p.cmp(q), want, "{p} against {q}");
            assert_eq!(p.partial_cmp(q), Some(want), "{p} against {q}");
            assert_eq!(p == q, want == Ordering::Equal, "{p} against {q}");
            let (cp, cq) = (Con::ge(p, &Lin::constant(0)), Con::ge(q, &Lin::constant(0)));
            assert_eq!(
                Formula::Con(cp).cmp(&Formula::Con(cq)),
                want,
                "{p} >= 0 against {q} >= 0"
            );
        }
    }
}

/// The check the benchmark makes of a named chain `a`, one built apart equal to it, `b`, and
/// [`extended_chain`] `c`: `a == b`, and `a` sorts before `c`.
pub(super) fn assert_chain_equal_and_before_extended([a, b, c]: &[Formula; 3]) {
    assert!(a == b);
    assert_eq!(a.cmp(c), Ordering::Less);
}

/// The checks the benchmarks make of [`shifted_pairs`]`(d)`: each pair compares as its
/// constraints written out compare, in both orders; the unequal pairs are `!=` both ways; and
/// equal pairs hash alike.
pub(super) fn assert_shifted_pairs_compare_as_written(d: usize) {
    for (a, b, o) in shifted_pairs(d) {
        assert_eq!(written(&a).cmp(&written(&b)), o, "d = {d}");
        assert_eq!(a.cmp(&b), o, "d = {d}");
        assert_eq!(b.cmp(&a), o.reverse(), "d = {d}");
        if o == Ordering::Equal {
            assert_eq!(hash(&a), hash(&b), "d = {d}");
        } else {
            assert!(a != b && b != a, "d = {d}");
        }
    }
}

/// The checks of the benchmarks of `bench/shared.rs` on [`extended_chain`] and
/// [`shifted_pairs`], at small depths.
#[test]
fn chains_and_shifted_pairs_of_the_benchmarks_compare_at_small_depths() {
    for d in [0, 1, 2, 7, 12] {
        for and in [true, false] {
            let three = [named_chain(d, and), named_chain(d, and), extended_chain(d, and)];
            assert_chain_equal_and_before_extended(&three);
        }
        assert_shifted_pairs_compare_as_written(d);
    }
}

//! Emptiness and subtyping against an exact oracle. The random types are Boolean combinations
//! of scalar leaves, universes, and tuples of length 1 and 2 whose components are Boolean
//! combinations of scalar leaves and universes. Every such type is a union of regions, and
//! `reps` holds one value of each region, so a type is empty exactly when no value of `reps`
//! is in it, and `a <: b` exactly when every value of `reps` in `a` is in `b`.

use std::collections::BTreeMap;

use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Refusal, Type, Universe, Verdict};
use zed_kernel::{Family, Value};
use zed_tests::instances::{Rng, pick_seeds};

#[derive(Clone, Debug)]
enum E {
    Base(&'static str),
    Lit(Value),
    Atom(&'static str),
    Universe(Universe),
    Tuple(Vec<E>),
    Or(Box<E>, Box<E>),
    And(Box<E>, Box<E>),
    Diff(Box<E>, Box<E>),
    Not(Box<E>),
}

/// A scalar or morphism value, a tuple of representatives, or the struct, which has no value
/// until L2.
#[derive(Clone, Debug)]
enum Rep {
    Value(Value),
    Tuple(Vec<Rep>),
    Struct,
}

fn holds(e: &E, r: &Rep) -> bool {
    let v = match r {
        Rep::Value(v) => v,
        Rep::Tuple(xs) => {
            return match e {
                E::Universe(u) => *u == Universe::Tuple,
                E::Tuple(es) => es.len() == xs.len() && es.iter().zip(xs).all(|(e, x)| holds(e, x)),
                E::Or(a, b) => holds(a, r) || holds(b, r),
                E::And(a, b) => holds(a, r) && holds(b, r),
                E::Diff(a, b) => holds(a, r) && !holds(b, r),
                E::Not(a) => !holds(a, r),
                _ => false,
            };
        }
        Rep::Struct => {
            return match e {
                E::Universe(u) => *u == Universe::Struct,
                E::Or(a, b) => holds(a, r) || holds(b, r),
                E::And(a, b) => holds(a, r) && holds(b, r),
                E::Diff(a, b) => holds(a, r) && !holds(b, r),
                E::Not(a) => !holds(a, r),
                _ => false,
            };
        }
    };
    match e {
        E::Base(b) => matches!(
            (*b, v),
            ("int", Value::Int(_)) | ("bool", Value::Bool(_)) | ("String", Value::Str(_))
        ),
        E::Lit(l) => l == v,
        E::Atom(n) => matches!(v, Value::Atom(a) if &*a.name == *n),
        E::Universe(u) => Universe::of(v) == *u,
        E::Tuple(_) => false,
        E::Or(a, b) => holds(a, r) || holds(b, r),
        E::And(a, b) => holds(a, r) && holds(b, r),
        E::Diff(a, b) => holds(a, r) && !holds(b, r),
        E::Not(a) => !holds(a, r),
    }
}

fn build(e: &E) -> Type {
    match e {
        E::Base("int") => Type::int(),
        E::Base("bool") => Type::bool(),
        E::Base(_) => Type::string(),
        E::Lit(v) => Type::lit(v).unwrap(),
        E::Atom(n) => Type::atom(n),
        E::Universe(u) => Type::universe(*u),
        E::Tuple(es) => Type::tuple(es.iter().map(build).collect()),
        E::Or(a, b) => build(a) | build(b),
        E::And(a, b) => build(a) & build(b),
        E::Diff(a, b) => build(a) - &build(b),
        E::Not(a) => !build(a),
    }
}

fn lits() -> Vec<Value> {
    vec![Value::Int(0), Value::Int(1), Value::str("a")]
}

/// One value of each region a component can tell apart: each literal, another integer and
/// string, a boolean, each named atom and another, another scalar, a tuple, a morphism and
/// the struct.
fn component_reps() -> Vec<Rep> {
    let mut vs = lits();
    vs.extend([
        Value::Int(2),
        Value::str("b"),
        Value::Bool(true),
        Value::atom("a"),
        Value::atom("b"),
        Value::atom("c"),
        Value::float(0.5),
        Value::Family(Family::new()),
    ]);
    let mut reps: Vec<Rep> = vs.into_iter().map(Rep::Value).collect();
    reps.push(Rep::Tuple(vec![]));
    reps.push(Rep::Struct);
    reps
}

/// The component regions, and the tuples of length 1 and 2 over them; the empty tuple stands
/// for every other length.
fn reps() -> Vec<Rep> {
    let comps = component_reps();
    let mut reps = comps.clone();
    for a in &comps {
        reps.push(Rep::Tuple(vec![a.clone()]));
        for b in &comps {
            reps.push(Rep::Tuple(vec![a.clone(), b.clone()]));
        }
    }
    reps
}

fn leaf(r: &mut Rng) -> E {
    match r.below(4) {
        0 => E::Base(r.pick(&["int", "bool", "String"])),
        1 => E::Lit(r.pick(&lits())),
        2 => E::Atom(r.pick(&["a", "b"])),
        _ => E::Universe(r.pick(&[
            Universe::Scalar,
            Universe::Tuple,
            Universe::Struct,
            Universe::Morphism,
        ])),
    }
}

/// A Boolean combination of depth at most `depth`, over `leaf`.
fn boolean(r: &mut Rng, depth: usize, leaf: &mut dyn FnMut(&mut Rng) -> E) -> E {
    if depth == 0 || r.below(3) == 0 {
        return leaf(r);
    }
    let op = r.below(4);
    let a = Box::new(boolean(r, depth - 1, leaf));
    let b = Box::new(boolean(r, depth - 1, leaf));
    match op {
        0 => E::Or(a, b),
        1 => E::And(a, b),
        2 => E::Diff(a, b),
        _ => E::Not(a),
    }
}

fn random(r: &mut Rng) -> E {
    boolean(r, 3, &mut |r| match r.below(3) {
        0 => leaf(r),
        n => E::Tuple(
            (0..n)
                .map(|_| boolean(r, 2, &mut |r: &mut Rng| leaf(r)))
                .collect(),
        ),
    })
}

/// A deeper combination, mostly of tuples, whose tuple part has diagrams of many nodes.
fn deep(r: &mut Rng) -> E {
    boolean(r, 6, &mut |r| match r.below(4) {
        0 => leaf(r),
        n => E::Tuple((0..n.min(2)).map(|_| leaf(r)).collect()),
    })
}

/// A type with no tuple and a type with one, built to give each answer of the tuple part:
/// `(0,) & (1,)` holds no tuple, since no component is both 0 and 1, and `(int,)` holds
/// `(0,)` (PROOF-test-count-thresholds).
fn built_empty_and_inhabited() -> [(E, bool); 2] {
    let one = |e: E| E::Tuple(vec![e]);
    let empty = E::And(
        Box::new(one(E::Lit(Value::Int(0)))),
        Box::new(one(E::Lit(Value::Int(1)))),
    );
    [(empty, true), (one(E::Base("int")), false)]
}

/// Checks `is_empty` of `e` and of its tuple part against the oracle; returns whether the
/// tuple part is empty.
fn check_emptiness(reps: &[Rep], e: &E, run: &str) -> bool {
    let want = !reps.iter().any(|v| holds(e, v));
    let t = build(e);
    assert_eq!(t.is_empty(), want, "{t}, from {e:?} ({run})");
    // The tuple part on its own, where the product split decides.
    let tuples = t.part(Universe::Tuple);
    let want_tuples = !reps
        .iter()
        .any(|v| matches!(v, Rep::Tuple(_)) && holds(e, v));
    assert_eq!(
        tuples.is_empty(),
        want_tuples,
        "{tuples}, from {e:?} ({run})"
    );
    want_tuples
}

#[test]
fn emptiness_agrees_with_the_oracle() {
    let reps = reps();
    // A new seed each run, printed; it was seed 23 (TEST-bench-move-l0123, author P169).
    let (mut r, seed) = Rng::fresh("random types");
    for _ in 0..1500 {
        let e = random(&mut r);
        check_emptiness(&reps, &e, &format!("ZED_TEST_SEED={seed}"));
    }
    // Both answers on every run, so neither "always empty" nor "never empty" would pass.
    for (e, empty) in built_empty_and_inhabited() {
        assert_eq!(check_emptiness(&reps, &e, "built"), empty, "{e:?}");
    }
}

#[test]
fn subtyping_agrees_with_the_oracle() {
    let reps = reps();
    // A new seed each run, printed; it was seed 5 (TEST-bench-move-l0123, author P169).
    let (mut r, seed) = Rng::fresh("random pairs");
    let check = |a: &E, b: &E, run: &str| -> bool {
        let want = reps.iter().all(|v| !holds(a, v) || holds(b, v));
        let (ta, tb) = (build(a), build(b));
        assert_eq!(ta.subtype(&tb), want, "{ta} <: {tb} ({run})");
        want
    };
    for _ in 0..1500 {
        let (a, b) = (random(&mut r), random(&mut r));
        // Half the pairs compare a type with a part of itself, so that subtyping holds often.
        let a = match r.below(2) {
            0 => E::And(Box::new(a), Box::new(b.clone())),
            _ => a,
        };
        check(&a, &b, &format!("ZED_TEST_SEED={seed}"));
    }
    // Both answers on every run, so neither "always yes" nor "always no" would pass:
    // `0 <: int` holds, since 0 is an integer, and `int <: 0` fails, since 1 is an integer.
    let (zero, int) = (E::Lit(Value::Int(0)), E::Base("int"));
    assert!(check(&zero, &int, "built"), "0 <: int");
    assert!(!check(&int, &zero, "built"), "int <: 0 fails");
}

#[test]
fn deep_combinations_are_decided_exactly() {
    // Deep combinations of tuple types make parts kept as expressions (a union or
    // intersection whose diagram would outgrow its operands); `is_empty` and subtyping agree
    // with the oracle on every one, with no budget to miss an empty type.
    let reps = reps();
    // A new seed each run, printed; it was seed 23 (TEST-bench-move-l0123, author P169).
    let (mut r, seed) = Rng::fresh("deep combinations");
    for _ in 0..3000 {
        let e = deep(&mut r);
        let t = build(&e);
        check_emptiness(&reps, &e, &format!("ZED_TEST_SEED={seed}"));
        let a = E::And(Box::new(deep(&mut r)), Box::new(e.clone()));
        let want = reps.iter().all(|v| !holds(&a, v) || holds(&e, v));
        assert_eq!(
            build(&a).subtype(&t),
            want,
            "{a:?} <: {e:?} (ZED_TEST_SEED={seed})"
        );
    }
    // Both answers on every run, as in `emptiness_agrees_with_the_oracle`.
    for (e, empty) in built_empty_and_inhabited() {
        assert_eq!(check_emptiness(&reps, &e, "built"), empty, "{e:?}");
    }
}

#[test]
fn verdicts_agree_with_the_oracle_in_any_order() {
    // `Empty` is claimed only of empty types and `Inhabited` only of inhabited ones, for a type
    // and for a pair compared; a refusal claims nothing. Each verdict is a function of the type
    // alone: the verdicts read in reverse order with nothing kept are the same.
    let reps = reps();
    // A new seed each run, printed; it was seed 41 (TEST-bench-move-l0123, author P169).
    let (mut r, seed) = Rng::fresh("random and deep types");
    let mut asked = Vec::new();
    for i in 0..3000 {
        let e = if i % 2 == 0 {
            random(&mut r)
        } else {
            deep(&mut r)
        };
        let want = !reps.iter().any(|v| holds(&e, v));
        asked.push((build(&e), want));
    }
    // The two built types last, an empty one and an inhabited one, asked among the others in
    // both orders; each must get its verdict, not a refusal, so a search that refused every
    // type would fail here (PROOF-test-count-thresholds).
    for (e, empty) in built_empty_and_inhabited() {
        let whole = !reps.iter().any(|v| holds(&e, v));
        assert_eq!(whole, empty, "{e:?}: its only values are tuples");
        asked.push((build(&e), empty));
    }
    let (mut empty, mut inhabited, mut refused) = (0, 0, BTreeMap::new());
    Type::forget_emptiness();
    let first: Vec<Verdict> = asked.iter().map(|(t, _)| t.verdict()).collect();
    for ((t, want), v) in asked.iter().zip(&first) {
        match v {
            Verdict::Empty => {
                assert!(*want, "{t} is inhabited, not empty (ZED_TEST_SEED={seed})");
                empty += 1;
            }
            Verdict::Inhabited => {
                assert!(!*want, "{t} is empty, not inhabited (ZED_TEST_SEED={seed})");
                assert!(!t.is_empty(), "{t}");
                inhabited += 1;
            }
            Verdict::Refused(why) => *refused.entry(format!("{why:?}")).or_insert(0) += 1,
        }
    }
    assert_eq!(
        first[first.len() - 2..],
        [Verdict::Empty, Verdict::Inhabited],
        "the built types (ZED_TEST_SEED={seed})"
    );
    Type::forget_emptiness();
    let again: Vec<Verdict> = asked.iter().rev().map(|(t, _)| t.verdict()).collect();
    assert!(first.iter().eq(again.iter().rev()), "ZED_TEST_SEED={seed}");
    println!("verdicts: {empty} empty, {inhabited} inhabited, refused {refused:?}");
    for pair in asked.chunks(2) {
        let (a, b) = (&pair[0].0, &pair[1].0);
        let a = a & b;
        match a.subtype_verdict(b) {
            Verdict::Empty => assert!(a.subtype(b), "{a} <: {b} (ZED_TEST_SEED={seed})"),
            v => panic!("{a} <: {b} holds, and its verdict is {v:?} (ZED_TEST_SEED={seed})"),
        }
        match b.subtype_verdict(&a) {
            Verdict::Empty => assert!(b.subtype(&a), "{b} <: {a} (ZED_TEST_SEED={seed})"),
            Verdict::Inhabited => assert!(!b.subtype(&a), "{b} <: {a} (ZED_TEST_SEED={seed})"),
            Verdict::Refused(_) => {}
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The two routes of `subtype_verdict` (plan item VERDICT-route)
// ---------------------------------------------------------------------------------------------

/// How `a.subtype_verdict(b)` and `(a - b).verdict()` compare on one pair, given the exact
/// answer: the first route may add the simulation's proof only where the search refuses.
#[derive(Default, Debug)]
struct Routes {
    /// Pairs whose two verdicts are the same.
    same: usize,
    /// Pairs `subtype_verdict` calls `Empty` and the search refuses.
    decided_over_refusal: usize,
    /// Pairs both refuse.
    refused: usize,
}

impl Routes {
    /// Records one pair, and returns whether only the simulation decided it; panics on a verdict
    /// against `holds` (whether `a <: b`) or on two verdicts that differ in any other way.
    fn record(&mut self, a: &Type, b: &Type, holds: bool) -> bool {
        Type::forget_emptiness();
        let first = a.subtype_verdict(b);
        Type::forget_emptiness();
        let second = (a - b).verdict();
        for v in [&first, &second] {
            match v {
                Verdict::Empty => assert!(holds, "{a} <: {b} fails, and a verdict says it holds"),
                Verdict::Inhabited => assert!(!holds, "{a} <: {b} holds, and a verdict says not"),
                Verdict::Refused(_) => {}
            }
        }
        match (&first, &second) {
            (Verdict::Empty, Verdict::Refused(_)) => {
                self.decided_over_refusal += 1;
                return true;
            }
            (Verdict::Refused(_), Verdict::Refused(_)) => self.refused += 1,
            (x, y) if x == y => self.same += 1,
            _ => panic!("{a} <: {b}: subtype_verdict {first:?}, (a - b).verdict() {second:?}"),
        }
        false
    }
}

/// The two routes on 1500 pairs of `subtyping_agrees_with_the_oracle` and
/// `deep_combinations_are_decided_exactly` drawn from `r`, each compared both ways.
fn boolean_routes(mut r: Rng) -> Routes {
    let reps = reps();
    let mut routes = Routes::default();
    let sub = |a: &E, b: &E| reps.iter().all(|v| !holds(a, v) || holds(b, v));
    for i in 0..1500 {
        let (a, b) = if i % 2 == 0 {
            (random(&mut r), random(&mut r))
        } else {
            (deep(&mut r), deep(&mut r))
        };
        let a = match r.below(2) {
            0 => E::And(Box::new(a), Box::new(b.clone())),
            _ => a,
        };
        let (ta, tb) = (build(&a), build(&b));
        routes.record(&ta, &tb, sub(&a, &b));
        routes.record(&tb, &ta, sub(&b, &a));
    }
    println!("boolean pairs: {routes:?}");
    routes
}

#[test]
fn the_two_routes_agree_on_boolean_types() {
    // Ran 3000 pairs from seed 5 (all 6000 comparisons the same); now 1500 from a new seed
    // each run, printed (TEST-bench-move-l0123, author P169). The refusals of the draw are not
    // held to a bound: a bound on a new seed is a threshold that some seed crosses with no
    // fault (PROOF-test-count-thresholds). A change in the rate of refusals fails
    // `a_fixed_draw_of_boolean_pairs_gives_its_counts`.
    let (r, _) = Rng::fresh("boolean pairs");
    boolean_routes(r);
    // Both routes decide a built pair each way: `0 <: int` holds, so `0 \ int` is empty and
    // both say `Empty`; `int <: 0` fails, 1 lying in `int \ 0`, and both say `Inhabited`.
    let reps = reps();
    let sub = |a: &E, b: &E| reps.iter().all(|v| !holds(a, v) || holds(b, v));
    let (zero, int) = (E::Lit(Value::Int(0)), E::Base("int"));
    let mut built = Routes::default();
    built.record(&build(&zero), &build(&int), sub(&zero, &int));
    built.record(&build(&int), &build(&zero), sub(&int, &zero));
    assert_eq!(built.same, 2, "0 <: int and int <: 0: {built:?}");
}

/// The 1500 pairs of seed 5, the seed the test once ran, with their exact counts, so that a
/// change in how many pairs the routes decide alike or refuse fails here on every run
/// (PROOF-test-count-thresholds).
#[test]
fn a_fixed_draw_of_boolean_pairs_gives_its_counts() {
    let routes = boolean_routes(Rng::new(5));
    assert_eq!(
        (routes.same, routes.decided_over_refusal, routes.refused),
        (3000, 0, 0),
        "{routes:?}"
    );
}

/// The generator of the cross-review's random recursive systems (wt/xv/Q1Q7/scripts/x_tail.rs,
/// `rs`), kept bit for bit so that its recorded cases are the same systems here.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self, n: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(2862933555777941757)
            .wrapping_add(3037000493);
        ((self.0 >> 33) % n as u64) as usize
    }
}

/// One alternative of a definition: `#nil`, `#stop`, `#cons(h, X_j)`, `#cons(h, X_i \ X_j)` or
/// `(X_i, X_j)`, with `h` a set of heads given as a mask.
#[derive(Clone, Copy, Debug)]
enum Alt {
    Nil,
    Stop,
    Cons(u8, usize),
    ConsDiff(u8, usize, usize),
    Pair(usize, usize),
}

/// The heads a value can tell apart: 0, 1 and 2, another integer, and a string.
const HEADS: usize = 5;

fn head_value(h: usize) -> Value {
    match h {
        0..=2 => Value::Int(h as i64),
        3 => Value::Int(99),
        _ => Value::str("s"),
    }
}

fn head_type(m: u8) -> Type {
    if m & 31 == 31 {
        return Type::top();
    }
    if m & 15 == 15 {
        return Type::int();
    }
    let mut t = Type::empty();
    for h in 0..3 {
        if m >> h & 1 == 1 {
            t = &t | &Type::lit(&Value::Int(h)).unwrap();
        }
    }
    if m >> 4 & 1 == 1 {
        t = &t | &Type::string();
    }
    t
}

fn head_mask(g: &mut Lcg) -> u8 {
    match g.next(6) {
        0 => 15,
        1 => 31,
        2 => 1,
        3 => 2,
        4 => 3,
        _ => 5,
    }
}

/// Whether a value with head `h` and tail of membership vector `tail`, or a pair of values of
/// vectors `pair`, is in `a`.
fn alt_holds(a: &Alt, h: Option<usize>, tail: Option<u32>, pair: Option<(u32, u32)>) -> bool {
    match (a, h, tail, pair) {
        (Alt::Cons(m, j), Some(h), Some(t), _) => m >> h & 1 == 1 && t >> j & 1 == 1,
        (Alt::ConsDiff(m, i, j), Some(h), Some(t), _) => {
            m >> h & 1 == 1 && t >> i & 1 == 1 && t >> j & 1 == 0
        }
        (Alt::Pair(i, j), _, _, Some((x, y))) => x >> i & 1 == 1 && y >> j & 1 == 1,
        _ => false,
    }
}

/// Every membership vector a finite value has, with one such value, found by closure from
/// the leaves; the system has at most five definitions, so at most 32 vectors.
fn reachable(eqs: &[Vec<Alt>]) -> BTreeMap<u32, Value> {
    let vec_of = |p: &dyn Fn(&Alt) -> bool| -> u32 {
        (0..eqs.len()).fold(0, |v, i| v | ((eqs[i].iter().any(p) as u32) << i))
    };
    let mut seen = BTreeMap::new();
    seen.insert(vec_of(&|a| matches!(a, Alt::Nil)), Value::atom("nil"));
    seen.entry(vec_of(&|a| matches!(a, Alt::Stop)))
        .or_insert(Value::atom("stop"));
    seen.entry(0).or_insert(Value::Int(7));
    loop {
        let cur: Vec<(u32, Value)> = seen.iter().map(|(a, b)| (*a, b.clone())).collect();
        let mut grew = false;
        for (v, val) in &cur {
            for h in 0..HEADS {
                let u = vec_of(&|a| alt_holds(a, Some(h), Some(*v), None));
                seen.entry(u).or_insert_with(|| {
                    grew = true;
                    Value::atom_with("cons", vec![head_value(h), val.clone()])
                });
            }
            for (w, wal) in &cur {
                let u = vec_of(&|a| alt_holds(a, None, None, Some((*v, *w))));
                seen.entry(u).or_insert_with(|| {
                    grew = true;
                    Value::Tuple(vec![val.clone(), wal.clone()].into())
                });
            }
        }
        if !grew {
            return seen;
        }
    }
}

fn system(g: &mut Lcg) -> Option<(Vec<Vec<Alt>>, Vec<Type>)> {
    let n = 2 + g.next(4);
    let eqs: Vec<Vec<Alt>> = (0..n)
        .map(|_| {
            let k = 1 + g.next(3);
            (0..k)
                .map(|_| match g.next(10) {
                    0 | 1 => Alt::Nil,
                    2 => Alt::Stop,
                    3..=6 => Alt::Cons(head_mask(g), g.next(n)),
                    7 => Alt::ConsDiff(head_mask(g), g.next(n), g.next(n)),
                    _ => Alt::Pair(g.next(n), g.next(n)),
                })
                .collect()
        })
        .collect();
    let r = |i: usize| Expr::Ref(i, vec![]);
    let defs = eqs
        .iter()
        .enumerate()
        .map(|(i, alts)| Def {
            name: format!("X{i}"),
            params: vec![],
            body: Expr::Union(
                alts.iter()
                    .map(|a| match *a {
                        Alt::Nil => Expr::Type(Type::atom("nil")),
                        Alt::Stop => Expr::Type(Type::atom("stop")),
                        Alt::Cons(m, j) => {
                            Expr::Atom("cons".into(), vec![Expr::Type(head_type(m)), r(j)])
                        }
                        Alt::ConsDiff(m, x, y) => Expr::Atom(
                            "cons".into(),
                            vec![
                                Expr::Type(head_type(m)),
                                Expr::Diff(Box::new(r(x)), Box::new(r(y))),
                            ],
                        ),
                        Alt::Pair(x, y) => Expr::Tuple(vec![r(x), r(y)]),
                    })
                    .collect(),
            ),
        })
        .collect();
    let group = Group::new(defs).ok()?;
    Some((eqs, group.instance(vec![])))
}

/// A Boolean term over the definitions of a system.
enum F {
    L(usize),
    Or(Box<F>, Box<F>),
    And(Box<F>, Box<F>),
    Not(Box<F>),
}

fn term(g: &mut Lcg, leaves: usize, d: usize) -> F {
    if d == 0 || g.next(4) == 0 {
        return F::L(g.next(leaves));
    }
    let (a, b) = (
        Box::new(term(g, leaves, d - 1)),
        Box::new(term(g, leaves, d - 1)),
    );
    match g.next(3) {
        0 => F::Or(a, b),
        1 => F::And(a, b),
        _ => F::Not(a),
    }
}

fn term_type(f: &F, ts: &[Type]) -> Type {
    match f {
        F::L(i) => ts[*i].clone(),
        F::Or(a, b) => &term_type(a, ts) | &term_type(b, ts),
        F::And(a, b) => &term_type(a, ts) & &term_type(b, ts),
        F::Not(a) => !&term_type(a, ts),
    }
}

fn term_holds(f: &F, v: u32) -> bool {
    match f {
        F::L(i) => v >> i & 1 == 1,
        F::Or(a, b) => term_holds(a, v) || term_holds(b, v),
        F::And(a, b) => term_holds(a, v) && term_holds(b, v),
        F::Not(a) => !term_holds(a, v),
    }
}

/// The pair `a`, `b` of system `idx` of `seed`, with a value of `a` outside `b` when there is
/// one; `None` when the group is rejected.
fn recursive_pair(seed: u64, idx: usize) -> Option<(Type, Type, Option<Value>)> {
    let (a, b, classes) = recursive_classes(seed, idx)?;
    let witness = classes
        .into_iter()
        .find(|(in_a, in_b, _)| *in_a && !*in_b)
        .map(|(_, _, w)| w);
    Some((a, b, witness))
}

/// Whether the values of one membership vector are in `a`, whether they are in `b`, and one of
/// them.
type Membership = (bool, bool, Value);

/// The pair `a`, `b` of system `idx` of `seed`, with each membership vector a finite value has
/// (`reachable`), as whether its values are in `a`, whether they are in `b`, and one of them;
/// `None` when the group is rejected.
fn recursive_classes(seed: u64, idx: usize) -> Option<(Type, Type, Vec<Membership>)> {
    let mut g = Lcg((seed << 32) ^ (idx as u64 * 2 + 1));
    for _ in 0..4 {
        g.next(2);
    }
    let (eqs, ts) = system(&mut g)?;
    let (fa, fb) = (term(&mut g, ts.len(), 3), term(&mut g, ts.len(), 3));
    let classes = reachable(&eqs)
        .into_iter()
        .map(|(v, w)| (term_holds(&fa, v), term_holds(&fb, v), w))
        .collect();
    Some((term_type(&fa, &ts), term_type(&fb, &ts), classes))
}

/// The pairs of the cross-review's random systems (wt/xv/Q1Q7/REPORT.md, check 4) on which
/// `subtype_verdict` was `Empty` and `(a - b).verdict()` refused, `a <: b` holding: seed 1,
/// systems 578, 1837 and 3099.
const DECIDED_BY_THE_SIMULATION: [(u64, usize); 3] = [(1, 578), (1, 1837), (1, 3099)];

#[test]
fn the_two_routes_agree_on_recursive_systems() {
    // Every system of seeds 1 and 2 the cross-review measured: no route says `Empty` where
    // the other says `Inhabited`, and none is wrong against the closure oracle. The
    // simulation decides a pair only where the search refuses it. Ran all 8000 (3980 the same,
    // 17 refused by both, 2 decided by the simulation alone), as `bench::every_recursive_system`
    // still does; now 1500 distinct systems drawn from them with a new seed each run, printed
    // (TEST-bench-move-l0123, author P169: random tests run fewer cases). The 8000 hold 19 pairs
    // not decided the same way by both routes, so any draw has fewer than 20, and the check
    // `same + 20 > accepted && refused < 20` once here held for every draw while the 8000 did.
    // Drawing with replacement, and asking `same > 690` of about 750 accepted, failed one run
    // in 45. The cases the simulation alone decides are checked each run in
    // `the_recorded_cases_are_decided_by_the_simulation`.
    //
    // The draw's counts are not held to bounds (PROOF-test-count-thresholds): a bound on a new
    // seed is a threshold, and one held only while the 8000 hold their 19 pairs is crossed by
    // some draw as soon as a change adds pairs, with no fault on that draw's systems. A change
    // in the counts fails `a_fixed_draw_of_recursive_systems_gives_its_counts`; that groups are
    // accepted and both routes decide them alike is checked on fixed systems each run, in
    // `the_systems_reaching_rare_branches_agree_with_the_oracle`.
    let (mut rng, first) = Rng::fresh("recursive systems drawn");
    drawn_recursive_routes(&mut rng, &format!("ZED_TEST_SEED={first}"));
}

/// The routes on 1500 distinct systems of seeds 1 and 2 drawn with `rng`, and the number of
/// systems whose group is accepted.
fn drawn_recursive_routes(rng: &mut Rng, run: &str) -> (Routes, usize) {
    let drawn = pick_seeds(rng, "recursive systems", 0..2 * SYSTEMS_PER_SEED, 1500);
    recursive_routes(
        drawn
            .into_iter()
            .map(|s| (1 + s / SYSTEMS_PER_SEED, (s % SYSTEMS_PER_SEED) as usize)),
        run,
    )
}

/// One draw of 1500 systems from a fixed seed, with its exact counts, so that a change in how
/// many systems are accepted, decided alike or refused fails here on every run
/// (PROOF-test-count-thresholds).
#[test]
fn a_fixed_draw_of_recursive_systems_gives_its_counts() {
    let (routes, accepted) = drawn_recursive_routes(&mut Rng::new(1), "fixed draw");
    assert_eq!(
        (
            accepted,
            routes.same,
            routes.decided_over_refusal,
            routes.refused
        ),
        (733, 731, 1, 1),
        "{routes:?}"
    );
}

/// Systems per seed of `recursive_pair` that the cross-review measured, for seeds 1 and 2.
const SYSTEMS_PER_SEED: u64 = 4000;

/// Checks the pairs of `systems` (seed, index) against the closure oracle and records the two
/// routes on each; returns the routes and the number of systems whose group is accepted. `run`
/// names the run in failure messages.
fn recursive_routes(systems: impl Iterator<Item = (u64, usize)>, run: &str) -> (Routes, usize) {
    let mut routes = Routes::default();
    let mut decided = Vec::new();
    let mut accepted = 0;
    for (seed, idx) in systems {
        let Some((a, b, witness)) = recursive_pair(seed, idx) else {
            continue;
        };
        accepted += 1;
        if let Some(w) = &witness {
            assert!(
                (&a - &b).contains(w),
                "{w} in {a} \\ {b} (system {seed}, {idx}; {run})"
            );
        }
        if routes.record(&a, &b, witness.is_none()) {
            decided.push((seed, idx));
        }
    }
    println!("recursive systems: {routes:?}, decided by the simulation alone: {decided:?}");
    (routes, accepted)
}

#[test]
fn the_recorded_cases_are_decided_by_the_simulation() {
    // On each, `a <: b` holds; the simulation proves it, and the search never says otherwise.
    for (seed, idx) in DECIDED_BY_THE_SIMULATION {
        let (a, b, witness) = recursive_pair(seed, idx).expect("the group is accepted");
        assert!(witness.is_none(), "system {idx}: {a} <: {b} fails");
        Type::forget_emptiness();
        assert_eq!(
            a.subtype_verdict(&b),
            Verdict::Empty,
            "system {idx}: {a} <: {b}"
        );
        assert!(a.subtype(&b), "system {idx}: {a} <: {b}");
        Type::forget_emptiness();
        let v = (&a - &b).verdict();
        assert!(v != Verdict::Inhabited, "system {idx}: {a} \\ {b} is {v:?}");
    }
}

/// Systems (seed, index) that reach branches of the emptiness search no other regular test
/// reaches; before, only the benchmark of every system reached them, and the regular test
/// above only when its fresh draw of 1500 included one (TEST-bench-move-l0123, author P188).
/// Found by running each system alone under llvm-cov.
const SYSTEMS_REACHING_RARE_BRANCHES: [(u64, usize); 5] = [
    // `affine_lists_empty`: an operand of the meet met a second time; `decide_counted`: pair
    // payload rows whose forced atoms do not satisfy the rows.
    (1, 1041),
    // The escape walk: a second stop that differs from the first.
    (1, 1663),
    // The escape walk: an element type over an alphabet that is not only integers.
    (1, 3612),
    // `affine_lists_empty`: two own states, neither with a step on a value, and a step that
    // neither keeps nor swaps them; a value named by an operand outside the swap.
    (1, 3800),
    // A chain plan's step whose link or stop differs from the chain's (`step_of`); and pair
    // payload rows as in (1, 1041).
    (2, 2916),
];

#[test]
fn the_systems_reaching_rare_branches_agree_with_the_oracle() {
    let (routes, accepted) = recursive_routes(
        SYSTEMS_REACHING_RARE_BRANCHES.into_iter(),
        "the systems reaching rare branches",
    );
    assert_eq!(accepted, SYSTEMS_REACHING_RARE_BRANCHES.len());
    // Fixed systems, so exact counts: both routes decide each alike.
    assert_eq!(routes.same, accepted, "{routes:?}");
}

/// Systems (seed, index) whose pair, compared both ways and met, reaches a branch of the
/// emptiness search that no test of the local suite reached (llvm-cov over the whole suite,
/// TEST-types-unreached-paths-2). Each was the first system of seeds 1 to 40 to reach its
/// branch, found with a counter at each unreached line; the one-way pairs of the systems above
/// reach none of them. With each, the refusals both routes give on it in the full build, out of
/// two (a record only: the test does not assert it, see below), and its meet's verdict.
const SYSTEMS_REACHING_RARE_BRANCHES_BOTH_WAYS: [((u64, usize), usize, Verdict); 11] = [
    // `nested_pieces`: `laminar_pieces` leaves a test undecided, so the pieces are cut one by
    // one, and a later cell is read against the pieces before it.
    ((32, 784), 0, Verdict::Inhabited),
    // `affine_lists_empty`: a list state met a second time on the walk.
    ((1, 23), 0, Verdict::Empty),
    // `swept`: the rows a sweep takes do not satisfy the part, so it gives no order.
    ((1, 2441), 0, Verdict::Empty),
    // `read_two_sat`: a literal held outright becomes a unit clause.
    ((1, 2735), 0, Verdict::Refused(Refusal::Fork)),
    // `affine_lists_empty`: no integer is left unnamed by a dead operand while some other is.
    ((1, 920), 0, Verdict::Empty),
    // `tuples`: no piece can be taken out, and cells held on a fork are read back.
    ((16, 3121), 0, Verdict::Inhabited),
    // The two-literal clauses: a meet of two operands asked a second time. One way is decided
    // since the pieces of crossing cells of literals are taken out (PERF-diagonal-rows-difference).
    ((21, 31), 1, Verdict::Inhabited),
    // `tuples`: a fork taken where a cell's row is forced.
    ((23, 3846), 0, Verdict::Empty),
    // `affine_lists_empty`: no step the walk can take on any value, so the lists are empty.
    ((35, 1552), 0, Verdict::Inhabited),
    // `bdd` meet of two diagrams: the left's keys fewer than the right's at one node.
    ((38, 3838), 0, Verdict::Inhabited),
    // `tuples`: a part shown empty by its classes while a blame is being kept.
    ((4, 3114), 1, Verdict::Inhabited),
];

#[test]
fn the_systems_reaching_rare_branches_both_ways_agree_with_the_oracle() {
    for ((seed, idx), _, meet) in SYSTEMS_REACHING_RARE_BRANCHES_BOTH_WAYS {
        let (a, b, classes) = recursive_classes(seed, idx).expect("the group is accepted");
        let none = |p: &dyn Fn(bool, bool) -> bool| !classes.iter().any(|(x, y, _)| p(*x, *y));
        let mut routes = Routes::default();
        // `record` checks each verdict against the closure oracle, and that the two routes
        // agree. Only the verdicts are asserted: how many of the two pairs are refused depends
        // on the digests, which differ between the full build and the short-addresses build
        // (system (4, 3114) is decided both ways under short addresses).
        routes.record(&a, &b, none(&|x, y| x && !y));
        routes.record(&b, &a, none(&|x, y| y && !x));
        Type::forget_emptiness();
        let v = (&a & &b).verdict();
        let disjoint = none(&|x, y| x && y);
        let wrong = if disjoint {
            Verdict::Inhabited
        } else {
            Verdict::Empty
        };
        assert!(v != wrong, "system {seed}, {idx}: {a} & {b} is {v:?}");
        assert_eq!(v, meet, "system {seed}, {idx}: {a} & {b}");
    }
}

mod bench;

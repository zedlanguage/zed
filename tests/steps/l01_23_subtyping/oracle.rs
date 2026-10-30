//! Emptiness and subtyping against an exact oracle. The random types are Boolean combinations
//! of scalar leaves, universes, and tuples of length 1 and 2 whose components are Boolean
//! combinations of scalar leaves and universes. Every such type is a union of regions, and
//! `reps` holds one value of each region, so a type is empty exactly when no value of `reps`
//! is in it, and `a <: b` exactly when every value of `reps` in `a` is in `b`.

use zed_kernel::types::{Type, Universe};
use zed_kernel::{Family, Value};
use zed_tests::instances::Rng;

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

#[test]
fn emptiness_agrees_with_the_oracle() {
    let reps = reps();
    let mut r = Rng::new(23);
    let (mut empty, mut inhabited) = (0, 0);
    for _ in 0..1500 {
        let e = random(&mut r);
        let want = !reps.iter().any(|v| holds(&e, v));
        let t = build(&e);
        assert_eq!(t.is_empty(), want, "{t}, from {e:?}");
        // The tuple part on its own, where the product split decides.
        let tuples = t.part(Universe::Tuple);
        let want_tuples = !reps
            .iter()
            .any(|v| matches!(v, Rep::Tuple(_)) && holds(&e, v));
        assert_eq!(tuples.is_empty(), want_tuples, "{tuples}, from {e:?}");
        match want_tuples {
            true => empty += 1,
            false => inhabited += 1,
        }
    }
    // Both answers occur often, so neither "always empty" nor "never empty" would pass.
    assert!(empty > 200 && inhabited > 200, "{empty} {inhabited}");
}

#[test]
fn subtyping_agrees_with_the_oracle() {
    let reps = reps();
    let mut r = Rng::new(5);
    let (mut yes, mut no) = (0, 0);
    for _ in 0..1500 {
        let (a, b) = (random(&mut r), random(&mut r));
        // Half the pairs compare a type with a part of itself, so that subtyping holds often.
        let a = match r.below(2) {
            0 => E::And(Box::new(a), Box::new(b.clone())),
            _ => a,
        };
        let want = reps.iter().all(|v| !holds(&a, v) || holds(&b, v));
        let (ta, tb) = (build(&a), build(&b));
        assert_eq!(ta.subtype(&tb), want, "{ta} <: {tb}");
        match want {
            true => yes += 1,
            false => no += 1,
        }
    }
    assert!(yes > 400 && no > 400, "{yes} {no}");
}

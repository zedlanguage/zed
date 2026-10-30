//! The connectives against a direct reading of the type expression: for random expressions
//! over the base types, literals, atoms, tuples and universes, a value is in the type the
//! connectives build exactly when the expression, read as a predicate, holds of it.

use std::sync::Arc;

use zed_kernel::types::{Type, Universe};
use zed_kernel::{Family, Value};
use zed_tests::instances::Rng;

/// A type expression.
#[derive(Clone, Debug)]
enum E {
    Base(&'static str),
    Lit(Value),
    Atom(&'static str),
    AtomWith(&'static str, Box<E>),
    Tuple(Vec<E>),
    Universe(Universe),
    Or(Box<E>, Box<E>),
    And(Box<E>, Box<E>),
    Diff(Box<E>, Box<E>),
    Not(Box<E>),
}

/// What membership is asked of: a value, or the struct an atom's struct payload is (no
/// struct value exists until L2).
#[derive(Clone, Copy)]
enum Probe<'a> {
    Value(&'a Value),
    Struct,
}

fn holds(e: &E, p: Probe) -> bool {
    let Probe::Value(v) = p else {
        return match e {
            E::Universe(u) => *u == Universe::Struct,
            E::Or(a, b) => holds(a, p) || holds(b, p),
            E::And(a, b) => holds(a, p) && holds(b, p),
            E::Diff(a, b) => holds(a, p) && !holds(b, p),
            E::Not(a) => !holds(a, p),
            _ => false,
        };
    };
    match e {
        E::Base(b) => matches!(
            (*b, v),
            ("int", Value::Int(_) | Value::Big(_))
                | ("rat", Value::Rat(_))
                | ("f64", Value::Float(_))
                | ("bool", Value::Bool(_))
                | ("String", Value::Str(_))
        ),
        E::Lit(l) => l == v,
        E::Atom(n) => matches!(v, Value::Atom(a) if &*a.name == *n && a.args.is_empty()),
        E::AtomWith(n, pay) => match v {
            Value::Atom(a) if &*a.name == *n && !a.args.is_empty() => {
                if a.fields.is_empty() {
                    holds(pay, Probe::Value(&Value::Tuple(a.args.clone())))
                } else {
                    holds(pay, Probe::Struct)
                }
            }
            _ => false,
        },
        E::Tuple(es) => match v {
            Value::Tuple(xs) | Value::Path(xs) => {
                es.len() == xs.len() && es.iter().zip(xs).all(|(e, x)| holds(e, Probe::Value(x)))
            }
            _ => false,
        },
        E::Universe(u) => Universe::of(v) == *u,
        E::Or(a, b) => holds(a, p) || holds(b, p),
        E::And(a, b) => holds(a, p) && holds(b, p),
        E::Diff(a, b) => holds(a, p) && !holds(b, p),
        E::Not(a) => !holds(a, p),
    }
}

fn build(e: &E) -> Type {
    match e {
        E::Base("int") => Type::int(),
        E::Base("rat") => Type::rat(),
        E::Base("f64") => Type::f64(),
        E::Base("bool") => Type::bool(),
        E::Base(_) => Type::string(),
        E::Lit(v) => Type::lit(v).unwrap(),
        E::Atom(n) => Type::atom(n),
        E::AtomWith(n, p) => Type::atom_with(n, &build(p)),
        E::Tuple(es) => Type::tuple(es.iter().map(build).collect()),
        E::Universe(u) => Type::universe(*u),
        E::Or(a, b) => build(a) | build(b),
        E::And(a, b) => build(a) & build(b),
        E::Diff(a, b) => build(a) - &build(b),
        E::Not(a) => !build(a),
    }
}

fn int(n: i64) -> Value {
    Value::Int(n)
}

fn small() -> Vec<Value> {
    vec![
        int(0),
        int(1),
        Value::str("a"),
        Value::atom("a"),
        Value::Bool(true),
    ]
}

/// Values of every universe: scalars of each base type, bare atoms and atoms with tuple and
/// struct payloads, tuples of length 0 to 2, a keypath and a family.
fn values() -> Vec<Value> {
    let mut vs = vec![
        int(2),
        Value::int_text("1208925819614629174706176", 10).unwrap(),
        Value::rat(zed_kernel::Rat::decimal("0.5").unwrap()),
        Value::float(0.5),
        Value::float(-1.0),
        Value::Bool(false),
        Value::str("b"),
        Value::atom("b"),
        Value::atom("c"),
        Value::atom_with("a", vec![int(1)]),
        Value::atom_with("a", vec![int(1), Value::str("a")]),
        Value::atom_with("b", vec![int(0)]),
        Value::atom_named("a", vec![(Arc::from("x"), int(1))]).unwrap(),
        Value::Path(vec![int(0), int(1)]),
        Value::Family(Family::new()),
        Value::Tuple(vec![]),
        Value::Tuple(vec![Value::Tuple(vec![int(0)])]),
    ];
    vs.extend(small());
    for a in small() {
        vs.push(Value::Tuple(vec![a.clone()]));
        for b in small() {
            vs.push(Value::Tuple(vec![a.clone(), b]));
        }
    }
    vs
}

fn random(r: &mut Rng, depth: usize) -> E {
    let leaf = depth == 0 || r.below(3) == 0;
    if leaf {
        return match r.below(6) {
            0 => E::Base(r.pick(&["int", "rat", "f64", "bool", "String"])),
            1 => E::Lit(r.pick(&small())),
            2 => E::Atom(r.pick(&["a", "b", "c"])),
            3 => E::Universe(r.pick(&[
                Universe::Scalar,
                Universe::Tuple,
                Universe::Struct,
                Universe::Morphism,
            ])),
            4 => E::Tuple((0..r.below(3)).map(|_| random(r, 0)).collect()),
            _ => E::AtomWith(r.pick(&["a", "b"]), Box::new(random(r, 0))),
        };
    }
    let op = r.below(6);
    let mut sub = || Box::new(random(r, depth - 1));
    match op {
        0 => E::Or(sub(), sub()),
        1 => E::And(sub(), sub()),
        2 => E::Diff(sub(), sub()),
        3 => E::Not(sub()),
        4 => E::Tuple(vec![*sub(), *sub()]),
        _ => E::AtomWith("a", sub()),
    }
}

#[test]
fn membership_is_the_expression_read_as_a_predicate() {
    let vs = values();
    let mut r = Rng::new(22);
    let (mut members, mut nonmembers) = (0, 0);
    for _ in 0..1500 {
        let e = random(&mut r, 3);
        let t = build(&e);
        assert!(t.decidable(), "{e:?}");
        for v in &vs {
            let want = holds(&e, Probe::Value(v));
            assert_eq!(t.contains(v), want, "{v} in {t}, from {e:?}");
            if want {
                members += 1;
            } else {
                nonmembers += 1;
            }
        }
    }
    // Both answers occur often, so neither a type that holds everything nor one that holds
    // nothing would pass.
    assert!(
        members > 10_000 && nonmembers > 10_000,
        "{members} {nonmembers}"
    );
}

#[test]
fn union_and_intersection_are_commutative_idempotent_and_canonical() {
    let mut r = Rng::new(7);
    for _ in 0..500 {
        let (a, b) = (build(&random(&mut r, 2)), build(&random(&mut r, 2)));
        assert_eq!(&a | &b, &b | &a, "{a} | {b}");
        assert_eq!(&a & &b, &b & &a, "{a} & {b}");
        assert_eq!(&a | &a, a);
        assert_eq!(&a & &a, a);
        assert_eq!((&a | &b).to_string(), (&b | &a).to_string());
    }
}

#[test]
fn a_type_and_its_complement_split_every_universe() {
    let mut r = Rng::new(11);
    for _ in 0..300 {
        let a = build(&random(&mut r, 3));
        let (both, either) = (&a & &!&a, &a | &!&a);
        for v in values() {
            assert!(!both.contains(&v), "{v} in {both}");
            assert!(either.contains(&v), "{v} not in {either}");
        }
        assert!(either.functions() && !both.functions(), "{a}");
    }
}

#[test]
fn the_scalar_part_is_exact() {
    // Within the scalars the representation is a normal form: two expressions that hold of
    // the same scalars build one type, so `a | !a` is every scalar exactly.
    let mut r = Rng::new(3);
    let scalars = Type::universe(Universe::Scalar);
    for _ in 0..500 {
        let a = build(&random(&mut r, 3)).part(Universe::Scalar);
        assert_eq!(&a | &(&scalars - &a), scalars, "{a}");
        assert_eq!((!&!&a).part(Universe::Scalar), a);
    }
}

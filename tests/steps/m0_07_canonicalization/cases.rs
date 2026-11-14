//! Completeness cases for the canonicalizer and the serialization (TEST-complete-m0, author
//! P189): one term for each form of kernel term, literal value and pattern, each checked to get
//! an address of its own, to keep it when its local names change, and to reach the same normal
//! form in one pass as by the rules one step at a time (DESIGN.md step M0.7). The case list is
//! `COMPLETENESS.md`.

use std::collections::BTreeMap;

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{
    Evidence, Family, FixKind, Grade, GuardPos, Pattern, Prim, Shared, Term, Value, Witness,
};
use zedc::address::ContentAddress;
use zedc::canon::{Def, Domain, binders};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::lattice::{Congruence, FiniteSet, Lattice};

use super::alpha::one_pass_is_stepwise;
use super::{addr, def};

fn s(t: Term) -> Shared {
    Shared::new(t)
}

fn evidence(entries: &[(&str, Grade)]) -> Evidence {
    entries.iter().map(|(p, g)| ((*p).into(), *g)).collect()
}

/// A fold of `xs` by `op`, with the given identity, depth and evidence.
fn fold(op: Term, identity: Option<Term>, depth: usize, ev: Evidence) -> Term {
    Term::Fold {
        family: s(var("xs")),
        op: s(op),
        identity: identity.map(s),
        depth,
        ev,
    }
}

/// One literal of each kind of value, and of each kind the variants that differ in one part.
fn values() -> Vec<Value> {
    use num_bigint::BigInt;
    use zed_kernel::Rat;
    let kept = Value::power_text("3^100").unwrap().unwrap();
    let Value::Big(kept_rat) = &kept else {
        panic!("3^100 is a Big: {kept:?}")
    };
    let kept_rat = Value::rat((**kept_rat).clone());
    let named = |f: &str| Value::atom_named("e", vec![(f.into(), Value::Int(1))]).unwrap();
    vec![
        Value::Bool(false),
        Value::Bool(true),
        Value::Int(0),
        Value::Int(-1),
        Value::float(0.0),
        Value::float32(0.0),
        Value::float32(1.0),
        Value::str(""),
        Value::str("e"),
        Value::atom("e"),
        Value::atom("f"),
        Value::atom_with("e", vec![]),
        Value::atom_with("e", vec![Value::Int(1)]),
        Value::atom_with("e", vec![Value::Int(1), Value::Int(1)]),
        named("code"),
        named("why"),
        Value::int(BigInt::from(1u64 << 63)),
        Value::int(-BigInt::from(1u64 << 63) - 1),
        kept.clone(),
        Value::power_text("-3^100").unwrap().unwrap(),
        Value::power_text("3^101").unwrap().unwrap(),
        Value::rat(Rat::new(BigInt::from(1), BigInt::from(2)).unwrap()),
        Value::rat(Rat::int(BigInt::from(2))),
        kept_rat,
        Value::tuple(vec![]),
        Value::tuple(vec![Value::Int(1)]),
        Value::tuple(vec![Value::Int(1), Value::Int(2)]),
        Value::path(vec![Value::Int(1)]),
        Value::Family(Family::new()),
        Value::Family(Family::of([(1, 2)])),
        Value::Family(Family::of([(1, 3)])),
        Value::Family(Family::of([(2, 2)])),
        Value::Family(Family::of([(1, 2), (2, 2)])),
    ]
}

/// One pattern of each kind, and the variants that differ in one part. Each binds `b` where it
/// binds, and the arm reads `b` there and the free `n` elsewhere.
fn patterns(b: &str) -> Vec<Pattern> {
    let bind = || Pattern::Bind(b.into());
    vec![
        Pattern::Wild,
        bind(),
        Pattern::Lit(Value::Int(1)),
        Pattern::Lit(Value::Int(2)),
        Pattern::Atom("e".into(), vec![]),
        Pattern::Atom("f".into(), vec![]),
        Pattern::Atom("e".into(), vec![bind()]),
        Pattern::Atom("e".into(), vec![Pattern::Wild]),
        Pattern::Fields("e".into(), vec![("code".into(), bind())]),
        Pattern::Fields("e".into(), vec![("why".into(), bind())]),
        Pattern::Fields("e".into(), vec![("code".into(), Pattern::Wild)]),
        Pattern::Fields(
            "e".into(),
            vec![("code".into(), bind()), ("why".into(), Pattern::Wild)],
        ),
        Pattern::Tuple(vec![]),
        Pattern::Tuple(vec![bind()]),
        Pattern::Tuple(vec![bind(), Pattern::Wild]),
        Pattern::AnyAtom,
        Pattern::Is(Type::int()),
        Pattern::Is(Type::bool()),
    ]
}

/// One term of each form, and the variants that differ in one part. Every local name is built
/// from `n`: `n` itself is free, to be bound by a lambda around the term, and the term's own
/// binders are `n` followed by a letter. So the catalogs of two names are α-equivalent term by
/// term once each is put under `lambda n`.
fn catalog(n: &str) -> Vec<Term> {
    let x = || var(n);
    let a = format!("{n}a");
    let b = format!("{n}b");
    let c = format!("{n}c");
    let id = || lam(&[&a], var(&a));
    // A definedness step reads `this` (`a`) and the key (`b`), which it binds; a lattice step
    // is a function from one iterate to the next, and its `this` and key are unused.
    let fix = |kind: FixKind, ev: Evidence| Term::Fix {
        init: s(lam(&[&b], var(&b))),
        step: s(match kind {
            FixKind::Definedness => app(var(&a), vec![prim(Prim::Sub, vec![var(&b), x()])]),
            FixKind::Lattice { .. } => lam(&[&a], prim(Prim::Add, vec![var(&a), x()])),
        }),
        this: a.as_str().into(),
        key: b.as_str().into(),
        kind,
        ev,
    };
    let reindex = |witness| Term::Reindex {
        family: s(x()),
        kf: s(id()),
        vf: s(id()),
        witness,
    };
    let generate = |pos| Term::Gen {
        init: s(lit(0)),
        step: s(lam(&[&a], prim(Prim::Add, vec![var(&a), x()]))),
        guard: s(id()),
        pos,
    };
    let mut terms = vec![
        x(),
        var("free"),
        lam(&[&a], x()),
        lam(&[&a], var(&a)),
        lam(&[&a, &b], var(&a)),
        lam(&[&a, &b], var(&b)),
        app(x(), vec![lit(1)]),
        app(x(), vec![lit(1), lit(1)]),
        prim(Prim::Add, vec![x(), lit(1)]),
        prim(Prim::Sub, vec![x(), lit(1)]),
        Term::PrimFn(Prim::Add),
        Term::PrimFn(Prim::Sub),
        let_(&a, x(), var(&a)),
        let_(&a, x(), x()),
        Term::If(s(x()), s(lit(1)), s(lit(2))),
        Term::If(s(x()), s(lit(2)), s(lit(1))),
        Term::Match(s(x()), vec![]),
        Term::Match(s(x()), vec![(Pattern::Wild, x()), (Pattern::Wild, lit(0))]),
        Term::Fam {
            domain: s(x()),
            var: a.as_str().into(),
            body: s(var(&a)),
        },
        Term::Fam {
            domain: s(x()),
            var: a.as_str().into(),
            body: s(x()),
        },
        reindex(Witness::Residue),
        reindex(Witness::Catalog("sortedKeys".into())),
        reindex(Witness::Catalog("shiftKeys".into())),
        Term::Discard {
            family: s(x()),
            sel: s(id()),
        },
        Term::Discard {
            family: s(id()),
            sel: s(x()),
        },
        fold(x(), None, 1, Evidence::new()),
        fold(x(), Some(lit(0)), 1, Evidence::new()),
        fold(x(), Some(lit(1)), 1, Evidence::new()),
        fold(x(), None, 2, Evidence::new()),
        fold(x(), None, 1, evidence(&[("commutative", Grade::Axiom)])),
        fix(FixKind::Definedness, Evidence::new()),
        fix(FixKind::Lattice { join: s(x()) }, Evidence::new()),
        fix(FixKind::Lattice { join: s(id()) }, Evidence::new()),
        fix(
            FixKind::Definedness,
            evidence(&[("monotone", Grade::Proved)]),
        ),
        // A definedness step with a binder of its own, inside `this` and the key.
        Term::Fix {
            init: s(x()),
            step: s(app(lam(&[&c], var(&c)), vec![var(&a), var(&b)])),
            this: a.as_str().into(),
            key: b.as_str().into(),
            kind: FixKind::Definedness,
            ev: Evidence::new(),
        },
        generate(GuardPos::Before),
        generate(GuardPos::After),
        Term::Read("stdin".into()),
        Term::Read("args".into()),
        Term::Push("stdout".into(), s(x())),
        Term::Push("stdout".into(), s(lit(1))),
        Term::Push("stderr".into(), s(x())),
    ];
    // Each grade of evidence, on one property and on two.
    for g in [
        Grade::Axiom,
        Grade::CheckedExhaustive,
        Grade::Proved,
        Grade::Bounded,
        Grade::Obligated,
        Grade::Assumed,
    ] {
        terms.push(fold(x(), None, 1, evidence(&[("associative", g)])));
    }
    terms.push(fold(
        x(),
        None,
        1,
        evidence(&[("associative", Grade::Axiom), ("commutative", Grade::Axiom)]),
    ));
    terms.extend(values().into_iter().map(Term::Lit));
    terms.extend(patterns(&b).into_iter().map(|p| {
        let arm = match binders::pattern_binds(&p).is_empty() {
            true => x(),
            false => var(&b),
        };
        Term::Match(s(x()), vec![(p, arm)])
    }));
    terms
}

/// The address of `lambda n -> t`.
fn under(n: &str, t: Term) -> ContentAddress {
    addr(&def("k", lam(&[n], t)))
}

#[test]
fn each_form_of_term_value_and_pattern_has_an_address_of_its_own() {
    // DESIGN.md M0.7: two declarations have equal serializations exactly when their canonical
    // forms are identical. The catalog's terms are pairwise distinct and not α-equivalent.
    let terms = catalog("x");
    let mut seen: BTreeMap<ContentAddress, usize> = BTreeMap::new();
    for (i, t) in terms.iter().enumerate() {
        if let Some(j) = seen.insert(under("x", t.clone()), i) {
            panic!("terms {j} and {i} share an address:\n{:?}\n{t:?}", terms[j]);
        }
    }
    // A free variable is hashed by its name, so the bare catalog's addresses differ too.
    let bare: std::collections::BTreeSet<ContentAddress> =
        terms.iter().map(|t| addr(&def("k", t.clone()))).collect();
    assert_eq!(bare.len(), terms.len());
}

#[test]
fn each_form_keeps_its_address_when_its_local_names_change() {
    let (xs, ys) = (catalog("x"), catalog("total"));
    for (x, y) in xs.into_iter().zip(ys) {
        assert_eq!(
            under("x", x.clone()),
            under("total", y.clone()),
            "{x:?}\n{y:?}"
        );
    }
}

#[test]
fn each_form_reaches_one_normal_form_in_one_pass_or_by_single_steps() {
    for t in catalog("x") {
        one_pass_is_stepwise(lam(&["x"], t.clone()));
        one_pass_is_stepwise(t);
    }
}

/// `index: <d> = i` as a definition.
fn index(d: Domain) -> Def {
    Def {
        name: "index".into(),
        domain: Some(d),
        facets: vec![],
        body: var("i"),
    }
}

#[test]
fn domain_endpoints_and_classes_past_64_bits_have_addresses_of_their_own() {
    let big = |v: i128| End::Fin(v.into());
    let p70: i128 = 1 << 70;
    let ints = |lo, hi| Domain {
        ints: IntervalSet::range(lo, hi),
        class: Congruence::top(),
        finite: FiniteSet::Top,
    };
    let class = |m: i128, r: i128| Domain {
        ints: IntervalSet::top(),
        class: Congruence::new(m, r),
        finite: FiniteSet::Top,
    };
    let domains = [
        ints(End::NegInf, End::of(5)),
        ints(End::NegInf, End::of(6)),
        ints(End::of(5), End::PosInf),
        ints(End::NegInf, big(p70)),
        ints(big(-p70), End::PosInf),
        ints(big(-p70), big(p70)),
        ints(End::of(i64::MAX), big(i128::from(i64::MAX) + 1)),
        ints(End::of(i64::MIN), End::of(i64::MAX)),
        ints(big(i128::from(i64::MIN) - 1), End::of(i64::MAX)),
        class(4, 1),
        class(p70, 1),
        class(p70, 3),
        class(p70 + 2, 1),
    ];
    let mut seen = BTreeMap::new();
    for (i, d) in domains.iter().enumerate() {
        let n = d.normal();
        assert_eq!(&n, d, "domain {i} is written in normal form");
        if let Some(j) = seen.insert(addr(&index(d.clone())), i) {
            panic!("domains {j} and {i} share an address");
        }
    }
    // `Domain::ints` is the interval with no other fact.
    assert_eq!(
        Domain::ints(IntervalSet::of(1, 3)),
        ints(End::of(1), End::of(3))
    );
    // A domain and no domain differ.
    assert_ne!(
        addr(&index(domains[0].clone())),
        addr(&def("index", var("i")))
    );
}

#[test]
fn a_body_held_in_place_has_the_address_of_its_definition() {
    // `address_of_body` is `address` of the definition with no domain and no facets.
    let none = |_: &str| None;
    for t in catalog("x") {
        let body = lam(&["x"], t);
        assert_eq!(
            zedc::canon::address_of_body("k", &body, &none).expect("memory"),
            addr(&def("k", body.clone())),
            "{body:?}"
        );
    }
}

#[test]
fn a_unit_address_hashes_its_exports_sorted_by_name_then_address() {
    // DESIGN.md M0.11: the exports sorted by name and then by address, each as its name and
    // its address; the order they are listed in does not matter.
    use zedc::canon::unit_address;
    let a = addr(&def("a", lit(1)));
    let b = addr(&def("b", lit(2)));
    assert_eq!(
        unit_address(&[("f", a), ("g", b)]),
        unit_address(&[("g", b), ("f", a)])
    );
    assert_eq!(
        unit_address(&[("f", a), ("f", b)]),
        unit_address(&[("f", b), ("f", a)]),
        "the arrows of an overloaded name"
    );
    let all = [
        unit_address(&[]),
        unit_address(&[("f", a)]),
        unit_address(&[("f", b)]),
        unit_address(&[("g", a)]),
        unit_address(&[("f", a), ("g", b)]),
        unit_address(&[("f", b), ("g", a)]),
        unit_address(&[("fg", a)]),
    ];
    for (i, x) in all.iter().enumerate() {
        for y in &all[i + 1..] {
            assert_ne!(x, y);
        }
    }
}

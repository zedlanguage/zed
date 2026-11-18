//! Plan row TEST-kernel-hash-keys: a definedness fix finds the entry a read names by a hash
//! lookup ([`key_index`], [`position`]) and builds its family with `Family::from_map`, where it
//! used a binary search of its ordered domain and `Family::from_leaves` (commit b8b284a09,
//! KERNEL-near-limit-benches). These tests check that the hash path gives the answers of the
//! ordered path on keys that are equal in more than one form, and each has a negative control:
//! a lookup or a hash known to be wrong is run through the same check and must be caught.

use std::collections::HashMap;
use std::hash::{BuildHasher, Hash, Hasher, RandomState};

use num_bigint::BigInt;

use super::{as_key, key_index, position};
use crate::num::Rat;
use crate::text::Text;
use crate::value::{Family, Id, Value};

/// A tuple of `xs`, built fresh, so that its sequence is held once.
fn tuple(xs: Vec<Value>) -> Value {
    Value::tuple(xs)
}

/// `s` joined from its parts cut at `at`, a string held as two pieces.
fn joined(s: &str, at: usize) -> Value {
    Value::Str(Text::join(&Text::from(&s[..at]), &Text::from(&s[at..])).expect("short"))
}

/// 3/4 in two forms: built from 3 and 4, and read as a decimal with its power of 10 kept.
fn three_quarters() -> (Value, Value) {
    let built = Rat::new(BigInt::from(3), BigInt::from(4)).expect("a denominator above 0");
    let decimal = Rat::decimal("75e-2").expect("memory").expect("a decimal");
    (Value::rat(built), Value::rat(decimal))
}

/// 10^19, beyond 64 bits, from its digits and from a decimal exponent.
fn ten_to_19() -> (Value, Value) {
    let digits = Value::int_text(&format!("1{}", "0".repeat(19)), 10)
        .expect("memory")
        .expect("digits");
    let r = Rat::decimal("1e19").expect("memory").expect("a decimal");
    (digits, Value::integer(r))
}

/// Keys of a fix's domain, each with other values equal to it built another way: `-0.0` for
/// `0.0` (alone and inside tuples, paths and atoms), NaN by other bits, a rational and a wide
/// integer in two forms, a string flat and joined, and tuples shared and fresh, nested or
/// holding one shared tuple twice.
fn keys() -> Vec<(Value, Vec<Value>)> {
    let long = format!("{}y", "x".repeat(70));
    let (rat, rat_other) = three_quarters();
    let (big, big_other) = ten_to_19();
    let pair = tuple(vec![Value::Int(1), Value::float(0.0)]);
    let inner = tuple(vec![Value::Int(2), Value::str("q")]);
    let twice = tuple(vec![inner.clone(), inner]);
    let nested = tuple(vec![
        tuple(vec![Value::float(0.0), Value::str("ab")]),
        rat.clone(),
        Value::float(f64::NAN),
    ]);
    vec![
        (Value::Bool(true), vec![]),
        (Value::Int(0), vec![]),
        (Value::float(0.0), vec![Value::float(-0.0)]),
        (Value::float32(0.0), vec![Value::float32(-0.0)]),
        (
            Value::float(f64::NAN),
            vec![
                Value::float(f64::from_bits(0x7ff8_0000_0000_0001)),
                Value::float(f64::from_bits(0xfff0_0000_0000_0001)),
                Value::float(-f64::NAN),
            ],
        ),
        (
            Value::float32(f32::NAN),
            vec![
                Value::float32(f32::from_bits(0x7fc0_0001)),
                Value::float32(f32::from_bits(0xff80_0001)),
            ],
        ),
        (rat, vec![rat_other.clone()]),
        (big, vec![big_other.clone()]),
        (Value::str(&long), vec![joined(&long, 1), joined(&long, 33)]),
        (
            pair.clone(),
            vec![
                pair,
                tuple(vec![Value::Int(1), Value::float(0.0)]),
                tuple(vec![Value::Int(1), Value::float(-0.0)]),
            ],
        ),
        (
            twice.clone(),
            vec![twice, {
                let fresh = || tuple(vec![Value::Int(2), joined("q", 0)]);
                tuple(vec![fresh(), fresh()])
            }],
        ),
        (
            nested.clone(),
            vec![
                nested,
                tuple(vec![
                    tuple(vec![Value::float(-0.0), joined("ab", 1)]),
                    rat_other,
                    Value::float(f64::from_bits(0x7ff8_0000_0000_00ff)),
                ]),
            ],
        ),
        (
            Value::path(vec![Value::Int(1), Value::float(0.0)]),
            vec![Value::path(vec![Value::Int(1), Value::float(-0.0)])],
        ),
        (
            tuple(vec![Value::atom_with(
                "e",
                vec![Value::float(0.0), big_other],
            )]),
            vec![tuple(vec![Value::atom_with(
                "e",
                vec![Value::float(-0.0), ten_to_19().0],
            )])],
        ),
    ]
}

/// Values in no domain built from [`keys`], each close to one of its keys.
fn misses() -> Vec<Value> {
    vec![
        Value::Bool(false),
        Value::float(1e-300),
        Value::float(-1e-300),
        Value::float32(1e-30),
        Value::float(f64::INFINITY),
        Value::rat(Rat::new(BigInt::from(3), BigInt::from(5)).expect("above 0")),
        Value::int_text(&format!("1{}1", "0".repeat(18)), 10)
            .expect("memory")
            .expect("digits"),
        Value::str(&"x".repeat(71)),
        tuple(vec![Value::Int(1), Value::float(1e-300)]),
        tuple(vec![Value::Int(1), Value::float(0.0), Value::float(0.0)]),
        tuple(vec![Value::Int(1)]),
        Value::path(vec![Value::Int(1)]),
        tuple(vec![Value::atom_with("e", vec![Value::float(0.0)])]),
        tuple(vec![Value::atom_with(
            "f",
            vec![Value::float(0.0), ten_to_19().0],
        )]),
    ]
}

/// The domain a fix over [`keys`] reads: the keys of the family it is given, which hold keys
/// and are distinct and in order.
fn domain() -> Box<[Value]> {
    let set = Family::set(keys().into_iter().map(|(k, _)| k));
    set.keys().cloned().collect()
}

/// Every probe of a lookup: each key, each other form of it, and each miss.
fn probes() -> Vec<Value> {
    let forms = keys().into_iter().flat_map(|(k, other)| [vec![k], other]);
    forms.flatten().chain(misses()).collect()
}

/// The probes, and the keys of `domain` itself held twice, for which `find` gives another
/// position than the ordered path does, with what each gave. The ordered path is checked
/// twice: a binary search of `domain` for the probe's key, and `Family::get` of a family
/// whose entries are the domain's positions.
fn disagreements(domain: &[Value], find: impl Fn(&Value) -> Option<usize>) -> Vec<String> {
    let at = Family::of(
        domain
            .iter()
            .enumerate()
            .map(|(i, k)| (k.clone(), i as i64)),
    );
    let mut out = Vec::new();
    for p in probes().into_iter().chain(domain.iter().cloned()) {
        let searched = domain.binary_search(&*as_key(&p)).ok();
        let got = at.get(&p).map(|v| match v {
            Value::Int(i) => *i as usize,
            _ => unreachable!("positions are integers"),
        });
        assert_eq!(searched, got, "the two ordered lookups of {p}");
        let found = find(&p);
        if found != searched {
            out.push(format!("{p}: {found:?}, ordered {searched:?}"));
        }
    }
    out
}

/// The hash index finds each key's entry from every form of the key, and nothing for a value
/// close to a key, as the ordered lookups do. Each key's other forms are checked to be found at
/// the key's own position, so the agreement is not one of finding nothing.
#[test]
fn the_hash_index_finds_what_the_ordered_lookup_finds() {
    let domain = domain();
    assert_eq!(domain.len(), keys().len(), "the keys are distinct");
    assert!(domain.iter().all(Value::is_key));
    let index = key_index(&domain);
    assert_eq!(index.len(), domain.len());
    assert_eq!(
        disagreements(&domain, |p| position(&index, p)),
        Vec::<String>::new()
    );
    let mut forms = 0;
    for (k, other) in keys() {
        let at = domain.binary_search(&k).expect("a key of the domain");
        for v in other {
            assert_eq!(position(&index, &v), Some(at), "{v} for {k}");
            forms += 1;
        }
    }
    assert_eq!(forms, 20);
    for m in misses() {
        assert_eq!(position(&index, &m), None, "{m}");
    }
}

/// Negative control: a lookup that skips `as_key` misses each key read through a `-0.0`, and
/// the check above reports it. Six of the forms hold a `-0.0`.
#[test]
fn a_lookup_that_does_not_take_the_key_is_caught() {
    let domain = domain();
    let index = key_index(&domain);
    let wrong = disagreements(&domain, |p| index.get(p).copied());
    assert_eq!(wrong.len(), 6, "{wrong:#?}");
    assert!(wrong.iter().all(|w| w.contains("-0.0")), "{wrong:#?}");
}

/// A value hashed as `Value` hashes it, and also by the id of its outermost sequence: a hash
/// that tells a shared tuple from an equal fresh one, which a hash on values must not. Two are
/// equal when their values are and they share that sequence, so the hash agrees with `==`.
///
/// Equality reads the sharing too, and not only the hash, so that a lookup of a fresh tuple
/// misses for certain. With `==` on values alone, a lookup whose hash differs from the key's
/// still finds the key when the map's 7-bit tag of the two hashes happens to agree, about one
/// lookup in 128 with the domain's keys in one probe group; the 11 fresh sequences then gave
/// fewer than 14 misses in 51 of 800 runs, by hash seed and by the ids a run draws.
#[derive(Eq)]
struct BySequence(Value);

impl BySequence {
    /// The id of the outermost sequence, for a tuple or a path.
    fn sequence(&self) -> Option<Id> {
        match &self.0 {
            Value::Tuple(xs) | Value::Path(xs) => Some(xs.id()),
            _ => None,
        }
    }
}

impl PartialEq for BySequence {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.sequence() == other.sequence()
    }
}

impl Hash for BySequence {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.sequence().hash(state);
    }
}

/// Negative control: an index whose hash and equality read the sharing of a tuple misses each
/// of the 14 fresh tuples and paths equal to a key, whatever the hash seed, and the check
/// reports it; the domain's own keys, held twice and so sharing their sequences, are still
/// found.
#[test]
fn an_index_whose_hash_reads_sharing_is_caught() {
    let domain = domain();
    let index: HashMap<BySequence, usize> = domain
        .iter()
        .enumerate()
        .map(|(i, k)| (BySequence(k.clone()), i))
        .collect();
    let find = |p: &Value| index.get(&BySequence(as_key(p).into_owned())).copied();
    let wrong = disagreements(&domain, find);
    assert_eq!(wrong.len(), 14, "{wrong:#?}");
    for (i, k) in domain.iter().enumerate() {
        assert_eq!(find(k), Some(i), "{k}");
    }
}

/// The pairs of `values` on which `hash` breaks the rule a hash table needs: equal values hash
/// alike. Each pair is also checked to be equal exactly when the order puts them together.
fn hash_faults(values: &[Value], hash: impl Fn(&Value) -> u64) -> (usize, Vec<String>) {
    let (mut equal, mut faults) = (0, Vec::new());
    for a in values {
        for b in values {
            assert_eq!(a == b, a.cmp(b).is_eq(), "{a} and {b}");
            if a == b {
                equal += 1;
                if hash(a) != hash(b) {
                    faults.push(format!("{a} and {b}"));
                }
            }
        }
    }
    (equal, faults)
}

/// Every value of the probes and of the forms with `-0.0` taken out, with the hash of the
/// standard map's random keys: `==` holds exactly when `cmp` gives `Equal`, and equal values
/// hash alike. The count of equal pairs shows that the forms were met.
#[test]
fn equal_keys_hash_alike_in_every_form() {
    let keys_of = probes()
        .iter()
        .map(|p| as_key(p).into_owned())
        .collect::<Vec<_>>();
    let values: Vec<Value> = probes().into_iter().chain(keys_of).collect();
    let state = RandomState::new();
    let (equal, faults) = hash_faults(&values, |v| state.hash_one(v));
    assert_eq!(faults, Vec::<String>::new());
    assert!(
        equal > 2 * values.len(),
        "{equal} equal pairs of {}",
        values.len()
    );
}

/// Negative control: the hash that reads sharing breaks the rule, and the check reports it.
#[test]
fn a_hash_that_reads_sharing_is_caught() {
    let state = RandomState::new();
    let (_, faults) = hash_faults(&probes(), |v| state.hash_one(BySequence(v.clone())));
    assert!(!faults.is_empty());
}

/// Values for a family over [`domain`]: numbers, a string, the empty family, a family, one
/// with an empty level, one two levels deep, and a set; in turn, so that each meets several
/// keys.
fn entry_values() -> Vec<Value> {
    let level = Family::of([(1_i64, 2_i64), (3, 4)]);
    let with_empty =
        Family::from_leaves([(vec![Value::Int(0)], Value::Family(Family::new()))]).expect("one");
    let deep = Family::of([("a", Value::Family(level.clone()))]);
    vec![
        Value::Int(7),
        Value::float(-0.0),
        Value::str("v"),
        Value::Family(Family::new()),
        Value::Family(level),
        Value::Family(with_empty),
        Value::Family(deep),
        Value::Family(Family::set([Value::float(0.0), Value::Int(1)])),
    ]
}

/// The family of the domain's entries built as the fix builds it, by `Family::from_map` of the
/// entries in order, and as it was built, by `Family::from_leaves` of one-key keypaths.
fn both_ways(entries: &[(Value, Value)]) -> (Family, Family) {
    let mapped = Family::from_map(entries.iter().cloned().collect());
    let leaves = entries.iter().map(|(k, v)| (vec![k.clone()], v.clone()));
    (mapped, Family::from_leaves(leaves).expect("distinct keys"))
}

/// The family `Family::from_map` builds from a fix's entries is the one `Family::from_leaves`
/// built: equal, with the same leaves, the same text and the same hash, for each placement of
/// the entry values on the keys. An empty family as a value is an empty level in both.
#[test]
fn the_family_of_a_fix_is_the_family_its_leaves_build() {
    let domain = domain();
    let values = entry_values();
    let state = RandomState::new();
    for shift in 0..values.len() {
        let entries: Vec<(Value, Value)> = domain
            .iter()
            .enumerate()
            .map(|(i, k)| (k.clone(), values[(i + shift) % values.len()].clone()))
            .collect();
        let (mapped, built) = both_ways(&entries);
        assert_eq!(mapped, built, "shift {shift}");
        assert_eq!(mapped.leaves(), built.leaves(), "shift {shift}");
        assert_eq!(mapped.to_string(), built.to_string(), "shift {shift}");
        let (a, b) = (Value::Family(mapped), Value::Family(built));
        assert_eq!(state.hash_one(&a), state.hash_one(&b), "shift {shift}");
    }
}

/// Negative control: one entry changed on the `from_leaves` side, a key's family value given
/// one more leaf, is caught by the equality and by the leaves.
#[test]
fn a_family_with_one_entry_changed_is_caught() {
    let domain = domain();
    let values = entry_values();
    let entries: Vec<(Value, Value)> = domain
        .iter()
        .enumerate()
        .map(|(i, k)| (k.clone(), values[i % values.len()].clone()))
        .collect();
    let mut changed = entries.clone();
    let last = changed.last_mut().expect("entries");
    last.1 = Value::Family(Family::of([(1_i64, 2_i64), (3, 4), (5, 6)]));
    let (mapped, _) = both_ways(&entries);
    let (_, built) = both_ways(&changed);
    assert_ne!(mapped, built);
    assert_ne!(mapped.leaves(), built.leaves());
}

/// Plan row PROOF-run-under-test-bug: [`super::Evaluator::run_under`] runs the build stage's
/// terms, never the program, so it does not stop where `ZEDC_TEST_BUG` asks the program's run
/// to stop; its one caller, zedc-stage, gives it a fresh evaluator, and the debug assertion in
/// it checks that no caller gives it one set to stop. This test gives it one and sees the
/// assertion fire; the next shows that the same run on a fresh evaluator gives its value.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "a run under globals is never asked to stop")]
fn a_run_under_globals_given_an_evaluator_set_to_stop_panics() {
    let mut ev = super::Evaluator::new(super::World::new());
    ev.panic_on_run();
    let one = crate::Term::Lit(Value::Int(1));
    let _ = ev.run_under(&one, &super::Globals::default(), &[]);
}

/// Row CLOSURE-captures-read-only (DESIGN.md sec:generations, "A closure holds only the values
/// it reads"): a lambda made where `a` and `b` are bound, each to a closure the test holds too,
/// keeps alive the one its body reads, a nested lambda's body included, and lets the other go
/// while the new closure lives. The count of the test's reference shows which are held: 2 held,
/// 1 not. The machine kept the whole scope before (2 for both).
#[test]
fn a_closure_holds_only_the_values_its_body_reads() {
    use super::{Closure, Drops, HashMap, Machine, Rc, V, bind};
    use crate::term::build::{app, lam, var};
    let unit = crate::Shared::new(crate::Term::Lit(Value::Int(0)));
    // The lambda, and whether `a` and `b` are kept. The terms outlive the closures made of them.
    let cases = [
        (lam(&["x"], var("a")), true, false),
        (lam(&["x"], lam(&["y"], var("a"))), true, false),
        (lam(&["x"], var("b")), false, true),
        (lam(&["x"], var("x")), false, false),
        // A nested lambda's parameter is not read from the scope (rows
        // FAIL-map-nest-bench-ratio-again, FAIL-elab-rows-reaching-ratio: every variable of
        // the body was kept before), unless the outer body reads the name itself.
        (lam(&["x"], lam(&["a"], var("a"))), false, false),
        (
            lam(&["x"], app(lam(&["a"], var("a")), vec![var("a")])),
            true,
            false,
        ),
    ];
    let mut ev = super::Evaluator::new(super::World::new());
    let drops: Rc<Drops<'_>> = Rc::default();
    let value = || {
        Rc::new(Closure {
            params: &[],
            body: &unit,
            at: 0,
            env: None,
            drops: drops.clone(),
            placed: None,
        })
    };
    let (a, b) = (value(), value());
    for (term, keeps_a, keeps_b) in &cases {
        let mut machine = Machine {
            ev: &mut ev,
            frames: Vec::new(),
            drops: drops.clone(),
            globals: None,
            made: HashMap::new(),
            short_paths: Vec::new(),
            failed: None,
            vals: Vec::new(),
        };
        let env = bind(None, "a", V::Closure(a.clone()), None);
        let env = bind(env, "b", V::Closure(b.clone()), None);
        let Ok(V::Closure(made)) = machine.run(term, env) else {
            panic!("a lambda gives a closure");
        };
        let what = crate::print::pretty(term, 80);
        assert_eq!(Rc::strong_count(&a), 1 + usize::from(*keeps_a), "a, {what}");
        assert_eq!(Rc::strong_count(&b), 1 + usize::from(*keeps_b), "b, {what}");
        drop(made);
        assert_eq!(
            (Rc::strong_count(&a), Rc::strong_count(&b)),
            (1, 1),
            "{what}"
        );
    }
}

/// A closure that keeps only what its body reads still runs: a nested lambda reads a name of
/// the outermost scope, and a lattice `fix` inside a lambda reads its join from the scope, a
/// name nothing else in the lambda reads (row CLOSURE-captures-read-only: the names read
/// missed the join before, [`super::made::reads`]).
#[test]
fn a_closure_that_keeps_what_it_reads_runs() {
    use crate::term::build::{app, lam, let_, lit, prim, var};
    use crate::term::{Evidence, FixKind, Prim, Shared, Term};
    let nested = let_(
        "a",
        lit(1i64),
        let_(
            "b",
            lit(2i64),
            app(
                app(
                    lam(
                        &["x"],
                        lam(&["y"], prim(Prim::Add, vec![var("a"), var("y")])),
                    ),
                    vec![lit(0i64)],
                ),
                vec![lit(10i64)],
            ),
        ),
    );
    let mut ev = super::Evaluator::new(super::World::new());
    assert_eq!(ev.run(&nested).expect("a sum"), Value::Int(11));
    let set = |xs: &[i64]| lit(Value::Family(Family::set(xs.iter().copied())));
    let ascent = Term::Fix {
        init: Shared::new(set(&[1])),
        step: Shared::new(lam(&["r"], set(&[2]))),
        this: "this".into(),
        key: "k".into(),
        kind: FixKind::Lattice {
            join: Shared::new(var("u")),
        },
        ev: Evidence::new(),
    };
    let joined = let_(
        "u",
        Term::PrimFn(Prim::Union),
        app(lam(&["x"], ascent), vec![lit(0i64)]),
    );
    let want = Value::Family(Family::set([1i64, 2]));
    assert_eq!(ev.run(&joined).expect("a set"), want);
}

/// The names a lambda body reads ([`super::made::reads`]) in a nest of lambdas, each reading
/// its own parameter and that of the lambda around it, are those two, at every depth: a nested
/// lambda's parameters are taken out of what it adds to the bodies around it. Every variable
/// of the body was kept before, `n - i` names at depth `i`, Θ(n²) in all (row
/// FAIL-map-nest-bench-ratio-again). The nest is deep enough that a walk by recursion would
/// need a stack of its depth. The sets are kept on the bodies, found once: a second call gives
/// the same set, and a body changed in place has its set found again.
#[test]
fn the_names_a_nest_of_lambdas_reads_are_its_free_names() {
    use crate::term::build::{lam, lit, prim, var};
    use crate::term::{Prim, Shared, Term};
    let n = 10_000;
    let q = |i: usize| format!("q{i}");
    let mut body = lit(0i64);
    for i in (0..n).rev() {
        let outer = if i == 0 { lit(0i64) } else { var(&q(i - 1)) };
        body = lam(&[&q(i)], prim(Prim::Tuple, vec![var(&q(i)), outer, body]));
    }
    let Term::Lam(_, top) = &body else {
        panic!("a lambda")
    };
    let names = |b: &Shared| -> Vec<String> {
        super::made::reads(b)
            .iter()
            .map(|x| x.to_string())
            .collect()
    };
    assert_eq!(names(top), ["q0"]);
    // Every body below: its own parameter and the one around it.
    let mut b = top.clone();
    for i in 1..n {
        let Term::Prim(_, parts) = &*b else {
            panic!("a tuple")
        };
        let Term::Lam(_, inner) = &parts[2] else {
            panic!("a lambda")
        };
        b = inner.clone();
        let mut want = [q(i - 1), q(i)];
        want.sort();
        assert_eq!(names(&b), want);
    }
    // Kept: a second call gives the set found, not a new one.
    let mut top = top.clone();
    assert!(std::sync::Arc::ptr_eq(
        &super::made::reads(&top),
        &super::made::reads(&top)
    ));
    // Changed in place: found again.
    *Shared::make_mut(&mut top) = var("z");
    assert_eq!(names(&top), ["z"]);
}

/// The names a lambda body reads ([`super::made::reads`]) leave out those its own binders bind
/// where they bind them, as the evaluator binds them: a `let`'s name over its body only, a
/// `match` arm's pattern names over the arm, a `fam`'s key over its body, a definedness `fix`'s
/// `this` and `key` over its step; a lattice `fix` binds nothing over its step or join. A
/// chain of n `let`s, each read inside its own body, reads only the name the first is bound to
/// (`x * i` is elaborated to such a `let`): every `let`'s name was kept before, and each of n
/// test rows that made the function's closure looked all n up (row
/// FAIL-elab-rows-reaching-ratio). A node reached twice is read under no scope, so a name bound
/// above it is kept, never a free one missed.
#[test]
fn the_names_a_body_reads_leave_out_those_its_binders_bind() {
    use crate::term::build::{let_, lit, prim, var};
    use crate::term::{Evidence, FixKind, Pattern, Prim, Shared, Term};
    let names = |t: Term| -> Vec<String> {
        let b = Shared::new(t);
        super::made::reads(&b)
            .iter()
            .map(|x| x.to_string())
            .collect()
    };
    let add = |a: Term, b: Term| prim(Prim::Add, vec![a, b]);
    // A `let`'s name is bound over its body, not over its value.
    assert_eq!(names(let_("k", var("x"), var("k"))), ["x"]);
    assert_eq!(names(let_("k", var("k"), var("k"))), ["k"]);
    assert_eq!(
        names(add(let_("k", var("x"), var("k")), var("k"))),
        ["k", "x"]
    );
    // A chain of n `let`s, each read inside its own body.
    let n = 10_000;
    let mut chain = var("x");
    for i in (0..n).rev() {
        let k = format!("$k{i}");
        chain = let_(&k, var("x"), add(var(&k), chain));
    }
    assert_eq!(names(chain), ["x"]);
    // A `match` arm's pattern binds over the arm, nested patterns too, not over the scrutinee or
    // the other arms.
    let pat = Pattern::Tuple(vec![
        Pattern::Bind("p".into()),
        Pattern::Atom("a".into(), vec![Pattern::Bind("q".into())]),
    ]);
    let m = Term::Match(
        Shared::new(var("p")),
        vec![
            (pat, add(var("p"), add(var("q"), var("r")))),
            (Pattern::Wild, var("q")),
        ],
    );
    assert_eq!(names(m), ["p", "q", "r"]);
    // A `fam`'s key over its body, not over its domain.
    let fam = |d: Term| Term::Fam {
        domain: Shared::new(d),
        var: "i".into(),
        body: Shared::new(add(var("i"), var("y"))),
    };
    assert_eq!(names(fam(var("d"))), ["d", "y"]);
    assert_eq!(names(fam(var("i"))), ["i", "y"]);
    // A definedness `fix` binds `this` and `key` over its step; a lattice one binds nothing.
    let fix = |kind| Term::Fix {
        init: Shared::new(var("this")),
        step: Shared::new(add(var("this"), var("k"))),
        this: "this".into(),
        key: "k".into(),
        kind,
        ev: Evidence::new(),
    };
    assert_eq!(names(fix(FixKind::Definedness)), ["this"]);
    let lattice = FixKind::Lattice {
        join: Shared::new(var("k")),
    };
    assert_eq!(names(fix(lattice)), ["k", "this"]);
    // A node reached twice, once under a `let` of its name and once not: kept.
    let shared = Shared::new(var("k"));
    let twice = Term::Let(
        "k".into(),
        Shared::new(lit(0i64)),
        Shared::new(Term::If(
            Shared::new(var("c")),
            shared.clone(),
            shared.clone(),
        )),
    );
    assert_eq!(names(twice), ["c", "k"]);
    let both = Term::If(
        Shared::new(var("c")),
        shared.clone(),
        Shared::new(Term::Let("k".into(), Shared::new(lit(0i64)), shared)),
    );
    assert_eq!(names(both), ["c", "k"]);
}

/// The run of [`a_run_under_globals_given_an_evaluator_set_to_stop_panics`] on a fresh
/// evaluator, which gives its value.
#[test]
fn a_run_under_globals_on_a_fresh_evaluator_gives_its_value() {
    let mut ev = super::Evaluator::new(super::World::new());
    let one = crate::Term::Lit(Value::Int(1));
    let got = ev.run_under(&one, &super::Globals::default(), &[]);
    assert_eq!(got.expect("a literal"), Value::Int(1));
}

/// Plan row TEST-reads-memo-not-in-key: the names a lambda body reads, kept on its node
/// (`ReadsMemo` in term.rs), take no part in equality, and no `Hash` or `Ord` is implemented
/// for `Shared` or `Term`, so no map key reads them. Two nodes built from one term, one whose
/// memo a run filled when it made a closure of it and one never run, are equal both ways, and
/// so are the terms that hold them; so is a node whose memo holds a wrong set. Seen to fail
/// with `Shared`'s equality made to read whether the memo is filled, and to stop compiling
/// with a `Hash` for `Shared` added (the negative controls, run once and not kept).
#[test]
fn the_names_a_body_reads_take_no_part_in_equality() {
    use crate::term::build::{app, lam, let_, lit, prim, var};
    use crate::term::{Prim, Shared, Term};
    /// Compiles only while `T` implements neither `Hash` nor `Ord`: were it to implement one,
    /// `check` would have two impls to choose from and the call would be ambiguous.
    trait NoKey<A> {
        fn check() {}
    }
    impl<T: ?Sized> NoKey<()> for T {}
    struct ByHash;
    struct ByOrd;
    impl<T: ?Sized + Hash> NoKey<ByHash> for T {}
    impl<T: ?Sized + Ord> NoKey<ByOrd> for T {}
    <Shared as NoKey<_>>::check();
    <Term as NoKey<_>>::check();

    let body = || prim(Prim::Tuple, vec![var("x"), var("y")]);
    let (run, never) = (Shared::new(body()), Shared::new(body()));
    let f = Term::Lam(vec!["x".into()], run.clone());
    let made = let_("y", lit(1i64), app(f, vec![lit(2i64)]));
    let want = Value::tuple(vec![Value::Int(2), Value::Int(1)]);
    assert_eq!(super::eval(&made).expect("a tuple"), want);
    assert!(run.reads_memo().get().is_some(), "the run filled the memo");
    assert!(never.reads_memo().get().is_none());
    assert_ne!(run.id(), never.id());
    assert!(run == never && never == run);
    let held = |b: &Shared| lam(&["z"], Term::Lam(vec!["x".into()], b.clone()));
    assert!(held(&run) == held(&never) && held(&never) == held(&run));
    // A memo that holds a wrong set changes nothing either.
    let wrong = Shared::new(body());
    let _ = wrong
        .reads_memo()
        .set(std::sync::Arc::from([std::sync::Arc::from("z")]));
    assert!(wrong == never && never == wrong && wrong == run);
    // The terms still differ where they differ.
    assert!(Shared::new(var("x")) != run);
}

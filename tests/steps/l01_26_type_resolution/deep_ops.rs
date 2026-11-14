//! The operations on a type nested as deep as the program keep their own stack (T2-ty): each
//! runs on a type [`DEEP`] levels deep on a stack of [`SHALLOW_STACK`] bytes, the same stack a
//! level as 2 MiB at 100,000 levels, and costs linear time in the depth (the benchmarks in
//! `bench::deep_ops`).
//!
//! `Debug` of a type or signature, [`Ty::meet`], [`Ty::meets`] and [`Ty::contains`] recursed
//! once a level and overflowed this stack; the others here passed before and are kept so that
//! none comes back. A meet, a `meets` and a `contains` walk a pair of nodes shared at many
//! places once, so a tuple with `2^n` paths through `n` nodes costs `O(n)`.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::Value;
use zed_kernel::types::Type;
use zed_tests::scaling;
use zedc::check::ty::{self, Binds, SParam, Shape, Sig, Ty, Vars};

/// The depth of the deep checks here. They ran 100,000 deep on a 2 MiB stack (T2-ty), and the
/// two slowest 20,000 deep on a fifth of it, after taking 73 s and over 80 s alone at load 42
/// (TESTS-l01_29-split); their time is linear in the depth, and they need no more stack at
/// 20,000 levels than at 100. Each now runs 13,000 deep, about an eighth of 100,000, on the
/// same fraction of 2 MiB; 13,000 and 100,000 leave the same remainder by 6, so the outermost
/// level of [`levels`] and the parity of the depth are as they were
/// (TEST-bench-move-l0126).
pub(super) const DEEP: usize = 13_000;

/// A 2 MiB stack scaled by [`DEEP`] / 100,000, so a check that takes stack a level overflows it
/// as it would overflow 2 MiB at 100,000 levels: a walk of two tuples that recurses once a
/// level, about 30 bytes a level, overflows both, while the checks here need under 128 KiB.
const SHALLOW_STACK: usize = (2 << 20) * DEEP / 100_000;

/// Runs `f` on a thread with a stack of [`SHALLOW_STACK`] bytes.
pub(super) fn on_shallow_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    scaling::on_a_thread(SHALLOW_STACK, f)
}

pub(super) fn z() -> Ty {
    Ty::set(Type::atom("z"))
}

pub(super) fn y() -> Ty {
    Ty::set(Type::atom("y"))
}

/// The atom `#a` with a payload of `items` and the field `f`.
fn atom(items: Vec<Ty>, f: Ty) -> Ty {
    let mut t = Ty::set(Type::atom_with("a", &Type::top()));
    let shape = Shape::new(items, [("f".into(), f)].into());
    t.payloads.insert("a".into(), Some(vec![shape]));
    t
}

/// The signature `(x: param) -> result`.
pub(super) fn sig(param: Ty, result: Ty) -> Sig {
    let x = SParam {
        name: "x".into(),
        positional: true,
        default: None,
    };
    let own: BTreeSet<Arc<str>> = param.vars.clone();
    let mut s = Sig::one(vec![x], vec![param], result);
    s.own = own;
    s
}

fn func(param: Ty, result: Ty) -> Ty {
    Ty::func(Arc::new(sig(param, result)))
}

/// A type `n` levels deep with `bottom` at the bottom, a tuple, an atom's payload and a
/// function's result in turn, each level built anew.
pub(super) fn levels(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, k| match k % 3 {
        0 => Ty::tuple(vec![t, z()]),
        1 => atom(vec![z(), t], z()),
        _ => func(z(), t),
    })
}

/// [`levels`] with no function: a tuple and an atom's payload in turn.
fn data(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, k| match k % 2 {
        0 => Ty::tuple(vec![t, z()]),
        _ => atom(vec![z(), t], z()),
    })
}

/// `((… (bottom, #z) …, #z), #z)`, `n` tuples deep, each built anew.
pub(super) fn tuples(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, _| Ty::tuple(vec![t, z()]))
}

/// A tuple `n` levels deep holding a variable at each level, in a tuple and a payload in turn.
fn open(n: usize) -> Ty {
    (0..n).fold(Ty::var("T".into()), |t, k| match k % 2 {
        0 => Ty::tuple(vec![t, Ty::var(format!("V{k}").into())]),
        _ => atom(vec![t], Ty::var("T".into())),
    })
}

/// The value `((… (#bottom, #z) …, #z), #z)`, `n` tuples deep.
pub(super) fn value(n: usize, bottom: &str) -> Value {
    (0..n).fold(Value::atom(bottom), |v, _| {
        Value::tuple(vec![v, Value::atom("z")])
    })
}

/// `(t, t)` for `t` the same `n - 1` deep, `bottom` at the bottom: `2^n` paths through `n`
/// tuples.
pub(super) fn shared(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, _| Ty::tuple(vec![t.clone(), t]))
}

/// The value of [`shared`] with `#z` at the bottom, its tuples shared too.
pub(super) fn shared_value(n: usize) -> Value {
    (0..n).fold(Value::atom("z"), |v, _| Value::tuple(vec![v.clone(), v]))
}

#[test]
fn clone_hash_and_drop_of_a_deep_type_run_on_a_shallow_stack() {
    on_shallow_stack(|| {
        let t = levels(DEEP, z());
        let u = t.clone();
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        let h = BuildHasherDefault::<DefaultHasher>::default();
        assert_eq!(h.hash_one(&t), h.hash_one(&u));
        drop(t);
        drop(u);
    });
}

#[test]
fn display_and_debug_of_a_deep_type_run_on_a_shallow_stack() {
    // The derived `Debug` of a type and a signature recursed once a level.
    on_shallow_stack(|| {
        let t = levels(DEEP, z());
        assert!(t.to_string().len() > DEEP);
        assert!(format!("{t:?}").len() > DEEP);
        assert!(format!("{t:#?}").len() > DEEP);
        let s = sig(levels(DEEP, z()), data(DEEP, z()));
        assert!(format!("{s:?}").len() > DEEP);
        assert!(format!("{:?}", tuples(DEEP, z()).tuples[0]).len() > DEEP);
    });
}

#[test]
fn debug_writes_what_a_derived_debug_writes() {
    // The parts are in the order and form of the derived `Debug` it replaced: the text of
    // 33 types and signatures, with needs of every kind, was compared with the derived text
    // and was the same (T2-ty).
    let t = atom(vec![tuples(1, z())], open(1));
    let text = format!("{t:?}");
    assert!(text.starts_with("Ty { set: "), "{text}");
    for part in [
        ", tuples: [], fns: [], vars: {}, dynamic: false, family: ",
        ", payloads: {\"a\": Some([Shape { items: [Ty { set: ",
        ", tuples: [[Ty { set: ",
        "payloads: {} }], fields: {\"f\": Ty { set: ",
        "vars: {\"V0\"}",
    ] {
        assert!(text.contains(part), "{part} in {text}");
    }
    assert!(text.ends_with("payloads: {} }} }])} }"), "{text}");
    assert_eq!(format!("{t:#?}"), text, "one line for {{:#?}} too");
    let s = format!("{:?}", sig(z(), z()));
    assert!(s.starts_with("Sig { params: [SParam { name: \"x\""), "{s}");
    assert!(s.contains("arrows: [Arrow { params: [Ty { set: "), "{s}");
    assert!(
        s.ends_with(", needs: [], own: {}, held: {}, named: 0, facts: _ }"),
        "{s}"
    );
}

#[test]
fn union_of_deep_types_runs_on_a_shallow_stack() {
    on_shallow_stack(|| {
        let (a, b, c) = (levels(DEEP, z()), levels(DEEP, z()), levels(DEEP, y()));
        assert_eq!(a.union(&b).fns.len() + a.union(&b).tuples.len(), 1);
        assert_eq!(a.union(&c).fns.len() + a.union(&c).tuples.len(), 2);
        assert_eq!(Ty::union_all([&a, &b, &c]).tuples.len(), 2);
    });
}

#[test]
fn meet_meets_and_contains_of_shallow_tuples_are_as_built() {
    for n in 0..7 {
        let (a, c) = (tuples(n, z()), tuples(n, y()));
        let both = a.union(&c);
        assert_eq!(a.meet(&tuples(n, z())), a, "{n} deep");
        assert_eq!(both.meet(&a), a, "{n} deep");
        assert_eq!(a.meet(&both), a, "{n} deep");
        assert!(a.meets(&both) && both.meets(&c), "{n} deep");
        assert!(both.contains(&value(n, "y")), "{n} deep");
        assert!(!a.contains(&value(n, "x")), "{n} deep");
        if n > 0 {
            assert!(a.meet(&c).is_empty(), "{n} deep");
            assert!(!a.meets(&c) && !c.meets(&a), "{n} deep");
            assert!(!a.contains(&value(n, "y")), "{n} deep");
            assert!(!a.contains(&value(n - 1, "z")), "{n} deep");
        }
        let (s, t) = (shared(n, z()), shared(n, Ty::union(&z(), &y())));
        assert_eq!(t.meet(&s), s, "{n} deep");
        assert!(t.meets(&s) && t.contains(&shared_value(n)), "{n} deep");
    }
    // A variable meets every value and holds every value.
    let v = tuples(3, Ty::var("T".into()));
    assert!(v.meets(&tuples(3, y())));
    assert!(v.contains(&value(3, "q")));
    assert!(!v.contains(&value(2, "q")));
}

#[test]
fn meet_meets_and_contains_of_deep_tuples_run_on_a_shallow_stack() {
    on_shallow_stack(|| {
        let (a, b, c) = (tuples(DEEP, z()), tuples(DEEP, z()), tuples(DEEP, y()));
        assert_eq!(a.meet(&b), a);
        assert!(a.meet(&c).is_empty());
        assert!(a.meets(&b));
        assert!(!a.meets(&c));
        let v = value(DEEP, "z");
        assert!(a.contains(&v));
        assert!(!c.contains(&v));
    });
}

#[test]
fn subtype_of_deep_types_runs_on_a_shallow_stack() {
    on_shallow_stack(|| {
        let (a, b) = (levels(DEEP, z()), levels(DEEP, z()));
        assert!(a.subtype(&b));
    });
}

#[test]
fn subtype_of_deep_data_runs_on_a_shallow_stack() {
    on_shallow_stack(|| {
        let (a, c) = (data(DEEP, z()), data(DEEP, y()));
        assert!(!a.subtype(&c));
        assert!(!a.refused(&c).contains("undecided"));
        let (a, b, c) = (
            tuples(DEEP, z()),
            tuples(DEEP, z()),
            tuples(DEEP, y()),
        );
        assert!(a.subtype(&b));
        assert!(!a.subtype(&c));
        let _ = a.verdict(&c);
    });
}

#[test]
fn diff_of_deep_types_runs_on_a_shallow_stack() {
    on_shallow_stack(|| {
        let (a, b, c) = (tuples(DEEP, z()), tuples(DEEP, z()), tuples(DEEP, y()));
        assert!(a.diff(&b).is_empty());
        assert_eq!(a.diff(&c), a);
        let (a, b) = (levels(DEEP, z()), levels(DEEP, z()));
        let _ = a.diff(&b);
    });
}

#[test]
fn kernel_of_deep_tuples_runs_on_a_shallow_stack() {
    on_shallow_stack(|| {
        let a = tuples(DEEP, z());
        assert!(a.kernel().is_some());
        assert!(a.exact_kernel().is_some());
        assert!(a.exact_data().is_some());
        assert!(a.held_wide().is_none());
        let _ = a.pieces();
        let _ = a.without_loose();
        let _ = a.without(&Type::atom("z"));
    });
}

#[test]
fn variables_of_a_deep_type_run_on_a_shallow_stack() {
    on_shallow_stack(|| {
        let t = open(DEEP);
        let mut out = Vars::default();
        t.vars_in(&mut out);
        assert_eq!(out.order.len(), DEEP.div_ceil(2) + 1);
        let mut out = Vars::default();
        t.vars_outside(&mut out);
        assert_eq!(out.order.len(), DEEP.div_ceil(2) + 1);
        let _ = t.var_facts();
        let mut b = Binds::new();
        assert!(t.sub(&open(DEEP), &mut b));
    });
}

#[test]
fn signatures_of_deep_types_run_on_a_shallow_stack() {
    on_shallow_stack(|| {
        let s = sig(levels(DEEP, z()), levels(DEEP, z()));
        let q = sig(levels(DEEP, z()), levels(DEEP, z()));
        assert!(ty::fits_sig(&s, &q));
        let _ = s.expand();
        let _ = s.int_params();
        assert!(s.same_kinds(&q));
        let _ = s.digest();
        let _ = s.facts();
        let _ = s.unheld();
        let mut t = s.clone();
        t.note_held();
    });
}

#[test]
fn signatures_of_deep_tuples_that_differ_run_on_a_shallow_stack() {
    on_shallow_stack(|| {
        let s = sig(tuples(DEEP, z()), tuples(DEEP, z()));
        let r = sig(tuples(DEEP, y()), tuples(DEEP, z()));
        assert!(!ty::fits_sig(&s, &r));
        let _ = ty::why_unfit(&s, &r);
    });
}

/// A type `n` levels deep in which the level below stands, in turn, as a function's parameter,
/// in a union in a function's result, as a tuple component and as a member of a union: the
/// places where a function type needs or does not need parentheses (PRINT-fn-parens).
pub(super) fn functions(n: usize) -> Ty {
    (0..n).fold(z(), |t, k| match k % 4 {
        0 => func(t, z()),
        1 => func(z(), t.union(&y())),
        2 => Ty::tuple(vec![t, z()]),
        _ => t.union(&y()),
    })
}

#[test]
fn a_type_with_a_function_at_every_place_prints_and_reads_back() {
    // A small instance of the benchmark
    // `bench::deep_ops::printing_a_type_with_a_function_at_every_place_takes_linear_time_in_the_depth`:
    // the printer decides each part's parentheses from where it stands, and what it writes
    // reads back as the type it printed.
    let printed = functions(5).to_string();
    assert_eq!(printed, "(((#z) -> ((#z) -> #z) | #y, #z) | #y) -> #z");
    let again = zedc::check::read::parse_type(&printed).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(again.to_string(), printed);
    assert!(again.subtype(&functions(5)) && functions(5).subtype(&again));
}

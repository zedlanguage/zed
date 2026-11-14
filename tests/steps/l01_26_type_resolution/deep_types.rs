//! Replacing variables in a type nested as deep as the program: [`Ty::subst`], [`Ty::replace`],
//! [`Ty::renamed`], [`Ty::replace_outside`], [`Ty::settle`] and [`Sig::settle`] keep their own
//! stack (TY-subst-stacks). Each recursed once a level through rows, payload shapes and
//! functions, and overflowed a 2 MiB stack a few thousand levels deep. The tests here check what
//! each gives on types a few levels deep; the benchmarks in `bench::deep_types` run them on a
//! type `bench::deep_ops::DEEP` levels deep on a stack as small a level as 2 MiB at 100,000
//! levels, and measure their time (author P178).
//!
//! Comparing two such types built apart, with `==`, keeps its own stack too (ROW-eq-deep).

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::types::Type;
use zedc::check::ty::{Binds, SParam, Shape, Sig, Ty};

/// The type `#z`, which the tests put in the place of a variable.
pub(super) fn z() -> Ty {
    Ty::set(Type::atom("z"))
}

/// The atom `#a` with a payload of `items` and the field `f`.
fn atom(items: Vec<Ty>, f: Ty) -> Ty {
    let mut t = Ty::set(Type::atom_with("a", &Type::top()));
    let shape = Shape::new(items, [("f".into(), f)].into());
    t.payloads.insert("a".into(), Some(vec![shape]));
    t
}

/// The function `(x: param) -> result`, the variables of `param` its own.
fn func(param: Ty, result: Ty) -> Ty {
    let x = SParam {
        name: "x".into(),
        positional: true,
        default: None,
    };
    let own: BTreeSet<Arc<str>> = param.vars.clone();
    let mut s = Sig::one(vec![x], vec![param], result);
    s.own = own;
    Ty::func(Arc::new(s))
}

/// A type `n` levels deep, a tuple, an atom's payload and a function's result in turn, each
/// holding `T`, the class variable `$0` and, in a function, its own variable `V`. Each variable
/// `v` is `leaf(v, inside)`, `inside` telling whether it is inside a function; so is `V` named
/// among the function's own variables.
pub(super) fn chain(n: usize, leaf: &dyn Fn(&str, bool) -> Ty) -> Ty {
    // The outermost function is at the highest level `k` with `k % 3 == 2`.
    let top = (0..n).rev().find(|k| k % 3 == 2);
    let mut t = leaf("T", top.is_some());
    for k in 0..n {
        let inside = top.is_some_and(|f| k < f);
        let v = |name| leaf(name, inside);
        t = match k % 3 {
            0 => Ty::tuple(vec![t, v("T"), v("$0")]),
            1 => atom(vec![t, v("$0")], v("T")),
            _ => func(v("V"), t),
        };
    }
    t
}

/// A variable kept as it is.
pub(super) fn same(v: &str, _: bool) -> Ty {
    Ty::var(v.into())
}

fn binds(pairs: &[(&str, Ty)]) -> Binds {
    pairs
        .iter()
        .map(|(v, t)| (Arc::from(*v), t.clone()))
        .collect()
}

/// `$0` settled to `#z`.
fn solve(v: &str) -> Option<Ty> {
    (v == "$0").then(z)
}

/// The results of each replacement over `t`.
pub(super) fn replaced_each_way(t: &Ty) -> [Ty; 6] {
    let tz = binds(&[("T", z()), ("V", z())]);
    let names = binds(&[("T", Ty::var("U".into())), ("V", Ty::var("W".into()))]);
    let held = Arc::new(Sig::one(Vec::new(), Vec::new(), t.clone()));
    [
        t.subst(&tz),
        t.replace(&tz),
        t.renamed(&names),
        t.replace_outside(&tz),
        t.settle(&solve),
        Ty::func(held.settle(&solve)),
    ]
}

/// What [`replaced_each_way`] gives for `chain(n, same)`, built with the replacements made.
pub(super) fn expected(n: usize) -> [Ty; 6] {
    // Outside functions `T` becomes `#z`; inside, `replace` replaces `T` but not `V`, which is
    // the function's own; `renamed` renames both.
    let outside = |v: &str, inside: bool| match v {
        "T" if !inside => z(),
        _ => same(v, inside),
    };
    let replaced = |v: &str, inside: bool| match v {
        "T" => z(),
        _ => same(v, inside),
    };
    let renamed = |v: &str, _: bool| match v {
        "T" => Ty::var("U".into()),
        "V" => Ty::var("W".into()),
        _ => Ty::var(v.into()),
    };
    let settled = |v: &str, inside: bool| match v {
        "$0" => z(),
        _ => same(v, inside),
    };
    let held = Arc::new(Sig::one(Vec::new(), Vec::new(), chain(n, &settled)));
    [
        chain(n, &outside),
        chain(n, &replaced),
        chain(n, &renamed),
        chain(n, &outside),
        chain(n, &settled),
        Ty::func(held),
    ]
}

/// The hash of each of `ts`: a row, payload shape and signature keeps the hash of what it
/// holds, so two types hash alike when they are alike at every depth, and the hash is read
/// at their outer level, where `==` would walk two types alike to the bottom.
pub(super) fn hashes(ts: &[Ty; 6]) -> [u64; 6] {
    use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
    ts.each_ref()
        .map(|t| BuildHasherDefault::<DefaultHasher>::default().hash_one(t))
}

#[test]
fn replacements_in_a_shallow_type_are_as_built() {
    for n in 0..7 {
        let made = replaced_each_way(&chain(n, &same));
        let want = expected(n);
        for (i, (m, w)) in made.iter().zip(&want).enumerate() {
            assert_eq!(m, w, "replacement {i}, {n} deep");
        }
        assert_eq!(hashes(&made), hashes(&want), "{n} deep");
    }
}

/// A type `n` levels deep in which each level holds the one below twice, so it has `2^n` paths
/// and `n` rows, shapes and functions, in a tuple: each replacement makes each once.
pub(super) fn shared(n: usize) -> Ty {
    let mut t = Ty::var("T".into());
    for k in 0..n {
        t = match k % 3 {
            0 => Ty::tuple(vec![t.clone(), t, Ty::var("$0".into())]),
            1 => atom(vec![t.clone(), t], Ty::var("T".into())),
            _ => func(Ty::var("V".into()), Ty::tuple(vec![t.clone(), t])),
        };
    }
    Ty::tuple(vec![t])
}

/// A type `n` levels deep with `bottom` at the bottom, a tuple, an atom's payload and a
/// function's result in turn, each level built anew: two calls share no row, shape or
/// signature, so `==` cannot take the shortcut of one shared node.
pub(super) fn levels(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, k| match k % 3 {
        0 => Ty::tuple(vec![t, z()]),
        1 => atom(vec![z(), t], z()),
        _ => func(z(), t),
    })
}

/// `((… (bottom, #z) …, #z), #z)`, `n` tuples deep, each built anew.
pub(super) fn tuples(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, _| Ty::tuple(vec![t, z()]))
}

#[test]
fn replacements_in_a_shared_type_make_each_node_once() {
    // A small instance of the benchmark
    // `bench::deep_types::replacements_in_a_shared_type_take_linear_time`.
    for n in 0..9 {
        let made = replaced_each_way(&shared(n));
        let (tys, held) = made.split_at(5);
        assert!(tys.iter().all(|t| t.tuples.len() == 1), "{n} deep");
        assert_eq!(held[0].fns.len(), 1, "{n} deep");
    }
}

#[test]
fn types_built_apart_compare_by_their_contents() {
    let y = || Ty::set(Type::atom("y"));
    for n in 0..7 {
        assert_eq!(levels(n, z()), levels(n, z()), "{n} deep");
        assert_eq!(tuples(n, z()), tuples(n, z()), "{n} deep");
        assert_eq!(shared(n), shared(n), "{n} deep");
        if n > 0 {
            assert_ne!(levels(n, z()), levels(n, y()), "{n} deep");
            assert_ne!(tuples(n, z()), tuples(n, y()), "{n} deep");
            assert_ne!(levels(n, z()), levels(n - 1, z()), "{n} deep");
        }
    }
    // The field of a payload, a function's parameter and a second component differ.
    let in_field = |f: Ty| atom(vec![z()], f);
    assert_ne!(in_field(z()), in_field(y()));
    assert_ne!(func(z(), z()), func(y(), z()));
    assert_ne!(Ty::tuple(vec![z(), z()]), Ty::tuple(vec![z(), y()]));
    assert_ne!(Ty::tuple(vec![z()]), Ty::tuple(vec![z(), z()]));
}

#[test]
fn a_value_shared_on_one_side_and_built_twice_on_the_other_compares_each_copy() {
    // `(x, x)` against `(x1, x2)`: once `x` is found equal to `x1`, the comparison must still
    // read `x2`, which may differ from both at the bottom.
    let x = levels(30, z());
    let one = Ty::tuple(vec![x.clone(), x]);
    let same = Ty::tuple(vec![levels(30, z()), levels(30, z())]);
    let other = Ty::tuple(vec![levels(30, z()), levels(30, Ty::set(Type::atom("y")))]);
    assert_eq!(one, same);
    assert_eq!(same, one);
    assert_ne!(one, other);
    assert_ne!(other, one);
}

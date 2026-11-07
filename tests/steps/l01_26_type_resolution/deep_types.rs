//! Replacing variables in a type nested as deep as the program: [`Ty::subst`], [`Ty::replace`],
//! [`Ty::renamed`], [`Ty::replace_outside`], [`Ty::settle`] and [`Sig::settle`] keep their own
//! stack (TY-subst-stacks). Each recursed once a level through rows, payload shapes and
//! functions, and overflowed a 2 MiB stack a few thousand levels deep.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::types::Type;
use zed_tests::deep::on_small_stack;
use zed_tests::scaling;
use zedc::check::ty::{Binds, SParam, Shape, Sig, Ty};

/// The type `#z`, which the tests put in the place of a variable.
fn z() -> Ty {
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
fn chain(n: usize, leaf: &dyn Fn(&str, bool) -> Ty) -> Ty {
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
fn same(v: &str, _: bool) -> Ty {
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
fn replaced_each_way(t: &Ty) -> [Ty; 6] {
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
fn expected(n: usize) -> [Ty; 6] {
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
fn hashes(ts: &[Ty; 6]) -> [u64; 6] {
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

#[test]
fn replacements_in_a_type_100000_deep_run_on_a_2_mib_stack() {
    on_small_stack(|| {
        let n = 100_000;
        let t = chain(n, &same);
        assert_eq!(hashes(&replaced_each_way(&t)), hashes(&expected(n)));
    });
}

/// A type `n` levels deep in which each level holds the one below twice, so it has `2^n` paths
/// and `n` rows, shapes and functions, in a tuple: each replacement makes each once.
fn shared(n: usize) -> Ty {
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

#[test]
fn replacements_in_a_shared_type_take_linear_time_on_a_2_mib_stack() {
    // Each run builds its type: `Sig::settle` keeps what it made in the signature, so a second
    // run on one type would not settle it again.
    on_small_stack(|| {
        scaling::check_order("each replacement in a shared type n deep", 4000, 1, |n| {
            let made = replaced_each_way(&shared(n));
            let (tys, held) = made.split_at(5);
            assert!(tys.iter().all(|t| t.tuples.len() == 1), "{n} deep");
            assert_eq!(held[0].fns.len(), 1, "{n} deep");
        });
    });
}

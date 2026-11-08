//! Replacing variables in a type nested as deep as the program: [`Ty::subst`], [`Ty::replace`],
//! [`Ty::renamed`], [`Ty::replace_outside`], [`Ty::settle`] and [`Sig::settle`] keep their own
//! stack (TY-subst-stacks). Each recursed once a level through rows, payload shapes and
//! functions, and overflowed a 2 MiB stack a few thousand levels deep.
//!
//! Comparing two such types built apart, with `==`, keeps its own stack too (ROW-eq-deep).

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

/// A type `n` levels deep with `bottom` at the bottom, a tuple, an atom's payload and a
/// function's result in turn, each level built anew: two calls share no row, shape or
/// signature, so `==` cannot take the shortcut of one shared node.
fn levels(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, k| match k % 3 {
        0 => Ty::tuple(vec![t, z()]),
        1 => atom(vec![z(), t], z()),
        _ => func(z(), t),
    })
}

/// `((… (bottom, #z) …, #z), #z)`, `n` tuples deep, each built anew.
fn tuples(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, _| Ty::tuple(vec![t, z()]))
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

#[test]
fn types_built_apart_100000_deep_compare_on_a_2_mib_stack() {
    // `==` recursed once a level through rows, payload shapes and signatures, and overflowed
    // this stack a few thousand levels deep (ROW-eq-deep).
    let n = 100_000;
    let (a, b, c) = (
        levels(n, z()),
        levels(n, z()),
        levels(n, Ty::set(Type::atom("y"))),
    );
    on_small_stack(|| {
        assert!(a == b);
        assert!(a != c);
    });
}

#[test]
fn tuples_built_apart_200000_deep_compare_on_an_8_mib_stack() {
    // The recursive `==` overflowed this stack (ROW-eq-deep).
    let n = 200_000;
    let (a, b, c) = (
        tuples(n, z()),
        tuples(n, z()),
        tuples(n, Ty::set(Type::atom("y"))),
    );
    scaling::on_a_thread(8 << 20, || {
        assert!(a == b);
        assert!(a != c);
    });
}

#[test]
fn shared_types_built_apart_compare_in_linear_time() {
    // Each side holds `2^n` paths through `n` nodes, and no node is shared between the sides:
    // a comparison that followed the paths took `2^n` time.
    let n = 2000;
    let pairs: std::collections::BTreeMap<usize, (Ty, Ty)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|k| (k, (shared(k), shared(k))))
        .collect();
    on_small_stack(|| {
        scaling::check_order("== on two shared types n deep built apart", n, 1, |k| {
            let (a, b) = &pairs[&k];
            assert!(a == b, "{k} deep");
        });
    });
}

/// Whether `a` and `b` are equal, by a plain recursion over the public fields: what a derived
/// `==` does, with no shortcut for one shared node and no stack of its own.
fn plain(a: &Ty, b: &Ty) -> bool {
    let all = |x: &[Ty], y: &[Ty]| x.len() == y.len() && x.iter().zip(y).all(|(p, q)| plain(p, q));
    a.set == b.set
        && a.tuples.len() == b.tuples.len()
        && (a.tuples.iter().zip(&b.tuples)).all(|(x, y)| all(x, y))
        && a.fns.len() == b.fns.len()
        && (a.fns.iter().zip(&b.fns)).all(|(x, y)| {
            x.params == y.params
                && x.arrows.len() == y.arrows.len()
                && (x.arrows.iter().zip(&y.arrows))
                    .all(|(p, q)| all(&p.params, &q.params) && plain(&p.result, &q.result))
                && x.bounds == y.bounds
                && x.data == y.data
                && x.word == y.word
                && x.needs == y.needs
                && x.own == y.own
                && x.held == y.held
                && x.named == y.named
        })
        && a.vars == b.vars
        && a.dynamic == b.dynamic
        && a.family == b.family
        && a.payloads.len() == b.payloads.len()
        && (a.payloads.iter().zip(&b.payloads)).all(|((k, x), (l, y))| {
            k == l
                && match (x, y) {
                    (Some(x), Some(y)) => {
                        x.len() == y.len()
                            && x.iter().zip(y).all(|(p, q)| {
                                all(&p.items, &q.items)
                                    && p.fields.len() == q.fields.len()
                                    && (p.fields.iter().zip(&q.fields))
                                        .all(|((k, x), (l, y))| k == l && plain(x, y))
                            })
                    }
                    (None, None) => true,
                    _ => false,
                }
        })
}

#[test]
fn shallow_types_compare_as_cheaply_as_a_plain_recursion() {
    // `==` keeps a stack of its own for types nested as deep as the program, and records
    // shared nodes so a type with `2^n` paths through `n` nodes compares in linear time. Types
    // a few levels deep, nearly all the checker compares, must pay nothing for either: each
    // pair here, equal and unequal, built apart so no node is shared, costs `==` no more
    // instructions than `plain`.
    let y = || Ty::set(Type::atom("y"));
    let cases: Vec<(&str, Ty, Ty)> = vec![
        ("an atom", z(), z()),
        ("a variable", Ty::var("T".into()), Ty::var("T".into())),
        ("1 tuple deep", tuples(1, z()), tuples(1, z())),
        ("2 tuples deep", tuples(2, z()), tuples(2, z())),
        ("3 tuples deep", tuples(3, z()), tuples(3, z())),
        ("5 tuples deep", tuples(5, z()), tuples(5, z())),
        ("2 levels deep", levels(2, z()), levels(2, z())),
        ("3 levels deep", levels(3, z()), levels(3, z())),
        ("5 levels deep", levels(5, z()), levels(5, z())),
        ("3 tuples deep, unequal", tuples(3, z()), tuples(3, y())),
        ("5 levels deep, unequal", levels(5, z()), levels(5, y())),
        ("5 levels deep, replaced", chain(5, &same), chain(5, &same)),
    ];
    let mut meter = scaling::Meter::new();
    let unit = meter.unit();
    let reps = 1000;
    // The least of five runs of `reps` comparisons each, per comparison.
    let mut cost = |f: &dyn Fn() -> bool| {
        (0..5)
            .map(|_| {
                meter
                    .work(|| {
                        for _ in 0..reps {
                            std::hint::black_box(f());
                        }
                    })
                    .units
            })
            .min()
            .expect("five runs")
            / reps
    };
    for (name, a, b) in &cases {
        let (a, b) = (std::hint::black_box(a), std::hint::black_box(b));
        assert_eq!(a == b, plain(a, b), "{name}");
        let ours = cost(&|| a == b);
        let theirs = cost(&|| plain(a, b));
        eprintln!("{name}: == {ours}, plain {theirs} {unit}");
        // Processor time, where no counter of instructions is open, moves with the load.
        assert!(
            ours <= theirs || !unit.starts_with("instructions"),
            "{name}: == took {ours} {unit}, a plain recursion {theirs}"
        );
    }
}

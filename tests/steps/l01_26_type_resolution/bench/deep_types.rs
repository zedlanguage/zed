//! The time of replacing variables in, and comparing, types with `2^n` paths through `n` nodes;
//! the replacements and `==` on types [`DEEP`] levels deep, on a stack as small a level as
//! 2 MiB at 100,000 levels; and the cost of `==` on types a few levels deep against a plain
//! recursion. What each gives on types a few levels deep is checked in `deep_types`.

use zed_kernel::types::Type;
use zed_tests::deep::on_small_stack;
use zed_tests::scaling;
use zedc::check::ty::Ty;

use super::deep_ops::{DEEP, on_shallow_stack};
use super::super::deep_types::{
    chain, expected, hashes, levels, replaced_each_way, same, shared, tuples, z,
};

#[test]
fn replacements_in_a_shared_type_take_linear_time() {
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

#[test]
fn replacements_in_a_deep_type_run_on_a_shallow_stack() {
    // Each recursed once a level and overflowed a 2 MiB stack a few thousand levels deep; the
    // stack here is as small a level as 2 MiB at 100,000 levels.
    on_shallow_stack(|| {
        let n = DEEP;
        let t = chain(n, &same);
        assert_eq!(hashes(&replaced_each_way(&t)), hashes(&expected(n)));
    });
}

#[test]
fn types_built_apart_deep_compare_on_a_shallow_stack() {
    // `==` recursed once a level through rows, payload shapes and signatures, and overflowed a
    // 2 MiB stack a few thousand levels deep (ROW-eq-deep).
    let n = DEEP;
    let (a, b, c) = (
        levels(n, z()),
        levels(n, z()),
        levels(n, Ty::set(Type::atom("y"))),
    );
    on_shallow_stack(|| {
        assert!(a == b);
        assert!(a != c);
    });
}

#[test]
fn tuples_built_apart_deep_compare_on_a_shallow_stack() {
    // The recursive `==` overflowed an 8 MiB stack 200,000 deep, about 42 bytes a level
    // (ROW-eq-deep); the stack here is about 21 bytes a level.
    let n = DEEP;
    let (a, b, c) = (
        tuples(n, z()),
        tuples(n, z()),
        tuples(n, Ty::set(Type::atom("y"))),
    );
    on_shallow_stack(|| {
        assert!(a == b);
        assert!(a != c);
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

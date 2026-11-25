//! The time of replacing variables in, and comparing, types with `2^n` paths through `n` nodes;
//! the replacements and `==` on types [`DEEP`] levels deep, on a stack as small a level as
//! 2 MiB at 100,000 levels; and the cost of `==` on types a few levels deep against a plain
//! recursion. What each gives on types a few levels deep is checked in `deep_types`.

use zed_kernel::types::Type;
use zed_tests::deep::on_small_stack;
use zed_tests::scaling;
use zedc::check::ty::{Sig, Ty};

use super::super::deep_types::{
    chain, expected, hashes, levels, replaced_each_way, same, shared, tuples, z,
};
use super::deep_ops::{DEEP, on_shallow_stack};

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

/// Besides its ratio: shared types built apart are equal. Small instance:
/// `deep_types::types_built_apart_compare_by_their_contents`.
#[test]
fn shared_types_built_apart_compare_in_linear_time() {
    // Each side holds `2^n` paths through `n` nodes, and no node is shared between the sides:
    // a comparison that followed the paths took `2^n` time.
    // Each pair is built only in the process that compares it (`scaling::check_inputs`;
    // FAIL-bench-first-phase-past-20s-l0126-l0129), on the 2 MiB stack of `on_small_stack`,
    // the default of the test thread they were built and dropped on before.
    let n = 32_000;
    on_small_stack(|| {
        scaling::check_inputs(
            "== on two shared types n deep built apart",
            n,
            |k| (k, shared(k), shared(k)),
            |(k, a, b)| {
                assert!(a == b, "{k} deep");
            },
        );
    });
}

/// Besides running on a shallow stack: each replacement equals the type built with it, hashes
/// alike. Small instance: `deep_types::replacements_in_a_shallow_type_are_as_built`.
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

/// Besides running on a shallow stack: types built apart are equal, and unequal where they
/// differ. Small instance: `deep_types::types_built_apart_compare_by_their_contents`.
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

/// Besides running on a shallow stack: tuples built apart are equal, and unequal where they
/// differ. Small instance: `deep_types::types_built_apart_compare_by_their_contents`.
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
            // Every field of the signature, in the order they are declared, as the derived
            // `==` takes them; the pattern names each, so a field added to `Sig` stops this
            // from compiling until it is compared here too. `facts` is a cache, not part of
            // the value. Before (FAIL-shallow-eq-three-levels), `dense` and `hull` were left
            // out, so once `==` compared `hull` (RANGE-result-hull) it did more than this.
            let Sig {
                params,
                arrows,
                bounds,
                data,
                dense,
                keys,
                word,
                needs,
                own,
                held,
                named,
                hull,
                facts: _,
            } = &**x;
            *params == y.params
                && arrows.len() == y.arrows.len()
                && (arrows.iter().zip(&y.arrows)).all(|(p, q)| {
                    all(&p.params, &q.params)
                        && plain(&p.result, &q.result)
                        && p.partial == q.partial
                        && p.stores_not_found == q.stores_not_found
                })
                && *bounds == y.bounds
                && *data == y.data
                && *dense == y.dense
                && *keys == y.keys
                && *word == y.word
                && *needs == y.needs
                && *own == y.own
                && *held == y.held
                && *named == y.named
                && *hull == y.hull
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

/// Besides its cost: `==` agrees with a plain recursion on each case, equal and unequal. Small
/// instance of each verdict: `deep_types::types_built_apart_compare_by_their_contents`.
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

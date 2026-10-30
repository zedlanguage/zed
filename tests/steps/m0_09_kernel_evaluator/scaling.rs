//! The evaluator's values at the rule of low complexity (DESIGN.md Part G). A family is
//! shared, not copied, when a variable, a literal or a lookup yields it, so reading a family
//! of `n` entries once per entry costs `O(n log n)`, not `O(n²)`. A union shares the larger
//! family's entries, so a `foldl` that adds one entry per step costs `O(n log n)` too. The
//! names in scope sit in a persistent map, so a name read past `n` later bindings costs
//! `O(log n)`, not `O(n)`.

use std::cmp::Ordering;
use zed_kernel::term::build::{app, lam, lit, prim, var};

use zed_kernel::{Evaluator, Family, KernelError, Prim, Term, Value, World};
use zed_tests::instances::Rng;
use zed_tests::kernel::*;
use zed_tests::scaling;

/// The keys `0..n`, each mapped to itself.
fn keys(n: usize) -> Value {
    Value::Family(Family::set(0..n as i64))
}

fn run(t: &Term) -> Value {
    Evaluator::new(World::new()).run(t).unwrap()
}

/// `fam(F, k -> F[k])`, reading the family `F` once per key: through a literal, or through a
/// variable bound to it, or through a family nested in a tuple.
fn reads(n: usize, how: usize) -> Term {
    let f = lit(keys(n));
    match how {
        0 => fam_with(f.clone(), |k| get(f, k)),
        1 => app(
            lam(&["f"], fam_with(var("f"), |k| get(var("f"), k))),
            vec![f],
        ),
        _ => {
            let t = prim(Prim::Tuple, vec![f, lit(1)]);
            app(
                lam(
                    &["t"],
                    fam_with(nth(var("t"), 0), |k| get(nth(var("t"), 0), k)),
                ),
                vec![t],
            )
        }
    }
}

#[test]
fn reading_a_family_once_per_entry_scales() {
    for (how, what) in ["a literal", "a variable", "a tuple"]
        .into_iter()
        .enumerate()
    {
        scaling::check(
            &format!("reading {what} once per entry, by entries"),
            2000,
            |n| {
                run(&reads(n, how));
            },
        );
    }
}

#[test]
fn each_read_yields_the_family() {
    for how in 0..3 {
        assert_eq!(run(&reads(100, how)), keys(100), "read {how}");
    }
}

/// `xs.foldl({}, (acc, x) -> acc ∪ {x -> x})` over the keys `0..n`.
fn accumulate(n: usize) -> Term {
    let one = reindex(
        lit(keys(1)),
        lam(&["p", "w"], path(vec![var("x")])),
        lam(&["p", "w"], var("x")),
    );
    let op = lam(&["acc", "x"], prim(Prim::Union, vec![var("acc"), one]));
    foldl(lit(keys(n)), lit(Value::Family(Family::new())), op)
}

#[test]
fn a_union_adding_one_entry_per_step_scales() {
    // Each union rebuilt both families from their leaves, and the family of the `n`
    // accumulators was built from all `n²/2` of their leaves: 75 s at 8,000 steps.
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            scaling::check("a foldl of unions, by steps", 1000, |n| {
                run(&accumulate(n));
            });
        })
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(run(&accumulate(50)), keys(50));
}

/// The union as the leaves of `a` and then those of `b`, a leaf of `b` that `a` already has
/// at its keypath left out: the definition the persistent union must agree with.
fn union_by_leaves(a: &Family, b: &Family) -> Result<Family, KernelError> {
    let mut leaves = a.leaves();
    for (path, v) in b.leaves() {
        if !leaves.iter().any(|(p, w)| *p == path && *w == v) {
            leaves.push((path, v));
        }
    }
    Family::from_leaves(leaves)
}

/// A random family of up to three levels over the keys `0..3` and the leaves `0..2`, so that
/// two of them often share keypaths, sometimes with the same leaf.
fn random_family(rng: &mut Rng, depth: usize) -> Family {
    let leaves = (0..rng.below(4)).map(|_| {
        let len = 1 + rng.below(depth);
        let path: Vec<Value> = (0..len).map(|_| Value::Int(rng.int(0, 2))).collect();
        (path, Value::Int(rng.int(0, 1)))
    });
    let leaves: Vec<_> = leaves.collect();
    (0..=leaves.len())
        .rev()
        .find_map(|n| Family::from_leaves(leaves[..n].to_vec()).ok())
        .expect("no leaves build the empty family")
}

#[test]
fn the_union_agrees_with_the_union_of_the_leaves() {
    let mut rng = Rng::new(17);
    let (mut collisions, mut overlaps) = (0, 0);
    for _ in 0..20_000 {
        let (a, b) = (random_family(&mut rng, 3), random_family(&mut rng, 3));
        let want = union_by_leaves(&a, &b);
        assert_eq!(a.union(&b), want, "{a} ∪ {b}");
        collisions += want.is_err() as usize;
        overlaps += (want.is_ok() && a.keys().any(|k| b.get(k).is_some())) as usize;
    }
    assert!(
        collisions > 2000 && overlaps > 2000,
        "{collisions} collisions, {overlaps} overlaps"
    );
}

#[test]
fn families_are_ordered_by_their_entries() {
    // A family of families is ordered by its keys, so the order of two families must stay
    // the order of their entries in key order.
    let mut rng = Rng::new(5);
    let mut both = [0; 3];
    for _ in 0..20_000 {
        let (a, b) = (random_family(&mut rng, 2), random_family(&mut rng, 2));
        let want = a.iter().cmp(b.iter());
        assert_eq!(a.cmp(&b), want, "{a} against {b}");
        both[(want as i8 + 1) as usize] += 1;
    }
    assert!(both.iter().all(|&n| n > 1000), "{both:?}");
    let _ = Ordering::Less;
}

#[test]
fn a_family_built_with_families_as_leaves_agrees_with_its_leaves() {
    // A family given as a leaf is kept whole where nothing else is written beneath its
    // keypath; the result, and the first collision, are those of its leaves given one by one.
    let mut rng = Rng::new(29);
    let (mut built, mut collisions) = (0, 0);
    for _ in 0..20_000 {
        let parts: Vec<(Vec<Value>, Value)> = (0..1 + rng.below(3))
            .map(|_| {
                let path = (0..1 + rng.below(2))
                    .map(|_| Value::Int(rng.int(0, 2)))
                    .collect();
                let v = match rng.below(3) {
                    0 => Value::Int(rng.int(0, 1)),
                    _ => Value::Family(random_family(&mut rng, 2)),
                };
                (path, v)
            })
            .collect();
        let flat = parts.iter().flat_map(|(p, v)| match v {
            Value::Family(f) => f
                .leaves()
                .into_iter()
                .map(|(q, w)| ([p.clone(), q].concat(), w))
                .collect(),
            v => vec![(p.clone(), v.clone())],
        });
        let want = Family::from_leaves(flat.collect::<Vec<_>>());
        assert_eq!(Family::from_leaves(parts.clone()), want, "{parts:?}");
        built += want.is_ok() as usize;
        collisions += want.is_err() as usize;
    }
    assert!(
        built > 2000 && collisions > 2000,
        "{built} built, {collisions} collisions"
    );
}

/// `let x0 = 0 in let x1 = x0 + 1 in … let x(n) = x0 + n in x0 + x(n)`: each `let` reads the
/// first name past all the names bound after it.
fn lets(n: usize) -> Term {
    let mut body = add(var("x0"), var(&format!("x{n}")));
    for i in (1..=n).rev() {
        let e = add(var("x0"), lit(Value::Int(i as i64)));
        body = Term::Let(format!("x{i}").into(), rc(e), rc(body));
    }
    Term::Let("x0".into(), rc(lit(Value::Int(0))), rc(body))
}

#[test]
fn a_name_read_past_many_bindings_scales() {
    // Each lookup walked the frames from the innermost binding out: a chain of `n` lets cost
    // `n²/2` comparisons of names.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            scaling::check(
                "a chain of lets reading the first name, by lets",
                2000,
                |n| {
                    assert_eq!(run(&lets(n)), Value::Int(n as i64));
                },
            )
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn an_inner_binding_hides_an_outer_one_within_its_scope_only() {
    let int = |i: i64| lit(Value::Int(i));
    let let_ = |x: &str, e: Term, body: Term| Term::Let(x.into(), rc(e), rc(body));
    // `let x = 1 in (let x = 2 in x) * 10 + x` is 21.
    let scoped = let_(
        "x",
        int(1),
        add(mul(let_("x", int(2), var("x")), int(10)), var("x")),
    );
    assert_eq!(run(&scoped), Value::Int(21));
    // `let x = 1 in let f = y -> x + y in let x = 10 in f(0) * 100 + x` is 110: the closure
    // keeps the `x` it captured.
    let captured = let_(
        "x",
        int(1),
        let_(
            "f",
            lam(&["y"], add(var("x"), var("y"))),
            let_(
                "x",
                int(10),
                add(mul(app(var("f"), vec![int(0)]), int(100)), var("x")),
            ),
        ),
    );
    assert_eq!(run(&captured), Value::Int(110));
    // A parameter hides the name it shares: `let x = 1 in (x -> x)(5) + x` is 6.
    let param = let_(
        "x",
        int(1),
        add(app(lam(&["x"], var("x")), vec![int(5)]), var("x")),
    );
    assert_eq!(run(&param), Value::Int(6));
}

/// `discard(F, (p, w) -> true)`, keeping every entry of `F`.
fn keep_all(f: Family) -> Term {
    discard(
        lit(Value::Family(f)),
        lam(&["p", "w"], lit(Value::Bool(true))),
    )
}

#[test]
fn a_discard_scales_with_its_entries_and_the_keypaths_it_gives() {
    // Each level of a discard was rebuilt from the leaves of the levels below it: a family of
    // depth `d` cost `O(L·d²)`. Now a level keeps each kept family whole. A discard gives
    // the selector the keypath of each entry, so a chain of depth `d` with a leaf beside each
    // level gives keypaths of lengths 1 to `d`, `d²` keys in all: work of order `d²`, which
    // it is allowed. Rebuilding each level from its leaves cost `d³/3`.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            let wide = |n: usize| {
                let leaves = (0..n as i64).flat_map(|i| {
                    (0..2).map(move |j| (vec![Value::Int(i), Value::Int(j)], Value::Int(i + j)))
                });
                Family::from_leaves(leaves).unwrap()
            };
            scaling::check("a discard of n pairs, by n", 2000, |n| {
                let f = wide(n);
                assert_eq!(run(&keep_all(f.clone())), Value::Family(f));
            });
            // The leaf `i` at the keypath of `i` zeros and then a one.
            let caterpillar = |d: usize| {
                let leaves = (0..d).map(|i| {
                    let mut path = vec![Value::Int(0); i];
                    path.push(Value::Int(1));
                    (path, Value::Int(i as i64))
                });
                Family::from_leaves(leaves).unwrap()
            };
            scaling::check_order("a discard of a caterpillar, by depth", 200, 2, |d| {
                let f = caterpillar(d);
                assert_eq!(run(&keep_all(f.clone())), Value::Family(f));
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

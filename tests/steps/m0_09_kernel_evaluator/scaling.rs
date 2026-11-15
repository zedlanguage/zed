//! The evaluator's values at the rule of low complexity (DESIGN.md Part G). A family is
//! shared, not copied, when a variable, a literal or a lookup yields it, so reading a family
//! of `n` entries once per entry costs `O(n log n)`, not `O(n²)`. A union shares the larger
//! family's entries, so a `foldl` that adds one entry per step costs `O(n log n)` too. The
//! names in scope sit in a persistent map, so a name read past `n` later bindings costs
//! `O(log n)`, not `O(n)`. The benchmarks that time these are in `bench/scaling.rs`; their
//! inputs are built here, and each is checked here at small sizes (TEST-bench-move-rest, P170).

use std::cmp::Ordering;
use zed_kernel::term::build::{app, lam, lit, prim, var};

use zed_kernel::{Evaluator, Family, KernelError, Prim, Term, Value, World};
use zed_tests::instances::Rng;
use zed_tests::kernel::*;

/// The keys `0..n`, each mapped to itself.
pub(super) fn keys(n: usize) -> Value {
    Value::Family(Family::set(0..n as i64))
}

pub(super) fn run(t: &Term) -> Value {
    Evaluator::new(World::new()).run(t).unwrap()
}

/// `fam(F, k -> F[k])`, reading the family `F` once per key: through a literal, or through a
/// variable bound to it, or through a family nested in a tuple.
pub(super) fn reads(n: usize, how: usize) -> Term {
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
fn each_read_yields_the_family() {
    for how in 0..3 {
        assert_eq!(run(&reads(100, how)), keys(100), "read {how}");
    }
}

/// `xs.foldl({}, (acc, x) -> acc ∪ {x -> x})` over the keys `0..n`.
pub(super) fn accumulate(n: usize) -> Term {
    let one = reindex(
        lit(keys(1)),
        lam(&["p", "w"], path(vec![var("x")])),
        lam(&["p", "w"], var("x")),
    );
    let op = lam(&["acc", "x"], prim(Prim::Union, vec![var("acc"), one]));
    foldl(lit(keys(n)), lit(Value::Family(Family::new())), op)
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

/// The family of `leaves`, each a keypath of integers and an integer leaf.
fn family(leaves: &[(&[i64], i64)]) -> Family {
    Family::from_leaves(int_leaves(leaves)).unwrap()
}

fn int_leaves(leaves: &[(&[i64], i64)]) -> Vec<(Vec<Value>, Value)> {
    leaves
        .iter()
        .map(|(p, v)| (p.iter().map(|&k| Value::Int(k)).collect(), Value::Int(*v)))
        .collect()
}

#[test]
fn the_union_agrees_with_the_union_of_the_leaves() {
    let mut rng = Rng::new(zed_tests::seed::seed(
        "the_union_agrees_with_the_union_of_the_leaves",
    ));
    for _ in 0..2_000 {
        union_agrees(&random_family(&mut rng, 3), &random_family(&mut rng, 3));
    }
    // Pairs built for each kind. `{0 -> 0}` and `{0 -> 1}` give two leaves at one keypath, a
    // collision; `{0 -> 0}` and `{0 -> 0, 1 -> 1}` share the key 0 with the same leaf, an
    // overlap the union keeps once.
    let zero = family(&[(&[0], 0)]);
    assert_eq!(
        union_agrees(&zero, &family(&[(&[0], 1)])),
        (true, false),
        "collision"
    );
    assert_eq!(
        union_agrees(&zero, &family(&[(&[0], 0), (&[1], 1)])),
        (false, true),
        "overlap"
    );
}

/// Asserts that `a ∪ b` is the union of their leaves; returns whether that is a collision, and
/// whether it is a union of families sharing a key.
fn union_agrees(a: &Family, b: &Family) -> (bool, bool) {
    let want = union_by_leaves(a, b);
    assert_eq!(a.union(b), want, "{a} ∪ {b}");
    (
        want.is_err(),
        want.is_ok() && a.keys().any(|k| b.get(k).is_some()),
    )
}

#[test]
fn families_are_ordered_by_their_entries() {
    // A family of families is ordered by its keys, so the order of two families must stay
    // the order of their entries in key order.
    let mut rng = Rng::new(zed_tests::seed::seed(
        "families_are_ordered_by_their_entries",
    ));
    for _ in 0..2_000 {
        ordered_by_entries(&random_family(&mut rng, 2), &random_family(&mut rng, 2));
    }
    // Pairs built for each order: `{0 -> 0}` before `{0 -> 1}`, since their first entries share
    // the key 0 and 0 < 1; after, the other way round; and equal to itself.
    let (a, b) = (family(&[(&[0], 0)]), family(&[(&[0], 1)]));
    assert_eq!(ordered_by_entries(&a, &b), Ordering::Less);
    assert_eq!(ordered_by_entries(&a, &a), Ordering::Equal);
    assert_eq!(ordered_by_entries(&b, &a), Ordering::Greater);
}

/// Asserts that `a` and `b` are ordered as their entries in key order are; returns the order.
fn ordered_by_entries(a: &Family, b: &Family) -> Ordering {
    let want = a.iter().cmp(b.iter());
    assert_eq!(a.cmp(b), want, "{a} against {b}");
    want
}

#[test]
fn a_family_built_with_families_as_leaves_agrees_with_its_leaves() {
    // A family given as a leaf is kept whole where nothing else is written beneath its
    // keypath; the result, and the first collision, are those of its leaves given one by one.
    let mut rng = Rng::new(zed_tests::seed::seed(
        "a_family_built_with_families_as_leaves_agrees_with_its_leaves",
    ));
    for _ in 0..2_000 {
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
        builds_as_its_leaves(parts);
    }
    // Parts built for each outcome. The family `{1 -> 0}` given at the keypath 0 is the leaf
    // 0 at the keypath (0, 1), which builds; a leaf 1 at (0, 1) besides it is a second leaf
    // at one keypath, a collision.
    let inner = Value::Family(family(&[(&[1], 0)]));
    let built = vec![(vec![Value::Int(0)], inner)];
    assert!(builds_as_its_leaves(built.clone()), "built");
    let collides = [built, int_leaves(&[(&[0, 1], 1)])].concat();
    assert!(!builds_as_its_leaves(collides), "collision");
}

/// Asserts that the family built from `parts` is the one built from their leaves, each family
/// given as a leaf flattened beneath its keypath; returns whether it builds.
fn builds_as_its_leaves(parts: Vec<(Vec<Value>, Value)>) -> bool {
    // An empty family given as a leaf is an empty level beneath its keypath, which is a
    // leaf of its own.
    let flat = parts.iter().flat_map(|(p, v)| match v {
        Value::Family(f) if !f.is_empty() => f
            .leaves()
            .into_iter()
            .map(|(q, w)| ([p.clone(), q].concat(), w))
            .collect(),
        v => vec![(p.clone(), v.clone())],
    });
    let want = Family::from_leaves(flat.collect::<Vec<_>>());
    assert_eq!(Family::from_leaves(parts.clone()), want, "{parts:?}");
    want.is_ok()
}

/// `let x0 = 0 in let x1 = x0 + 1 in … let x(n) = x0 + n in x0 + x(n)`: each `let` reads the
/// first name past all the names bound after it.
pub(super) fn lets(n: usize) -> Term {
    let mut body = add(var("x0"), var(&format!("x{n}")));
    for i in (1..=n).rev() {
        let e = add(var("x0"), lit(Value::Int(i as i64)));
        body = Term::Let(format!("x{i}").into(), rc(e), rc(body));
    }
    Term::Let("x0".into(), rc(lit(Value::Int(0))), rc(body))
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
pub(super) fn keep_all(f: Family) -> Term {
    discard(
        lit(Value::Family(f)),
        lam(&["p", "w"], lit(Value::Bool(true))),
    )
}

/// `n` keys, each with the leaves `(i, 0) -> i` and `(i, 1) -> i + 1`.
pub(super) fn wide(n: usize) -> Family {
    let leaves = (0..n as i64)
        .flat_map(|i| (0..2).map(move |j| (vec![Value::Int(i), Value::Int(j)], Value::Int(i + j))));
    Family::from_leaves(leaves).unwrap()
}

/// The leaf `i` at the keypath of `i` zeros and then a one, for each `i` below `d`.
pub(super) fn caterpillar(d: usize) -> Family {
    let leaves = (0..d).map(|i| {
        let mut path = vec![Value::Int(0); i];
        path.push(Value::Int(1));
        (path, Value::Int(i as i64))
    });
    Family::from_leaves(leaves).unwrap()
}

/// A discard that keeps every entry gives back the family it was given.
pub(super) fn keeps_all(f: Family) {
    assert_eq!(run(&keep_all(f.clone())), Value::Family(f));
}

/// What each benchmark of `bench/scaling.rs` asserts besides its ratio, at small sizes: a
/// `foldl` of unions gives the keys, a chain of lets reads its first name, and a discard keeps
/// each wide family and each caterpillar whole. Reading a family once per entry is checked by
/// `each_read_yields_the_family`.
#[test]
fn unions_lets_and_discards_give_their_values_at_small_sizes() {
    for n in [1, 2, 9] {
        assert_eq!(run(&accumulate(n)), keys(n));
        assert_eq!(run(&lets(n)), Value::Int(n as i64));
        keeps_all(wide(n));
        keeps_all(caterpillar(n));
    }
    assert_eq!(run(&accumulate(50)), keys(50));
}

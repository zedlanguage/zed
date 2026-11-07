//! Tuple parts whose tuple types are each open on one component, with cells that share no value
//! (item EMPTY-overlap-chain): a tuple of the box picks one cell or none on each component, and
//! the part is decided in one pass over its nodes (`Searching::one_pass`): decision lists and
//! exclusive ors exactly, `!`, `|`, and `&` of operands open on no component in common. The
//! answers are compared with an enumeration of the tuples on random parts, and the families of
//! exclusive ors and chains of overlapping tuple types are decided in time linear in them. An
//! `&` whose operands share a component through different cells, such as the comparison
//! `x & !y` of two such parts, is left to the split into tuple types, of quadratic cost, which
//! the last tests record (COMPLEXITY.md K71, question A46).

use zed_kernel::Value;
use zed_kernel::types::{Type, Verdict};
use zed_tests::instances::Rng;
use zed_tests::scaling;

fn lit(i: usize) -> Type {
    Type::lit(&Value::Int(i as i64)).expect("an integer literal")
}

/// The tuple type of `width` components with the literal `v` at component `j` and `top`
/// elsewhere.
fn row(width: usize, j: usize, v: usize) -> Type {
    let mut c = vec![Type::top(); width];
    c[j] = lit(v);
    Type::tuple(c)
}

/// A part over tuple types `row(width, j, v)`, as built and as an enumeration reads it.
#[derive(Clone, Debug)]
enum F {
    Row(usize, usize),
    Not(Box<F>),
    Or(Box<F>, Box<F>),
    And(Box<F>, Box<F>),
    /// The exclusive or of the rows.
    Xor(Vec<(usize, usize)>),
    /// The rows joined in turn to the empty type, each by `|` when `true` and by `-` when not.
    Chain(Vec<(usize, usize, bool)>),
}

impl F {
    fn ty(&self, width: usize) -> Type {
        let all = Type::tuple(vec![Type::top(); width]);
        match self {
            F::Row(j, v) => row(width, *j, *v),
            F::Not(x) => &all - &x.ty(width),
            F::Or(x, y) => &x.ty(width) | &y.ty(width),
            F::And(x, y) => &x.ty(width) & &y.ty(width),
            F::Xor(rows) => rows.iter().fold(Type::empty(), |x, &(j, v)| {
                let t = row(width, j, v);
                &(&x - &t) | &(&t - &x)
            }),
            F::Chain(rows) => rows.iter().fold(Type::empty(), |x, &(j, v, or)| {
                let t = row(width, j, v);
                if or { &x | &t } else { &x - &t }
            }),
        }
    }

    fn holds(&self, p: &[usize]) -> bool {
        match self {
            F::Row(j, v) => p[*j] == *v,
            F::Not(x) => !x.holds(p),
            F::Or(x, y) => x.holds(p) || y.holds(p),
            F::And(x, y) => x.holds(p) && y.holds(p),
            F::Xor(rows) => rows.iter().filter(|&&(j, v)| p[j] == v).count() % 2 == 1,
            F::Chain(rows) => {
                rows.iter().fold(
                    false,
                    |x, &(j, v, or)| if or { x || p[j] == v } else { x && p[j] != v },
                )
            }
        }
    }
}

/// The literals a component's cells are made of, and the one value outside them all.
const VALUES: usize = 4;
const OUTSIDE: usize = 99;

/// A random part on the components `on` (at least one), of depth at most `depth`. An `&` takes
/// operands on two halves of `on`, so the part is one the pass decides, unless `shared`, when
/// one `&` in four takes both operands on all of `on`.
fn random(g: &mut Rng, on: &[usize], depth: usize, shared: bool) -> F {
    let atom = |g: &mut Rng| (on[g.below(on.len())], g.below(VALUES));
    let k = if depth == 0 { g.below(3) } else { g.below(7) };
    match k {
        0 => {
            let (j, v) = atom(g);
            F::Row(j, v)
        }
        1 => F::Xor((0..1 + g.below(5)).map(|_| atom(g)).collect()),
        2 => F::Chain(
            (0..1 + g.below(6))
                .map(|_| {
                    let (j, v) = atom(g);
                    (j, v, g.below(2) == 0)
                })
                .collect(),
        ),
        3 => F::Not(Box::new(random(g, on, depth - 1, shared))),
        4 => F::Or(
            Box::new(random(g, on, depth - 1, shared)),
            Box::new(random(g, on, depth - 1, shared)),
        ),
        _ => {
            if on.len() < 2 || (shared && g.below(4) == 0) {
                return F::And(
                    Box::new(random(g, on, depth - 1, shared)),
                    Box::new(random(g, on, depth - 1, shared)),
                );
            }
            let cut = 1 + g.below(on.len() - 1);
            F::And(
                Box::new(random(g, &on[..cut], depth - 1, shared)),
                Box::new(random(g, &on[cut..], depth - 1, shared)),
            )
        }
    }
}

/// Whether a tuple of the box is in `f`, each component of the box its values among the
/// literals and the value outside them.
fn by_enumeration(f: &F, boxed: &[Vec<usize>]) -> bool {
    let mut p = vec![0; boxed.len()];
    let mut at = vec![0; boxed.len()];
    loop {
        for (j, &i) in at.iter().enumerate() {
            p[j] = boxed[j][i];
        }
        if f.holds(&p) {
            return true;
        }
        let Some(j) = (0..boxed.len()).find(|&j| at[j] + 1 < boxed[j].len()) else {
            return false;
        };
        at[j] += 1;
        at[..j].fill(0);
    }
}

/// A random box: each component `top`, or the union of a nonempty set of the literals, which
/// leaves it no value outside the cells.
fn random_box(g: &mut Rng, width: usize) -> (Type, Vec<Vec<usize>>) {
    let mut types = Vec::new();
    let mut values = Vec::new();
    for _ in 0..width {
        if g.below(3) == 0 {
            let mut vs: Vec<usize> = (0..VALUES).filter(|_| g.below(2) == 0).collect();
            if vs.is_empty() {
                vs.push(g.below(VALUES));
            }
            types.push(Type::union_all(vs.iter().map(|&v| lit(v))));
            values.push(vs);
        } else {
            types.push(Type::top());
            values.push((0..VALUES).chain([OUTSIDE]).collect());
        }
    }
    (Type::tuple(types), values)
}

/// Decides `f` on a random box against the enumeration, cold, by `verdict` and `is_empty`.
fn decide(g: &mut Rng, width: usize, f: &F, answers: &mut [usize; 2]) {
    let (b, boxed) = random_box(g, width);
    let t = &b & &f.ty(width);
    let inhabited = by_enumeration(f, &boxed);
    let expected = if inhabited {
        Verdict::Inhabited
    } else {
        Verdict::Empty
    };
    Type::forget_emptiness();
    assert_eq!(t.verdict(), expected, "{f:?} on {boxed:?}");
    Type::forget_emptiness();
    assert_eq!(t.is_empty(), !inhabited, "{f:?} on {boxed:?}");
    answers[usize::from(inhabited)] += 1;
}

/// Random parts the pass decides, on two to four components, each decided as enumeration
/// decides it; both answers are met.
#[test]
fn random_parts_of_one_choice_per_component_are_decided_as_enumeration_decides_them() {
    zed_tests::deep::on_small_stack(|| {
        let mut g = Rng::new(71);
        let mut answers = [0; 2];
        for width in 2..=4 {
            let on: Vec<usize> = (0..width).collect();
            for _ in 0..150 {
                let f = random(&mut g, &on, 3, false);
                decide(&mut g, width, &f, &mut answers);
            }
        }
        assert!(answers[0] >= 40 && answers[1] >= 40, "{answers:?}");
    });
}

/// Random parts with some `&` of operands on shared components, which the pass leaves to the
/// search: the answers are the same.
#[test]
fn random_parts_the_pass_leaves_to_the_search_are_decided_as_enumeration_decides_them() {
    zed_tests::deep::on_small_stack(|| {
        let mut g = Rng::new(72);
        let mut answers = [0; 2];
        for width in 2..=3 {
            let on: Vec<usize> = (0..width).collect();
            for _ in 0..150 {
                let f = random(&mut g, &on, 3, true);
                decide(&mut g, width, &f, &mut answers);
            }
        }
        assert!(answers[0] >= 20 && answers[1] >= 20, "{answers:?}");
    });
}

/// The corners of the pass: a component with no value outside its cells, where a parity of
/// one cell per component is fixed; a decision list that refuses every cell of such a
/// component; two tuple types with one cell, which an exclusive or of the two takes out; and a
/// list that takes two cells of one component.
#[test]
fn the_corners_of_one_choice_per_component_are_decided() {
    let (a, b) = (&lit(1) | &lit(2), &lit(3) | &lit(4));
    let boxed = Type::tuple(vec![a.clone(), b.clone()]);
    let x = F::Xor(vec![(0, 1), (0, 2), (1, 3), (1, 4)]).ty(2);
    assert_eq!((&boxed & &x).verdict(), Verdict::Empty);
    assert_eq!((&boxed - &x).verdict(), Verdict::Inhabited);
    let three = F::Xor(vec![(0, 1), (0, 2), (1, 3)]).ty(2);
    assert_eq!((&boxed & &three).verdict(), Verdict::Inhabited);
    assert_eq!((&boxed - &three).verdict(), Verdict::Inhabited);

    // `(1, _) | (2, _)` holds the box, so a list that refuses both cells of component 0 after
    // taking a cell of component 1 has no tuple in it, and one that refuses one cell has one.
    let refused = F::Chain(vec![(1, 3, true), (0, 1, false), (0, 2, false)]).ty(2);
    assert_eq!((&boxed & &refused).verdict(), Verdict::Empty);
    let one = F::Chain(vec![(1, 3, true), (1, 4, true), (0, 1, false)]).ty(2);
    assert_eq!((&boxed & &one).verdict(), Verdict::Inhabited);

    // `(1, _)` and `(1, int)` have one cell on the box `(_, int)`: their exclusive or is empty
    // there, and with `(_, 3)` it is `(_, 3)`.
    let ints = Type::tuple(vec![Type::top(), Type::int()]);
    let (r1, r2) = (row(2, 0, 1), Type::tuple(vec![lit(1), Type::int()]));
    let same = &(&r1 - &r2) | &(&r2 - &r1);
    assert_eq!((&ints & &same).verdict(), Verdict::Empty);
    let r3 = row(2, 1, 3);
    let odd = &(&same - &r3) | &(&r3 - &same);
    assert_eq!((&(&ints & &odd) - &r3).verdict(), Verdict::Empty);
    assert_eq!((&ints & &odd).verdict(), Verdict::Inhabited);

    // A list that takes `(1, _)` and then `(2, _)` on one tuple has no tuple.
    let both = &row(2, 0, 1) & &row(2, 0, 2);
    assert_eq!((&both | &(&boxed & &refused)).verdict(), Verdict::Empty);
}

/// The exclusive or of `c` tuple types `(1000 + i, _)` for even `i` and `(_, 1000 + i)` for odd
/// `i`, built in turn, or in reverse when `reverse`.
fn parity(c: usize, reverse: bool) -> F {
    let mut rows: Vec<(usize, usize)> = (0..c).map(|i| (i % 2, 1000 + i)).collect();
    if reverse {
        rows.reverse();
    }
    F::Xor(rows)
}

/// The chain of the same tuple types, joined by `|` and `-` in turn.
fn chain(c: usize) -> F {
    F::Chain((0..c).map(|i| (i % 2, 1000 + i, i % 2 == 0)).collect())
}

/// The box whose components are the literals of the even and of the odd tuple types of
/// [`parity`], so a tuple of it is in exactly one tuple type on each component.
fn tight(c: usize) -> Type {
    let side = |o: usize| Type::union_all((0..c).filter(|i| i % 2 == o).map(|i| lit(1000 + i)));
    Type::tuple(vec![side(0), side(1)])
}

/// The families of the item at `c` tuple types, built before the runs: the box `tight(c)` met
/// with the exclusive or (empty) and less it (inhabited), the complement of the chain, and the
/// union of the exclusive or with the complement of the chain.
fn families(c: usize) -> Vec<(Type, Verdict)> {
    let all = Type::tuple(vec![Type::top(), Type::top()]);
    let (x, l) = (parity(c, false).ty(2), chain(c).ty(2));
    let b = tight(c);
    vec![
        (&b & &x, Verdict::Empty),
        (&b - &x, Verdict::Inhabited),
        (&all - &l, Verdict::Inhabited),
        (&b - &l, Verdict::Inhabited),
        (&x | &(&all - &l), Verdict::Inhabited),
    ]
}

/// Each family of [`families`] is decided by `is_empty` and `verdict` in time linear in the
/// tuple types, 32 against 256. Before the pass, `is_empty` on `tight(c) - x` took 298M and
/// 5,513M instructions at 32 and 128 tuple types (order `c²`).
#[test]
fn exclusive_ors_and_chains_of_overlapping_tuple_types_are_decided_in_one_pass() {
    let types = scaling::inputs(32, families);
    scaling::check(
        "one pass over exclusive ors and chains, by tuple types",
        32,
        |c| {
            for (t, expected) in &types[&c] {
                Type::forget_emptiness();
                assert_eq!(t.is_empty(), *expected == Verdict::Empty, "{c}");
                Type::forget_emptiness();
                assert_eq!(t.verdict(), *expected, "{c}");
            }
        },
    );
}

/// Two builds of one exclusive or, in two orders, are one node (item CHAIN-zip-size), so they
/// are equal in time linear in the tuple types.
#[test]
fn an_exclusive_or_built_in_two_orders_is_equal_to_itself_in_linear_time() {
    let types = scaling::inputs(32, |c| (parity(c, false).ty(2), parity(c, true).ty(2)));
    scaling::check(
        "an exclusive or against its reverse build, by tuple types",
        32,
        |c| {
            let (x, y) = &types[&c];
            Type::forget_emptiness();
            assert!(x.equiv(y), "{c}");
        },
    );
}

/// The known limit (COMPLEXITY.md K71, question A46): the exclusive or of `c` tuple types
/// against that of `c + 1`, an `&` of two parts open on both components through different
/// cells, is decided by the split into tuple types, order `c²`: 333M, 1,253M and 4,414M
/// instructions at 32, 64 and 128.
#[test]
fn overlapping_exclusive_ors_are_compared_at_quadratic_cost() {
    let types = scaling::inputs(16, |c| (parity(c, false).ty(2), parity(c + 1, false).ty(2)));
    scaling::check_order(
        "an exclusive or against one more, by tuple types",
        16,
        2,
        |c| {
            let (x, y) = &types[&c];
            Type::forget_emptiness();
            assert!(!x.equiv(y), "{c}");
        },
    );
}

/// The same limit for two chains, `c` and `c + 1` tuple types: 9.5M, 31.0M and 110M
/// instructions at 32, 64 and 128.
#[test]
fn overlapping_decision_lists_are_compared_at_quadratic_cost() {
    let types = scaling::inputs(32, |c| (chain(c).ty(2), chain(c + 1).ty(2)));
    scaling::check_order("a chain against one more, by tuple types", 32, 2, |c| {
        let (x, y) = &types[&c];
        Type::forget_emptiness();
        assert!(!x.equiv(y), "{c}");
    });
}

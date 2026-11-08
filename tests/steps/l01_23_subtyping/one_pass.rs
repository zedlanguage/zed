//! Tuple parts whose tuple types are each open on one component, with cells that share no value
//! (item EMPTY-overlap-chain): a tuple of the box picks one cell or none on each component, and
//! the part is decided in one pass over its nodes (`Searching::one_pass`): decision lists and
//! exclusive ors exactly, `!`, `|`, and `&` of operands open on no component in common. The
//! answers are compared with an enumeration of the tuples on random parts, and the families of
//! exclusive ors and chains of overlapping tuple types are decided in time linear in them. An
//! `&` or `|` whose operands share a component through different cells is read exactly when
//! both are decision lists or exclusive ors under `!`, such as the comparison `x & !y` of two
//! such parts (item EMPTY-overlap-fast), in time `O(n log n)`; other such meets are refused
//! with `Refusal::SharedCells` naming the component (COMPLEXITY.md K71, answer A46), since
//! they encode Orthogonal Vectors.

use zed_kernel::Value;
use zed_kernel::types::{Refusal, Type, Verdict};
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

/// A random decision list or exclusive or on the components `on`, under one `!` or none.
fn random_leaf(g: &mut Rng, on: &[usize]) -> F {
    let atom = |g: &mut Rng| (on[g.below(on.len())], g.below(VALUES));
    let leaf = match g.below(3) {
        0 => {
            let (j, v) = atom(g);
            F::Row(j, v)
        }
        1 => F::Xor((0..1 + g.below(6)).map(|_| atom(g)).collect()),
        _ => F::Chain(
            (0..1 + g.below(7))
                .map(|_| {
                    let (j, v) = atom(g);
                    (j, v, g.below(2) == 0)
                })
                .collect(),
        ),
    };
    if g.below(3) == 0 {
        F::Not(Box::new(leaf))
    } else {
        leaf
    }
}

/// A random part of the class the pass decides with the meets of step EMPTY-overlap-fast: an
/// `&` or `|` either of operands on two halves of `on`, or of two lists or exclusive ors on two
/// sets of components that share one or more, under `!` or not.
fn random_in_class(g: &mut Rng, on: &[usize], depth: usize) -> F {
    let k = if depth == 0 || on.len() < 2 {
        g.below(2)
    } else {
        g.below(5)
    };
    match k {
        0 => random_leaf(g, on),
        1 => {
            // Two sets of components with at least one in common.
            let common = on[g.below(on.len())];
            let pick = |g: &mut Rng| -> Vec<usize> {
                let mut s: Vec<usize> = on.iter().copied().filter(|_| g.below(2) == 0).collect();
                s.push(common);
                s.sort_unstable();
                s.dedup();
                s
            };
            let (a, b) = (pick(g), pick(g));
            let (x, y) = (Box::new(random_leaf(g, &a)), Box::new(random_leaf(g, &b)));
            let meet = if g.below(2) == 0 {
                F::And(x, y)
            } else {
                F::Or(x, y)
            };
            if g.below(3) == 0 {
                F::Not(Box::new(meet))
            } else {
                meet
            }
        }
        2 => F::Not(Box::new(random_in_class(g, on, depth - 1))),
        _ => {
            let cut = 1 + g.below(on.len() - 1);
            let (x, y) = (
                Box::new(random_in_class(g, &on[..cut], depth - 1)),
                Box::new(random_in_class(g, &on[cut..], depth - 1)),
            );
            if k == 3 { F::And(x, y) } else { F::Or(x, y) }
        }
    }
}

/// Random parts whose `&` and `|` of operands on shared components are of two lists or
/// exclusive ors under `!`, on two to five components, each decided as enumeration decides
/// it; both answers are met.
#[test]
fn random_meets_of_lists_and_exclusive_ors_are_decided_as_enumeration_decides_them() {
    zed_tests::deep::on_small_stack(|| {
        let mut g = Rng::new(73);
        let mut answers = [0; 2];
        for width in 1..=5 {
            let on: Vec<usize> = (0..width).collect();
            for _ in 0..200 {
                let f = random_in_class(&mut g, &on, 2);
                decide(&mut g, width, &f, &mut answers);
            }
        }
        assert!(answers[0] >= 60 && answers[1] >= 60, "{answers:?}");
    });
}

/// Random parts with some `&` of operands of any form on shared components, a third of them
/// an `&` of three lists or exclusive ors, which the pass does not read, and of a union of
/// tuple types on component 0, so that the part is false where every tuple type is (the
/// meets the pass refuses): each is decided as enumeration decides it, or refused naming one
/// of the part's components, and then counted inhabited by `is_empty`; parts of each answer
/// and refused parts are all met.
#[test]
fn random_parts_out_of_the_class_are_decided_or_refused() {
    zed_tests::deep::on_small_stack(|| {
        let mut g = Rng::new(72);
        let mut answers = [0; 3];
        for width in 2..=3 {
            let on: Vec<usize> = (0..width).collect();
            for n in 0..150 {
                let f = if n % 3 == 0 {
                    let mut leaf = || random_leaf(&mut g, &on);
                    let (x, y, z) = (leaf(), leaf(), leaf());
                    let rows = F::Or(
                        Box::new(F::Row(0, g.below(VALUES))),
                        Box::new(F::Row(0, g.below(VALUES))),
                    );
                    let three = F::And(Box::new(F::And(Box::new(x), Box::new(y))), Box::new(z));
                    F::And(Box::new(three), Box::new(rows))
                } else {
                    random(&mut g, &on, 3, true)
                };
                let (b, boxed) = random_box(&mut g, width);
                let t = &b & &f.ty(width);
                let inhabited = by_enumeration(&f, &boxed);
                Type::forget_emptiness();
                let v = t.verdict();
                Type::forget_emptiness();
                let empty = t.is_empty();
                match v {
                    Verdict::Refused(Refusal::SharedCells(j)) => {
                        assert!(j < width && !empty, "{f:?} on {boxed:?}");
                        answers[2] += 1;
                    }
                    _ => {
                        let expected = if inhabited {
                            Verdict::Inhabited
                        } else {
                            Verdict::Empty
                        };
                        assert_eq!(v, expected, "{f:?} on {boxed:?}");
                        assert_eq!(empty, !inhabited, "{f:?} on {boxed:?}");
                        answers[usize::from(inhabited)] += 1;
                    }
                }
            }
        }
        // Most parts that reach a meet the pass does not read are inhabited, and a value is
        // found before any refusal; the refusal itself is tested on its own by
        // `an_orthogonal_vectors_meet_is_refused_naming_its_component`.
        assert!(
            answers[0] >= 5 && answers[1] >= 5 && answers[2] >= 1,
            "{answers:?}"
        );
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

/// The comparisons of item EMPTY-overlap-fast (COMPLEXITY.md K71), each an `&` of two parts open
/// on both components through different cells, at `c` tuple types: the exclusive or of `c`
/// against that of `c + 1`, the chain of `c` against that of `c + 1`, and the chain against
/// the exclusive or, each not equal; and the box `tight(c)` met with the chain and the
/// complement of the exclusive or, inhabited.
fn comparisons(c: usize) -> (Vec<(Type, Type)>, Type) {
    let (x, x1) = (parity(c, false).ty(2), parity(c + 1, false).ty(2));
    let (l, l1) = (chain(c).ty(2), chain(c + 1).ty(2));
    let all = Type::tuple(vec![Type::top(), Type::top()]);
    let meet = &(&tight(c) & &l) & &(&all - &x);
    (vec![(x.clone(), x1), (l.clone(), l1), (l, x)], meet)
}

/// The comparisons of [`comparisons`] are decided in time `O(c log c)`, 32 against 256 tuple
/// types. Before the item, the split into tuple types took 333M, 1,253M and 4,414M
/// instructions at 32, 64 and 128 on the exclusive ors, and 9.5M, 31.0M and 110M on the
/// chains (order `c²`).
#[test]
fn overlapping_exclusive_ors_and_chains_are_compared_in_n_log_n() {
    let types = scaling::inputs(32, comparisons);
    scaling::check(
        "an exclusive or or a chain against one more and against each other, by tuple types",
        32,
        |c| {
            let (pairs, meet) = &types[&c];
            for (x, y) in pairs {
                Type::forget_emptiness();
                assert!(!x.equiv(y), "{c}");
            }
            Type::forget_emptiness();
            assert_eq!(meet.verdict(), Verdict::Inhabited, "{c}");
        },
    );
}

/// The chain of `c` tuple types less the chain of `c + 1`, empty at even `c` and inhabited at
/// odd, decided in time `O(c log c)`, 32 against 256 (and 33 against 257). The last tuple type
/// of the longer chain is `|` at even `c` and `-` at odd, so both kinds of end are measured.
/// Once the two tuple types the longer chain adds or takes are refused, the two chains are one
/// decision list and its complement, which meet in `false` at once. Before
/// that was seen (`Connect::same_as_not` on lists other than literals), the part stayed an `&`
/// of the two and narrowing refused one tuple type a pass, 6.6M, 24.8M, 97.7M and 394M
/// instructions at 32, 64, 128 and 256 (order `c²`).
#[test]
fn a_chain_less_a_longer_one_is_decided_in_n_log_n() {
    let all = Type::tuple(vec![Type::top(), Type::top()]);
    let types = scaling::inputs(32, |c| {
        [c, c + 1].map(|c| {
            let (l, l1) = (chain(c).ty(2), chain(c + 1).ty(2));
            (&l & &(&all - &l1), c % 2 == 1)
        })
    });
    scaling::check("a chain less one a tuple type longer", 32, |c| {
        for (t, inhabited) in &types[&c] {
            Type::forget_emptiness();
            let want = if *inhabited {
                Verdict::Inhabited
            } else {
                Verdict::Empty
            };
            assert_eq!(t.verdict(), want, "{c}");
        }
    });
}

/// Chains on three components each, sharing two: `x` on components 0 to 2 and `y` on 1 to 3,
/// `c` tuple types each, met and compared, so the components only one operand is open on are
/// chosen freely beside the shared ones.
fn wide(c: usize) -> (Type, Type) {
    let on = |first: usize| {
        let rows = (0..c).map(|i| (first + i % 3, 1000 + i / 3, i % 2 == 0));
        F::Chain(rows.collect()).ty(4)
    };
    (on(0), on(1))
}

/// The meets of [`wide`] are decided in time `O(c log c)`, 30 against 240 tuple types, and
/// agree with the enumeration at 30.
#[test]
fn chains_sharing_two_of_four_components_are_met_in_n_log_n() {
    let types = scaling::inputs(30, wide);
    let all = Type::tuple(vec![Type::top(); 4]);
    let run = |c: usize| {
        let (x, y) = &types[&c];
        let mut verdicts = Vec::new();
        for t in [x & y, x - y, y - x, &all - &(x | y)] {
            Type::forget_emptiness();
            let v = t.verdict();
            assert!(!matches!(v, Verdict::Refused(_)), "{c}");
            verdicts.push(v);
        }
        verdicts
    };
    // At 30 the enumeration reads each component's 10 literals and one value outside them.
    let boxed: Vec<Vec<usize>> = vec![(1000..1010).chain([OUTSIDE]).collect(); 4];
    let f = |first: usize| {
        let rows = (0..30).map(|i| (first + i % 3, 1000 + i / 3, i % 2 == 0));
        F::Chain(rows.collect())
    };
    let (x, y) = (Box::new(f(0)), Box::new(f(1)));
    let expected: Vec<Verdict> = [
        F::And(x.clone(), y.clone()),
        F::And(x.clone(), Box::new(F::Not(y.clone()))),
        F::And(y.clone(), Box::new(F::Not(x.clone()))),
        F::Not(Box::new(F::Or(x, y))),
    ]
    .iter()
    .map(|f| match by_enumeration(f, &boxed) {
        true => Verdict::Inhabited,
        false => Verdict::Empty,
    })
    .collect();
    assert_eq!(run(30), expected);
    scaling::check(
        "chains on three components sharing two, by tuple types",
        30,
        |c| {
            run(c);
        },
    );
}

/// The Orthogonal Vectors meet (COMPLEXITY.md K71): component 0 picks one of `n` vectors `u`,
/// component 1 one of `n` vectors `v`, of `d` bits, and the part is the `and` over the bits
/// `b` of `!(U_b & V_b)`, `U_b` the tuple types of the `u` with bit `b` set, beside some `u`
/// and some `v`. The vectors here are those of 5 bits with 3 or more set, so any two share a
/// bit and the part is empty, though no bit is set in all of them (one would make the part
/// empty on its face); the pass reads no such `and`, and the check is refused naming
/// component 0.
#[test]
fn an_orthogonal_vectors_meet_is_refused_naming_its_component() {
    let d = 5;
    let u: Vec<usize> = (0..1usize << d).filter(|w| w.count_ones() >= 3).collect();
    let v = u.clone();
    let n = u.len();
    let rows = |j: usize, of: &[usize], b: Option<usize>| {
        let has = |w: &usize| b.is_none_or(|b| w >> b & 1 == 1);
        let all: Vec<Type> = (0..of.len())
            .filter(|&i| has(&of[i]))
            .map(|i| row(2, j, 1000 * (j + 1) + i))
            .collect();
        Type::union_all(all)
    };
    let mut part = &rows(0, &u, None) & &rows(1, &v, None);
    for b in 0..d {
        part = &part - &(&rows(0, &u, Some(b)) & &rows(1, &v, Some(b)));
    }
    let boxed = Type::tuple(vec![
        Type::union_all((0..n).map(|i| lit(1000 + i))),
        Type::union_all((0..n).map(|i| lit(2000 + i))),
    ]);
    let t = &boxed & &part;
    Type::forget_emptiness();
    assert_eq!(t.verdict(), Verdict::Refused(Refusal::SharedCells(0)));
    Type::forget_emptiness();
    assert!(!t.is_empty());
    let m = Refusal::SharedCells(0).message();
    assert!(
        m.contains("component 0") && m.contains("Orthogonal Vectors"),
        "{m}"
    );
}

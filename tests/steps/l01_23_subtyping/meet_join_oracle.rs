//! The boxes of a meet whose smaller operand has a box with an unbounded column, which
//! `types::part_boxes` meets with the join of the other operand's boxes (`join_of`), against
//! a search of every point of a small box (test audit 2026-11-08, row 2,
//! TESTS-coverage-projection-paths). Each type is a meet of unions or exclusive ors of pairs
//! whose columns are literals, sets of literals, `int` and `int` less one literal; its
//! membership is worked out here from that description, not by the kernel, and compared with
//! `contains`, with `finite` and with the values `each_value` lists.
//!
//! DESIGN.md step L1.23: subtyping is semantic, a type is the set of values it holds; and the
//! finite listing (T6, SYNTHESIS Q4): a type known finite lists exactly the values it holds,
//! and a type that holds infinitely many is not known finite.

use std::collections::BTreeSet;

use zed_kernel::Value;
use zed_kernel::types::Type;
use zed_tests::instances::Rng;

/// The seed of the random types; each type's own seed is printed with a failure.
const SEED: u64 = 0x7c9_0003;

/// The integers the points are made of. The types name only 0..3, so 7 stands for every other
/// integer: a type that holds a pair with a 7 in it holds infinitely many.
const INTS: [i64; 5] = [0, 1, 2, 3, 7];

/// A column of a pair type.
#[derive(Clone, Debug)]
enum Col {
    /// The integers whose bits are set, of 0..3.
    Set(u8),
    Int,
    /// `int` less one literal.
    IntBut(i64),
}

impl Col {
    fn ty(&self) -> Type {
        let lit = |i: i64| Type::lit(&Value::Int(i)).unwrap();
        match self {
            Col::Set(bits) => Type::union_all((0..4).filter(|i| bits >> i & 1 == 1).map(lit)),
            Col::Int => Type::int(),
            Col::IntBut(k) => &Type::int() - &lit(*k),
        }
    }

    fn holds(&self, v: i64) -> bool {
        match self {
            Col::Set(bits) => (0..4).contains(&v) && bits >> v & 1 == 1,
            Col::Int => true,
            Col::IntBut(k) => v != *k,
        }
    }
}

/// Pair types joined, or taken in exclusive or, one at a time from the left.
#[derive(Clone, Debug)]
struct Side {
    pairs: Vec<(Col, Col)>,
    xor: bool,
}

impl Side {
    fn ty(&self) -> Type {
        let pair = |(a, b): &(Col, Col)| Type::tuple(vec![a.ty(), b.ty()]);
        let mut it = self.pairs.iter().map(pair);
        let first = it.next().expect("a side has a pair");
        it.fold(first, |acc, p| match self.xor {
            true => &(&acc - &p) | &(&p - &acc),
            false => &acc | &p,
        })
    }

    fn holds(&self, a: i64, b: i64) -> bool {
        let n = (self.pairs.iter())
            .filter(|(x, y)| x.holds(a) && y.holds(b))
            .count();
        match self.xor {
            true => n % 2 == 1,
            false => n > 0,
        }
    }
}

/// The meet of the sides, from the left.
fn meet(sides: &[Side]) -> Type {
    let mut it = sides.iter().map(Side::ty);
    let first = it.next().expect("a meet has a side");
    it.fold(first, |acc, s| &acc & &s)
}

fn pair(a: i64, b: i64) -> Value {
    Value::tuple(vec![Value::Int(a), Value::Int(b)])
}

/// How a type compared with the search.
#[derive(Debug, PartialEq)]
enum Found {
    Listed,
    Infinite,
    /// Finite, but not known finite, as `part_boxes` documents for a join wider than the meet.
    Missed,
}

/// Checks `contains`, `finite` and `each_value` of the meet of `sides` against the points it
/// holds by its description; `case` names it in a failure.
fn check(sides: &[Side], case: &str) -> Found {
    let t = meet(sides);
    let mut holds = BTreeSet::new();
    for a in INTS {
        for b in INTS {
            let want = sides.iter().all(|s| s.holds(a, b));
            assert_eq!(t.contains(&pair(a, b)), want, "({a}, {b}) in {t}: {case}");
            if want {
                holds.insert((a, b));
            }
        }
    }
    let finite = !holds.iter().any(|&(a, b)| a == 7 || b == 7);
    let listed = t.each_value().map(|vs| {
        let vs: Vec<Value> = vs.collect();
        let set: BTreeSet<Value> = vs.iter().cloned().collect();
        assert_eq!(set.len(), vs.len(), "each value once: {t}: {case}");
        set
    });
    assert_eq!(t.finite(), listed.is_some(), "{t}: {case}");
    match listed {
        Some(got) => {
            assert!(finite, "an infinite type listed: {t}: {case}");
            let want: BTreeSet<Value> = holds.iter().map(|&(a, b)| pair(a, b)).collect();
            assert_eq!(got, want, "{t}: {case}");
            Found::Listed
        }
        None if finite => Found::Missed,
        None => Found::Infinite,
    }
}

fn union(pairs: Vec<(Col, Col)>) -> Side {
    Side { pairs, xor: false }
}

#[test]
fn a_meet_whose_smaller_side_has_an_unbounded_column_lists_the_meet_with_the_join() {
    use Col::{Int, IntBut, Set};
    let s = Set(0b0111);
    // `((int, 0) | (0, int)) & ((0..3, 1) | (1, 0..3))`: each box of the left has `int`, and
    // the join of the right, `(0..3, 0..3)`, bounds it, so the meet is listed: `(1, 0)` and
    // `(0, 1)`. Met with the right on the left too, and with an exclusive or.
    let left = union(vec![(Int, Set(1)), (Set(1), Int)]);
    let right = union(vec![(s.clone(), Set(2)), (Set(2), s.clone())]);
    for sides in [
        vec![left.clone(), right.clone()],
        vec![right.clone(), left.clone()],
        vec![
            Side {
                xor: true,
                ..left.clone()
            },
            right.clone(),
        ],
    ] {
        assert_eq!(check(&sides, &format!("{sides:?}")), Found::Listed);
    }
    // A complement column in the smaller side, bounded by the join of a larger one.
    let few = union(vec![(IntBut(1), Set(0b11))]);
    let many = union(vec![
        (Set(0b11), Set(1)),
        (Set(0b110), Set(0b10)),
        (Set(0b1000), Int),
    ]);
    assert_eq!(check(&[few, many], "complement column"), Found::Listed);
    // The example `part_boxes` documents: the pairs meet to finite boxes, the joins do not, so
    // the meet `{(0, 1), (1, 0)}` is not known finite.
    let left = union(vec![(Int, Set(1)), (Set(1), Int)]);
    let right = union(vec![(Int, Set(2)), (Set(2), Int)]);
    assert_eq!(check(&[left, right], "documented"), Found::Missed);
}

/// A random column: a literal or a set of them half the time, else `int` or `int` less one.
fn random_col(rng: &mut Rng) -> Col {
    match rng.below(4) {
        0 | 1 => Col::Set(1 + rng.below(15) as u8),
        2 => Col::Int,
        _ => Col::IntBut(rng.int(0, 3)),
    }
}

fn random_side(rng: &mut Rng) -> Side {
    let n = 1 + rng.below(3);
    Side {
        pairs: (0..n).map(|_| (random_col(rng), random_col(rng))).collect(),
        xor: rng.below(3) == 0,
    }
}

#[test]
fn each_random_meet_of_unions_with_unbounded_columns_agrees_with_a_search_of_all_points() {
    // Each type's seed is its index's, so a failure is reproduced by the seed it prints.
    let (mut listed, mut infinite, mut missed) = (0, 0, 0);
    for i in 0..2000u64 {
        let seed = SEED + i;
        let mut rng = Rng::new(seed);
        let sides: Vec<Side> = (0..2 + rng.below(2))
            .map(|_| random_side(&mut rng))
            .collect();
        let case = format!(
            "seed {seed:#x} (type {i}), {sides:?}; rerun with /home/luke/Work/wt/zrun \
             tools/run_tests.sh --no-doc --only '^l01_23_subtyping::meet_join_oracle'"
        );
        match check(&sides, &case) {
            Found::Listed => listed += 1,
            Found::Infinite => infinite += 1,
            Found::Missed => missed += 1,
        }
    }
    eprintln!("listed {listed}, infinite {infinite}, finite but not known finite {missed}");
    // 705, 1120 and 175 when written. A box of the smaller side met as written, not with the
    // join, leaves 376 finite but not known finite.
    assert!(
        listed >= 300 && infinite >= 300 && missed <= 200,
        "{listed} listed, {infinite} infinite, {missed} missed"
    );
}

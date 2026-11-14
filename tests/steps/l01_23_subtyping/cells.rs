//! The table of cells that decides when a product less a union of tuple types is empty (DESIGN.md
//! L1.23), the check that a `match` on a tuple of fields is exhaustive. For each component, the
//! table holds the distinct types the negated tuple types take there, and tests each once for all
//! the tuple types that share it. Its answers are compared with a brute-force oracle over small
//! enumerations, under renaming and in any order of queries, and it is timed on the arms of a
//! decision tree, whose input is of size `Θ(c²)` in its `c` columns (the bound DESIGN.md L1.23
//! gives), in both orders of the columns.

use std::collections::BTreeMap;

use zed_kernel::Value;
use zed_kernel::types::Type;
use zed_tests::instances::Rng;
use zed_tests::scaling;

fn lit(i: usize) -> Type {
    Type::lit(&Value::Int(i as i64)).unwrap()
}

/// The arms of a `match` on `c` fields of `{b, b + 1, b + 2}`, a decision tree: on field `i`,
/// after `b + 2` in every field before it, `b` and `b + 1` each end an arm and `b + 2` goes on;
/// on the last field `b + 2` ends an arm too. Field `i` of the scrutinee is component
/// `place(i)` of the tuple. Returns the scrutinee's type and the arms.
fn arms(c: usize, b: usize, place: impl Fn(usize) -> usize) -> (Type, Vec<Type>) {
    let field = Type::union_all((b..b + 3).map(lit));
    let arm = |i: usize, v: usize| {
        let mut row = vec![field.clone(); c];
        for j in 0..i {
            row[place(j)] = lit(b + 2);
        }
        row[place(i)] = lit(v);
        Type::tuple(row)
    };
    let mut rows: Vec<Type> = (0..c).flat_map(|i| [arm(i, b), arm(i, b + 1)]).collect();
    rows.push(arm(c - 1, b + 2));
    (Type::tuple(vec![field; c]), rows)
}

#[test]
fn a_decision_tree_is_exhaustive_in_any_column_order() {
    for c in [1usize, 2, 3, 7] {
        let h = c.div_ceil(2);
        let orders = [
            ("forward", (0..c).collect::<Vec<usize>>()),
            ("reversed", (0..c).rev().collect()),
            (
                "evens then odds",
                (0..c)
                    .map(|i| if i < h { 2 * i } else { 2 * (i - h) + 1 })
                    .collect(),
            ),
        ];
        for (name, place) in &orders {
            let (p, rows) = arms(c, 40, |i| place[i]);
            assert!(
                (&p - &Type::union_all(rows.iter().cloned())).is_empty(),
                "c = {c}, {name}"
            );
            for left_out in 0..rows.len() {
                let mut less = rows.clone();
                less.remove(left_out);
                assert!(
                    !(&p - &Type::union_all(less)).is_empty(),
                    "c = {c}, {name}, arm {left_out} left out"
                );
            }
        }
    }
}

/// The values a field may take: three integers and two atoms. `Names` says what each is called.
const VALUES: usize = 5;

/// What the values are called: the integers start at `base`, and the atoms are `prefix` with a
/// letter. Renaming changes each value's hash, so the order in which the check meets the
/// tuple types and their components.
struct Names {
    base: usize,
    prefix: &'static str,
    /// The value with index `i` is called by the name of index `perm[i]`.
    perm: [usize; VALUES],
}

impl Names {
    fn value(&self, i: usize) -> Type {
        match self.perm[i] {
            v @ 0..3 => lit(self.base + v),
            v => Type::atom(&format!("{}{}", self.prefix, ["x", "y"][v - 3])),
        }
    }

    /// The union of the values whose bits are set in `set`. In an arm, `wild` is set, and all
    /// values are written `_`, `Type::top()`, which holds more than the five.
    fn field(&self, set: u8, wild: bool) -> Type {
        if wild && set == FULL {
            return Type::top();
        }
        Type::union_all(
            (0..VALUES)
                .filter(|i| set >> i & 1 == 1)
                .map(|i| self.value(i)),
        )
    }

    fn tuple(&self, sets: &[u8], wild: bool) -> Type {
        Type::tuple(sets.iter().map(|&s| self.field(s, wild)).collect())
    }
}

const FULL: u8 = (1 << VALUES) - 1;

/// A `match` table: the scrutinee's fields, an optional guard on the whole tuple, and the arms.
/// Each field of an arm comes from a pool of three sets, so arms share their components' types.
struct Table {
    scrutinee: Vec<u8>,
    guard: Option<Vec<u8>>,
    arms: Vec<Vec<u8>>,
}

fn table(r: &mut Rng) -> Table {
    let width = 1 + r.below(4);
    let set = |r: &mut Rng| match r.below(6) {
        0 => FULL,
        _ => 1 + r.below(FULL as usize) as u8,
    };
    let pools: Vec<[u8; 3]> = (0..width).map(|_| [set(r), set(r), set(r)]).collect();
    let scrutinee = (0..width).map(|_| set(r)).collect();
    let guard = (r.below(3) == 0).then(|| (0..width).map(|_| set(r)).collect());
    let arms = (0..r.below(9))
        .map(|_| pools.iter().map(|pool| pool[r.below(3)]).collect())
        .collect();
    Table {
        scrutinee,
        guard,
        arms,
    }
}

/// True when some value of the scrutinee within the guard matches no arm, by listing them all.
fn missed_by_listing(t: &Table) -> bool {
    let width = t.scrutinee.len();
    let within = |sets: &[u8], v: &[usize]| sets.iter().zip(v).all(|(s, &i)| s >> i & 1 == 1);
    (0..VALUES.pow(width as u32)).any(|code| {
        let v: Vec<usize> = (0..width)
            .map(|j| code / VALUES.pow(j as u32) % VALUES)
            .collect();
        within(&t.scrutinee, &v)
            && t.guard.as_ref().is_none_or(|g| within(g, &v))
            && !t.arms.iter().any(|a| within(a, &v))
    })
}

/// The type of the values the arms miss, under the names `n`.
fn missed(t: &Table, n: &Names) -> Type {
    let mut s = n.tuple(&t.scrutinee, false);
    if let Some(g) = &t.guard {
        s = &s & &n.tuple(g, false);
    }
    &s - &Type::union_all(t.arms.iter().map(|a| n.tuple(a, true)))
}

fn tables(seed: u64, count: usize) -> Vec<Table> {
    let mut r = Rng::new(seed);
    (0..count).map(|_| table(&mut r)).collect()
}

const PLAIN: Names = Names {
    base: 0,
    prefix: "",
    perm: [0, 1, 2, 3, 4],
};

#[test]
fn match_tables_agree_with_listing_their_values() {
    let mut empty = 0;
    for (i, t) in tables(23, 4000).iter().enumerate() {
        let expected = !missed_by_listing(t);
        empty += expected as usize;
        let ty = missed(t, &PLAIN);
        assert_eq!(ty.is_empty(), expected, "table {i}: {ty}");
    }
    // Both answers are common, so the comparison means something either way.
    assert!((1000..3000).contains(&empty), "{empty} of 4000 exhaustive");
}

#[test]
fn the_answers_do_not_depend_on_names() {
    let renamings = [
        Names {
            base: 1000,
            prefix: "q",
            perm: [0, 1, 2, 3, 4],
        },
        Names {
            base: 77,
            prefix: "status_",
            perm: [2, 0, 1, 4, 3],
        },
        Names {
            base: 5,
            prefix: "z",
            perm: [3, 4, 0, 2, 1],
        },
    ];
    for (i, t) in tables(29, 1500).iter().enumerate() {
        let plain = missed(t, &PLAIN).is_empty();
        for (k, n) in renamings.iter().enumerate() {
            assert_eq!(missed(t, n).is_empty(), plain, "table {i}, renaming {k}");
        }
    }
}

#[test]
fn the_answers_do_not_depend_on_the_order_of_queries() {
    // Each answer is decided once alone, after forgetting all others, and then all in one order
    // and in the reverse order, each sequence keeping what it decided.
    let built: Vec<Type> = tables(31, 1500).iter().map(|t| missed(t, &PLAIN)).collect();
    let alone: Vec<bool> = built
        .iter()
        .map(|ty| {
            Type::forget_emptiness();
            ty.is_empty()
        })
        .collect();
    Type::forget_emptiness();
    let forward: Vec<bool> = built.iter().map(Type::is_empty).collect();
    Type::forget_emptiness();
    let mut backward: Vec<bool> = built.iter().rev().map(Type::is_empty).collect();
    backward.reverse();
    assert_eq!(forward, alone);
    assert_eq!(backward, alone);
}

mod bench;

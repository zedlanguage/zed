//! Product and remainder trees over `BigUint`, the one copy for zedc-int (`remainders`, under
//! `Int::is_perfect_power`), zedc-check `check/coprime.rs` (`base_of` and its remainders) and
//! zedc-presburger `presburger/modular.rs` (the batch "shares a factor" test, the CRT tree and
//! `batch_remainders`), DRY-number-theory-wide item 2.
//!
//! The product tree of leaves `m_0 .. m_{k-1}` multiplies them in pairs, then those in pairs,
//! up to one product `P`; a level of odd length carries its last node up unchanged, so node
//! `j` of a level is the product of nodes `2 j` and `2 j + 1` of the level below, or equal to
//! node `2 j` when there is no `2 j + 1`. The remainder tree goes back down: each node `v`
//! divides its parent `u`, so `x mod v = (x mod u) mod v`, and the leaves get `x mod m_i`.
//! With `P mod v^2` in place of `x mod v` (`v^2` divides `u^2`; at the root `P < P^2` already),
//! each leaf gets `P mod m^2`, and as `m` divides both `P` and `m^2` that is `m ((P / m) mod
//! m)`, so one exact division gives `(P / m) mod m`. Then `gcd(m, (P / m) mod m) > 1` exactly
//! when `m` shares a prime with the product of the other leaves: the batch gcd step. These
//! are the textbook product and remainder trees; the proofs are the divisibility facts just
//! given, and no paper is relied on here (the callers cite D. J. Bernstein's papers for the
//! method; those citations are theirs).
//!
//! Complexity tradeoff: a level of the tree holds at most `B + k` bits for `k` leaves of `B`
//! bits in all, so the products cost O(M(B)) a level and O(M(B) log k) in all with the
//! kernel's `mul_uint` (transforms past 512 words), and the remainders O(M(X + B)) at the root
//! and O(M(B)) a level below with `rem_uint` (Newton's reciprocal); one division of `x` by
//! each leaf costs O(k M(X)) for `x` of `X` bits. Tests: `num::trees::tests`, against one
//! division a leaf on no leaf, one leaf, leaves 1, equal leaves, a carried node at every
//! level, and leaves past the transform width.

use std::borrow::{Borrow, Cow};

use num_bigint::BigUint;

use super::{div_rem_uint, mul_uint, rem_uint};

/// The levels of the product tree of `leaves` above the leaves themselves: the products of
/// pairs of leaves first, then of pairs of those, up to the one product of all, a node with no
/// partner carried up as it is. Empty for no leaf or one leaf. A leaf 0 makes its ancestors
/// 0, which [`remainders`] and [`cofactors_mod_leaves`] do not accept.
pub fn product_tree<L: Borrow<BigUint>>(leaves: &[L]) -> Vec<Vec<BigUint>> {
    let mut levels: Vec<Vec<BigUint>> = Vec::new();
    if leaves.len() > 1 {
        let first = (leaves.chunks(2))
            .map(|c| pair(c[0].borrow(), c.get(1).map(Borrow::borrow)))
            .collect();
        levels.push(first);
    }
    while let Some(top) = levels.last().filter(|l| l.len() > 1) {
        let up = top.chunks(2).map(|c| pair(&c[0], c.get(1))).collect();
        levels.push(up);
    }
    levels
}

/// `a * b`, or `a` where `b` is missing (a node carried up).
fn pair(a: &BigUint, b: Option<&BigUint>) -> BigUint {
    match b {
        Some(b) => mul_uint(a, b),
        None => a.clone(),
    }
}

/// The product of all `leaves`, given `levels`, their [`product_tree`]: its root, or the one
/// leaf; 1 for no leaf.
pub fn tree_product<'a, L: Borrow<BigUint>>(
    leaves: &'a [L],
    levels: &'a [Vec<BigUint>],
) -> Cow<'a, BigUint> {
    match (levels.last(), leaves.first()) {
        (Some(top), _) => Cow::Borrowed(&top[0]),
        (None, Some(leaf)) => Cow::Borrowed(leaf.borrow()),
        (None, None) => Cow::Owned(BigUint::from(1u32)),
    }
}

/// `x mod m` for each leaf `m` of `leaves`, every leaf above 0, by the remainder tree down
/// `levels`, their [`product_tree`].
pub fn remainders<L: Borrow<BigUint>>(
    x: &BigUint,
    leaves: &[L],
    levels: &[Vec<BigUint>],
) -> Vec<BigUint> {
    if leaves.is_empty() {
        return Vec::new();
    }
    let top = rem_uint(x, &tree_product(leaves, levels));
    descend(top, leaves, levels, |r, v| rem_uint(r, v))
}

/// `(P / m) mod m` for each leaf `m` of `leaves`, every leaf above 0, with `P` their product,
/// by the remainder tree on `P mod v^2` down `levels`, their [`product_tree`]. For one leaf
/// `P / m` is 1, so the answer is `1 mod m`.
pub fn cofactors_mod_leaves<L: Borrow<BigUint>>(
    leaves: &[L],
    levels: &[Vec<BigUint>],
) -> Vec<BigUint> {
    if leaves.is_empty() {
        return Vec::new();
    }
    let p = tree_product(leaves, levels).into_owned();
    let rems = descend(p, leaves, levels, |r, v| rem_uint(r, &mul_uint(v, v)));
    // `r = P mod m^2` is a multiple of `m` (module comment), so the exact quotient `r / m`,
    // below `m`, is `(P / m) mod m`.
    (rems.iter().zip(leaves))
        .map(|(r, m)| div_rem_uint(r, m.borrow()).0)
        .collect()
}

/// The values at the leaves, `leaves` not empty, when `top` is the root's value and each
/// node's value is `reduce(its parent's value, the node)`.
fn descend<L: Borrow<BigUint>>(
    top: BigUint,
    leaves: &[L],
    levels: &[Vec<BigUint>],
    reduce: impl Fn(&BigUint, &BigUint) -> BigUint,
) -> Vec<BigUint> {
    // From the level below the root down to the first level above the leaves, then the leaves.
    // With one leaf the root is that leaf, reduced once more, which changes neither `x mod m`
    // nor `P mod m^2`.
    let mut vals = vec![top];
    for level in levels.iter().rev().skip(1) {
        vals = (level.iter().enumerate())
            .map(|(j, v)| reduce(&vals[j / 2], v))
            .collect();
    }
    (leaves.iter().enumerate())
        .map(|(j, m)| reduce(&vals[j / 2], m.borrow()))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn big(v: u64) -> BigUint {
        BigUint::from(v)
    }

    /// The leaf sets: none, one, ones, equal, every count from 2 to 17 (a carried node at some
    /// level for each count that is not a power of 2), and leaves past 512 words.
    fn leaf_sets() -> Vec<Vec<BigUint>> {
        let mut sets = vec![
            vec![],
            vec![big(1)],
            vec![big(7)],
            vec![big(1), big(1), big(1)],
            vec![big(12), big(12), big(12)],
            vec![big(1), big(5), big(1), big(5), big(9)],
            vec![big(u64::MAX); 6],
        ];
        for k in 2..=17u64 {
            sets.push((0..k).map(|i| big(3 * i * i + 2 * i + 1)).collect());
        }
        let wide = |e: u32, c: u64| big(18446744073709551557).pow(e) * c + 1u32;
        sets.push(vec![
            wide(600, 1),
            wide(700, 3),
            wide(10, 5),
            wide(1200, 7),
            big(2),
        ]);
        sets
    }

    #[test]
    fn the_product_tree_multiplies_and_carries() {
        for leaves in leaf_sets() {
            let levels = product_tree(&leaves);
            let want: BigUint = leaves.iter().product();
            assert_eq!(*tree_product(&leaves, &levels), want, "{leaves:?}");
            assert_eq!(levels.is_empty(), leaves.len() <= 1);
            let mut below: Vec<BigUint> = leaves.clone();
            for level in &levels {
                assert_eq!(level.len(), below.len().div_ceil(2));
                for (j, v) in level.iter().enumerate() {
                    let want: BigUint = below[2 * j..(2 * j + 2).min(below.len())].iter().product();
                    assert_eq!(*v, want);
                }
                below = level.clone();
            }
        }
    }

    #[test]
    fn the_remainders_agree_with_one_division_a_leaf() {
        let xs = [
            big(0),
            big(1),
            big(11),
            big(3).pow(5000) + 17u32,
            big(18446744073709551557).pow(3000),
        ];
        for leaves in leaf_sets() {
            let levels = product_tree(&leaves);
            for x in &xs {
                let want: Vec<BigUint> = leaves.iter().map(|m| x % m).collect();
                assert_eq!(
                    remainders(x, &leaves, &levels),
                    want,
                    "x {} {leaves:?}",
                    x.bits()
                );
            }
        }
    }

    #[test]
    fn the_cofactors_agree_with_division() {
        for leaves in leaf_sets() {
            let levels = product_tree(&leaves);
            let p: BigUint = leaves.iter().product();
            let want: Vec<BigUint> = leaves.iter().map(|m| (&p / m) % m).collect();
            assert_eq!(cofactors_mod_leaves(&leaves, &levels), want, "{leaves:?}");
        }
        // Borrowed leaves give the same as owned ones.
        let owned = [big(6), big(10), big(15), big(7)];
        let refs: Vec<&BigUint> = owned.iter().collect();
        let levels = product_tree(&refs);
        assert_eq!(
            cofactors_mod_leaves(&refs, &levels),
            cofactors_mod_leaves(&owned, &levels)
        );
    }
}

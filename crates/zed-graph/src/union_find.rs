//! Disjoint sets over the numbers `0..n` (union-find), written once for every crate.
//!
//! [`UnionFind`] links by rank and halves paths on each find (R. Tarjan and J. van Leeuwen,
//! "Worst-case analysis of set union algorithms", JACM 31(2), 245-281, 1984): m operations on n
//! elements take O(m α(m, n)) time, α the inverse of Ackermann's function. A caller that must
//! choose which root stays (because the root is a class's printed or ordered name) links with
//! [`UnionFind::union_into`] or [`UnionFind::union_least`]; with the root so chosen, path
//! halving alone bounds m ≥ n operations by O(m log_{1 + m/n} n), the same paper's bound for
//! halving with arbitrary linking.
//!
//! [`OffsetUnionFind`] keeps, beside each class, the difference between each element's value
//! and its root's in a group (integers under `+`): it records `x_a = x_b + d` and answers
//! `x_v - x_root`.
//!
//! Variants measured before this one was chosen (DRY-graph-shared, release build, 2,000,000
//! elements, 4,000,000 unions of random pairs then a find of each, best of 5, at load 30 and
//! 41 on 32 cores): halving with rank 158 and 242 ms; halving with size 335 and 448 ms;
//! halving with no rule (the shape of most of the inline copies this replaced) 461 and 593
//! ms; full compression in two passes with size 409 and 378 ms, with rank 523 and 316 ms,
//! with no rule 1,269 and 683 ms. A rank is one byte (ranks are at most log2 n ≤ 64), a size
//! a word, so the rank array is an eighth of the memory, which is the likely cause of its lead.

use std::ops::{Add, Sub};

/// Disjoint sets over `0..len()`.
#[derive(Clone, Debug, Default)]
pub struct UnionFind {
    /// Each element's parent; a root is its own parent.
    parent: Vec<usize>,
    /// Each root's rank, an upper bound on the height of its tree while only
    /// [`UnionFind::union`] links (at most log2 n, so a byte holds it); kept saturating, as a
    /// guide only, once a caller chooses roots.
    rank: Vec<u8>,
}

impl UnionFind {
    /// The `n` classes `{0}, …, {n - 1}`.
    pub fn new(n: usize) -> Self {
        UnionFind {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    /// The number of elements.
    pub fn len(&self) -> usize {
        self.parent.len()
    }

    /// Whether there is no element.
    pub fn is_empty(&self) -> bool {
        self.parent.is_empty()
    }

    /// Adds the element `len()` in a class of its own and returns it.
    pub fn push(&mut self) -> usize {
        let x = self.parent.len();
        self.parent.push(x);
        self.rank.push(0);
        x
    }

    /// The root of `x`'s class, halving the path from `x`: each element passed is pointed at
    /// its grandparent, with no stack and no allocation.
    pub fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            let up = self.parent[self.parent[x]];
            self.parent[x] = up;
            x = up;
        }
        x
    }

    /// The root of `x`'s class, changing nothing: O(height), for a caller holding the sets
    /// shared.
    pub fn find_shared(&self, mut x: usize) -> usize {
        while self.parent[x] != x {
            x = self.parent[x];
        }
        x
    }

    /// Whether `a` and `b` are in one class.
    pub fn same(&mut self, a: usize, b: usize) -> bool {
        self.find(a) == self.find(b)
    }

    /// Joins the classes of `a` and `b`, the root of lower rank under the other (on equal
    /// ranks, `b`'s under `a`'s); false when they were one class already.
    pub fn union(&mut self, a: usize, b: usize) -> bool {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return false;
        }
        if self.rank[ra] < self.rank[rb] {
            self.link(rb, ra);
        } else {
            self.link(ra, rb);
        }
        true
    }

    /// Joins the classes of `keep` and `other` with `keep`'s root as the root of the whole;
    /// false when they were one class already. For a caller whose class names are its roots.
    pub fn union_into(&mut self, keep: usize, other: usize) -> bool {
        let (rk, ro) = (self.find(keep), self.find(other));
        if rk == ro {
            return false;
        }
        self.link(rk, ro);
        true
    }

    /// Joins the classes of `a` and `b` with the lesser of their roots as the root, so that,
    /// when every union is by this rule, each class's root is its least element: the rule of
    /// callers that name a class by it. False when they were one class already.
    pub fn union_least(&mut self, a: usize, b: usize) -> bool {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return false;
        }
        self.link(ra.min(rb), ra.max(rb));
        true
    }

    /// Puts the root `child` under the root `root`, the new tree's height at most
    /// `max(height(root), height(child) + 1)`, which the rank follows (saturating at 255,
    /// reached only when roots are chosen, since rank-linked ranks stay under 64).
    fn link(&mut self, root: usize, child: usize) {
        self.parent[child] = root;
        let up = self.rank[child].saturating_add(1);
        if self.rank[root] < up {
            self.rank[root] = up;
        }
    }
}

/// Disjoint sets over `0..len()` with, for each element `v`, the difference `x_v - x_root`
/// between its value and its root's, in a group whose `+` and `-` are those of `&T` and whose
/// zero is `T::default()` (as the integers are).
#[derive(Clone, Debug)]
pub struct OffsetUnionFind<T> {
    parent: Vec<usize>,
    /// `x_v - x_parent(v)`; the zero at a root.
    off: Vec<T>,
}

impl<T> OffsetUnionFind<T>
where
    T: Clone + Default,
    for<'a> &'a T: Add<&'a T, Output = T> + Sub<&'a T, Output = T>,
{
    /// The `n` classes `{0}, …, {n - 1}`.
    pub fn new(n: usize) -> Self {
        OffsetUnionFind {
            parent: (0..n).collect(),
            off: vec![T::default(); n],
        }
    }

    /// The root of `v` and `x_v - x_root`, halving the path: each element passed is pointed
    /// at its grandparent, its offset summed with its parent's (`x_e - x_g = (x_e - x_p) +
    /// (x_p - x_g)`), with no stack and no allocation.
    // Complexity tradeoff: the copies this replaced (zedc-preimage holes.rs and loops.rs)
    // compressed the whole path, through a `Vec` of it allocated on every find; halving takes
    // the same amortized bound with the root chosen by the caller (O(m log_{1 + m/n} n) for
    // m ≥ n operations, Tarjan and van Leeuwen 1984, as `UnionFind`), with one sum per element
    // passed and no allocation beyond the sums.
    pub fn find(&mut self, v: usize) -> (usize, T) {
        let mut x = v;
        let mut acc = T::default();
        while self.parent[x] != x {
            let p = self.parent[x];
            let g = self.parent[p];
            if g != p {
                self.off[x] = &self.off[x] + &self.off[p];
                self.parent[x] = g;
            }
            acc = &acc + &self.off[x];
            x = g;
        }
        (x, acc)
    }

    /// Records `x_a = x_b + d`, the root of `b`'s class becoming the root of the whole:
    /// `Ok(())` when that joined two classes; `Err(c)` when `a` and `b` were in one class
    /// already, with `c` the difference `x_a - x_b` the class holds (equal to `d` exactly when
    /// the record agrees with it).
    pub fn union_into(&mut self, b: usize, a: usize, d: &T) -> Result<(), T> {
        let (ra, oa) = self.find(a);
        let (rb, ob) = self.find(b);
        if ra == rb {
            return Err(&oa - &ob);
        }
        // x_ra = x_a - oa = x_b + d - oa = x_rb + ob + d - oa.
        self.parent[ra] = rb;
        self.off[ra] = &(&ob + d) - &oa;
        Ok(())
    }
}

#[cfg(test)]
mod tests;

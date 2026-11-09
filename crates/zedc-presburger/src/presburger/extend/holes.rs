//! The holes of the clauses over one term (LOAD-bound-holes): a clause `x < 10 || x > 20`
//! says that `x` lies outside the hole `10..=20`, and the holes of the clauses over one atom
//! are kept as disjoint intervals in a persistent treap, so that a chain whose call moves such
//! a clause (`p{i}(x) = q(x: x) && p{i-1}(x: x + 3)`) adds one hole a link in O(log n), its
//! callee's holes read through the call's binding in O(1), and a point is checked against them
//! in O(log n), and not one clause a link read again at each link.
//!
//! The intervals are kept in a base coordinate `s = scale * y + shift` of the atom `y` they are
//! read over, so that reading them through a binding `y == c * z + d` changes the map alone.
//! Only the images of integers are ever asked, so each interval cut is widened by
//! `|scale| - 1` at each end, past no other image, and two holes adjacent over `y` meet.

use std::cmp::Ordering;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::Arc;

use super::{Atom, Con, Formula, Lin, Rel, Shared};
use zedc_int::int::Int;

/// A treap of disjoint intervals of the base coordinate, ordered by their lower ends, each
/// node's priority fixed by its ends so that one set of intervals has one shape whatever the
/// order they were cut in.
type Tree = Option<Arc<Node>>;

struct Node {
    lo: Int,
    hi: Int,
    prio: u64,
    size: usize,
    left: Tree,
    right: Tree,
}

/// A deterministic splitmix64 priority from an interval's ends.
fn prio_of(lo: &Int, hi: &Int) -> u64 {
    let mut h = DefaultHasher::new();
    lo.hash(&mut h);
    hi.hash(&mut h);
    let mut z = h.finish().wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn size(t: &Tree) -> usize {
    t.as_ref().map_or(0, |n| n.size)
}

/// The node of `lo..=hi` with the priority `prio` over `left` and `right`.
fn node(lo: Int, hi: Int, prio: u64, left: Tree, right: Tree) -> Tree {
    let size = size(&left) + size(&right) + 1;
    Some(Arc::new(Node {
        lo,
        hi,
        prio,
        size,
        left,
        right,
    }))
}

/// The intervals of `t` whose lower end is below `k`, and the others. O(log n) expected,
/// copying the path it walks.
fn split(t: &Tree, k: &Int) -> (Tree, Tree) {
    let Some(n) = t else {
        return (None, None);
    };
    let again = |left: Tree, right: Tree| node(n.lo.clone(), n.hi.clone(), n.prio, left, right);
    match n.lo < *k {
        true => {
            let (a, b) = split(&n.right, k);
            (again(n.left.clone(), a), b)
        }
        false => {
            let (a, b) = split(&n.left, k);
            (a, again(b, n.right.clone()))
        }
    }
}

/// The intervals of `a` and then of `b`, every one of `a` below every one of `b`. O(log n)
/// expected.
fn join(a: Tree, b: Tree) -> Tree {
    match (a, b) {
        (None, t) | (t, None) => t,
        (Some(x), Some(y)) => match x.prio >= y.prio {
            true => {
                let right = join(x.right.clone(), Some(y));
                node(x.lo.clone(), x.hi.clone(), x.prio, x.left.clone(), right)
            }
            false => {
                let left = join(Some(x), y.left.clone());
                node(y.lo.clone(), y.hi.clone(), y.prio, left, y.right.clone())
            }
        },
    }
}

/// The last interval of `t`.
fn last(t: &Tree) -> Option<&Node> {
    let mut n = t.as_deref()?;
    while let Some(r) = n.right.as_deref() {
        n = r;
    }
    Some(n)
}

/// The holes over one atom: intervals of integers it lies outside of.
// Complexity tradeoff: naive version, each clause `x < a || x > b` of a face kept as a
// disjunction, so a chain that moves a hole through n calls carries n disjunctions and is
// decided whole, O(n²) (0.39/1.62/7.06 s at 40/80/160 links). Used: the clauses over one atom
// kept as an ordered map of disjoint intervals, a persistent treap shared between faces,
// O(log n) a cut, read through each call's binding (0.032/0.098/0.198 s). Tradeoffs: one
// treap node per hole; the answers are main's, except that a link decided through the faces
// with nothing fixed (`Faces::free`) may answer where the conjunction decided whole is
// refused. Test `l01_38_presburger::one_scope::the_questions_of_a_chain_moving_a_hole_scale`;
// COMPLEXITY.md row LOAD-bound-holes.
#[derive(Clone)]
pub(super) struct Holes {
    tree: Tree,
    /// The base coordinate of a value `y` is `scale * y + shift`; `scale` is never 0.
    scale: Int,
    shift: Int,
}

impl Holes {
    pub(super) fn new() -> Holes {
        Holes {
            tree: None,
            scale: Int::ONE,
            shift: Int::ZERO,
        }
    }

    /// The number of disjoint intervals kept.
    pub(super) fn len(&self) -> usize {
        size(&self.tree)
    }

    /// The hole `lo..=hi` added, merged with those it meets or touches. O(log n) expected.
    pub(super) fn cut(&mut self, lo: &Int, hi: &Int) {
        if lo > hi {
            return;
        }
        let at = |y: &Int| &(&self.scale * y) + &self.shift;
        let (a, b) = (at(lo), at(hi));
        let (p, q) = match a <= b {
            true => (a, b),
            false => (b, a),
        };
        let wide = &self.scale.abs() - &Int::ONE;
        let (mut p, mut q) = (&p - &wide, &q + &wide);
        let (mut below, rest) = split(&self.tree, &p);
        if let Some(n) = last(&below)
            && n.hi >= &p - &Int::ONE
        {
            let l = n.lo.clone();
            q = q.max(n.hi.clone());
            below = split(&below, &l).0;
            p = l;
        }
        let (met, above) = split(&rest, &(&q + &Int::from(2)));
        if let Some(n) = last(&met) {
            q = q.max(n.hi.clone());
        }
        let prio = prio_of(&p, &q);
        let one = node(p, q, prio, None, None);
        self.tree = join(join(below, one), above);
    }

    /// Whether `y` lies in a hole. O(log n) expected.
    pub(super) fn holds(&self, y: &Int) -> bool {
        let s = &(&self.scale * y) + &self.shift;
        let mut t = self.tree.as_deref();
        while let Some(n) = t {
            t = match (s.cmp(&n.lo), s.cmp(&n.hi)) {
                (Ordering::Less, _) => n.left.as_deref(),
                (_, Ordering::Greater) => n.right.as_deref(),
                _ => return true,
            };
        }
        false
    }

    /// The holes read over `z` where `y == c * z + d`, `c` not 0. O(1): the tree is shared.
    pub(super) fn through(&self, c: &Int, d: &Int) -> Holes {
        Holes {
            tree: self.tree.clone(),
            scale: &self.scale * c,
            shift: &(&self.scale * d) + &self.shift,
        }
    }

    /// The holes as intervals of `y`, in increasing order, those adjacent joined. Time of the
    /// intervals.
    pub(super) fn intervals(&self) -> Vec<(Int, Int)> {
        let mut base: Vec<(&Int, &Int)> = Vec::with_capacity(self.len());
        let mut stack: Vec<&Node> = Vec::new();
        let mut t = self.tree.as_deref();
        while t.is_some() || !stack.is_empty() {
            while let Some(n) = t {
                stack.push(n);
                t = n.left.as_deref();
            }
            let n = stack.pop().expect("a node");
            base.push((&n.lo, &n.hi));
            t = n.right.as_deref();
        }
        let (c, d) = (&self.scale, &self.shift);
        // The values `y` with `p <= c * y + d <= q`.
        let ys = |p: &Int, q: &Int| match c.is_positive() {
            true => (-&(d - p).div_floor(c), (q - d).div_floor(c)),
            false => (-&(d - q).div_floor(c), (p - d).div_floor(c)),
        };
        let mut ranges: Vec<(Int, Int)> = (base.iter())
            .map(|&(p, q)| ys(p, q))
            .filter(|(lo, hi)| lo <= hi)
            .collect();
        if !c.is_positive() {
            ranges.reverse();
        }
        let mut out: Vec<(Int, Int)> = Vec::with_capacity(ranges.len());
        for (lo, hi) in ranges {
            match out.last_mut() {
                Some(prev) if lo <= &prev.1 + &Int::ONE => prev.1 = prev.1.clone().max(hi),
                _ => out.push((lo, hi)),
            }
        }
        out
    }

    /// The holes added to those of `other`, the smaller set cut into the larger. O(the smaller
    /// times log of the larger).
    pub(super) fn merged(self, other: Holes) -> Holes {
        let (mut big, small) = match self.len() >= other.len() {
            true => (self, other),
            false => (other, self),
        };
        for (lo, hi) in small.intervals() {
            big.cut(&lo, &hi);
        }
        big
    }

    /// The holes over `a` written as clauses, `a <= lo - 1 || a >= hi + 1` for each. Time of
    /// the holes.
    pub(super) fn clauses(&self, a: &Atom) -> Vec<Formula> {
        let y = Lin::atom(a.clone());
        (self.intervals().into_iter())
            .map(|(lo, hi)| {
                let below = Con::ge(&Lin::constant(&lo - &Int::ONE), &y);
                let above = Con::ge(&y, &Lin::constant(&hi + &Int::ONE));
                Formula::Or(Shared::new(vec![Formula::Con(below), Formula::Con(above)]))
            })
            .collect()
    }
}

/// The atom and hole of a clause over one atom whose disjuncts are inequalities, one or more
/// below and one or more above: `Some((a, None))` when they cover every value, so the clause
/// always holds. `None` for any other clause. Time of the clause.
pub(super) fn hole_of(f: &Formula) -> Option<(Atom, Option<(Int, Int)>)> {
    let Formula::Or(ds) = f else {
        return None;
    };
    let mut atom: Option<&Atom> = None;
    let (mut above, mut below): (Option<Int>, Option<Int>) = (None, None);
    for d in ds.iter() {
        let Formula::Con(c) = d else {
            return None;
        };
        let mut terms = c.lin.terms.iter();
        let (Rel::Ge, Some((a, k)), None) = (c.rel, terms.next(), terms.next()) else {
            return None;
        };
        if atom.is_some_and(|b| b != a) {
            return None;
        }
        atom = Some(a);
        let k0 = &c.lin.constant;
        // k·a + k0 >= 0.
        match k.is_positive() {
            // a >= ceil(-k0 / k).
            true => {
                let l = -&k0.div_floor(k);
                above = Some(above.map_or(l.clone(), |o| o.min(l)));
            }
            // a <= floor(k0 / -k).
            false => {
                let u = k0.div_floor(&-k);
                below = Some(below.map_or(u.clone(), |o| o.max(u)));
            }
        }
    }
    let (Some(a), Some(l), Some(u)) = (atom, above, below) else {
        return None;
    };
    let (lo, hi) = (&u + &Int::ONE, &l - &Int::ONE);
    Some((a.clone(), (lo <= hi).then_some((lo, hi))))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(v: i64) -> Int {
        Int::from(v)
    }

    /// The values in `-60..60` that lie in one of the intervals `cuts`.
    fn values(cuts: &[(i64, i64)]) -> Vec<i64> {
        (-60..60)
            .filter(|&y| cuts.iter().any(|&(lo, hi)| lo <= y && y <= hi))
            .collect()
    }

    #[test]
    fn holes_read_through_bindings_hold_where_the_cut_intervals_do() {
        let mut seed: u64 = 7;
        let mut next = |m: u64| {
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (seed >> 33) % m
        };
        for _ in 0..300 {
            let mut h = Holes::new();
            let mut cuts: Vec<(i64, i64)> = Vec::new();
            for _ in 0..1 + next(12) {
                if next(3) == 0 {
                    // A binding y == c' z + d'.
                    let c1 = [1, -1, 2, -3][next(4) as usize];
                    let d1 = next(9) as i64 - 4;
                    h = h.through(&int(c1), &int(d1));
                    cuts = cuts
                        .iter()
                        .flat_map(|&(lo, hi)| {
                            // The values z with lo <= c1 z + d1 <= hi, by brute force.
                            let zs: Vec<i64> = (-200..200)
                                .filter(|&z| lo <= c1 * z + d1 && c1 * z + d1 <= hi)
                                .collect();
                            zs.first().map(|&a| (a, *zs.last().expect("a value")))
                        })
                        .collect();
                } else {
                    let lo = next(80) as i64 - 40;
                    let hi = lo + next(9) as i64;
                    h.cut(&int(lo), &int(hi));
                    cuts.push((lo, hi));
                }
            }
            let want = values(&cuts);
            let got: Vec<i64> = (-60..60).filter(|&z| h.holds(&int(z))).collect();
            assert_eq!(got, want);
            let written: Vec<i64> = (-60..60)
                .filter(|&z| (h.intervals().iter()).any(|(lo, hi)| *lo <= int(z) && int(z) <= *hi))
                .collect();
            assert_eq!(written, want);
            // Merging gives the union, in either order.
            let mut o = Holes::new();
            o.cut(&int(-5), &int(5));
            let union: Vec<i64> = (-60..60)
                .filter(|&z| want.contains(&z) || (-5..=5).contains(&z))
                .collect();
            for m in [h.clone().merged(o.clone()), o.merged(h)] {
                let got: Vec<i64> = (-60..60).filter(|&z| m.holds(&int(z))).collect();
                assert_eq!(got, union);
            }
        }
    }

    #[test]
    fn overlapping_and_adjacent_holes_are_kept_as_one() {
        let mut h = Holes::new();
        for k in 0..100 {
            h.cut(&int(10 - 3 * k), &int(20 - 3 * k));
        }
        assert_eq!(h.len(), 1);
        assert_eq!(h.intervals(), vec![(int(-287), int(20))]);
        let mut h = Holes::new().through(&int(-2), &int(1));
        h.cut(&int(0), &int(0));
        h.cut(&int(1), &int(1));
        assert_eq!(h.len(), 1);
        assert_eq!(h.intervals(), vec![(int(0), int(1))]);
    }
}

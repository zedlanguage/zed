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
use std::sync::Arc;

use super::{Atom, Con, Formula, Lin, Rel, Shared};
use zed_collections::priority::Priorities;
use zedc_int::int::Int;

/// A treap of disjoint intervals of the base coordinate, ordered by their lower ends, each
/// node's priority drawn once per run from its ends ([`prio_of`]), so that in a run one set of
/// intervals has one shape whatever the order they were cut in.
type Tree = Option<Arc<Node>>;

struct Node {
    lo: Int,
    hi: Int,
    prio: u64,
    size: usize,
    left: Tree,
    right: Tree,
}

/// The priorities of the holes, drawn once per run ([`zed_collections::priority`]).
static PRIORITIES: Priorities = Priorities::new(8);

/// The priority of the interval `lo..=hi` of the base coordinate: the run's random polynomial
/// of degree 4 at a random polynomial hash of its ends ([`Priorities::hash`]; `Int`'s stream is
/// one-to-one, so distinct intervals have distinct streams and tie with probability at most
/// `(S + 1)/p` a pair for streams of `S` symbols). The priorities are otherwise 5-wise
/// independent and uniform, and every node's depth is `O(log n)` in expectation for every set
/// of holes (Seidel and Aragon, "Randomized search trees", Algorithmica 16, 1996,
/// doi:10.1007/BF01940876, Theorem 3.3 and section 6; the full comment and the proof are in
/// module [`zed_collections::priority`]), where the fixed hash this replaces had no bound for chosen
/// intervals (COMPLEXITY.md K123). The shape is never shown: the tree is a private field of
/// [`Holes`], and each of its reads gives one answer for every tree over the same intervals:
/// `len` is a size, `holds` a search by key, `intervals` an in-order walk (which `merged` and
/// `clauses` read), and `cut` splits and joins by key, so the intervals it leaves depend only
/// on the intervals it was given. So the priorities choose the cost alone.
fn prio_of(lo: &Int, hi: &Int) -> u64 {
    PRIORITIES.hash(&(lo, hi))
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
// refused. Test `l01_38_omega_test::one_scope::the_questions_of_a_chain_moving_a_hole_scale`;
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
    ///
    /// Proof that the widening adds no value: the values `y` are seen only through their
    /// images `s * y + shift`, `s` the scale now, which are `|s|` apart, so the images next to
    /// `[p, q]`, the images of `lo..=hi`, are `p - |s|` and `q + |s|`, outside `[p - |s| + 1,
    /// q + |s| - 1]`. A later [`Holes::through`] reads `y == c * z + d`, whose images `s * (c *
    /// z + d) + shift` are images of the `y == c * z + d`, so the widened interval holds no
    /// image of any later coordinate that is not an image of `lo..=hi`. The merges join two
    /// intervals of the base coordinate that overlap or touch (`n.hi >= p - 1`, and the lower
    /// ends up to `q + 1`), whose union is one interval of integers, so they keep the set of
    /// base integers held. Hence `holds` is true of a value exactly where some cut, read in
    /// the coordinate it was made in, holds it.
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

    /// The holes of the runs `runs` of a call node's set (`HoleSet::runs`, sorted and
    /// disjoint), read over the node's term itself: scale 1, shift 0 (LOAD-call-disj-spread,
    /// META3 H7). Read over the one atom `a` of a term `k * a + e` through
    /// [`Holes::through`]`(k, e)`. O(n log n) expected for n runs, made once a set
    /// (`Faces::leaf` keeps it).
    pub(super) fn of_runs(runs: &[(Int, Int)]) -> Holes {
        let mut h = Holes::new();
        for (lo, hi) in runs {
            h.cut(lo, hi);
        }
        h
    }

    /// The holes added to those of `other`, the smaller set cut into the larger. O(the smaller
    /// times log of the larger), and O(1) when both are one tree read through one map.
    ///
    /// The second case, a set merged with itself, is the call node read at each link of a
    /// chain: its holes are in the face of the link before and in the link's own node, over
    /// one tree (`Faces::leaf` reads one tree a set) through one binding. A union of a set with
    /// itself is the set, so `self` is returned unchanged (design-b22-load5.md section 2, Cost:
    /// "a merge of two leaves of the same payload and the same total binding is idempotent and
    /// skips the walk", Codex C4); without it each link cut the n runs again, Θ(n log n) a link.
    /// Counted (`counts::HOLES_SAME`).
    pub(super) fn merged(self, other: Holes) -> Holes {
        if self.same(&other) {
            super::counts::add(super::counts::HOLES_SAME, 1);
            return self;
        }
        let (mut big, small) = match self.len() >= other.len() {
            true => (self, other),
            false => (other, self),
        };
        super::counts::add(super::counts::HOLES_MERGED_RUNS, small.len());
        for (lo, hi) in small.intervals() {
            big.cut(&lo, &hi);
        }
        big
    }

    /// Whether `self` and `other` are one tree read through one map, so that they hold the
    /// same values. O(1) but for the two maps' bit lengths. Not equality of the sets: two trees
    /// built apart over the same intervals are not the same here.
    pub(super) fn same(&self, other: &Holes) -> bool {
        let one = match (&self.tree, &other.tree) {
            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
            (None, None) => true,
            _ => false,
        };
        one && self.scale == other.scale && self.shift == other.shift
    }

    /// The holes over `a` written as clauses, `a <= lo - 1 || a >= hi + 1` for each, counted
    /// (`counts::HOLES_WRITTEN`, the clause emissions of the hole route, META3 H7). Time of the
    /// holes.
    pub(super) fn clauses(&self, a: &Atom) -> Vec<Formula> {
        super::counts::add(super::counts::HOLES_WRITTEN, self.len());
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
        let mut rng = crate::seed::Rng::new(7);
        for _ in 0..300 {
            let mut h = Holes::new();
            let mut cuts: Vec<(i64, i64)> = Vec::new();
            for _ in 0..1 + rng.below(12) {
                if rng.below(3) == 0 {
                    // A binding y == c' z + d'.
                    let c1 = rng.pick(&[1_i64, -1, 2, -3]);
                    let d1 = rng.int(-4, 4);
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
                    let lo = rng.int(-40, 39);
                    let hi = lo + rng.int(0, 8);
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

    /// `Holes::merged` of one tree with itself through one map is the set unchanged, taken
    /// without a walk (`counts::HOLES_SAME`); the same intervals built apart, or one tree read
    /// through another map, are merged by the walk and give the union.
    #[test]
    fn holes_merged_with_themselves_are_taken_whole() {
        let runs: Vec<(Int, Int)> = (0..20).map(|j| (int(3 * j), int(3 * j + 1))).collect();
        let h = Holes::of_runs(&runs);
        super::super::counts::take();
        let m = h.clone().merged(h.clone());
        assert_eq!(
            super::super::counts::take()[super::super::counts::HOLES_SAME],
            1
        );
        assert!(m.same(&h));
        assert_eq!(m.intervals(), h.intervals());
        let apart = Holes::of_runs(&runs);
        assert!(!apart.same(&h));
        assert_eq!(h.clone().merged(apart).intervals(), h.intervals());
        let shifted = h.through(&int(1), &int(1));
        assert!(!shifted.same(&h));
        let want = values(&[(-1, 1)]);
        let both = h.clone().merged(shifted);
        let got: Vec<i64> = (-1..2).filter(|&z| both.holds(&int(z))).collect();
        assert_eq!(got, want);
        assert_eq!(
            super::super::counts::take()[super::super::counts::HOLES_SAME],
            0
        );
    }
}

//! The numbers whose primes divide the coefficients of a product the checker sizes, and the
//! proofs that two such coefficients share no factor (plan row CONST-too-large-coprime-base).
//!
//! `Ck::least_built` proves a least size for `x * y` and `x / y` only where the kernel cancels
//! nothing: the parts a reduction divides by their gcd share no factor, and no prime one
//! operand keeps as a power divides a part of the other. Each coefficient carries a set of
//! numbers the text fixes, its roots, such that every prime of the coefficient divides one of
//! them: `rat(b) ^ (2^60)` has the root `b`, and `rat(b) ^ (2^59) * (rat(c) ^ (2^59))` the
//! roots `b` and `c`. Two coefficients share no factor where no root of one shares a prime
//! with a root of the other.
//!
//! Where both sides are one number, that is one gcd, decided at once. Where a side is a set
//! made by products, the check waits for the end of the walk ([`Roots::settle`]), which builds
//! one coprime base of every root (Bernstein, "Factoring into coprimes in essentially linear
//! time", J. Algorithms 54, 2005): pairwise coprime numbers such that each root is, up to
//! exponents, a product of some of them. Two sets then share a prime exactly when the base
//! elements of their roots meet, a set lookup per element.
//!
//! This file calls nothing of the walk, as `check/limits.rs` does not (step S.1f).

use std::collections::HashMap;
use std::rc::Rc;

use imbl::OrdSet;
use num_bigint::BigUint;
use zed_kernel::num::{gcd_uint, mul_uint, rem_uint};

/// A set of roots: an index into [`Roots::sets`].
pub(super) type SetId = u32;

/// A proof that some sets of roots are pairwise coprime: an index into [`Roots::proofs`].
pub(super) type ProofId = u32;

/// The set of no roots, of a coefficient of magnitude 1.
pub(super) const EMPTY: SetId = 0;

/// A set of roots as the walk builds it: one number, or the union of two sets.
enum Set {
    Empty,
    Leaf(u32),
    Union(SetId, SetId),
}

/// What a product's least size rests on beyond what the walk decided: the proofs of its
/// operands, and the pairs of sets of roots that must share no prime.
struct Proof {
    needs: [Option<ProofId>; 2],
    checks: Vec<(SetId, SetId)>,
}

/// The roots the walk met, the sets it built of them, and the proofs left to the end of the
/// walk. Append-only: a repair tried and undone leaves its sets, which nothing then reads.
pub(super) struct Roots {
    /// Each distinct root, a number above 1, by its index.
    values: Vec<Rc<BigUint>>,
    /// The set of each root, by value, so that a number the text writes twice is one root.
    index: HashMap<Rc<BigUint>, SetId>,
    sets: Vec<Set>,
    proofs: Vec<Proof>,
}

impl Default for Roots {
    fn default() -> Roots {
        Roots {
            values: Vec::new(),
            index: HashMap::new(),
            sets: vec![Set::Empty],
            proofs: Vec::new(),
        }
    }
}

impl Roots {
    /// The set of the one root `v`, above 0; [`EMPTY`] for 1, which has no prime. A coefficient
    /// 0, which every prime divides, has no root. A number met again gives the same set, so
    /// that a product of two coefficients with the one root `b` has that root, not a union.
    pub(super) fn leaf(&mut self, v: BigUint) -> SetId {
        debug_assert!(v.bits() != 0, "a root is above 0");
        if v.bits() == 1 {
            return EMPTY;
        }
        let v = Rc::new(v);
        if let Some(&set) = self.index.get(&v) {
            return set;
        }
        let at = self.values.len() as u32;
        let set = self.push_set(Set::Leaf(at));
        self.values.push(v.clone());
        self.index.insert(v, set);
        set
    }

    /// The set holding the roots of `a` and of `b`: O(1), a node over the two.
    pub(super) fn union(&mut self, a: SetId, b: SetId) -> SetId {
        match (a, b) {
            (EMPTY, s) | (s, EMPTY) => s,
            _ if a == b => a,
            _ => self.push_set(Set::Union(a, b)),
        }
    }

    fn push_set(&mut self, s: Set) -> SetId {
        self.sets.push(s);
        (self.sets.len() - 1) as SetId
    }

    /// Whether no root of `a` shares a prime with a root of `b`, where that is decided now:
    /// either is empty, or both are one number, by one gcd (the half gcd, O(M(b) log b) in
    /// their bits `b`). `None` where a side is a union, left to [`Self::settle`].
    pub(super) fn coprime_now(&self, a: SetId, b: SetId) -> Option<bool> {
        match (&self.sets[a as usize], &self.sets[b as usize]) {
            (Set::Empty, _) | (_, Set::Empty) => Some(true),
            (Set::Leaf(x), Set::Leaf(y)) => Some(
                gcd_uint(&self.values[*x as usize], &self.values[*y as usize]).bits() == 1,
            ),
            _ => None,
        }
    }

    /// The proof that the operands' proofs `needs` hold and each pair of `checks` shares no
    /// prime; `None`, proved outright, where there is nothing to prove, and the one operand's
    /// proof where it is all there is.
    pub(super) fn proof(
        &mut self,
        needs: [Option<ProofId>; 2],
        checks: Vec<(SetId, SetId)>,
    ) -> Option<ProofId> {
        if checks.is_empty() {
            match needs {
                [None, n] | [n, None] => return n,
                [Some(a), Some(b)] if a == b => return Some(a),
                _ => {}
            }
        }
        self.proofs.push(Proof { needs, checks });
        Some((self.proofs.len() - 1) as ProofId)
    }

    /// Whether each proof holds, by its index, read once the walk has made every proof.
    ///
    /// Complexity tradeoff: the naive method tests each pair of sets by the gcd of the
    /// products of their roots, or each root of one against each of the other, which for a
    /// chain of `n` products, each checking a new factor against all before it, is O(n^2)
    /// gcds, or gcds of O(n)-word numbers at each of the `n` steps; a coprime base kept as the
    /// walk goes splits each new root against every base element, O(n) gcds a root and O(n^2)
    /// in all. Used: the base is built once, over every root ([`base_of`]); each set is then
    /// the set of its roots' base elements, a persistent ordered set (`imbl::OrdSet`) made from
    /// its two halves by inserting the smaller into a copy of the larger, O(1) to copy and
    /// O(s log n) for `s` inserted; each check looks the smaller set's elements up in the
    /// larger, O(s log n). An expression tree of `n` products moves each element O(log n)
    /// times, so O(n log^2 n) lookups and no gcd past the base. What it gives up: a value read
    /// by many products, as `y = x * x0` repeated with one `x0` of `r` roots, costs `r`
    /// lookups at each, the work of the smaller operand each time; no method is known that
    /// decides, for every node of a DAG, whether two of its reachable sets meet in less.
    pub(super) fn settle(&self) -> Vec<bool> {
        let base = base_of(&self.values);
        let mut sets: Vec<OrdSet<u32>> = Vec::with_capacity(self.sets.len());
        for s in &self.sets {
            let made = match s {
                Set::Empty => OrdSet::new(),
                Set::Leaf(r) => base[*r as usize].iter().copied().collect(),
                Set::Union(a, b) => {
                    let (a, b) = (&sets[*a as usize], &sets[*b as usize]);
                    let (big, small) = if a.len() >= b.len() { (a, b) } else { (b, a) };
                    let mut u = big.clone();
                    u.extend(small.iter().copied());
                    u
                }
            };
            sets.push(made);
        }
        let disjoint = |a: SetId, b: SetId| {
            let (a, b) = (&sets[a as usize], &sets[b as usize]);
            let (big, small) = if a.len() >= b.len() { (a, b) } else { (b, a) };
            !small.iter().any(|e| big.contains(e))
        };
        let mut holds: Vec<bool> = Vec::with_capacity(self.proofs.len());
        for p in &self.proofs {
            let h = p.needs.iter().flatten().all(|n| holds[*n as usize])
                && p.checks.iter().all(|&(a, b)| disjoint(a, b));
            holds.push(h);
        }
        holds
    }
}

/// For each root of `roots`, distinct numbers above 1, the indices of the elements of a coprime
/// base it is a product of: pairwise coprime numbers, each of whose primes divide exactly the
/// same roots, so that two roots share a prime exactly when their lists meet.
///
/// Complexity tradeoff: the naive method refines the base one root at a time, splitting each
/// against every element that shares a factor with it (factor refinement, Bach, Driscoll and
/// Shallit, "Factor refinement", J. Algorithms 15, 1993), O(n) gcds a root and O(n^2) in all.
/// Used: first, which roots share a prime with any other, by Bernstein's product and remainder
/// trees (D. J. Bernstein, "How to find smooth parts of integers", 2004, the batch gcd): with
/// `P` the product of all roots, a root `r` shares none exactly when `gcd(r, (P mod r^2) / r)`
/// is 1. The tree costs O(M(N) log n) for `n` roots of `N` bits in all (`mul_uint`, by
/// transforms past 512 words; `rem_uint`, O(M) by Newton's reciprocal), plus one gcd a root.
/// Each root that shares none is its own element. Only the `m` roots that share a prime with
/// another go through factor refinement, O(m e) gcds for `e` elements, since each prime they
/// share is at least in two of them. Bernstein's coprime base ("Factoring into coprimes in
/// essentially linear time", J. Algorithms 54, 2005, `cbmerge`) would make that part
/// O(M(N) log^k N) too; roots of a program that share primes are few, as `b` and `b * b`.
fn base_of(roots: &[Rc<BigUint>]) -> Vec<Vec<u32>> {
    if roots.is_empty() {
        return Vec::new();
    }
    // The product tree, leaves first; an odd node out is carried up.
    let mut levels: Vec<Vec<BigUint>> = vec![roots.iter().map(|r| (**r).clone()).collect()];
    while let Some(top) = levels.last().filter(|l| l.len() > 1) {
        let up = (top.chunks(2))
            .map(|c| match c {
                [a, b] => mul_uint(a, b),
                [a] => a.clone(),
                _ => unreachable!("chunks of 2"),
            })
            .collect();
        levels.push(up);
    }
    // The remainder tree: each node's `P mod node^2`, from its parent's, as `node^2` divides
    // the parent's square.
    let mut rems = levels.pop().expect("one level at least");
    for level in levels.iter().rev() {
        rems = (level.iter().enumerate())
            .map(|(i, p)| rem_uint(&rems[i / 2], &mul_uint(p, p)))
            .collect();
    }
    let mut base: Vec<Vec<u32>> = vec![Vec::new(); roots.len()];
    let mut next = 0u32;
    let mut shared: Vec<usize> = Vec::new();
    for (i, r) in roots.iter().enumerate() {
        // `P mod r^2` is `r * ((P / r) mod r)`.
        let rest = rems[i].clone() / &**r;
        if gcd_uint(r, &rest).bits() == 1 {
            base[i].push(next);
            next += 1;
        } else {
            shared.push(i);
        }
    }
    // Factor refinement of the roots that share a prime: each number met is split by its gcd
    // with the element it shares a factor with, until the elements are pairwise coprime; the
    // product of all numbers held falls by that gcd at each split, so it ends.
    let mut elements: Vec<BigUint> = Vec::new();
    for &i in &shared {
        let mut work = vec![(*roots[i]).clone()];
        while let Some(y) = work.pop() {
            if y.bits() <= 1 {
                continue;
            }
            let met = (elements.iter())
                .map(|q| gcd_uint(&y, q))
                .enumerate()
                .find(|(_, g)| g.bits() > 1);
            match met {
                None => elements.push(y),
                Some((at, g)) => {
                    let q = elements.swap_remove(at);
                    work.push(&q / &g);
                    work.push(&y / &g);
                    work.push(g);
                }
            }
        }
    }
    // Each root that shares a prime is, up to exponents, the product of the elements it meets.
    for &i in &shared {
        for (k, q) in elements.iter().enumerate() {
            if gcd_uint(&roots[i], q).bits() > 1 {
                base[i].push(next + k as u32);
            }
        }
    }
    base
}

#[cfg(test)]
mod tests {
    use super::*;

    fn roots(ns: &[u64]) -> Vec<Rc<BigUint>> {
        ns.iter().map(|&n| Rc::new(BigUint::from(n))).collect()
    }

    /// Two roots share a prime exactly when their base lists meet.
    fn agrees(ns: &[u64]) {
        let base = base_of(&roots(ns));
        for (i, a) in ns.iter().enumerate() {
            for (j, b) in ns.iter().enumerate() {
                let share = gcd_uint(&BigUint::from(*a), &BigUint::from(*b)).bits() > 1;
                let meet = base[i].iter().any(|e| base[j].contains(e));
                assert_eq!(share, meet, "{a} and {b} in {ns:?}: {base:?}");
            }
        }
    }

    #[test]
    fn a_coprime_base_meets_where_the_roots_share_a_prime() {
        agrees(&[7]);
        agrees(&[6, 35]);
        agrees(&[6, 10, 35]);
        agrees(&[12, 18, 5, 49, 77]);
        agrees(&[4, 8, 16, 3]);
        agrees(&[30, 42, 70, 105, 11, 13 * 17, 17 * 19]);
        // Primes past one word, as the roots of `rat(b) ^ (2^60)` are.
        let p = 18446744073709551557u64; // the largest prime below 2^64
        let big = |m: u64| Rc::new(BigUint::from(p) * BigUint::from(m));
        let rs = vec![big(3), big(5), Rc::new(BigUint::from(15u8))];
        let base = base_of(&rs);
        assert!(base[0].iter().any(|e| base[1].contains(e)));
        assert!(base[0].iter().any(|e| base[2].contains(e)));
    }

    #[test]
    fn a_union_proves_what_its_roots_prove() {
        let mut r = Roots::default();
        let (a, b, c, d) = (
            r.leaf(BigUint::from(6u8)),
            r.leaf(BigUint::from(35u8)),
            r.leaf(BigUint::from(11u8)),
            r.leaf(BigUint::from(10u8)),
        );
        let ab = r.union(a, b);
        let free = r.proof([None, None], vec![(ab, c)]);
        let meets = r.proof([None, None], vec![(ab, d)]);
        let both = r.proof([free, None], vec![(c, a)]);
        let held = r.settle();
        assert!(held[free.unwrap() as usize]);
        assert!(!held[meets.unwrap() as usize]);
        assert!(held[both.unwrap() as usize]);
        assert_eq!(r.coprime_now(a, b), Some(false));
        assert_eq!(r.coprime_now(a, c), Some(true));
        assert_eq!(r.coprime_now(ab, c), None);
    }
}

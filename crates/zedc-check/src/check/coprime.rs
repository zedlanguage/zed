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
            (Set::Leaf(x), Set::Leaf(y)) => {
                Some(gcd_uint(&self.values[*x as usize], &self.values[*y as usize]).bits() == 1)
            }
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
    /// O(s log n) for `s` inserted. A check of two sets costs the least of: the smaller set's
    /// elements looked up in the larger, O(s log n); where a check of one set against the
    /// larger half of the other was made before, its answer and the smaller half against the
    /// one set; where one of the two larger halves was, its answer and both smaller halves.
    /// So no check costs more than the lookups, an expression tree of `n` products moves each
    /// element O(log n) times, O(n log^2 n) lookups and no gcd past the base, and a chain
    /// `z = z / rat(q)` whose every link meets one fixed set `x`, as `y = x * z` at each link,
    /// costs O(log n) a link, where the lookups alone cost the link's length, O(n^2) in all.
    /// What it gives up: a set checked against many sets none of which was checked against a
    /// part of it, as `x * z_i` for `n` unrelated `z_i` of `r` roots each, costs `r` lookups
    /// at each; no method is known that decides, for every pair of nodes of a DAG, whether
    /// their reachable sets meet in less.
    pub(super) fn settle(&self) -> Vec<bool> {
        let base = base_of(&self.values);
        let mut sets: Vec<OrdSet<u32>> = Vec::with_capacity(self.sets.len());
        // For a union, the half whose set it extends and the other half.
        let mut halves: Vec<Option<(SetId, SetId)>> = Vec::with_capacity(self.sets.len());
        for s in &self.sets {
            let (made, split) = match s {
                Set::Empty => (OrdSet::new(), None),
                Set::Leaf(r) => (base[*r as usize].iter().copied().collect(), None),
                Set::Union(a, b) => {
                    let (a, b) = match sets[*a as usize].len() >= sets[*b as usize].len() {
                        true => (*a, *b),
                        false => (*b, *a),
                    };
                    let mut u = sets[a as usize].clone();
                    u.extend(sets[b as usize].iter().copied());
                    (u, Some((a, b)))
                }
            };
            sets.push(made);
            halves.push(split);
        }
        let mut checked: HashMap<(SetId, SetId), bool> = HashMap::new();
        let mut holds: Vec<bool> = Vec::with_capacity(self.proofs.len());
        for p in &self.proofs {
            let h = p.needs.iter().flatten().all(|n| holds[*n as usize])
                && (p.checks.iter()).all(|&(a, b)| disjoint(&sets, &halves, &mut checked, a, b));
            holds.push(h);
        }
        holds
    }
}

/// A way [`disjoint`] can decide a check: the lookups it costs, the answer of the check made
/// before that it rests on, if any, and the pairs of sets it looks up.
type Way = (usize, Option<bool>, Vec<(SetId, SetId)>);

/// Whether the sets `a` and `b` share no element, by the least of the ways of
/// [`Roots::settle`], the answer kept in `checked` by the pair.
fn disjoint(
    sets: &[OrdSet<u32>],
    halves: &[Option<(SetId, SetId)>],
    checked: &mut HashMap<(SetId, SetId), bool>,
    a: SetId,
    b: SetId,
) -> bool {
    let pair = |a: SetId, b: SetId| (a.min(b), a.max(b));
    if let Some(&known) = checked.get(&pair(a, b)) {
        return known;
    }
    let size = |s: SetId| sets[s as usize].len();
    // The lookups that test `s` against `t`, and their answer.
    let cost = |s: SetId, t: SetId| size(s).min(size(t));
    let free = |s: SetId, t: SetId| {
        let (s, t) = (&sets[s as usize], &sets[t as usize]);
        let (big, small) = if s.len() >= t.len() { (s, t) } else { (t, s) };
        !small.iter().any(|e| big.contains(e))
    };
    let mut ways: Vec<Way> = vec![(cost(a, b), None, vec![(a, b)])];
    for (x, y) in [(a, b), (b, a)] {
        if let Some((big, small)) = halves[y as usize]
            && let Some(&known) = checked.get(&pair(x, big))
        {
            ways.push((cost(x, small), Some(known), vec![(x, small)]));
        }
    }
    if let (Some((ab, asm)), Some((bb, bsm))) = (halves[a as usize], halves[b as usize])
        && let Some(&known) = checked.get(&pair(ab, bb))
    {
        ways.push((
            cost(asm, b) + cost(bsm, a),
            Some(known),
            vec![(asm, b), (bsm, a)],
        ));
    }
    // A check made before that found a shared element decides at once.
    let (_, before, rest) = (ways.into_iter())
        .min_by_key(|(n, before, _)| match before {
            Some(false) => 0,
            _ => n + 1,
        })
        .expect("the lookups are one way");
    let known = before != Some(false) && rest.iter().all(|&(s, t)| free(s, t));
    checked.insert(pair(a, b), known);
    known
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
        assert_eq!(r.coprime_now(a, b), Some(true));
        assert_eq!(r.coprime_now(a, d), Some(false));
        assert_eq!(r.coprime_now(a, c), Some(true));
        assert_eq!(r.coprime_now(ab, c), None);
    }

    /// Each check of a chain against a fixed set, and of two chains in step, gives what a
    /// direct test of the roots gives, whichever way `settle` takes.
    #[test]
    fn a_check_reusing_one_made_before_agrees_with_the_roots() {
        let mut r = Roots::default();
        let chain = |r: &mut Roots, ns: &[u64]| -> Vec<(SetId, Vec<u64>)> {
            let mut out: Vec<(SetId, Vec<u64>)> = Vec::new();
            for &n in ns {
                let leaf = r.leaf(BigUint::from(n));
                let (set, mut had) = match out.last() {
                    Some((s, had)) => (r.union(*s, leaf), had.clone()),
                    None => (leaf, Vec::new()),
                };
                had.push(n);
                out.push((set, had));
            }
            out
        };
        // `x` of the odd primes to 13; `z` of the next six, then 15, which meets `x`, then two
        // more; `w` of 2, 4 and 8 in step with `z`.
        let x = chain(&mut r, &[3, 5, 7, 11, 13]);
        let z = chain(&mut r, &[17, 19, 23, 29, 31, 37, 15, 41, 43]);
        let w = chain(&mut r, &[2, 4, 8, 2, 4, 8, 2, 4, 8]);
        let (xs, xr) = x.last().unwrap().clone();
        let mut want = Vec::new();
        let mut ids = Vec::new();
        for (i, (zs, zr)) in z.iter().enumerate() {
            let (ws, wr) = &w[i];
            for (a, ar, b, br) in [(xs, &xr, *zs, zr), (*ws, wr, *zs, zr)] {
                let share = ar.iter().any(|m| {
                    br.iter()
                        .any(|n| gcd_uint(&BigUint::from(*m), &BigUint::from(*n)).bits() > 1)
                });
                ids.push(r.proof([None, None], vec![(a, b)]));
                want.push(!share);
            }
        }
        let held = r.settle();
        let got: Vec<bool> = ids.iter().map(|p| held[p.unwrap() as usize]).collect();
        assert_eq!(got, want);
        // `x` against `z` holds for the six links before 15 and fails from it on.
        assert_eq!(want.iter().step_by(2).filter(|h| **h).count(), 6);
    }

    #[test]
    fn the_short_cases_add_no_set_and_no_proof() {
        let mut r = Roots::default();
        // No root and no proof: nothing to settle.
        assert!(r.settle().is_empty());
        assert_eq!(r.leaf(BigUint::from(1u8)), EMPTY);
        let a = r.leaf(BigUint::from(6u8));
        assert_eq!(r.leaf(BigUint::from(6u8)), a);
        assert_eq!(r.union(EMPTY, a), a);
        assert_eq!(r.union(a, EMPTY), a);
        assert_eq!(r.union(a, a), a);
        assert_eq!(r.coprime_now(EMPTY, a), Some(true));
        assert_eq!(r.proof([None, None], Vec::new()), None);
        let p = r.proof([None, None], vec![(a, a)]);
        assert_eq!(r.proof([p, None], Vec::new()), p);
        assert_eq!(r.proof([None, p], Vec::new()), p);
        assert_eq!(r.proof([p, p], Vec::new()), p);
        // Two proofs and no check is a new proof, and fails where a need fails.
        let q = r.proof([None, None], vec![(a, EMPTY)]);
        let pq = r.proof([p, q], Vec::new());
        assert!(pq != p && pq != q);
        let held = r.settle();
        assert_eq!(held.len(), 3);
        assert!(!held[p.unwrap() as usize]);
        assert!(held[q.unwrap() as usize]);
        assert!(!held[pq.unwrap() as usize]);
    }
}

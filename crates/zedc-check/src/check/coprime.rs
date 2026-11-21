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
//! time", J. Algorithms 54(1), 2005, pp. 1-30, doi:10.1016/j.jalgor.2004.04.009; see
//! [`coprime_base`] for the sections used): pairwise coprime numbers such that each root is, up to
//! exponents, a product of some of them. Two sets then share a prime exactly when the base
//! elements of their roots meet, a set lookup per element.
//!
//! This file calls nothing of the walk, as `check/limits.rs` does not (step S.1f).

use std::collections::HashMap;
use std::rc::Rc;

use imbl::OrdSet;
use num_bigint::BigUint;
use zed_collections::index::to_u32;
use zed_kernel::num::coprime::coprime_base;
use zed_kernel::num::gcd_uint;

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
        let at = to_u32(self.values.len(), "values");
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
    /// Plan row CONST-coprime-check-many-sets: many unions from one pool checked against one
    /// set, as `x * (u_i * v_j)` for `k` sets `u_i` and `k` sets `v_j` of `r` roots each, cost
    /// `r` lookups at each of the `k^2` checks, O(k^2 r). Used: a check of one set against
    /// each half of the other, a half not checked before by lookups, keeps the answer of each
    /// half; where a half is shared (a half of two unions or more, or in two checks), that way
    /// counts half its lookups and wins a tie, so it costs at most twice the cheapest way and
    /// each later check through that half finds it kept; and a union is built only when a check
    /// looks it up ([`Sets`]), so the `k^2` unions whose halves were each checked before are
    /// never built: O(k r log n + k^2) for the family, measured in `bench::too_large`. What it
    /// gives up: deciding every pair `(u_i, v_j)` of two pools
    /// for a shared element is Boolean matrix multiplication, with no known combinatorial
    /// method below O(k^2 r / polylog); only the part repeated against one set is saved, and a
    /// set checked against many unrelated sets, as `x * z_i` for `n` `z_i` sharing no part,
    /// still costs `r` lookups at each.
    pub(super) fn settle(&self) -> Vec<bool> {
        self.settle_with(&base_of(&self.values))
    }

    /// [`Roots::settle`] with `base`, the base of the roots.
    fn settle_with(&self, base: &[Vec<u32>]) -> Vec<bool> {
        let mut sets = Sets {
            defs: &self.sets,
            base,
            made: vec![None; self.sets.len()],
            size: Vec::with_capacity(self.sets.len()),
        };
        // For a union, the half of the larger size and the other half.
        let mut halves: Vec<Option<(SetId, SetId)>> = Vec::with_capacity(self.sets.len());
        for s in &self.sets {
            let (size, split) = match s {
                Set::Empty => (0, None),
                Set::Leaf(r) => (base[*r as usize].len(), None),
                Set::Union(a, b) => {
                    let (a, b) = match sets.size[*a as usize] >= sets.size[*b as usize] {
                        true => (*a, *b),
                        false => (*b, *a),
                    };
                    let size = sets.size[a as usize].saturating_add(sets.size[b as usize]);
                    (size, Some((a, b)))
                }
            };
            sets.size.push(size);
            halves.push(split);
        }
        // The sets a later check may ask about again: a half of two unions or more, or in two
        // checks.
        let mut uses: Vec<u8> = vec![0; self.sets.len()];
        let mut used = |s: SetId| uses[s as usize] = uses[s as usize].saturating_add(1);
        for s in &self.sets {
            if let Set::Union(a, b) = s {
                used(*a);
                used(*b);
            }
        }
        for &(a, b) in self.proofs.iter().flat_map(|p| &p.checks) {
            used(a);
            used(b);
        }
        let shared: Vec<bool> = uses.iter().map(|&n| n >= 2).collect();
        let mut checked: HashMap<(SetId, SetId), bool> = HashMap::new();
        let mut holds: Vec<bool> = Vec::with_capacity(self.proofs.len());
        for p in &self.proofs {
            let h = p.needs.iter().flatten().all(|n| holds[*n as usize])
                && (p.checks.iter())
                    .all(|&(a, b)| disjoint(&mut sets, &halves, &shared, &mut checked, a, b));
            holds.push(h);
        }
        holds
    }
}

/// Plan row CONST-coprime-check-many-sets: the set `x`, each union of one of the sets `us` and
/// one of `vs`, a check of `x` against each union, and the base of their roots, built before a
/// scaling test, so that it times [`Roots::settle`] past the base alone, as [`super::Operands`]
/// does for [`super::Ck::equal`].
#[doc(hidden)]
pub struct Pool {
    x: Vec<u128>,
    us: Vec<Vec<u128>>,
    vs: Vec<Vec<u128>>,
    base: Vec<Vec<u32>>,
}

impl Pool {
    /// `x`, `us` and `vs` hold numbers above 1.
    #[doc(hidden)]
    pub fn new(x: Vec<u128>, us: Vec<Vec<u128>>, vs: Vec<Vec<u128>>) -> Pool {
        let mut pool = Pool {
            x,
            us,
            vs,
            base: Vec::new(),
        };
        pool.base = base_of(&pool.roots().values);
        pool
    }

    /// The roots, sets and checks: O(n) for `n` roots and checks, the same each time, so that
    /// the base made once fits them. They hold [`Rc`], which a scaling test cannot share with
    /// the thread it times.
    fn roots(&self) -> Roots {
        let mut roots = Roots::default();
        let mut set_of = |ns: &[u128]| {
            (ns.iter()).fold(EMPTY, |s, &n| {
                let leaf = roots.leaf(BigUint::from(n));
                roots.union(s, leaf)
            })
        };
        let x = set_of(&self.x);
        let us: Vec<SetId> = self.us.iter().map(|ns| set_of(ns)).collect();
        let vs: Vec<SetId> = self.vs.iter().map(|ns| set_of(ns)).collect();
        for &u in &us {
            for &v in &vs {
                let s = roots.union(u, v);
                roots.proof([None, None], vec![(x, s)]);
            }
        }
        roots
    }

    /// Whether each check holds, in the order of `us`, then `vs`.
    #[doc(hidden)]
    pub fn settle(&self) -> Vec<bool> {
        self.roots().settle_with(&self.base)
    }
}

/// The sets of base elements of [`Roots::settle`], each built the first time a check looks it
/// up, so that a union no lookup needs, as `u_i * v_j` whose halves were each checked before
/// against the one set it meets, costs nothing past its size.
///
/// Complexity tradeoff: building each union from its halves as the walk made it, the smaller
/// inserted into a copy of the larger, costs O(s log n) for `s` inserted at every union, so
/// `k^2` unions of two of `2k` sets of `r` roots cost O(k^2 r log n) whatever the checks need
/// (plan row CONST-coprime-check-many-sets). Built on demand, a set costs that only where a
/// check looks it up, at most once, and never more than all built at once; a set not yet built
/// has the sum of its halves' sizes as its size, an upper bound that only steers the choice
/// of way.
struct Sets<'a> {
    defs: &'a [Set],
    base: &'a [Vec<u32>],
    made: Vec<Option<OrdSet<u32>>>,
    /// The size of each set built, and of each other set at most this.
    size: Vec<usize>,
}

impl Sets<'_> {
    /// Builds `s`, and each set under it not yet built, by a stack, not recursion: a chain of
    /// `n` unions is `n` deep. Each set is built once, its halves first.
    fn build(&mut self, s: SetId) {
        let mut todo = vec![s];
        while let Some(&t) = todo.last() {
            let t = t as usize;
            if self.made[t].is_some() {
                todo.pop();
                continue;
            }
            let made = match self.defs[t] {
                Set::Empty => OrdSet::new(),
                Set::Leaf(r) => self.base[r as usize].iter().copied().collect(),
                Set::Union(a, b) => {
                    let (sa, sb) = (&self.made[a as usize], &self.made[b as usize]);
                    let (Some(sa), Some(sb)) = (sa, sb) else {
                        todo.extend(
                            [a, b]
                                .into_iter()
                                .filter(|h| self.made[*h as usize].is_none()),
                        );
                        continue;
                    };
                    let (big, small) = if sa.len() >= sb.len() {
                        (sa, sb)
                    } else {
                        (sb, sa)
                    };
                    let mut u = big.clone();
                    u.extend(small.iter().copied());
                    u
                }
            };
            self.size[t] = made.len();
            self.made[t] = Some(made);
            todo.pop();
        }
    }

    /// Whether `s` and `t` share no element: the smaller looked up in the larger.
    fn free(&mut self, s: SetId, t: SetId) -> bool {
        self.build(s);
        self.build(t);
        let made = |s: SetId| self.made[s as usize].as_ref().expect("built above");
        let (s, t) = (made(s), made(t));
        let (big, small) = if s.len() >= t.len() { (s, t) } else { (t, s) };
        !small.iter().any(|e| big.contains(e))
    }
}

/// A way [`disjoint`] can decide a check: the lookups it costs, the answer of the checks made
/// before that it rests on, if any, the pairs of sets it looks up, and whether it keeps the
/// answer of a pair a later check may ask again.
type Way = (usize, Option<bool>, Vec<(SetId, SetId)>, bool);

/// Whether the sets `a` and `b` share no element, by the least of the ways of
/// [`Roots::settle`], the answer kept in `checked` by the pair, with that of each pair it
/// looked up. `shared` tells the sets that are a half of two unions or more, or in two checks.
fn disjoint(
    sets: &mut Sets,
    halves: &[Option<(SetId, SetId)>],
    shared: &[bool],
    checked: &mut HashMap<(SetId, SetId), bool>,
    a: SetId,
    b: SetId,
) -> bool {
    let pair = |a: SetId, b: SetId| (a.min(b), a.max(b));
    if let Some(&known) = checked.get(&pair(a, b)) {
        return known;
    }
    let size = |s: SetId| sets.size[s as usize];
    // The lookups that test `s` against `t`, and their answer.
    let cost = |s: SetId, t: SetId| size(s).min(size(t));
    let mut ways: Vec<Way> = vec![(cost(a, b), None, vec![(a, b)], false)];
    // One set against each half of the other, each half by its check made before or by
    // lookups.
    for (x, y) in [(a, b), (b, a)] {
        if let Some((big, small)) = halves[y as usize] {
            let mut way: Way = (0, Some(true), Vec::new(), false);
            for h in [big, small] {
                match checked.get(&pair(x, h)) {
                    Some(&known) => way.1 = Some(way.1 == Some(true) && known),
                    None => {
                        way.0 += cost(x, h);
                        way.2.push((x, h));
                        way.3 |= shared[h as usize];
                    }
                }
            }
            ways.push(way);
        }
    }
    if let (Some((ab, asm)), Some((bb, bsm))) = (halves[a as usize], halves[b as usize])
        && let Some(&known) = checked.get(&pair(ab, bb))
    {
        ways.push((
            cost(asm, b) + cost(bsm, a),
            Some(known),
            vec![(asm, b), (bsm, a)],
            false,
        ));
    }
    // A check made before that found a shared element decides at once. A way that keeps the
    // answer of a shared half counts half its lookups, and wins a tie.
    let (_, before, rest, _) = (ways.into_iter())
        .min_by_key(|(n, before, _, keeps)| match before {
            Some(false) => (0, false),
            _ if *keeps => (1 + n.div_ceil(2), false),
            _ => (1 + n, true),
        })
        .expect("the lookups are one way");
    let mut known = before != Some(false);
    for (s, t) in rest {
        if !known {
            break;
        }
        known = sets.free(s, t);
        checked.insert(pair(s, t), known);
    }
    checked.insert(pair(a, b), known);
    known
}

/// For each root of `roots`, distinct numbers above 1, the indices of the elements of their
/// natural coprime base that it is a product of powers of: pairwise coprime numbers above 1,
/// each prime of a root in exactly one of them, so that two roots share a prime exactly when
/// their lists meet. By zed-kernel's `num::coprime::coprime_base` (Bernstein, "Factoring into
/// coprimes in essentially linear time", J. Algorithms 54(1), 2005,
/// doi:10.1016/j.jalgor.2004.04.009; the method, its proof and its cost are in that module's
/// comment), the one copy for zedc-int, zedc-presburger and this crate (DRY-coprime-bases-one,
/// 2026-11-20).
///
/// Complexity tradeoff: the naive method refines the base one root at a time, splitting each
/// against every element that shares a factor with it (factor refinement, Bach, Driscoll and
/// Shallit, "Factor refinement", J. Algorithms 15(2), 1993, pp. 199-222,
/// doi:10.1006/jagm.1993.1038; sections 1 and 2 read 2026-11-20 from page images, PDF,
/// LibGen, verification only: its method and bound are quoted at zed-kernel's
/// `num::coprime`), O(n) gcds a root and O(n^2) in
/// all, as for `n` wide even numbers, all of which share 2. Used: the kernel first finds which
/// roots share a prime with any other (`num::coprime::shares_a_factor`: a table of least prime
/// factors when the largest root is at most the bits of all of them, O(N) word operations for
/// `N` bits in all; otherwise the product tree and the remainder tree, `gcd(r, (P / r) mod r)`,
/// O(M(N) log n)); each that shares none is its own element, and the others get the base by
/// halves (Algorithm 18.1), O(M(N) log N log n) a merge and a factor `log n` for the halves.
/// This file had its own copy of the halves, which kept only which primes a root has, not
/// their exponents (6 for the roots 6 and 12, where the natural base is 2 and 3), and so
/// skipped Algorithm 13.2's pair bases; that is the one cost the kernel adds, at most `2N` bits
/// of pairs a merge (proved in the kernel's module comment). Benches: `bench::too_large` here
/// (`bounding_a_chain_of_products_*`, `settling_checks_of_one_set_against_unions_from_one_pool
/// _scales`) and the kernel's `the_coprime_base_of_the_first_primes_scales`.
fn base_of(roots: &[Rc<BigUint>]) -> Vec<Vec<u32>> {
    (coprime_base(roots).factors.into_iter())
        .map(|f| f.into_iter().map(|(e, _)| e).collect())
        .collect()
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

    /// The primes below `n`.
    fn primes(n: u64) -> Vec<u64> {
        (2..n).filter(|&q| zed_numtheory::is_prime(q)).collect()
    }

    /// The kernel's base of `ns`, as `base_of` reads it: its elements are above 1 and pairwise
    /// coprime; each root's list holds exactly the elements it shares a prime with, once each,
    /// in increasing order; each factor is a power of its element, and the factors of a root
    /// multiply to it, so every prime of the root is in its list. (The base by halves of this
    /// file was replaced by the kernel's by DRY-coprime-bases-one; these inputs, the shapes
    /// `bench::too_large` builds, stay as its test here.)
    fn a_valid_base(ns: &[BigUint]) {
        let cb = coprime_base(ns);
        let base = &cb.elements;
        assert_eq!(cb.factors.len(), ns.len());
        for (i, a) in base.iter().enumerate() {
            assert!(a.bits() > 1, "{a} in {ns:?}");
            for b in &base[i + 1..] {
                assert_eq!(gcd_uint(a, b).bits(), 1, "{a}, {b} of {ns:?}: {base:?}");
            }
        }
        let one = BigUint::from(1u8);
        for (r, factors) in ns.iter().zip(&cb.factors) {
            let meets: Vec<u32> = (0..to_u32(base.len(), "base elements"))
                .filter(|&e| gcd_uint(r, &base[e as usize]).bits() > 1)
                .collect();
            let list: Vec<u32> = factors.iter().map(|(e, _)| *e).collect();
            assert_eq!(list, meets, "{r} of {ns:?}: {base:?}");
            for (e, q) in factors {
                let (mut q, b) = (q.clone(), &base[*e as usize]);
                while q != one {
                    let (d, m) = (&q / b, &q % b);
                    assert!(m.bits() == 0, "{r}: a factor not a power of {b}");
                    q = d;
                }
            }
            let all = (factors.iter()).fold(one.clone(), |acc, (_, q)| acc * q);
            assert_eq!(&all, r, "{r} of {ns:?}: {base:?}");
        }
    }

    fn big(ns: &[u64]) -> Vec<BigUint> {
        ns.iter().map(|&n| BigUint::from(n)).collect()
    }

    #[test]
    fn a_base_by_halves_holds_the_primes_of_each_root() {
        a_valid_base(&[]);
        a_valid_base(&big(&[7]));
        a_valid_base(&big(&[6, 12]));
        a_valid_base(&big(&[6, 35, 10]));
        a_valid_base(&big(&[12, 18, 5, 49, 77]));
        a_valid_base(&big(&[30, 42, 70, 105, 11, 13 * 17, 17 * 19]));
        let ps = primes(140);
        // Each of 2 p for the odd primes p: all share 2, the case factor refinement makes
        // quadratic; with 1 to 9 roots, so that each split has an odd half.
        for n in 1..=9 {
            a_valid_base(&big(&ps[1..=n].iter().map(|p| 2 * p).collect::<Vec<_>>()));
        }
        a_valid_base(&big(&ps[1..].iter().map(|p| 2 * p).collect::<Vec<_>>()));
        // A chain of neighbors `p_i p_{i+1}`, each sharing a prime with two others, out of
        // order: 7 i mod 31 for the 31 links.
        let chain: Vec<u64> = (0..31u64)
            .map(|i| (7 * i) % 31)
            .map(|i| ps[i as usize] * ps[i as usize + 1])
            .collect();
        a_valid_base(&big(&chain));
        // One root of every prime below 50, against each of those primes and their squares.
        let small = primes(50);
        let mut all = vec![BigUint::from(small.iter().product::<u64>())];
        all.extend(
            small
                .iter()
                .flat_map(|&p| [p, p * p * 3])
                .map(BigUint::from),
        );
        a_valid_base(&all);
        // High exponents.
        let pow = |b: u64, e: u32, m: u64| BigUint::from(b).pow(e) * m;
        a_valid_base(&[pow(2, 200, 3), pow(2, 100, 5), pow(3, 50, 2), pow(5, 3, 1)]);
        a_valid_base(&[pow(2, 300, 1), pow(2, 1, 3), pow(3, 999, 7)]);
        // Primes past one word, and products past the 512 words where `mul_uint` transforms.
        let wide = |m: u64| BigUint::from(18446744073709551557u64).pow(3) * m;
        let mut many: Vec<BigUint> = ps.iter().map(|&p| wide(p)).collect();
        many.push(pow(2, 40000, 1));
        many.push(pow(3, 40000, 5));
        a_valid_base(&many);
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

    /// Plan row CONST-coprime-check-many-sets: each union of a set of one pool and one of
    /// another, checked against one set `x` either way round, gives what a direct test of the
    /// roots gives, whether a half meets `x` or not, and whichever half a check finds kept.
    #[test]
    fn checks_of_unions_from_one_pool_agree_with_the_roots() {
        let mut r = Roots::default();
        let set_of = |r: &mut Roots, ns: &[u64]| {
            (ns.iter()).fold(EMPTY, |s, &n| {
                let leaf = r.leaf(BigUint::from(n));
                r.union(s, leaf)
            })
        };
        let meets = |ms: &[u64], ns: &[u64]| {
            let big = |n: &u64| BigUint::from(*n);
            (ms.iter()).any(|m| ns.iter().any(|n| gcd_uint(&big(m), &big(n)).bits() > 1))
        };
        let xr = [3, 5, 7];
        let x = set_of(&mut r, &xr);
        // `u[2]` meets `x` by 15, `v[2]` by 49.
        let us = [[11, 13], [17, 19], [23, 15], [29, 31]];
        let vs = [[37, 41], [43, 47], [53, 49], [59, 61]];
        let u: Vec<SetId> = us.iter().map(|ns| set_of(&mut r, ns)).collect();
        let v: Vec<SetId> = vs.iter().map(|ns| set_of(&mut r, ns)).collect();
        let (mut ids, mut want) = (Vec::new(), Vec::new());
        for (i, ui) in us.iter().enumerate() {
            for (j, vj) in vs.iter().enumerate() {
                let s = r.union(u[i], v[j]);
                let check = match (i + j) % 2 == 0 {
                    true => (x, s),
                    false => (s, x),
                };
                ids.push(r.proof([None, None], vec![check]));
                want.push(!meets(&xr, ui) && !meets(&xr, vj));
            }
        }
        let held = r.settle();
        let got: Vec<bool> = ids.iter().map(|p| held[p.unwrap() as usize]).collect();
        assert_eq!(got, want);
        assert_eq!(want.iter().filter(|h| **h).count(), 9);
    }

    /// The checks a scaling test settles past the base ([`Pool`]) come in the order of `us`,
    /// then `vs`, and fail where a half meets `x`, `u_1` by 2 and `v_0` by 3.
    #[test]
    fn a_pool_settles_each_union_against_x() {
        let pool = Pool::new(
            vec![2, 3],
            vec![vec![5], vec![7, 4]],
            vec![vec![9], vec![11, 13]],
        );
        assert_eq!(pool.settle(), [false, true, false, false]);
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

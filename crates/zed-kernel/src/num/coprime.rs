//! The natural coprime base of a list of positive integers, and each integer factored over it:
//! the copy for zedc-check (`check/coprime.rs`, which roots share a prime) and
//! zedc-presburger (`modular.rs` `coprime_factorization`, the moduli over pairwise coprime
//! bases), plan row DRY-coprime-bases-one. zedc-int (`Core::same`, the equality of products of
//! powers) keeps its own factor refinement for a measured reason, stated at its
//! `coprime_base`: on its inputs, a few integers of many bits sharing small primes, the `ppi`
//! and pair steps here take gcds of two wide numbers, O(M(n) log n), where refinement takes
//! gcds against small elements and strips powers, O(M(n)); 22.8e9 instructions against 2.1e9
//! on `l01_24 equality_over_a_wide_odd_base_scales_with_its_bits`, ratio 11.9 against 9.2
//! (2026-11-20). Plan row PERF-coprime-base-wide-few.
//!
//! Source: D. J. Bernstein, "Factoring into coprimes in essentially linear time", J.
//! Algorithms 54(1), 2005, pp. 1-30, doi:10.1016/j.jalgor.2004.04.009. Checked 2026-11-19 in
//! the author's preprint (cr.yp.to/lineartime/dcba-20040404.pdf, its text read in full for
//! sections 7, 11, 12, 13, 15 and 18; the journal version not read, its numbering said by the
//! earlier citations in this tree to agree). What is used:
//! - Section 7: the closure `T` of a set `S` is the least set holding `S` and 1 and closed
//!   under products, exact quotients and gcds; the natural coprime base `cb S` is the set of
//!   minimal elements of `T - {1}`, and Theorem 7.3: "Let P be a coprime base for S ... If
//!   P ⊆ T − {1} then P = cb S". So any pairwise coprime set of numbers above 1, each a
//!   product, quotient or gcd of numbers built from `S`, over which each element of `S` is a
//!   product of powers, is `cb S`; that is how each step here is proved natural.
//! - Section 11, Algorithm 11.3 (`ppi`, the powers in `a` of the primes inside `c`): `x <-
//!   gcd(a, c)`, `y <- a / x`, then while `g = gcd(x, y) > 1`, `x <- x g`, `y <- y / g`;
//!   Theorem 11.1: it stops after at most `lg lg a + 1` rounds with `x = ppi(a, c)` and
//!   `y = ppo(a, c)`. Algorithm 11.4 (`ppg`, `pple`) is the same loop from `y <- gcd(a, b)`,
//!   `x <- a / y`. Here as `ppi_by` and `gcd_ppg_pple`.
//! - Section 13, Algorithm 13.2, `cb{a, b}` of two numbers (`pair_base`), quoted there.
//! - Section 15, Algorithm 15.3, `split(a, P) = {(p, ppi(a, p)) : p ∈ P}` for coprime `P`, by
//!   `b <- ppi(a, prod P)` and then the same for each half of `P` on `b` (`split`).
//! - Section 18, Algorithm 18.1: `cb S` as `cb(cb T ∪ cb(S - T))` for `T` half of `S`.
//!
//! Departure, the merge of two coprime bases `P` and `Q` (`merged`): Bernstein's Algorithm
//! 17.3 extends `P` by `2 lg #Q` products of parts of `Q` (Algorithm 16.2 each). Here each
//! `a` of `P` is split over `Q` and each `b` of `Q` over `P` (15.3), which gives every pair
//! `(a, b)` that shares a prime with `ppi(a, b)` and `ppi(b, a)`, and also `ppo(a, prod Q)`
//! and `ppo(b, prod P)`. The merged base is the union of those `ppo` above 1 and of
//! `cb{ppi(a, b), ppi(b, a)}` over the pairs (13.2). Proof that it is `cb(P ∪ Q)`: (1) it is
//! coprime: the primes of `ppo(a, prod Q)` are in `a` only; those of `cb{ppi(a, b), ppi(b,
//! a)}` are in `a` and `b` only, and `a` (`b`) is coprime to the other elements of `P` (`Q`),
//! so two distinct pieces share no prime, and within one pair 13.2's output is coprime. (2) It
//! is a base: `a = ppo(a, prod Q) prod_b ppi(a, b)` (Theorem 15.1), and each `ppi(a, b)` is a
//! product of powers of `cb{ppi(a, b), ppi(b, a)}` (Theorem 7.1); the same for `b`. (3) Each
//! element is in the closure of `P ∪ Q`: `ppi` and `ppo` are built by gcds, products and exact
//! quotients (Algorithm 11.3), and 13.2's output lies in the closure of its two inputs
//! (Theorem 13.1, whose last step is Theorem 7.3). Then Theorem 7.3 gives `cb(P ∪ Q)`; and as
//! `P` and `Q` lie in the closures of the halves of `S` and are bases of them, the merge is a
//! coprime base of `S` inside its closure, so `cb S`, which is the step 18.1 rests on.
//!
//! Complexity tradeoff: factor refinement (Bach, Driscoll and Shallit, "Factor refinement", J.
//! Algorithms 15(2), 1993, pp. 199-222, doi:10.1006/jagm.1993.1038, Crossref metadata only,
//! not read) splits each new number against every element of the base it meets, O(k^2) gcds
//! for `k` elements, as for `k` distinct primes, each tried against all before it. Bernstein's
//! 17.3 costs about `(lg z) mu(lg z)` times a polynomial of degree 4 in `lg lg z` a merge
//! (Theorem 17.4). The merge here costs two splits, each O(M(N) log N log k) on the kernel's
//! trees for `N` bits in all: a level of the descent holds each element of the base split
//! over once, and pairwise coprime divisors of each number split, so at most `2N` bits (the
//! bound proved at `split`); plus 13.2 on the pairs, whose inputs over all pairs of one
//! merge total at most `2N` bits. The halves add a factor `log k`. The answer is exact;
//! no step is skipped for any size. Tests: `num::coprime::tests`, against a base found by
//! factoring every input into primes (the definition above, by exponent vectors), on every
//! triple of small inputs, ones, equal inputs, powers, and inputs past one word; benches
//! `num::bench::the_coprime_base_of_*`.

use std::borrow::Borrow;

use num_bigint::BigUint;
use num_traits::One;

use super::{div_rem_uint, gcd_uint, mul_uint, trees};

/// The natural coprime base of some positive integers and each one written over it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CoprimeBase {
    /// The elements: pairwise coprime, each above 1, no two equal, in no set order. Each
    /// prime of an input is in exactly one of them.
    pub elements: Vec<BigUint>,
    /// For each input, in the order given, its factors `(e, q)`: `q` the largest power of
    /// `elements[e]` that divides the input, for each element that shares a prime with it, by
    /// increasing `e`. The `q` of one input multiply to it; an input 1 has none.
    pub factors: Vec<Vec<(u32, BigUint)>>,
}

/// The natural coprime base `cb S` of `xs` and each of `xs` over it, every `x` above 0 (see
/// the module comment for the method and its proof). Inputs may repeat. For 4 and 8 the
/// base is 2 (4 = 2^2, 8 = 2^3); for 6 and 12 it is 2 and 3; for 4 alone it is 4, and for 1
/// alone it is empty.
///
/// First, which inputs share a prime with any other, by [`shares_a_factor`]: an input that
/// shares none is its own element, its one factor itself. Only the others go through the
/// halves (Algorithm 18.1, `base_by_halves`) and are then split over their base (Algorithm
/// 15.3, `split`) to get their factors.
pub fn coprime_base<L: Borrow<BigUint>>(xs: &[L]) -> CoprimeBase {
    let mut out = CoprimeBase {
        elements: Vec::new(),
        factors: vec![Vec::new(); xs.len()],
    };
    // The inputs above 1; a 1 has no factor.
    let above: Vec<usize> = (0..xs.len())
        .filter(|&i| {
            let x = xs[i].borrow();
            assert!(x.bits() > 0, "a coprime base of positive integers, given 0");
            x.bits() > 1
        })
        .collect();
    let leaves: Vec<&BigUint> = above.iter().map(|&i| xs[i].borrow()).collect();
    let mut shared: Vec<usize> = Vec::new();
    for (k, (x, s)) in leaves.iter().zip(shares_a_factor(&leaves)).enumerate() {
        if s {
            shared.push(k);
        } else {
            out.factors[above[k]].push((index(out.elements.len()), (*x).clone()));
            out.elements.push((*x).clone());
        }
    }
    let rest: Vec<&BigUint> = shared.iter().map(|&k| leaves[k]).collect();
    let base = base_by_halves(&rest);
    let offset = out.elements.len();
    let held: Vec<&BigUint> = base.iter().collect();
    let (pieces, _) = split(&rest, &held);
    for (x, e, q) in pieces {
        out.factors[above[shared[x as usize]]].push((index(offset + e as usize), q));
    }
    for f in &mut out.factors {
        f.sort_unstable_by_key(|&(e, _)| e);
    }
    out.elements.extend(base);
    out
}

/// For each of `xs` (each at least 1), whether it shares a prime factor with another of them.
/// Equal values above 1 share one; a value 1 shares none. The one copy for the workspace
/// (moved from zedc-presburger `modular.rs` by DRY-coprime-bases-one, 2026-11-20; zedc-check
/// `base_of` had the tree method alone).
// Complexity tradeoff: the general method is the product tree and the remainder tree,
// O(M(B) log k) for `k` values of `B` bits in all, which on k word-size values is 15 to 25
// times the work at 8 times the values (products of 82 to 872 words at 512 to 4096 values,
// multiplied and divided by num-bigint below the transform sizes; perf, 2026-11-19). When the
// largest value `V` is at most `B`, a table of least prime factors up to `V` costs no more
// than reading the input, O(V + B) = O(B) word operations and about 2 V + 4 k bytes
// ([`zed_numtheory::shares_a_factor_by_table`]), so that case is answered from the table.
// The condition is the one under which the table method is proved linear in the input size;
// it is not a timed crossover. Measured 2026-11-19 (instructions, values 1 + i * stride,
// `the_shared_factor_crossover_axis`, load 47 to 50): wherever the condition holds the table
// took 2.6 to 29 times fewer instructions than the tree (16 values up to 61: 7,131 against
// 18,297; 4096 values up to 16,381: 1,198,814 against 35,079,991) and fewer bytes; beyond it
// the table is still the cheaper up to `V` of about 2 `B` at 16 values and 4 to 13 `B` at
// 128 to 4096 values, and the dearer after that (4096 values up to 4,193,281, `B` = 86,008:
// 176.8 M against 80.1 M). So `V <= c B` with a larger fixed `c` would also be linear and
// cheaper; `c` = 1 needs no timing to justify it. Both methods give the same answer
// (`the_shared_factor_methods_agree`). What is left on the tree: wide values, and values
// sparser than one in `log2 V` (`V > B`); no method of lower order than O(M(B) log k) is
// known for those (Bernstein 2005 gives B^(1 + o(1))), and the tree side is 13 to 18 times the
// work at 8 times the values (plan row PERF-negated-chain-unsolved, whose deferred benches
// are in wt/scratch/deferred-tests/PERF-negated-chain-unsolved.rs); COMPLEXITY.md C31c.
pub fn shares_a_factor<L: Borrow<BigUint>>(xs: &[L]) -> Vec<bool> {
    match dense_values(xs) {
        Some((small, top)) => zed_numtheory::shares_a_factor_by_table(&small, top),
        None => shares_a_factor_by_tree(xs),
    }
}

/// `xs` as `u32` with their largest, when every value is in `1..=u32::MAX` and the largest is
/// at most the number of bits of all of them together: the side of [`shares_a_factor`] that
/// takes the table. A largest value over `u32::MAX` that passed the second condition would
/// need more than 2^32 bits of values.
pub fn dense_values<L: Borrow<BigUint>>(xs: &[L]) -> Option<(Vec<u32>, u32)> {
    let mut small = Vec::with_capacity(xs.len());
    let mut bits = 0u64;
    for x in xs {
        let x = x.borrow();
        let v = u32::try_from(x).ok().filter(|&v| v > 0)?;
        small.push(v);
        bits += x.bits();
    }
    let top = small.iter().copied().max()?;
    (u64::from(top) <= bits).then_some((small, top))
}

/// [`shares_a_factor`] by one product tree and one remainder tree: `gcd(x, (P / x) mod x)` for
/// the product `P` of all values ([`trees::cofactors_mod_leaves`]; for a lone value it is
/// `1 mod x`, so it shares none). O(M(B) log k).
pub(super) fn shares_a_factor_by_tree<L: Borrow<BigUint>>(xs: &[L]) -> Vec<bool> {
    let cof = trees::cofactors_mod_leaves(xs, &trees::product_tree(xs));
    (xs.iter().zip(&cof))
        .map(|(v, c)| !gcd_uint(v.borrow(), c).is_one())
        .collect()
}

/// An index into the elements as a `u32`. There are at most as many elements as bits in the
/// product of the inputs, which bounds them by the memory the inputs take in bits, not by
/// `2^32` (512 MiB of inputs is `2^32` bits), so past `u32::MAX` it panics.
fn index(i: usize) -> u32 {
    zed_collections::index::to_u32(i, "elements of a coprime base")
}

/// `cb S` for `xs`, each above 1, by halves (Algorithm 18.1): the base of one input is the
/// input itself, and of more, the [`merged`] bases of the two halves.
fn base_by_halves(xs: &[&BigUint]) -> Vec<BigUint> {
    match xs {
        [] => Vec::new(),
        [x] => vec![(*x).clone()],
        _ => {
            let (left, right) = xs.split_at(xs.len() / 2);
            merged(base_by_halves(left), base_by_halves(right))
        }
    }
}

/// `cb(P ∪ Q)` for coprime bases `p` and `q` (module comment, "Departure"): `ppo(a, prod q)`
/// for each `a` of `p`, `ppo(b, prod p)` for each `b` of `q`, where above 1, and the natural
/// base of `ppi(a, b)` and `ppi(b, a)` for each pair that shares a prime.
fn merged(p: Vec<BigUint>, q: Vec<BigUint>) -> Vec<BigUint> {
    if p.is_empty() {
        return q;
    }
    if q.is_empty() {
        return p;
    }
    let (pr, qr): (Vec<&BigUint>, Vec<&BigUint>) = (p.iter().collect(), q.iter().collect());
    let (mut of_p, p_out) = split(&pr, &qr);
    let (mut of_q, q_out) = split(&qr, &pr);
    let mut base: Vec<BigUint> = (p_out.into_iter().chain(q_out))
        .filter(|r| r.bits() > 1)
        .collect();
    // `ppi(a, b) > 1` exactly when `a` and `b` share a prime, exactly when `ppi(b, a) > 1`, so
    // the two lists hold the same pairs; sorted by the pair, they line up.
    of_p.sort_unstable_by_key(|&(a, b, _)| (a, b));
    of_q.sort_unstable_by_key(|&(b, a, _)| (a, b));
    debug_assert_eq!(of_p.len(), of_q.len());
    for ((a, b, x), (b2, a2, y)) in of_p.into_iter().zip(of_q) {
        debug_assert_eq!((a, b), (a2, b2));
        pair_base(&mut base, x, y);
    }
    base
}

/// Algorithm 15.3 of Bernstein (2005) for many numbers at once: for each `x` of `xs` (each
/// above 0) and `p` of `ps` (pairwise coprime, each above 1) that share a prime, `(i, j,
/// ppi(x_i, p_j))`, in no set order; and for each `x`, `ppo(x, prod ps)`.
///
/// One descent of the product tree of `ps` ([`trees::product_tree`]): at the root each `x`
/// holds `h = ppi(x, prod ps)`, by `g = gcd(x, (prod ps) mod x)` and then [`ppi_by`] on `g`
/// (the primes of `x` inside `prod ps` are those of `g`), the remainders `(prod ps) mod x` of
/// all `x` being one remainder tree ([`trees::remainders`]). At a node whose held values all
/// have only primes of the node's product, the left child gets `ppi(h, left)` the same way,
/// by one remainder tree of the left product over the held values of the node, and the right
/// child `h / ppi(h, left)`, which is `ppi(h, right)` as the children's products are coprime
/// and `h` has no prime outside them (Theorem 15.1). A leaf `p_j` then holds `ppi(x, p_j)`
/// (Theorem 15.2). A node with no right child is carried up with the same product, and its
/// held values with it.
///
/// Cost: the values held at one level for one `x` divide `x` and are pairwise coprime, so they
/// total at most twice the bits of `x` (each at least 2, so its bits at most twice its log),
/// and the products of a level total at most the bits of `prod ps` plus the count of `ps`;
/// so a level costs O(M(N) log k) by the trees, with the [`ppi_by`] rounds, O(log log N) gcds
/// of numbers that total `2N` bits, for `N` the bits of all of `xs` and `ps`; and there are
/// `log k` levels for `k` of `ps`. Splitting each `x` over each `p` alone costs `k` gcds of
/// the width of `x` for every `x`, O(n k) of them.
fn split(xs: &[&BigUint], ps: &[&BigUint]) -> (Vec<(u32, u32, BigUint)>, Vec<BigUint>) {
    if ps.is_empty() {
        return (Vec::new(), xs.iter().map(|&x| x.clone()).collect());
    }
    let tree = trees::product_tree(ps);
    let all = trees::tree_product(ps, &tree);
    // The node, the input and the value held, grouped by node in increasing order.
    let mut at: Vec<usize> = Vec::new();
    let mut from: Vec<u32> = Vec::new();
    let mut held: Vec<BigUint> = Vec::new();
    let mut outside: Vec<BigUint> = Vec::with_capacity(xs.len());
    for (i, (x, r)) in xs.iter().zip(rems_of(&all, xs)).enumerate() {
        let g = gcd_uint(x, &r);
        if g.is_one() {
            outside.push((*x).clone());
            continue;
        }
        let h = ppi_by(x, g);
        outside.push(div_rem_uint(x, &h).0);
        at.push(0);
        from.push(index(i));
        held.push(h);
    }
    let below = (tree.iter().rev().skip(1))
        .map(|l| l.iter().collect::<Vec<_>>())
        .chain([ps.to_vec()]);
    for level in below {
        let (mut next_at, mut next_from, mut next_held) = (Vec::new(), Vec::new(), Vec::new());
        let mut start = 0;
        while start < at.len() {
            let node = at[start];
            let end = start + at[start..].iter().take_while(|&&n| n == node).count();
            let (left, right) = (2 * node, 2 * node + 1);
            if right >= level.len() {
                next_at.extend(std::iter::repeat_n(left, end - start));
                next_from.extend_from_slice(&from[start..end]);
                next_held.extend(held[start..end].iter_mut().map(std::mem::take));
            } else {
                let hs: Vec<&BigUint> = held[start..end].iter().collect();
                let rs = rems_of(level[left], &hs);
                let mut rights: Vec<(u32, BigUint)> = Vec::new();
                for (k, (h, r)) in hs.iter().zip(rs).enumerate() {
                    let g = gcd_uint(h, &r);
                    if g.is_one() {
                        rights.push((from[start + k], (*h).clone()));
                        continue;
                    }
                    let l = ppi_by(h, g);
                    if l != **h {
                        rights.push((from[start + k], div_rem_uint(h, &l).0));
                    }
                    next_at.push(left);
                    next_from.push(from[start + k]);
                    next_held.push(l);
                }
                for (i, h) in rights {
                    next_at.push(right);
                    next_from.push(i);
                    next_held.push(h);
                }
            }
            start = end;
        }
        (at, from, held) = (next_at, next_from, next_held);
    }
    let pieces = (from.into_iter().zip(at).zip(held))
        .map(|((i, j), h)| (i, index(j), h))
        .collect();
    (pieces, outside)
}

/// `x mod m` for each `m` of `ms`, above 0, by one remainder tree over their product tree
/// ([`trees::remainders`]): O(M(X + B) log k) for `x` of `X` bits and `k` moduli of `B` bits
/// in all, where one division a modulus costs O(k M(X)).
fn rems_of(x: &BigUint, ms: &[&BigUint]) -> Vec<BigUint> {
    trees::remainders(x, ms, &trees::product_tree(ms))
}

/// `ppi(a, c)` given `g = gcd(a, c) > 1`: Algorithm 11.3 of Bernstein (2005) from its second
/// step, `x = g`, `y = a / g`, then `x <- x gcd(x, y)` and `y <- y / gcd(x, y)` until the gcd
/// is 1. The exponent of a prime of `c` in `x` doubles each round until it is its exponent in
/// `a` (Theorem 11.1, `ord_p x_n = min(e, 2^n f)`), so the rounds are at most `lg lg a + 1`;
/// dividing by `gcd(y, g)` until it is 1, one prime power at a time, takes as many rounds as
/// the largest exponent.
fn ppi_by(a: &BigUint, g: BigUint) -> BigUint {
    let mut y = div_rem_uint(a, &g).0;
    let mut x = g;
    loop {
        let d = gcd_uint(&x, &y);
        if d.is_one() {
            return x;
        }
        y = div_rem_uint(&y, &d).0;
        x = mul_uint(&x, &d);
    }
}

/// `(gcd(a, b), ppg(a, b), pple(a, b))`, Algorithm 11.4 of Bernstein (2005): `ppg` holds the
/// prime powers of `a` above those of `b`, `pple` those at most them (Theorem 11.2). The
/// same rounds as [`ppi_by`], from `y = gcd(a, b)`, `x = a / y`.
fn gcd_ppg_pple(a: &BigUint, b: &BigUint) -> (BigUint, BigUint, BigUint) {
    let mut y = gcd_uint(a, b);
    let g = y.clone();
    let mut x = div_rem_uint(a, &y).0;
    loop {
        let d = gcd_uint(&x, &y);
        if d.is_one() {
            return (g, x, y);
        }
        x = mul_uint(&x, &d);
        y = div_rem_uint(&y, &d).0;
    }
}

/// `(ppi(a, b), ppo(a, b))`, Algorithm 11.3 of Bernstein (2005) from its first step.
fn ppi_ppo(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    let g = gcd_uint(a, b);
    if g.is_one() {
        return (g, a.clone());
    }
    let x = ppi_by(a, g);
    let y = div_rem_uint(a, &x).0;
    (x, y)
}

/// Pushes `cb{a, b}` to `out`, Algorithm 13.2 of Bernstein (2005), with an explicit stack in
/// place of its two recursive calls, pushed in reverse so that they run in its order (the
/// order matters for its time bound, Theorem 13.3, not for the answer). Its steps, quoted:
/// "1. If b = 1: Print a if a ≠ 1. Stop. 2. Compute (a, r) ← (ppi, ppo)(a, b) by Algorithm
/// 11.3. 3. Print r if r ≠ 1. 4. Compute (g, h, c) ← (gcd, ppg, pple)(a, b) by Algorithm
/// 11.4. 5. Set c0 ← c. Set x ← c0. 6. Set n ← 1. 7. Compute (g, h, c) ← (gcd, ppg,
/// pple)(h, g^2) by Algorithm 11.4. 8. Set d ← gcd{c, b}. ... 9. Set x ← xd. 10. Compute
/// y ← d^(2^(n−1)) by Algorithm 10.1. 11. Recursively apply Algorithm 13.2 to (c/y, d).
/// 12. If h ≠ 1: Set n ← n + 1. Return to Step 7. 13. Recursively apply Algorithm 13.2 to
/// (b/x, c0)." Departures: `a = b` and `a = 1` stop at once with `a` and `b` (the answers
/// the steps reach, as `cb{a, a} = {a}` and `cb{1, b} = {b}`), and `d^(2^(n-1))` is built by
/// squaring (Algorithm 10.1 is a repeated squaring too). Cost: Theorem 13.4, about
/// `lg ab mu(3 lg ab)` times a polynomial of degree 3 in `lg lg ab`.
fn pair_base(out: &mut Vec<BigUint>, a: BigUint, b: BigUint) {
    let mut stack = vec![(a, b)];
    while let Some((a, b)) = stack.pop() {
        if b.is_one() || a == b {
            if !a.is_one() {
                out.push(a);
            }
            continue;
        }
        if a.is_one() {
            out.push(b);
            continue;
        }
        let (a, r) = ppi_ppo(&a, &b);
        if !r.is_one() {
            out.push(r);
        }
        let (mut g, mut h, c0) = gcd_ppg_pple(&a, &b);
        let mut x = c0.clone();
        let mut calls: Vec<(BigUint, BigUint)> = Vec::new();
        let mut n = 1u32;
        loop {
            let c;
            (g, h, c) = gcd_ppg_pple(&h, &mul_uint(&g, &g));
            let d = gcd_uint(&c, &b);
            x = mul_uint(&x, &d);
            let mut y = d.clone();
            for _ in 1..n {
                y = mul_uint(&y, &y);
            }
            calls.push((div_rem_uint(&c, &y).0, d));
            if h.is_one() {
                break;
            }
            n += 1;
        }
        stack.push((div_rem_uint(&b, &x).0, c0));
        stack.extend(calls.into_iter().rev());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn big(v: u64) -> BigUint {
        BigUint::from(v)
    }

    /// The prime factors of `n > 0` with their exponents, by trial division.
    fn primes_of(mut n: u64) -> BTreeMap<u64, u32> {
        let mut out = BTreeMap::new();
        let mut p = 2;
        while p * p <= n {
            while n % p == 0 {
                *out.entry(p).or_insert(0) += 1;
                n /= p;
            }
            p += 1;
        }
        if n > 1 {
            *out.entry(n).or_insert(0) += 1;
        }
        out
    }

    /// `cb S` by its definition through exponent vectors: two primes are in one element when
    /// their exponent vectors over the inputs are proportional; the element is `prod p^l_p`
    /// where `v_p = l_p w` for the vector `w` of the class with coprime entries. (Each element
    /// of a coprime base holds primes with proportional vectors, so there are at least as many
    /// elements as classes, and this set, a coprime base inside the closure, is `cb S` by
    /// Theorem 7.3.) Sorted.
    fn by_primes(xs: &[u64]) -> Vec<BigUint> {
        let fs: Vec<_> = xs.iter().map(|&x| primes_of(x)).collect();
        let mut vectors: BTreeMap<u64, Vec<u32>> = BTreeMap::new();
        for (i, f) in fs.iter().enumerate() {
            for (&p, &e) in f {
                vectors.entry(p).or_insert_with(|| vec![0; xs.len()])[i] = e;
            }
        }
        let gcd = |a: u32, b: u32| {
            let (mut a, mut b) = (a, b);
            while b != 0 {
                (a, b) = (b, a % b);
            }
            a
        };
        // Each class by its primitive vector, with `l_p` the gcd of the prime's entries.
        let mut classes: BTreeMap<Vec<u32>, BigUint> = BTreeMap::new();
        for (p, v) in vectors {
            let l = v.iter().fold(0, |g, &e| gcd(g, e));
            let w: Vec<u32> = v.iter().map(|e| e / l).collect();
            let e = classes.entry(w).or_insert_with(|| big(1));
            *e *= big(p).pow(l);
        }
        let mut out: Vec<BigUint> = classes.into_values().collect();
        out.sort();
        out
    }

    /// The base of `xs` is `cb S`, and each factor list is the input's: powers of distinct
    /// elements, each the largest that divides it, whose product is it.
    fn valid(xs: &[BigUint], want: Option<&[BigUint]>) -> CoprimeBase {
        let cb = coprime_base(xs);
        let mut got = cb.elements.clone();
        got.sort();
        for w in got.windows(2) {
            assert!(w[0] != w[1], "{xs:?}: an element twice in {got:?}");
        }
        for (i, a) in cb.elements.iter().enumerate() {
            assert!(a.bits() > 1, "{xs:?}: {a}");
            for b in &cb.elements[i + 1..] {
                assert!(gcd_uint(a, b).is_one(), "{xs:?}: {a} and {b}");
            }
        }
        if let Some(want) = want {
            assert_eq!(got, want, "{xs:?}");
        }
        assert_eq!(cb.factors.len(), xs.len());
        for (x, fs) in xs.iter().zip(&cb.factors) {
            let mut prod = big(1);
            for w in fs.windows(2) {
                assert!(w[0].0 < w[1].0, "{x}: {fs:?}");
            }
            for (e, q) in fs {
                let c = &cb.elements[*e as usize];
                // `q` is a power of `c`, and no higher power divides `x`.
                let mut r = q.clone();
                while (&r % c).bits() == 0 && r.bits() > 1 {
                    r /= c;
                }
                assert!(r.is_one(), "{x}: {q} is not a power of {c}");
                assert!(
                    (x / q % c).bits() > 0,
                    "{x}: a higher power of {c} than {q}"
                );
                prod *= q;
            }
            assert_eq!(&prod, x, "{x}: {fs:?}");
            // Every element that divides `x` is in its list.
            let listed = fs.len();
            let meets = (cb.elements.iter())
                .filter(|c| !gcd_uint(c, x).is_one())
                .count();
            assert_eq!(listed, meets, "{x}: {fs:?} of {:?}", cb.elements);
        }
        cb
    }

    fn check(xs: &[u64]) {
        let bx: Vec<BigUint> = xs.iter().map(|&x| big(x)).collect();
        valid(&bx, Some(&by_primes(xs)));
    }

    #[test]
    fn the_natural_base_of_short_lists() {
        check(&[]);
        check(&[1]);
        check(&[1, 1]);
        check(&[2]);
        check(&[4]);
        check(&[4, 8]);
        check(&[4, 4]);
        check(&[6, 12]);
        check(&[12, 18]);
        check(&[6, 35, 10]);
        check(&[12, 18, 5, 49, 77]);
        check(&[4, 8, 16, 3]);
        check(&[30, 42, 70, 105, 11, 13 * 17, 17 * 19]);
        check(&[2 * 2 * 3, 2 * 3 * 3, 1, 36, 36, 216]);
        check(&[1 << 40, 3u64.pow(20), 6u64.pow(10), 12]);
        check(&[2u64.pow(6) * 3u64.pow(4), 2u64.pow(3) * 3u64.pow(2), 5]);
    }

    /// The base for 6 and 12 is 2 and 3 (12 = 2^2 3 is no power of 6), where the old
    /// zedc-check base by prime sets alone was 6; and for 4 alone it is 4, not 2.
    #[test]
    fn the_base_keeps_apart_primes_of_unequal_exponents() {
        let cb = valid(&[big(6), big(12)], Some(&[big(2), big(3)]));
        let parts: Vec<Vec<BigUint>> = (cb.factors.iter())
            .map(|f| f.iter().map(|(_, q)| q.clone()).collect())
            .collect();
        let mut six = parts[0].clone();
        let mut twelve = parts[1].clone();
        six.sort();
        twelve.sort();
        assert_eq!((six, twelve), (vec![big(2), big(3)], vec![big(3), big(4)]));
        valid(&[big(4)], Some(&[big(4)]));
    }

    #[test]
    fn the_natural_base_of_every_small_triple() {
        for a in 1..24 {
            for b in a..32 {
                for c in b..40 {
                    check(&[a, b, c]);
                }
            }
        }
    }

    /// Sets of products of small prime powers, from a fixed linear congruential sequence: many
    /// pairs meet, with unequal exponents, so the halves, the splits and 13.2 all run.
    #[test]
    fn the_natural_base_of_products_of_prime_powers() {
        let primes = [2u64, 3, 5, 7, 11, 13];
        let mut s = 0x2545_f491_4f6c_dd1du64;
        let mut next = || {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            s >> 33
        };
        for round in 0..400 {
            let n = 1 + round % 9;
            let xs: Vec<u64> = (0..n)
                .map(|_| {
                    let mut x = 1u64;
                    for &p in &primes {
                        let e = next() % 4;
                        if e > 0 && next() % 2 == 0 {
                            x *= p.pow(e as u32);
                        }
                    }
                    x
                })
                .collect();
            check(&xs);
        }
    }

    /// Inputs past one word and past the transform width, where the kernel's fast products,
    /// remainders and gcds run: `p^a q^b` for primes past 2^64 and exponents that make some
    /// powers share a class and some not.
    #[test]
    fn the_natural_base_of_wide_inputs() {
        let p = big(18446744073709551557); // the largest prime below 2^64
        let q = (big(1) << 127u32) - 1u32; // the Mersenne prime 2^127 - 1
        let r = big(1_000_000_007);
        let xs = vec![
            p.pow(3) * q.pow(3),
            p.pow(5) * q.pow(5) * &r,
            p.clone() * q.pow(2),
            r.pow(40),
            q.pow(600),
        ];
        // p and q: vectors (3, 5, 1, 0, 0) and (3, 5, 2, 0, 600), not proportional, so apart;
        // r: (0, 1, 0, 40, 0). The base is p, q and r.
        let mut want = vec![p.clone(), q.clone(), r.clone()];
        want.sort();
        valid(&xs, Some(&want));
        // p q and its powers alone: p q is one element.
        let pq = &p * &q;
        let xs = vec![pq.pow(2), pq.pow(3), pq.pow(500)];
        valid(&xs, Some(std::slice::from_ref(&pq)));
        // One input coprime to all the others is its own element even when composite.
        let xs = vec![p.pow(2) * &r, q.clone(), q.pow(2)];
        let cb = valid(&xs, None);
        assert!(cb.elements.contains(&(p.pow(2) * &r)));
    }

    /// The pieces of [`split`]: `ppi(x, p)` for each pair that meets and `ppo(x, prod ps)`,
    /// against a gcd loop for each pair.
    #[test]
    fn a_split_holds_each_part_inside_and_the_rest_outside() {
        let ps: Vec<BigUint> = [4u64, 9, 5, 49, 11, 13, 17].map(big).to_vec();
        let xs: Vec<BigUint> = [1u64, 2, 360, 7 * 7 * 7 * 19, 23, 11 * 13 * 17 * 4 * 27]
            .map(big)
            .to_vec();
        let (pr, xr): (Vec<&BigUint>, Vec<&BigUint>) = (ps.iter().collect(), xs.iter().collect());
        let (mut pieces, outside) = split(&xr, &pr);
        pieces.sort_unstable_by_key(|&(i, j, _)| (i, j));
        let mut want = Vec::new();
        let mut rests = Vec::new();
        for (i, x) in xs.iter().enumerate() {
            let mut rest = x.clone();
            for (j, p) in ps.iter().enumerate() {
                let (inside, _) = ppi_ppo(x, p);
                if inside.bits() > 1 {
                    rest /= &inside;
                    want.push((i as u32, j as u32, inside));
                }
            }
            rests.push(rest);
        }
        assert_eq!(pieces, want);
        assert_eq!(outside, rests);
    }

    /// `shares_a_factor` by its definition, a gcd of every pair.
    fn shares_a_factor_by_pairs(xs: &[BigUint]) -> Vec<bool> {
        (0..xs.len())
            .map(|i| (0..xs.len()).any(|j| j != i && !gcd_uint(&xs[i], &xs[j]).is_one()))
            .collect()
    }

    /// The table method and the tree method of `shares_a_factor` give the pairwise answer on
    /// arithmetic progressions on both sides of the table method's condition (the largest value
    /// at most the bits of all the values): each method is run on every case, whichever side
    /// the case is on, and `shares_a_factor` itself takes the table on 164 of the 384. (Moved
    /// from zedc-presburger `pncx_shared_factor_methods_agree`.)
    #[test]
    fn the_shared_factor_methods_agree() {
        let (mut table_side, mut tree_side) = (0, 0);
        for start in 1..7u32 {
            for stride in [1u32, 2, 3, 5, 6, 30, 97, 210] {
                for n in [1u32, 2, 3, 5, 8, 13, 40, 120] {
                    let small: Vec<u32> = (0..n).map(|i| start + i * stride).collect();
                    let xs: Vec<BigUint> = small.iter().map(|&v| BigUint::from(v)).collect();
                    let top = start + (n - 1) * stride;
                    let want = shares_a_factor_by_pairs(&xs);
                    let table = zed_numtheory::shares_a_factor_by_table(&small, top);
                    assert_eq!(table, want, "{small:?}");
                    assert_eq!(shares_a_factor_by_tree(&xs), want, "{small:?}");
                    assert_eq!(shares_a_factor(&xs), want, "{small:?}");
                    match dense_values(&xs) {
                        Some(dense) => {
                            assert_eq!(dense, (small, top));
                            table_side += 1;
                        }
                        None => tree_side += 1,
                    }
                }
            }
        }
        assert_eq!((table_side, tree_side), (164, 220));
    }

    /// Where `shares_a_factor` changes method: 97 (7 bits) with 90 ones is 97 bits of values,
    /// so the largest value, 97, is at most the bits and the table answers; with 89 ones it is
    /// not. A value over `u32::MAX` and no values at all go to the tree. (Moved from
    /// zedc-presburger `pncx_shared_factor_method_boundary`.)
    #[test]
    fn the_shared_factor_method_boundary() {
        let with_ones = |v: BigUint, ones: usize| {
            let mut xs = vec![v];
            xs.extend(vec![big(1); ones]);
            xs
        };
        assert_eq!(
            dense_values(&with_ones(big(97), 90)).map(|(_, top)| top),
            Some(97)
        );
        assert_eq!(dense_values(&with_ones(big(97), 89)), None);
        for ones in [89, 90] {
            let xs = with_ones(big(97), ones);
            assert_eq!(shares_a_factor(&xs), vec![false; ones + 1]);
        }
        // Equal values above 1 share a factor on both sides; a value 1 shares none.
        for ones in [0, 200] {
            let mut xs = with_ones(big(97), ones);
            xs.push(big(97));
            assert_eq!(dense_values(&xs).is_some(), ones == 200);
            let mut want = vec![false; ones + 2];
            want[0] = true;
            want[ones + 1] = true;
            assert_eq!(shares_a_factor(&xs), want);
        }
        let wide = big(1) << 200u32;
        for odd in [big(1 << 32), wide.clone()] {
            assert_eq!(dense_values(&with_ones(odd, 300)), None);
        }
        assert_eq!(dense_values(&with_ones(big(u64::from(u32::MAX)), 0)), None);
        assert_eq!(dense_values::<BigUint>(&[]), None);
        assert_eq!(shares_a_factor::<BigUint>(&[]), Vec::<bool>::new());
        // A wide value among small ones: the tree, with the pairwise answer.
        let xs = vec![big(6), wide, big(35), big(11)];
        assert_eq!(shares_a_factor(&xs), vec![true, true, false, false]);
    }

    /// The tree side on wide values (40 words each, and 1 among them, a repeated value and a
    /// product of two others), against the pairwise answer. (Moved from zedc-presburger
    /// `the_kernel_trees_agree_on_wide_values`, its shared-factor half.)
    #[test]
    fn the_shared_factors_of_wide_values_are_the_pairwise_ones() {
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut wide = || {
            let mut v = big((next() >> 20) | 1);
            for _ in 0..40 {
                v = (v << 64u32) + big(next());
            }
            v
        };
        for k in [1usize, 2, 3, 16, 17] {
            let mut xs: Vec<BigUint> = (0..k).map(|_| wide()).collect();
            xs.push(big(1));
            if k >= 3 {
                xs.push(xs[1].clone());
                xs.push(&xs[0] * &xs[2]);
            }
            assert_eq!(dense_values(&xs), None);
            assert_eq!(shares_a_factor(&xs), shares_a_factor_by_pairs(&xs), "k {k}");
        }
    }
}

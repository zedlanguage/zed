//! The natural coprime base of a list of positive integers, and each integer factored over it:
//! the copy for zedc-check (`check/coprime.rs`, which roots share a prime) and
//! zedc-presburger (`modular.rs` `coprime_factorization`, the moduli over pairwise coprime
//! bases), plan row DRY-coprime-bases-one, and zedc-int (`Core::same`, the equality of
//! products of powers, by `coprime_base_exponents`), plan row PERF-coprime-base-wide-few. Its
//! inputs are often one integer of many bits among a few small ones that share its primes; on
//! those Bernstein's `ppi` and pair steps take gcds of two wide numbers, O(M(n) log n), so such
//! inputs take `with_one_wide` (gcds against the small ones and strips of their powers,
//! O(M(n)), proved there) under the bound proved at `one_wide`. A few inputs of one word each
//! take factor refinement on words (`zed_numtheory::coprime_base_u64`) up to the measured
//! switchover `WORD_INPUTS`.
//!
//! Source: D. J. Bernstein, "Factoring into coprimes in essentially linear time", J.
//! Algorithms 54(1), 2005, pp. 1-30, doi:10.1016/j.jalgor.2004.04.009. Checked 2026-11-19 in
//! the author's preprint (cr.yp.to/lineartime/dcba-20040404.pdf, its text read in full for
//! sections 7, 11, 12, 13, 15 and 18). The journal version read 2026-11-21 (PDF, LibGen,
//! verification only): its sections 7, 11, 13, 15, 16, 17 and 18 have the same numbers and
//! titles, and Theorem 7.3, Theorem 11.1, Algorithms 11.3, 11.4, 13.2, 15.3, 16.2, 17.3,
//! 18.1 and Theorem 17.4 are at those numbers there; Theorem 11.1 (1) reads "If n ⩾ 0 and
//! 2^n ⩾ lg a then gcd{x_n, y_n} = 1", the round bound used below. What is used:
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
//! Algorithms 15(2), 1993, pp. 199-222, doi:10.1006/jagm.1993.1038; sections 1 and 2 read
//! 2026-11-20, PDF page images, LibGen, verification only; the later sections not read). Its
//! method, p. 201: "given m = m1 m2, we compute d = gcd(m1, m2) and write m = (m1/d)(d^2)(m2/d).
//! This process is then continued until all factors are relatively prime. A similar method is
//! used in the case where there are more than two inputs"; its bound, pp. 201-202,
//! "O((log m)^2) bit operations" in "the naive arithmetic model" (abstract, p. 199), quadratic
//! in the bits. Counted in gcds, each new number is split against every element of the base
//! it meets, O(k^2) gcds for `k` elements, as for `k` distinct primes, each tried against all
//! before it (this count is ours, not the paper's). Bernstein's
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

use std::borrow::{Borrow, Cow};

use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};

use super::{div_rem_uint, gcd_uint, mul_uint, rem_uint, trees};

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

/// The natural coprime base of some positive integers and the multiplicity of each element in
/// each integer: what [`CoprimeBase`] gives with each factor `q = e ^ k` replaced by `k`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CoprimeExponents {
    /// The elements, as [`CoprimeBase::elements`].
    pub elements: Vec<BigUint>,
    /// For each input, in the order given, `(e, k)` with `k >= 1` the multiplicity of
    /// `elements[e]` in the input, for each element that shares a prime with it, by increasing
    /// `e`. A multiplicity is below the bits of its input, so it fits in a `u64`.
    pub exponents: Vec<Vec<(u32, u64)>>,
}

/// The natural coprime base `cb S` of `xs` and each of `xs` over it, every `x` above 0 (see
/// the module comment for the method and its proof). Inputs may repeat. For 4 and 8 the
/// base is 2 (4 = 2^2, 8 = 2^3); for 6 and 12 it is 2 and 3; for 4 alone it is 4, and for 1
/// alone it is empty.
///
/// At most `WORD_INPUTS` inputs, each of one word, take the word path (`words`); one input
/// much wider than all the others together (the condition at `one_wide`) takes
/// `with_one_wide`, O(M(n)) for `n` bits at a fixed width of the others; all other inputs take
/// `by_halves`, Bernstein's algorithms.
pub fn coprime_base<L: Borrow<BigUint>>(xs: &[L]) -> CoprimeBase {
    // At most `WORD_INPUTS` word inputs, the measured switchover documented there; then word
    // inputs of at most `FACTOR_BITS` bits, the measured switchover documented there.
    let word_base = (words(xs).map(|ws| zed_numtheory::coprime_base_u64(&ws)))
        .or_else(|| factor_words(xs).map(|ws| zed_numtheory::coprime_base_by_factoring(&ws)));
    if let Some((elements, exponents)) = word_base {
        // `c ^ k` divides a word input, so it is a word and `k < 64`.
        let factors = (exponents.into_iter())
            .map(|ks| {
                (ks.into_iter())
                    .map(|(e, k)| {
                        let k = u32::try_from(k).expect("a multiplicity in a word is below 64");
                        (e, BigUint::from(elements[e as usize].pow(k)))
                    })
                    .collect()
            })
            .collect();
        let elements = elements.into_iter().map(BigUint::from).collect();
        return CoprimeBase { elements, factors };
    }
    let Some(w) = one_wide(xs) else {
        return by_halves(xs);
    };
    let (mut out, ks) = with_one_wide(xs, w);
    // `pow_uint` by squaring, O(M(n)) for each of the at most `m` elements of the wide input,
    // `m` the bits of the others (proved at `with_one_wide`).
    out.factors[w] = (ks.into_iter())
        .map(|(e, k)| (e, super::pow_uint(&out.elements[e as usize], k)))
        .collect();
    out
}

/// [`coprime_base`] with multiplicities in place of factors, for zedc-int `Core::same`, which
/// compares products of powers by their exponents over the base. On the wide input of
/// `with_one_wide` the multiplicities are found without building the powers; on the word path
/// they are counted by word divisions; on every other input each factor `q` of element `e` is
/// divided by `e` ([`strip`]), O(M(bits q)).
pub fn coprime_base_exponents<L: Borrow<BigUint>>(xs: &[L]) -> CoprimeExponents {
    // At most `WORD_INPUTS` word inputs, then word inputs of at most `FACTOR_BITS` bits, the
    // measured switchovers documented there.
    let word_base = (words(xs).map(|ws| zed_numtheory::coprime_base_u64(&ws)))
        .or_else(|| factor_words(xs).map(|ws| zed_numtheory::coprime_base_by_factoring(&ws)));
    if let Some((elements, exponents)) = word_base {
        let elements = elements.into_iter().map(BigUint::from).collect();
        return CoprimeExponents {
            elements,
            exponents,
        };
    }
    let (base, wide) = match one_wide(xs) {
        Some(w) => {
            let (base, ks) = with_one_wide(xs, w);
            (base, Some((w, ks)))
        }
        None => (by_halves(xs), None),
    };
    let mut exponents: Vec<Vec<(u32, u64)>> = (base.factors.into_iter())
        .map(|f| {
            (f.into_iter())
                .map(|(e, q)| (e, multiplicity(q, &base.elements[e as usize])))
                .collect()
        })
        .collect();
    if let Some((w, ks)) = wide {
        exponents[w] = ks;
    }
    CoprimeExponents {
        elements: base.elements,
        exponents,
    }
}

/// The most inputs, each of one word, that the word path takes: `zed_numtheory::
/// coprime_base_u64`, factor refinement on words, O(k^2) word gcds for `k` inputs (proved
/// there), against `by_halves`, near linear in `k` but with an allocation in each step on big
/// integers and the product and remainder trees.
///
/// A measured switchover, not a proved bound: the largest `k` at which the word path is the
/// cheaper on every family of `num::bench::the_word_crossover_axis` (author decision A96),
/// which keeps `k = WORD_INPUTS` and `k = WORD_INPUTS + 1` on its axis. Instructions/bytes,
/// measured 2026-11-20 on Linux x86_64, load 71.5 of 32 cores (the counts are instructions, so
/// the load moves them little):
///
/// | family   | k  | word path     | `by_halves`     |
/// |----------|----|---------------|-----------------|
/// | distinct | 12 | 14,634/1,504  | 14,987/2,964    |
/// | shared   | 12 | 37,473/1,504  | 666,066/64,580  |
/// | random   | 12 | 121,101/1,504 | 724,070/56,884  |
/// | distinct | 13 | 16,389/1,592  | 15,578/3,137    |
/// | shared   | 13 | 41,350/1,592  | 798,578/79,905  |
/// | random   | 13 | 161,572/1,848 | 879,475/70,769  |
///
/// Only the distinct primes (no prime shared, refinement's worst case: each new input is tried
/// against every element before it) cross here; on shared and random words the word path
/// stays the cheaper past `k = 128`, so a later caller with many shared words may want a
/// switch on more than the count. Rerun the bench for each target platform and after a change
/// to code generation.
///
/// What relies on it: only the cost. Both paths give `cb S` (Bernstein's Theorem 7.3, proved
/// at each), so any value gives the same answers; `tests::the_paths_agree_at_the_word_
/// switchover` holds the two paths equal at `WORD_INPUTS` and one more. Used by `words`, the
/// one test of the path, so by `coprime_base` and `coprime_base_exponents`. Its first caller
/// is zedc-int `Core::same`, whose roots are mostly a few small integers (l01_24
/// `equal_cores_scale_with_the_bits_of_the_exponent`, roots 9 and 3, and 6, 2 and 3).
pub(super) const WORD_INPUTS: usize = 12;

/// The inputs as words when there are at most [`WORD_INPUTS`] of them and each is below
/// `2^64`; otherwise `None`.
fn words<L: Borrow<BigUint>>(xs: &[L]) -> Option<Vec<u64>> {
    if xs.len() > WORD_INPUTS {
        return None;
    }
    xs.iter().map(|x| x.borrow().to_u64()).collect()
}

/// The most bits of the largest of the word inputs that are factored into primes
/// (`zed_numtheory::coprime_base_by_factoring` and `shares_a_factor_by_factoring`, linear in
/// the count beside one `factor` an input) rather than taken through the trees (`by_halves`,
/// `shares_a_factor_by_tree`, O(M(N) log^2 N) and O(M(N) log k)). Pollard's rho costs about
/// `2^(b/4)` products on a product of two primes of `b / 2` bits, so past some width the trees
/// are the cheaper. That figure is Pollard's heuristic; up to 44 bits the cost of `factor` on
/// one input also has a proved bound, a constant (Brent's rho with `c = 1`,
/// doi:10.1007/BF01933190, bounded by a table over every prime below 2^22, and Lehman's method,
/// doi:10.1090/S0025-5718-1974-0340163-2; every step at `zed_numtheory::factor`,
/// PROOF-factored-coprime-cost), so the factoring path is proved linear in the count.
///
/// The factoring path is taken only from [`FACTOR_INPUTS`] inputs on: factoring costs a fixed
/// amount for each input at a width, and the trees' share for each input grows with the count
/// (3 to 4 times the instructions an input at 8 times the inputs), so the crossover is in both.
///
/// Measured switchovers, not proved bounds (author decision A96), from
/// `num::bench::the_factor_bits_crossover_axis` (2026-11-20, load 51, instructions of
/// factoring over those of the trees, base / shared inputs; under 1 means factoring is the
/// cheaper). The worst family at a width is the disjoint products of two primes of half the
/// width, where rho takes about `2^(b/4)` products: at 4096 inputs 0.39 at 33 bits, 0.51 at
/// 39, 0.80 at 43 and 1.36 at 47; at 512 inputs 1.1 at 27 bits, 1.48 at 31, 2.59 at 43.
/// Distinct primes (a primality test each) are the cheaper by factoring at 512 inputs and more
/// at every width (0.31 to 0.82; 0.13 to 0.22 at 4096) and the dearer at 64 and fewer (1.1 to
/// 2.2); chains `p_i p_(i+1)` lie between (0.09 to 0.35 at 4096 up to 47 bits). So the path is
/// taken where it is the cheaper on every family measured: 44 bits and 4096 inputs. The width
/// one past it (45 bits) and the count below it (2048 inputs) are on the axis.
///
/// What relies on them: only the cost. Both methods give `cb S` and the same shared inputs
/// (proved at each), so any values give the same answers; `tests::the_factored_paths_agree`
/// holds the methods equal on both sides. Used by `factor_words`, the one test of the path,
/// so by `coprime_base`, `coprime_base_exponents` and `shares_a_factor`. Run the axis again for
/// each target platform and after a change to code generation or to `zed_numtheory::factor`.
pub(super) const FACTOR_BITS: u32 = 44;

/// The fewest inputs that take the factoring path: see [`FACTOR_BITS`], where both are measured.
pub(super) const FACTOR_INPUTS: usize = 4096;

/// The inputs as words when there are at least [`FACTOR_INPUTS`] of them, each is below `2^64`
/// and the largest has at most [`FACTOR_BITS`] bits; otherwise `None`.
fn factor_words<L: Borrow<BigUint>>(xs: &[L]) -> Option<Vec<u64>> {
    if xs.len() < FACTOR_INPUTS {
        return None;
    }
    let ws: Vec<u64> = xs
        .iter()
        .map(|x| x.borrow().to_u64())
        .collect::<Option<_>>()?;
    let top = ws.iter().copied().max().unwrap_or(0);
    (top.checked_ilog2().map_or(0, |l| l + 1) <= FACTOR_BITS).then_some(ws)
}

/// The `k` of `q = e ^ k`, for `e >= 2` and `q` a power of it.
fn multiplicity(mut q: BigUint, e: &BigUint) -> u64 {
    let k = strip(&mut q, e);
    debug_assert!(
        q.is_one(),
        "a factor over a coprime base is a power of its element"
    );
    k
}

/// The index `w` of the one wide input that [`with_one_wide`] takes, when there is one: the
/// first of the widest inputs, when the bits `m` of all the other inputs above 1 together are
/// at most `log2` of its bits `n` (`m <= floor(log2 n)`); otherwise `None`. Every input must be
/// above 0. With `m > 0` the condition makes `w` strictly the widest, since then some other
/// input has between 2 and `m` bits and `m < n`.
// Complexity tradeoff: the condition is the proved bound under which `with_one_wide` costs no
// more in order than the general path's bound, not a timed switch. `with_one_wide` costs
// O(m M(n)) plus the general path on `O(m)` inputs of at most `m` bits each (proved there);
// with `m <= log2 n` that is O(M(n) log n), and the general path costs at least one `ppi` of
// the wide input, O(M(n) log n) by Bernstein's Theorem 11.1 bound on its rounds (`lg lg a + 1`
// squarings and gcds of numbers of up to `n` bits). Measured on zedc-int `Core::same`, where a
// wide root meets a few small ones (`l01_24 equality_over_a_wide_odd_base_scales_with_its_bits`
// and `equality_over_a_wide_base_scales_with_its_bits`, `m` = 4): see `with_one_wide`. Both
// sides of the condition are measured by `num::bench::the_one_wide_crossover_axis` (author
// decision A96).
pub(super) fn one_wide<L: Borrow<BigUint>>(xs: &[L]) -> Option<usize> {
    let mut wide: Option<(usize, u64)> = None;
    let mut all = 0u64;
    for (i, x) in xs.iter().enumerate() {
        let b = x.borrow().bits();
        assert!(b > 0, "a coprime base of positive integers, given 0");
        if b < 2 {
            continue;
        }
        all += b;
        if wide.is_none_or(|(_, n)| b > n) {
            wide = Some((i, b));
        }
        // Stop once the condition cannot hold. Proof: with `n` the widest seen so far and the
        // final widest `n' >= n`, the final `m` is at least `all - n`. If the final widest is
        // still to come, every input seen is among the others, so `m >= all >= all - n`. If it
        // has been seen, it is the current widest, and the rest seen are among the others, so
        // `m >= all - n`. And `floor(log2 n') <= 63`, since `n'` is a `u64`. So `all - n > 63`
        // makes `m > floor(log2 n')`, and the answer is `None`. Without this stop the scan
        // reads the bits of every input, about 33 instructions each: 3% of
        // `num::bench::the_coprime_base_of_the_first_n_primes_scales`, whose answer the scan
        // never changes. 63 is the bit width of `u64` less 1, not a tuned value. A zero input
        // after the stop is refused by `by_halves`, which checks every input.
        if wide.is_some_and(|(_, n)| all - n > 63) {
            return None;
        }
    }
    let (w, n) = wide?;
    (all - n <= u64::from(n.ilog2())).then_some(w)
}

/// The natural coprime base of `xs` when `xs[w]` is wide (`n` bits) and the others above 1 are
/// `m` bits together, with the multiplicity of each element in `xs[w]`: the base and the factors
/// of every input but `w`, whose list is left empty, and the `(e, k)` of `xs[w]` by increasing
/// `e`.
///
/// Method. Let `P` be the product of the other inputs. Strip the powers of `d_0 = gcd(xs[w],
/// P)` from `t = xs[w]` ([`strip`], `k_0 >= 1` of them), then of `d_1 = gcd(t, d_0)`, and so
/// on until `d_r = 1`. The base is `cb` of the other inputs and the `d_i`, by the general path
/// ([`by_halves`], on inputs of at most `m` bits each), with what is left of `t` added when it
/// is above 1. The multiplicity of an element `e` in `xs[w]` is the sum over `i` of `k_i` times
/// that of `e` in `d_i`.
///
/// Proof, with `x = xs[w]` and `T` the closure of the inputs `S` (D. J. Bernstein, "Factoring
/// into coprimes in essentially linear time", J. Algorithms 54(1), 2005, pp. 1-30,
/// doi:10.1016/j.jalgor.2004.04.009, Section 7, quoted in the module comment: `T` is the least
/// set holding `S` and 1 closed under products, exact quotients and gcds; Theorem 7.3: a
/// coprime base of `S` inside `T - {1}` is `cb S`). The descent of steps 1 to 3 is not from
/// that paper; its proof is all here:
/// 1. Each `d_i` divides the `t` it is stripped from, so `k_i >= 1`: `d_0 = gcd(x, P)` divides
///    `x`, and `d_(i+1) = gcd(t_(i+1), d_i)` divides `t_(i+1)`.
/// 2. Invariant: every prime of `P` that divides `t_i` divides `d_i`. At `i = 0`, a prime of
///    `P` and of `x` divides `gcd(x, P)`. If it holds at `i` and a prime `p` of `P` divides
///    `t_(i+1)`, it divides `t_i` (a divisor of it), so `p | d_i`, so `p | gcd(t_(i+1), d_i)`.
/// 3. The rounds end, at most `Omega(d_0) <= log2 d_0 <= m` of them (`Omega` the count of
///    prime factors with multiplicity): `strip` leaves `d_i` not dividing `t_(i+1)`, so
///    `d_(i+1) = gcd(t_(i+1), d_i)` is a proper divisor of `d_i`, and `Omega(d_(i+1)) <
///    Omega(d_i)`. At the end `d_r = 1`, so by step 2 the last `t` has no prime of `P`, and
///    `x = t * prod d_i ^ k_i` by construction.
/// 4. The result is pairwise coprime: the elements of `cb` of the others and the `d_i` are, and
///    each has only primes of `P` (each `d_i` divides `P`), which `t` has none of.
/// 5. It is a coprime base of `S`: each other input is a product of powers of `cb` of a set
///    holding it, and `x` is by step 3, with the multiplicity of `e` the sum given above.
/// 6. Each element lies in `T`: `P` is a product, `d_0` a gcd, `t_(i+1) = t_i / d_i ^ k_i` an
///    exact quotient and `d_(i+1)` a gcd, all of members of `T`; `cb U` of a set `U` of
///    members of `T` is by its definition (Section 7) a set of members of the closure of `U`,
///    which lies inside `T` since `T` is closed and holds `U`; and the last `t` is in `T`.
/// 7. By Theorem 7.3 a coprime base of `S` inside `T - {1}` is `cb S`, the result of
///    [`by_halves`] on the same inputs.
///
/// Cost: `P` and `d_0` cost O(M(m)) and O(n) (`gcd_uint` reduces `x` modulo the narrow `P`,
/// streamed over its words when `P` has at most 64 bits); each of the at most `m` rounds costs
/// a `strip` of `t` (O(M(n)), proved at `strip`) and a gcd of `t` and the narrow `d_i` (O(n)
/// again); the general path runs on at most `m` other inputs and `m` divisors of `P`, of at
/// most `m` bits each, O(m^2) bits, polynomial in `m`; the multiplicities in the `d_i` are
/// strips of numbers of at most `m` bits. So O(m M(n) + poly(m)), which is O(M(n)) at a fixed
/// `m`. Complexity tradeoff: the general path on the same inputs runs `ppi` and the pair steps
/// on `x` itself, gcds of two numbers of `n` bits each, O(M(n) log n): on
/// `l01_24 equality_over_a_wide_odd_base_scales_with_its_bits` (roots `3^n * 2`, 3 and 2, `n` =
/// 2^20) 22.8e9 instructions at the first size and 11.9 times that at 8 times the size, past
/// the limit 10.5 (DRY-coprime-bases-one, 2026-11-20); factor refinement, zedc-int's copy
/// before PERF-coprime-base-wide-few, took the same strips and gcds against each element, which
/// is O(M(n)) here too, but O(k^2) gcds for `k` elements on the general inputs.
pub(super) fn with_one_wide<L: Borrow<BigUint>>(
    xs: &[L],
    w: usize,
) -> (CoprimeBase, Vec<(u32, u64)>) {
    let x = xs[w].borrow();
    let others: Vec<usize> = (0..xs.len()).filter(|&i| i != w).collect();
    let p = (others.iter())
        .map(|&i| xs[i].borrow())
        .fold(BigUint::one(), |p, y| mul_uint(&p, y));
    let mut t = x.clone();
    let mut d = gcd_uint(&t, &p);
    let mut ds: Vec<(BigUint, u64)> = Vec::new();
    while !d.is_one() {
        let k = strip(&mut t, &d);
        debug_assert!(k >= 1, "each d divides the t it is stripped from (step 1)");
        let next = gcd_uint(&t, &d);
        ds.push((d, k));
        d = next;
    }
    let mut inputs: Vec<&BigUint> = others.iter().map(|&i| xs[i].borrow()).collect();
    inputs.extend(ds.iter().map(|(d, _)| d));
    let inner = by_halves(&inputs);
    let mut ks = vec![0u64; inner.elements.len()];
    let mut factors = inner.factors.into_iter();
    let mut out = CoprimeBase {
        elements: Vec::new(),
        factors: vec![Vec::new(); xs.len()],
    };
    for &i in &others {
        out.factors[i] = factors.next().expect("one factor list for each input");
    }
    for ((_, k), f) in ds.iter().zip(factors) {
        for (e, q) in f {
            ks[e as usize] += k * multiplicity(q, &inner.elements[e as usize]);
        }
    }
    out.elements = inner.elements;
    if !t.is_one() {
        out.elements.push(t);
        ks.push(1);
    }
    let ks = (ks.into_iter().enumerate())
        .filter(|&(_, k)| k > 0)
        .map(|(e, k)| (index(e), k))
        .collect();
    (out, ks)
}

/// The natural coprime base of `xs` by Bernstein's algorithms, for any inputs above 0.
///
/// First, which inputs share a prime with any other, by `shares_by_table_or_tree` (never by
/// factoring: `coprime_base` sends the word lists of at most `FACTOR_BITS` bits to the
/// factoring path before this, and the crossover benches measure this as the general method,
/// so it must not take that path itself): an input that
/// shares none is its own element, its one factor itself. Only the others go through the
/// halves (Algorithm 18.1, `base_by_halves`) and are then split over their base (Algorithm
/// 15.3, `split`) to get their factors.
pub(super) fn by_halves<L: Borrow<BigUint>>(xs: &[L]) -> CoprimeBase {
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
    for (k, (x, s)) in leaves
        .iter()
        .zip(shares_by_table_or_tree(&leaves))
        .enumerate()
    {
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

/// The multiplicity `k` of `c >= 2` in `rest`, divided out of it. For `c` a power of 2, `2^t`,
/// `k` is the trailing zeros of `rest` over `t`, rounded down, taken out by one shift.
/// Otherwise, after one division by `c`, which ends it when `c` does not divide `rest`, the
/// powers `P_i = c ^ (2^i)` are built by squaring. A power is tested against `rest` by its
/// remainder when its bits are at least the square of the bits of the last one tested (`c`
/// first) and their square is at most the bits of `rest`. The squaring stops at the first
/// `P_J` that fails such a test or is above `rest`, with `x = rest mod P_J`, or at the last
/// `P_(J-1)` whose square is surely above `rest`, with `x = rest`. Either way the multiplicity
/// left is below `2^J`, `x` has it, and `x` is below `P_J`. From `i = J - 1` down to 0, `x` is
/// replaced by `x / P_i`, adding `2^i` to `k`, when `P_i` divides it, and by `x mod P_i` when
/// not, which has the same multiplicity, below `2^i`, since `c` to that multiplicity plus one
/// divides `P_i`; either way `x` is below `P_i` after, so the widths halve. Last, `rest` is
/// divided once by `c ^ k`, the product of the `P_i` of the binary digits of `k`; but when `x`
/// started as `rest` and no step left a remainder with a quotient above 0, `x` is already
/// `rest / c ^ k` (each step either divided it or left it as it was), and is taken as it is
/// (item PERF-wide-odd-base-ratio-9: 23% fewer instructions on
/// `equality_over_a_wide_odd_base_scales_with_its_bits` at 2^20 digits, whose time is almost
/// all `strip(3 ^ (n - 1), 3)`). With the
/// kernel's arithmetic a test of `P_i` costs about `n log d` for `n` bits of `rest` and `d` of
/// `P_i`, and the tested `log d` at least double and stay below `log n / 2`, so the tests cost
/// O(n log n); the squares and the steps down cost O(M(w)) for `w` the bits of `P_J`, at most
/// `n` and at most about the square of the bits of `c ^ k`; and the last division
/// O(n log (k bits(c))). So `strip` costs O(M(n)) = O(n log n), and about O(n) for a small
/// `c ^ k` (item SCALE-fix-strip-odd). Dividing all of `rest` by each `P_i` on the way up cost
/// O(n log^2 n), and num-bigint's division made that O(n^2) for a small `c`; building the
/// powers up to the width of `rest` before any test cost O(M(n)) for every `k`, and grew 85
/// times in bytes on `equality_over_a_wide_base_scales_with_its_bits`. (Moved from zedc-int
/// `int.rs` by PERF-coprime-base-wide-few, 2026-11-20, with its tests.)
///
/// The ratio this predicts from `n` to `8n` (item PERF-wide-odd-base-ratio-9). Every product
/// and division above num-bigint's leaf goes through the transforms of `fast.rs`, whose cost
/// is `TRANSFORM_COST N log2 N` for `N` points, the power of two at or above the
/// coefficients, one 64-bit word each (`transform_cost`; a division is a fixed number of such
/// products, Newton's iteration costing about 5/3 of one). So the variable of the `log` is
/// `N`, not the bits or digits of the input. Step by step, for `T(N) = a N log2 N + b N`, the
/// transforms plus the linear passes (carries, CRT, copies), with `a, b >= 0`:
/// 1. the squares, the steps down and the first division each run on widths that halve from
///    the top, so each sums to at most twice its top term: `T` of the top width, times a
///    constant;
/// 2. from `n` to `8n` every width of the top terms is 8 times as large, and since 8 is a power
///    of two the padding to `N` is the same at both sizes, so the top terms go from `N` to
///    `8N` points, and the terms below the top are the same set at both sizes plus 3 wider;
/// 3. `T(8N) / T(N) = 8 (a (log2 N + 3) + b) / (a log2 N + b)`, which is at most
///    `8 (log2 N + 3) / log2 N`, reached when `b = 0`, and at least 8, reached when `a = 0`.
///
/// For `strip(3 ^ (n - 1), 3)` at `n = 2^20` digits `rest` has 1,661,951 bits, 25,968 words;
/// the top step down divides it by `3 ^ (2^19)`, 12,985 words, with products of about
/// 12,985 by 12,985 words, 25,969 coefficients, on `N = 2^15` points; at `8n`, `2^18`. So
/// the predicted ratio is at most `8 * 18 / 15 = 9.6`. Measured on instructions at load 61
/// (2026-11-20): the square of `3 ^ (n/2)` 8.70, the division of `3 ^ (n-2)` by
/// `3 ^ (n/2)` 8.99, the squarings 8.81, the steps down 9.34, the whole strip 9.26, and the
/// bench `equality_over_a_wide_odd_base_scales_with_its_bits` 9.25: each between 8 and 9.6.
/// The bound in digits, `8 ln(8n) / ln n = 9.20` for `n = 2^20`, takes the `log` of a
/// variable 32 times as large as `N` (`2^20` against `2^15`), and so predicts a ratio closer
/// to 8 than this code's cost has. Below the leaves num-bigint's Toom-3 (about `n^1.465`)
/// runs only on the small widths, which are the same at both sizes (step 2).
pub fn strip(rest: &mut BigUint, c: &BigUint) -> u64 {
    if c.count_ones() == 1 {
        let t = c.bits() - 1;
        let k = rest.trailing_zeros().expect("rest is at least 1") / t;
        *rest >>= k * t;
        return k;
    }
    let (q, r) = div_rem_uint(rest, c);
    if !r.is_zero() {
        return 0;
    }
    *rest = q;
    let mut pows: Vec<Cow<'_, BigUint>> = vec![Cow::Borrowed(c)];
    // The bits of the last power tested by its remainder.
    let mut tested = 0u64;
    let mut x: Cow<'_, BigUint> = loop {
        let top = pows.last().expect("the power left by the last step");
        if **top > *rest {
            pows.pop();
            break Cow::Borrowed(&*rest);
        }
        // Complexity tradeoff: a test by remainder costs about `n log d`, the kernel's division
        // of `n` bits by `d` (about ten products of `d` bits for each `d` bits of `rest`). It
        // ends the squaring early when `c ^ k` is small, which keeps `strip` near O(n) there;
        // above `d = sqrt(n)` the squares left cost less than a test, so none is made there.
        // Without tests the squares cost O(M(n)) whatever `k` (85 times the bytes from 65536 to
        // 524288 bits on `equality_over_a_wide_base_scales_with_its_bits`); with a test at
        // every width allowed by the first rule the odd-base test took 13.9 times the
        // instructions from 2^19 to 2^22 digits, against 11.1 (2026-11-07).
        if top.bits() >= tested * tested && top.bits() * top.bits() <= rest.bits() {
            tested = top.bits();
            let r = rem_uint(rest, top);
            if !r.is_zero() {
                pows.pop();
                break Cow::Owned(r);
            }
        }
        // `top ^ 2` is at least `2 ^ (2 (bits - 1))`.
        if 2 * (top.bits() - 1) >= rest.bits() {
            break Cow::Borrowed(&*rest);
        }
        let square = mul_uint(top, top);
        pows.push(Cow::Owned(square));
    };
    let mut more = 0u64;
    // Whether `x` is `rest / c ^ more`: so when it starts as `rest`, and while every step
    // either divides or leaves `x` as it was (a quotient of 0, so `x mod P_i = x`). Then `x`
    // is the quotient the last division below would compute, and that division and the
    // product of its divisor are skipped.
    let mut quotient = matches!(x, Cow::Borrowed(_));
    for (i, pw) in pows.iter().enumerate().rev() {
        let (q, r) = div_rem_uint(&x, pw);
        x = Cow::Owned(match r.is_zero() {
            true => {
                more += 1 << i;
                q
            }
            false => {
                quotient &= q.is_zero();
                r
            }
        });
    }
    if quotient {
        if more > 0 {
            let q = x.into_owned();
            *rest = q;
        }
        return 1 + more;
    }
    drop(x);
    // The smaller powers first, so that each product is of a number by a wider one.
    let divisor = pows
        .iter()
        .enumerate()
        .filter(|(i, _)| more >> i & 1 == 1)
        .map(|(_, pw)| pw)
        .fold(None, |acc: Option<Cow<'_, BigUint>>, pw| {
            Some(match acc {
                None => Cow::Borrowed(&**pw),
                Some(a) => Cow::Owned(mul_uint(&a, pw)),
            })
        });
    if let Some(d) = divisor {
        #[cfg(test)]
        tests::STRIP_LAST_DIVISIONS.with(|n| n.set(n.get() + 1));
        let (q, r) = div_rem_uint(rest, &d);
        debug_assert!(r.is_zero(), "c ^ {more} divides what is left");
        *rest = q;
    }
    1 + more
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
// (`the_shared_factor_methods_agree`). Sparse word values (`V > B`) of at most `FACTOR_BITS`
// bits, at least `FACTOR_INPUTS` of them, are factored into primes instead
// ([`zed_numtheory::shares_a_factor_by_factoring`]): one `factor` each, about `V^(1/4)`
// products in a typical case by Pollard's rho (expected, not proved), and at most a proved
// constant below 2^44 (Brent's rho with c = 1, doi:10.1007/BF01933190, bounded by a table over
// every prime below 2^22, and Lehman 1974, doi:10.1090/S0025-5718-1974-0340163-2; every step at
// `zed_numtheory::factor`, PROOF-factored-coprime-cost), then a count of each prime in
// O(k) expected hash operations, so linear in `k` at a fixed width; a measured switchover, at
// `FACTOR_BITS`. Measured 2026-11-20 (load 42, `pncx_common_factor_tree_side_scale`, 512 and
// 4096 values): 16.105 on the trees before, 6.683 after. What is left on the tree: wide
// values, fewer than `FACTOR_INPUTS` sparse values, and values past `FACTOR_BITS`; no method of
// lower order than O(M(B) log k) is known for those (Bernstein 2005 gives B^(1 + o(1))), and
// the tree side is 13 to 18 times the work at 8 times the values (plan row
// PERF-negated-chain-unsolved); COMPLEXITY.md C31c.
pub fn shares_a_factor<L: Borrow<BigUint>>(xs: &[L]) -> Vec<bool> {
    // The table where its proved condition holds; then word values of at most `FACTOR_BITS`
    // bits, the measured switchover documented there; then the trees.
    if let Some((small, top)) = dense_values(xs) {
        return zed_numtheory::shares_a_factor_by_table(&small, top);
    }
    match factor_words(xs) {
        Some(ws) => zed_numtheory::shares_a_factor_by_factoring(&ws),
        None => shares_a_factor_by_tree(xs),
    }
}

/// [`shares_a_factor`] without the factoring path: the table where its proved condition holds,
/// otherwise the trees. The general method that `by_halves` uses.
fn shares_by_table_or_tree<L: Borrow<BigUint>>(xs: &[L]) -> Vec<bool> {
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
    // Two singletons, as at every lowest merge of `base_by_halves`: `cb({a} ∪ {b})` is
    // `cb{a, b}`, which `pair_base` (Algorithm 13.2) gives from `a` and `b` themselves, its
    // steps 2-3 and 13 printing the parts `ppo(a, b)` and `ppo(b, a)` that the two `split`s
    // below would take out. So the two remainder trees and the sorts are skipped; the answer is
    // the same set, and this function's output has no set order. It serves the lowest merges
    // of lists longer than `WORD_INPUTS` or with an input wider than a word. Measured
    // 2026-11-20 by running the bench set with and without it (instructions, which the load
    // moves little): without it, l01_24 `equality_over_a_wide_base_scales_with_its_bits`
    // (`(2^n * 3)^1000`) costs 1.32% more at its first size and 0.26% more at 8 times it, and
    // l01_29 `bounding_a_chain_of_products` (products by even numbers) 0.07% more; no bench
    // costs less.
    if let ([a], [b]) = (&p[..], &q[..]) {
        let mut base = Vec::new();
        pair_base(&mut base, a.clone(), b.clone());
        return base;
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
    use std::cell::Cell;
    use std::collections::BTreeMap;

    thread_local! {
        /// How many times `strip` has divided `rest` by the product of its powers at its end.
        pub(super) static STRIP_LAST_DIVISIONS: Cell<u64> = const { Cell::new(0) };
    }

    fn big(v: u64) -> BigUint {
        BigUint::from(v)
    }

    /// The prime factors of `n > 0` with their exponents, by `zed_numtheory::factor` (tested
    /// on its own in zed-numtheory; trial division took about 2^32 steps on a word with two
    /// prime factors near 2^32, as the word path's tests have).
    fn primes_of(n: u64) -> BTreeMap<u64, u32> {
        (zed_numtheory::factor(n).into_iter())
            .map(|(p, e)| {
                (
                    p,
                    u32::try_from(e).expect("an exponent in a word is below 64"),
                )
            })
            .collect()
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

    /// `coprime_base` is `cb S` with valid factors, and on word inputs (the word path when there
    /// are at most `WORD_INPUTS` of them) `by_halves` gives the same elements and factors, so
    /// both paths are held to the definition.
    fn check(xs: &[u64]) {
        let bx: Vec<BigUint> = xs.iter().map(|&x| big(x)).collect();
        let cb = valid(&bx, Some(&by_primes(xs)));
        assert_eq!(by_value(&cb), by_value(&by_halves(&bx)), "{xs:?}");
        exponents_are_the_factors(&bx);
    }

    /// The elements sorted and each input's factors as (element, power) sorted, so that two
    /// results that list the elements in different orders compare.
    type ByValue = (Vec<BigUint>, Vec<Vec<(BigUint, BigUint)>>);
    fn by_value(cb: &CoprimeBase) -> ByValue {
        let mut elements = cb.elements.clone();
        elements.sort();
        let factors = (cb.factors.iter())
            .map(|f| {
                let mut v: Vec<_> = (f.iter())
                    .map(|(e, q)| (cb.elements[*e as usize].clone(), q.clone()))
                    .collect();
                v.sort();
                v
            })
            .collect();
        (elements, factors)
    }

    /// `coprime_base_exponents` gives the elements of `coprime_base` in its order, and for each
    /// factor `q` of element `c` the `k` with `c ^ k = q`.
    fn exponents_are_the_factors(xs: &[BigUint]) {
        let cb = coprime_base(xs);
        let ex = coprime_base_exponents(xs);
        assert_eq!(ex.elements, cb.elements, "{xs:?}");
        assert_eq!(ex.exponents.len(), xs.len());
        for (ks, fs) in ex.exponents.iter().zip(&cb.factors) {
            assert_eq!(ks.len(), fs.len(), "{xs:?}: {ks:?}");
            for (&(e, k), (f, q)) in ks.iter().zip(fs) {
                assert_eq!(e, *f, "{xs:?}");
                assert!(k >= 1, "{xs:?}");
                let c = &cb.elements[e as usize];
                assert_eq!(&crate::num::pow_uint(c, k), q, "{xs:?}: {c} ^ {k}");
            }
        }
    }

    /// `xs` takes the one-wide path, and it gives what the general path gives on the same
    /// inputs: the same elements and the same factors of each input.
    fn both_paths(xs: &[BigUint]) {
        let w = one_wide(xs).unwrap_or_else(|| panic!("{xs:?} has no one wide input"));
        let others: u64 = (xs.iter().enumerate())
            .filter(|&(i, x)| i != w && x.bits() > 1)
            .map(|(_, x)| x.bits())
            .sum();
        assert!(others <= u64::from(xs[w].bits().ilog2()));
        let general = by_value(&by_halves(xs));
        assert_eq!(by_value(&valid(xs, None)), general, "{xs:?}");
        // `with_one_wide` itself, as `coprime_base` may take the word path on word inputs.
        let (mut one, ks) = with_one_wide(xs, w);
        one.factors[w] = (ks.into_iter())
            .map(|(e, k)| (e, crate::num::pow_uint(&one.elements[e as usize], k)))
            .collect();
        assert_eq!(by_value(&one), general, "{xs:?}");
        exponents_are_the_factors(xs);
    }

    fn pow(p: u64, k: u64) -> BigUint {
        crate::num::pow_uint(&big(p), k)
    }

    /// PERF-coprime-base-wide-few: the one-wide path against the general path on the inputs
    /// it is for (zedc-int `Core::same`'s roots `3^n * 2`, 3 and 2 and `2^n * 3`, 2 and 3) and
    /// on adversarial ones: shared primes at unequal exponents, one input a power of another,
    /// the wide input a power of a small one times one more factor of it (two rounds of the
    /// descent), a power of 2 against 4 (an odd exponent left over), the wide input coprime to
    /// the rest, ones and repeats among the others, the wide input alone, and widths from 2
    /// bits to past the division leaf of 4096 bits.
    #[test]
    fn the_one_wide_path_gives_the_general_base() {
        let n = 5000;
        let cases: Vec<Vec<BigUint>> = vec![
            vec![pow(3, n) * 2u32, big(3), big(2)],
            vec![pow(2, n) * 3u32, big(2), big(3)],
            vec![big(12), pow(2, 500) * pow(3, 777)],
            vec![pow(2, 1000) * pow(3, 1000), big(6)],
            vec![pow(6, 999) * 2u32, big(6)],
            vec![big(10), pow(10, 700)],
            vec![big(4), pow(2, 1001)],
            vec![big(9), pow(3, 1001)],
            vec![big(4), big(8), pow(2, 300) * pow(5, 100)],
            vec![big(6), pow(5, 500) * 7u32],
            vec![big(1), big(3), pow(3, 600) * pow(7, 90), big(3), big(1)],
            vec![pow(7, 3000)],
            vec![big(1), pow(5, 40), big(1)],
            vec![big(2), big(3), big(5), big(7), pow(210, 300) * pow(7, 11)],
            vec![big(15), pow(3, 2000) * pow(5, 1999) * (pow(2, 64) + 1u32)],
        ];
        for xs in &cases {
            both_paths(xs);
        }
        // Random: up to four others from small values, of at most 12 bits together, and a wide
        // input of their primes at random exponents times random odd words, at least `2^m` bits.
        let (mut rng, seed) = crate::seed::Rng::fresh("the_one_wide_path_gives_the_general_base");
        let smalls = [1u64, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 18, 30];
        for case in 0..200 {
            let mut xs: Vec<BigUint> = Vec::new();
            let mut m = 0u64;
            for _ in 0..1 + rng.below(4) {
                let y = rng.pick(&smalls);
                let b = u64::from(64 - y.leading_zeros());
                if y > 1 && m + b > 12 {
                    continue;
                }
                if y > 1 {
                    m += b;
                }
                xs.push(big(y));
            }
            let mut x = big(1);
            for p in [2u64, 3, 5, 7] {
                x *= pow(p, rng.below_u64(1500));
            }
            for _ in 0..rng.below(3) {
                x *= rng.next_u64() | 1;
            }
            // At least 2 bits, so that `x` is above 1 when the others are all 1.
            while x.bits() < (1 << m).max(2) {
                x *= rng.next_u64() | 1;
            }
            let at = rng.below(xs.len() + 1);
            xs.insert(at, x);
            assert!(one_wide(&xs).is_some(), "case {case}, seed {seed}");
            both_paths(&xs);
        }
    }

    /// Where `one_wide` changes path: the bits `m` of the others at `floor(log2 n)` for `n`
    /// bits of the widest take the one-wide path, and one more bit does not. Ones count for
    /// nothing; two widest inputs of equal width never take it unless all else is 1.
    #[test]
    fn the_one_wide_condition_at_its_boundary() {
        // 3 is 2 bits; 8 to 15 are 4 bits, `floor(log2 4)` = 2.
        assert_eq!(one_wide(&[big(3), big(8)]), Some(1));
        assert_eq!(one_wide(&[big(15), big(3), big(1)]), Some(0));
        // 7 is 3 bits.
        assert_eq!(one_wide(&[big(7), big(8)]), None);
        // 2 and 3 are 4 bits; `2^15` is 16 bits (log 4), `2^14` 15 bits (log 3).
        assert_eq!(one_wide(&[big(2), big(1 << 15), big(3)]), Some(1));
        assert_eq!(one_wide(&[big(2), big(1 << 14), big(3)]), None);
        assert_eq!(one_wide(&[big(1 << 20), big(1 << 20)]), None);
        assert_eq!(one_wide(&[big(1), big(1 << 20), big(1)]), Some(1));
        assert_eq!(one_wide(&[big(1), big(1)]), None);
        assert_eq!(one_wide::<BigUint>(&[]), None);
        // Both sides give the natural base.
        for xs in [[big(3), big(8)], [big(7), big(8)], [big(6), big(12)]] {
            valid(&xs, None);
            assert_eq!(by_value(&coprime_base(&xs)), by_value(&by_halves(&xs)));
        }
        // The wide input last, after others of 20 bits together and ones: `2^(2^20)` has
        // `2^20 + 1` bits, `floor(log2)` 20.
        let mut late: Vec<BigUint> = [3u64, 5, 7, 9, 11, 1, 1].map(big).to_vec();
        late.extend([big(13), big(1), pow(2, 1 << 20)]);
        assert_eq!(
            late[..9]
                .iter()
                .map(|x| x.bits())
                .filter(|&b| b > 1)
                .sum::<u64>(),
            20
        );
        assert_eq!(one_wide(&late), Some(9));
        late.insert(0, big(2));
        assert_eq!(one_wide(&late), None);
    }

    /// `one_wide`'s condition by a scan of every input, with no early stop.
    fn one_wide_by_full_scan(xs: &[BigUint]) -> Option<usize> {
        let bits: Vec<u64> = xs.iter().map(|x| x.bits()).collect();
        let n = bits.iter().copied().filter(|&b| b > 1).max()?;
        let w = bits
            .iter()
            .position(|&b| b == n)
            .expect("the widest is one of them");
        let m: u64 = bits.iter().copied().filter(|&b| b > 1).sum::<u64>() - n;
        (m <= u64::from(n.ilog2())).then_some(w)
    }

    /// `one_wide`'s early stop (once the bits of the others seen pass 63) gives the answer of
    /// the full scan: random lists, half of up to 7 inputs of 1 to 4 bits (where the condition
    /// often holds) and half of up to 199 inputs of 1 to 70 bits (where the stop is reached),
    /// with ones among them and, in two thirds, one power of 3 of 102 to 1,624 bits at a random
    /// place.
    #[test]
    fn the_one_wide_stop_agrees_with_the_full_scan() {
        let (mut rng, seed) =
            crate::seed::Rng::fresh("the_one_wide_stop_agrees_with_the_full_scan");
        let (mut some, mut none) = (0, 0);
        for case in 0..2000 {
            let (k, top) = if case % 2 == 0 { (8, 4) } else { (200, 70) };
            let k = rng.below(k);
            let mut xs: Vec<BigUint> = (0..k)
                .map(|_| match rng.below(4) {
                    0 => big(1),
                    _ => pow(2, rng.below(top) as u64) + big(1),
                })
                .collect();
            if rng.below(3) != 0 {
                let at = rng.below(xs.len() + 1);
                xs.insert(at, pow(3, 1 << (6 + rng.below(5))));
            }
            let want = one_wide_by_full_scan(&xs);
            assert_eq!(one_wide(&xs), want, "case {case}, seed {seed}");
            if want.is_some() { some += 1 } else { none += 1 }
        }
        assert!(
            some > 100 && none > 100,
            "both answers met: {some} and {none}"
        );
    }

    #[test]
    #[should_panic(expected = "a coprime base of positive integers, given 0")]
    fn a_zero_input_after_the_one_wide_stop_is_refused() {
        let mut xs: Vec<BigUint> = zed_numtheory::first_primes(40)
            .into_iter()
            .map(big)
            .collect();
        xs.push(big(0));
        assert_eq!(one_wide(&xs), None);
        coprime_base(&xs);
    }

    #[test]
    #[should_panic(expected = "a coprime base of positive integers, given 0")]
    fn a_zero_input_is_refused_before_either_path() {
        coprime_base(&[pow(2, 100), big(0)]);
    }

    #[test]
    #[should_panic(expected = "a coprime base of positive integers, given 0")]
    fn a_zero_input_is_refused_on_the_word_path() {
        coprime_base(&[big(6), big(0)]);
    }

    /// PERF-coprime-base-wide-few: the word path (`words`, `zed_numtheory::coprime_base_u64`)
    /// against the definition and `by_halves`, through `check`. Where `words` changes path: at
    /// `WORD_INPUTS` word inputs it takes them, at one more or with one input of 65 bits it
    /// does not. Adversarial words: the largest word, the top bit alone, powers of 2 up to the
    /// top bit, the square of the largest prime below 2^32, a word that is a power of another
    /// input, repeats and ones, and chains in which each input shares a prime with the next.
    /// Random: lists of up to `WORD_INPUTS` products of small primes at random exponents, and
    /// random words, some times a random small prime.
    #[test]
    fn the_word_path_gives_the_general_base() {
        let ws: Vec<u64> = (1..=WORD_INPUTS as u64).map(|i| i * 6).collect();
        let bx: Vec<BigUint> = ws.iter().map(|&w| big(w)).collect();
        assert_eq!(words(&bx), Some(ws.clone()));
        check(&ws);
        let mut more = bx.clone();
        more.push(big(7));
        assert_eq!(words(&more), None);
        let mut wide = bx[1..].to_vec();
        wide.push(pow(2, 64));
        assert_eq!(words(&wide), None);
        let p32 = 4_294_967_291u64;
        check(&[u64::MAX]);
        check(&[u64::MAX, 3, 5, 17, 257, 65537, 641, 6_700_417]);
        check(&[1 << 63, 1 << 62, 4, 8, 3 << 61]);
        check(&[p32 * p32, p32, p32 * 2]);
        check(&[3u64.pow(40), 9, 3u64.pow(40), 1, 1]);
        check(&[6, 10, 15, 21, 35, 77, 143, 221]);
        check(&[2 * 3, 3 * 5, 5 * 7, 7 * 11, 11 * 13, 13 * 2]);
        check(&[
            2u64.pow(60),
            2u64.pow(6) * 3,
            3u64.pow(30) * 2,
            6u64.pow(20),
        ]);
        let (mut rng, seed) = crate::seed::Rng::fresh("the_word_path_gives_the_general_base");
        let smalls = [2u64, 3, 5, 7, 11, 13];
        for case in 0..300 {
            let k = 1 + rng.below(WORD_INPUTS);
            let ws: Vec<u64> = (0..k)
                .map(|_| {
                    if rng.below(4) == 0 {
                        let w = rng.next_u64() | 1;
                        return if rng.below(2) == 0 {
                            w
                        } else {
                            (w >> 4) * rng.pick(&smalls)
                        };
                    }
                    let mut w = 1u64;
                    for _ in 0..rng.below(5) {
                        let p = rng.pick(&smalls);
                        for _ in 0..1 + rng.below(6) {
                            if let Some(v) = w.checked_mul(p) {
                                w = v;
                            }
                        }
                    }
                    w
                })
                .collect();
            let bx: Vec<BigUint> = ws.iter().map(|&w| big(w)).collect();
            assert!(words(&bx).is_some(), "case {case}, seed {seed}");
            check(&ws);
        }
    }

    /// The two paths agree at the switchover `WORD_INPUTS` (author decision A96): at
    /// `WORD_INPUTS` inputs `coprime_base` takes the word path and at one more the general one,
    /// so on lists of both lengths `zed_numtheory::coprime_base_u64` is run directly and its
    /// elements and powers held equal to `by_halves`'s, and `coprime_base` to both. Families as
    /// on `num::bench::the_word_crossover_axis`: distinct primes, products of three shared
    /// primes, random words at the top bit; and random products of small primes.
    #[test]
    fn the_paths_agree_at_the_word_switchover() {
        let (mut rng, seed) = crate::seed::Rng::fresh("the_paths_agree_at_the_word_switchover");
        let primes = zed_numtheory::first_primes(2 * WORD_INPUTS + 2);
        let smalls = [2u64, 3, 5, 7, 11, 13];
        for k in [WORD_INPUTS, WORD_INPUTS + 1] {
            let mut lists = vec![primes[..k].to_vec()];
            for case in 0..50 {
                lists.push(match case % 3 {
                    0 => (0..k)
                        .map(|_| (0..3).map(|_| primes[rng.below(k)]).product())
                        .collect(),
                    1 => (0..k).map(|_| rng.next_u64() | 1 << 63).collect(),
                    _ => (0..k)
                        .map(|_| (0..1 + rng.below(4)).map(|_| rng.pick(&smalls)).product())
                        .collect(),
                });
            }
            for ws in lists {
                let bx: Vec<BigUint> = ws.iter().map(|&w| big(w)).collect();
                assert_eq!(words(&bx).is_some(), k <= WORD_INPUTS, "k {k}");
                let (elements, exponents) = zed_numtheory::coprime_base_u64(&ws);
                let word = from_words(elements, exponents);
                let general = by_value(&by_halves(&bx));
                assert_eq!(by_value(&word), general, "k {k}, {ws:?}, seed {seed}");
                assert_eq!(
                    by_value(&coprime_base(&bx)),
                    general,
                    "k {k}, {ws:?}, seed {seed}"
                );
            }
        }
    }

    /// `coprime_base`'s result from a word method's elements and exponents.
    fn from_words(elements: Vec<u64>, exponents: Vec<Vec<(u32, u64)>>) -> CoprimeBase {
        CoprimeBase {
            factors: (exponents.into_iter())
                .map(|ks| {
                    (ks.into_iter())
                        .map(|(e, n)| (e, crate::num::pow_uint(&big(elements[e as usize]), n)))
                        .collect()
                })
                .collect(),
            elements: elements.into_iter().map(big).collect(),
        }
    }

    /// `k` primes from a random start at or above `2^(b - 1)`, in a row; `b` bits each while
    /// there are that many of `b` bits.
    fn primes_in_a_row(rng: &mut crate::seed::Rng, b: u32, k: usize) -> Vec<u64> {
        let next = |p: u64| zed_numtheory::next_prime(p).expect("a prime below 2^64");
        let mut ps = vec![next((1 << (b - 1)) + rng.below_u64(1 << (b / 4)))];
        while ps.len() < k {
            ps.push(next(ps[ps.len() - 1] + 1));
        }
        ps
    }

    /// PERF-negated-chain-unsolved: the factoring methods (`zed_numtheory::
    /// coprime_base_by_factoring`, `shares_a_factor_by_factoring`) and the switch to them. On
    /// short lists of `WORD_INPUTS + 1` and 40 inputs, widths `FACTOR_BITS` and one more, the
    /// methods are run directly: the base is `cb S` by the definition (`by_primes`) and has
    /// `by_halves`'s elements and factors, and the shared inputs are
    /// `shares_a_factor_by_tree`'s. Families as on `num::bench::the_factor_bits_crossover_axis`:
    /// distinct primes of the width, products and chains of primes of half the width, and
    /// random products of those primes with repeats and small primes; a 1 among the inputs in
    /// some lists. Then the switch: `FACTOR_INPUTS - 1` inputs never take the path, and
    /// `FACTOR_INPUTS` take it exactly when the largest has at most `FACTOR_BITS` bits; on
    /// `FACTOR_INPUTS` distinct primes and disjoint products at both widths `coprime_base` and
    /// `shares_a_factor` agree with `by_halves` and the tree, and on the factoring side the
    /// exponents are the factors.
    #[test]
    fn the_factored_paths_agree() {
        let (mut rng, seed) = crate::seed::Rng::fresh("the_factored_paths_agree");
        for b in [FACTOR_BITS, FACTOR_BITS + 1] {
            // Primes of `ceil(b / 2)` bits, whose products of two have `b` bits or one more or
            // less: at `FACTOR_BITS + 1` the products are past `FACTOR_BITS`.
            let h = b.div_ceil(2);
            for k in [WORD_INPUTS + 1, 40] {
                let halves = primes_in_a_row(&mut rng, h, k + 1);
                let mut lists = vec![
                    primes_in_a_row(&mut rng, b, k),
                    (0..k).map(|i| halves[i] * halves[i + 1]).collect(),
                    (0..k)
                        .map(|i| halves[i] * halves[(i + k / 2) % (k + 1)])
                        .collect(),
                ];
                for _ in 0..20 {
                    let mut ws: Vec<u64> = (0..k)
                        .map(|_| match rng.below(3) {
                            0 => rng.pick(&halves) * rng.pick(&halves),
                            1 => rng.pick(&halves) * rng.pick(&[1u64, 2, 3, 4, 9, 12]),
                            _ => rng.pick(&[2u64, 3, 5, 6, 8, 25]),
                        })
                        .collect();
                    if rng.below(4) == 0 {
                        ws[rng.below(k)] = 1;
                    }
                    lists.push(ws);
                }
                for ws in lists {
                    let bx: Vec<BigUint> = ws.iter().map(|&w| big(w)).collect();
                    let at = format!("b {b}, k {k}, {ws:?}, seed {seed}");
                    let (elements, exponents) = zed_numtheory::coprime_base_by_factoring(&ws);
                    let factored = by_value(&from_words(elements, exponents));
                    assert_eq!(factored.0, by_primes(&ws), "{at}");
                    assert_eq!(factored, by_value(&by_halves(&bx)), "{at}");
                    assert_eq!(
                        zed_numtheory::shares_a_factor_by_factoring(&ws),
                        shares_a_factor_by_tree(&bx),
                        "{at}"
                    );
                }
            }
            let k = FACTOR_INPUTS;
            let halves = primes_in_a_row(&mut rng, h, 2 * k);
            let distinct = primes_in_a_row(&mut rng, b, k);
            let pairs: Vec<u64> = (0..k).map(|i| halves[2 * i] * halves[2 * i + 1]).collect();
            for ws in [distinct, pairs] {
                let bx: Vec<BigUint> = ws.iter().map(|&w| big(w)).collect();
                let at = format!("b {b}, {} .. {}, seed {seed}", ws[0], ws[k - 1]);
                let top = ws.iter().map(|w| 64 - w.leading_zeros()).max().unwrap_or(0);
                assert_eq!(factor_words(&bx).is_some(), top <= FACTOR_BITS, "{at}");
                assert_eq!(factor_words(&bx[1..]), None, "{at}");
                assert_eq!(
                    by_value(&coprime_base(&bx)),
                    by_value(&by_halves(&bx)),
                    "{at}"
                );
                assert_eq!(shares_a_factor(&bx), shares_a_factor_by_tree(&bx), "{at}");
                if top <= FACTOR_BITS {
                    exponents_are_the_factors(&bx);
                }
            }
        }
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

    /// Item PERF-wide-odd-base-ratio-9: when the steps down start from `rest` itself and each
    /// either divides or leaves `x` as it was, `x` ends as `rest / c ^ k`, and `strip` takes it
    /// without its last division. On `3 ^ 499 * u` for `u` below 3, `3 ^ 256` is the last power
    /// built (its square is above `rest`), so the steps start from `rest`; before the shortcut
    /// each strip made the last division once. On `3 ^ 5 * 1000`, a step leaves a remainder
    /// with a quotient above 0, so the last division stays.
    #[test]
    fn stripping_from_rest_itself_skips_the_last_division() {
        for u in [1u32, 2] {
            let mut rest = BigUint::from(3u32).pow(500) * u;
            STRIP_LAST_DIVISIONS.with(|n| n.set(0));
            assert_eq!(strip(&mut rest, &big(3)), 500, "u = {u}");
            assert_eq!(rest, BigUint::from(u), "u = {u}");
            assert_eq!(STRIP_LAST_DIVISIONS.with(Cell::get), 0, "u = {u}");
        }
        let mut rest = BigUint::from(3u32).pow(5) * 1000u32;
        STRIP_LAST_DIVISIONS.with(|n| n.set(0));
        assert_eq!(strip(&mut rest, &big(3)), 5);
        assert_eq!(rest, big(1000));
        assert_eq!(STRIP_LAST_DIVISIONS.with(Cell::get), 1);
    }

    /// (Moved from zedc-int `int.rs` with `strip` by PERF-coprime-base-wide-few.)
    #[test]
    fn stripping_a_power_of_2_agrees_with_dividing_once_per_factor() {
        for t in [1u32, 2, 3, 7, 64, 65, 200] {
            let c = BigUint::from(1u32) << t;
            for (z, odd) in [
                (0u32, 1u32),
                (1, 3),
                (6, 5),
                (64, 7),
                (199, 1),
                (1000, 9),
                (1001, 1),
            ] {
                let mut rest = BigUint::from(odd) << z;
                let (mut want, mut k) = (rest.clone(), 0u64);
                while (&want % &c).is_zero() {
                    want /= &c;
                    k += 1;
                }
                assert_eq!(strip(&mut rest, &c), k, "t = {t}, z = {z}");
                assert_eq!(rest, want, "t = {t}, z = {z}");
            }
        }
    }

    /// Item SCALE-fix-strip-odd: `strip` by a factor that is not a power of 2, odd, even,
    /// composite, a power of another, or wider than a word, against dividing once per factor,
    /// on `c ^ k * u` for multiplicities `k` around powers of 2 and random `u`, some with a
    /// divisor and a quotient past the kernel's division leaf of 4096 bits, where it weighs
    /// num-bigint's division against its others (it picks num-bigint at these widths). (Moved
    /// from zedc-int `int.rs` with `strip` by PERF-coprime-base-wide-few.)
    #[test]
    fn stripping_any_factor_agrees_with_dividing_once_per_factor() {
        let (mut rng, _) =
            crate::seed::Rng::fresh("stripping_any_factor_agrees_with_dividing_once_per_factor");
        let wide = BigUint::from_slice(&[0x8000_0001, 0x1234_5679, 0xdead_beef, 0x7]);
        let factors = [
            BigUint::from(3u32),
            BigUint::from(5u32),
            BigUint::from(6u32),
            BigUint::from(9u32),
            BigUint::from(15u32),
            BigUint::from(12u32),
            BigUint::from(u64::MAX),
            wide,
        ];
        let ks = [
            0u64, 1, 2, 3, 7, 8, 9, 63, 64, 65, 255, 1000, 4095, 4096, 6000,
        ];
        for c in &factors {
            // The largest `k` with `c ^ k` of at most 20,000 bits: from 6435 bits (`wide ^ 65`)
            // to 18,000 (`5 ^ 6000`).
            let top = ks.iter().copied().filter(|k| k * c.bits() <= 20_000).max();
            for k in ks {
                if k * c.bits() > 20_000 {
                    continue;
                }
                for words in [1usize, 2, 40, 300] {
                    // A `u` of 300 words only at the largest `k`, once for each factor: the
                    // last division then has a divisor and a quotient past 4096 bits, and
                    // the test stays small.
                    if words == 300 && Some(k) != top {
                        continue;
                    }
                    let u = BigUint::from_slice(
                        &(0..2 * words)
                            .map(|_| rng.next_u64() as u32)
                            .collect::<Vec<_>>(),
                    ) + 1u32;
                    let mut rest = c.pow(u32::try_from(k).unwrap()) * &u;
                    let (mut want, mut times) = (rest.clone(), 0u64);
                    while (&want % c).is_zero() {
                        want /= c;
                        times += 1;
                    }
                    assert_eq!(strip(&mut rest, c), times, "c = {c}, k = {k}, u = {u}");
                    assert_eq!(rest, want, "c = {c}, k = {k}, u = {u}");
                }
            }
        }
    }
}

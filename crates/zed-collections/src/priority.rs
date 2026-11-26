//! Treap priorities drawn at random once per run, so that a treap's expected depth is
//! `O(log n)` for every input whose keys are distinct points of the draw, chosen keys included
//! (COMPLEXITY.md K123, plan row PERF-treap-seeded-priorities). Keys at one point tie under
//! every draw (below); where the point is a type's 64-bit digest a program can choose many such
//! keys (plan row PERF-set-tied-digest-depth).
//!
//! A [`Priorities`] is a polynomial `q` of degree 4 ([`Priorities::new`]) or 7
//! ([`Priorities::eight_wise`]) over the field of the prime `p = 2^64 - 59`, its coefficients
//! drawn uniformly from `0..p` from the operating system's random bytes when the priorities are
//! first asked for. The values of a `q` of degree `d` at any `d + 1` distinct points are
//! independent and uniform over `0..p`, since the matrix that maps the coefficients to the
//! values is a Vandermonde matrix, invertible on distinct points.
//!
//! Source. R. Seidel and C. R. Aragon, "Randomized search trees", Algorithmica 16(4/5),
//! 464-497, 1996, doi:10.1007/BF01940876. Section 3, before Theorem 3.3, and the start of
//! section 6 give this generator: "Xi = q(i) mod U for 1 <= i <= n, where U >= n^3 is a prime
//! number and q is a degree 7 polynomial whose coefficients are drawn uniformly and
//! independently from {0, ..., U - 1}". Departures: the prime is the fixed `2^64 - 59`, so the
//! paper's `U >= n^3` holds for `n <= 2^21` and the bounds below carry the `n(n - 1)/p` of a
//! tie instead; the points are the keys (or their hash, below), not `1..n`; and degree 4 is
//! used where the paper's 5-wise case suffices. Seidel and Aragon state the independence
//! without proof; the Vandermonde step is from M. N. Wegman and J. L. Carter, "New hash
//! functions and their use in authentication and set equality", J. Comput. Syst. Sci. 22(3),
//! 265-279, 1981, doi:10.1016/0022-0000(81)90033-7, section 1: over a finite field, "the class
//! of polynomials of degree less than n" is strongly universal_n, since through any n distinct
//! points "there is exactly one polynomial of degree less than n" ("the standard linear algebra
//! proof which uses the invertibility of the Vandermonde matrix also works with finite
//! fields"). Checked 2026-11-19 against both papers' text (Seidel and Aragon sections 3, 4 and
//! 6; Wegman and Carter section 1) and Crossref. Tested by
//! zed-numtheory's `tests::m64_59::p_is_the_largest_prime_below_2_to_the_64` (the field) and
//! `a_priority_is_the_polynomial_at_the_key` (the evaluation); no test measures independence.
//!
//! Degree 7, for the treaps whose set operations are joins of two treaps (`set::union_if_agree`,
//! `set::difference_if_agree`, `set::symmetric`, `settings::combine`; plan row
//! PROOF-join-work-limited-independence, COMPLEXITY.md K123). The proof is the cross-review's
//! (round R7, part (c), checked by three seats; the plan row has the record): under
//! 8-wise independence two fixed key sets `S`, `T` with `v` in `S` and `u != v` in `T` have
//! `Pr[v holds the strict maximum of S and u that of T] <= C1 / (|S| |T|)` (a sixth central
//! moment, or mixed moments of orders 2 and 4, after the two endpoint values are fixed: six-wise
//! independence remains). Each node an operation visits is charged to a pair (pivot, node
//! visited) for which such an event on fixed intervals of the operands holds, and the sum of
//! `1 / (|S| |T|)` over the pairs of two sorted key sets of `m <= n` keys is
//! `O(m log(1 + n/m))`. With `N` keys in all, the work is then at most
//! `C0 m log(1 + n/m) + 64 m N min(1, delta + N(N - 1)/(2p))` in expectation, `delta` the
//! probability that two keys share a point of `q` (the case `T0` below): the finger bound when
//! no two keys share a point and `N^3 / p` is bounded. It costs three multiplications more per
//! priority (205 against 114 instructions per evaluation, measured by the cross-review), so
//! the other treaps keep degree 4, and the treaps of degree 7 keep each node's priority when
//! they rebuild it rather than evaluating `q` again. So kept, degree 7 did 1.0006, 1.0017 and
//! 1.0014 times the work of degree 4 over the kernel's benchmarks under seeds 0, 1 and 2: the
//! forced atoms, which make many settings, 1.019 under each seed, and the benchmarks whose work
//! follows the drawn shape from 0.975 to 1.056, a new draw giving a new shape.
//!
//! The steps of the degree-7 bound (PROOF-kernel-proofdoc3a-gaps (k); the record is
//! `cd-xr/XR-xor-shape-rounds-4-6/r7/codex/R7_CODEX.md`, R7-Q1 (c), which re-derives the
//! cross-review's R4 Lemmas 6.2 and 6.3; step 1 below is re-derived here, step 2 is the record's
//! sketch). Fix the operands `X`, `Y` and every key's point before `q` is drawn; `m <= n` their
//! sizes, `N <= m + n <= p` the keys in all. Write `w = 1 - x/p` for a priority `x`.
//!
//! 1. The event bound. Let `S`, `T` be fixed sets of keys at distinct points, `v` in `S`,
//!    `u != v` in `T`. Take `u` out of `S` and `v` out of `T` (a set of two or more keys keeps at
//!    least half of its size; a set of one is the one-maximum case of Seidel and Aragon); write
//!    `C` for the competitors the two sets share, `A` for those of `S` alone, `B` of `T` alone.
//!    Fix the priorities `x` of `v` and `y` of `u`. Eight-wise independence leaves the others
//!    six-wise independent and uniform, so any moment of the counts above `x` or `y` built from
//!    at most six competitors has its value under full independence. For a sum `Z` of
//!    independent indicators of mean `mu`, centered terms `Y_i` with `E|Y_i|^k <= Pr[i]`:
//!    `E (Z - mu)^2 <= mu`, `E (Z - mu)^4 <= mu + 3 mu^2` and
//!    `E (Z - mu)^6 <= mu + 25 mu^2 + 15 mu^3 <= 41 mu^3` for `mu >= 1` (expand: the terms with
//!    one index, two indices and three indices). Both endpoints strict maxima means no
//!    competitor of `C` is above `min(x, y)`, none of `A` above `x`, none of `B` above `y`.
//!    (i) If `|C|` is at least a third of the larger of `|S|`, `|T|`: by Markov on the sixth
//!    moment, `Pr <= 41 / (|C| W)^3` with `W = max(w_x, w_y)`, and
//!    `E[min(1, K / W^3)] = O(1/|C|^2)`
//!    for `K = 41/|C|^3` (`W` has density `2W`; split at `W = K^(1/3)`), which is
//!    `O(1 / (|S| |T|))`. (ii) Otherwise two blocks among `A`, `B`, `C` that are disjoint have
//!    sizes `a`, `b` at constant fractions of `|S|` and `|T|`, with means `alpha = a w`,
//!    `beta = b w'` (`w'` the other endpoint's `w`, or `W` for `C`, and `W >= w'`). The mixed
//!    moments of orders `(4, 2)` and `(2, 4)` use at most six competitors and so factor:
//!    `Pr <= min(1, 4 / (alpha^2 beta), 4 / (alpha beta^2)) = min(1, 4 / (alpha beta max(alpha, beta)))`.
//!    Substituting `alpha`, `beta` for `w`, `w'` gives `Pr <= (1/(ab)) J`, `J` the integral
//!    of that minimum over the positive quadrant, which is finite: on `alpha <= beta`, beyond
//!    `beta = 1`, it is at most `integral beta^-2 (1 + log(beta^3)) d beta`, and symmetrically.
//!    Sums over the `p` priorities are at most these integrals plus a term `O(1/p)`, the bound
//!    being monotone in `w`. So `Pr <= C1 / (|S| |T|)`.
//! 2. Summing pairs. For two disjoint colors of a sorted sequence, `a` and `b` keys, the sum
//!    over pairs of opposite colors of `1 / (first color in [v, u] * second color in [v, u])` is
//!    `O(min(a, b) log(1 + max(a, b)/min(a, b)))`: split `1/(ab) = 1/(b(a + b)) + 1/(a(a + b))`;
//!    the first part telescopes to at most one per key of the smaller color, and the second is
//!    bounded by grouping the intervals by dyadic counts of the smaller color, windows of three
//!    blocks, and concavity of `log` (record, R4 Lemma 6.3; not re-derived here). A key in both
//!    operands becomes two adjacent copies, one of each color; an interval's counts only fall.
//! 3. The charging. With all priorities distinct, each node `u` visited at pivot `v` (the root
//!    the recursion splits at) meets one of these events on fixed sets, `I = [v, u]`, `M(S, k)`
//!    meaning `k` holds the strict maximum of `S`: the splits of the other operand `B` at `v` in
//!    `set::union_if_agree`, `set::symmetric` and `settings::combine`, `M((X | Y) & I, v)` and
//!    `M(B & I, u)` (the current interval excludes every earlier pivot, so the sets are the
//!    operands cut to `I`); `set::get` in union, a prefix of that split's path; in
//!    `set::difference_if_agree`, its `get`, the descent of `set::remove`, and the split above a
//!    removed `v`, `M(Y & I, v)` and `M(X & I, u)`; the `set::join` inside `remove` and the split
//!    below a removed `v`, `M((X | Y) & I, v)` and `M((X - {v}) & I, u)`; the final joins (of
//!    `symmetric`, of difference, of `combine` for Meet), `M(D & I, v)` and `M(R & I, u)` with
//!    `(D, R)` the fixed disjoint `(X & Y, X ^ Y)`, `(Y, X - Y)` and `((X | Y) - (X & Y), X & Y)`.
//!    Each pair is charged a constant number of times; equal keys cost `O(1)` each, `O(m)` in
//!    all; a split or join builds no more nodes than it visits. Steps 1 and 2 then bound the
//!    expected work on the draws with distinct priorities by `C0 m log(1 + n/m)`.
//! 4. Ties. The draw is not conditioned on distinct priorities (that would break the
//!    independence); on the other draws the work is at most `64 m N`, and two keys at distinct
//!    points tie with probability `1/p`, so by the union bound these draws add at most
//!    `64 m N min(1, delta + N(N - 1)/(2p))`.
//!
//! The record checked the events of step 3 on every priority order and operand pair of six
//! keys, over the four operations (11,430,720 cases, `r7/codex/probes/r7_events.rs`); that
//! probe is not among the kernel's tests, and no test here measures the bound.
//!
//! The bound. Seidel and Aragon's Lemma 6.1: "Let X be a set of n random variables, each
//! uniformly distributed over a common integer range of size at least n. X has the d-max
//! property if its random variables are (3d + 2)-wise independent", where the `d`-max property
//! is `Pr[X_1 > X_2 > ... > X_d > {X_(d+1), ..., X_m}] <= c/m^d` for every `m` of them. So for
//! `d = 1` and 5-wise independence there is a constant `c` with `Pr[X_1 > X_2, ..., X_m] <=
//! c/m`. Their section 6 shows that the 1-max property alone gives Corollaries 4.5 and 4.6 and
//! Theorem 4.7 (i) and (ii): the expected depth of a node and the expected size of its subtree
//! are `O(log n)`, so "5-wise independence of the random priorities provably suffices" for
//! logarithmic expected search and update times (also their Theorem 3.3). They credit the lemma
//! as "essentially due to Mulmuley", with a proof in K. Mulmuley, "Computational Geometry: An
//! Introduction through Randomized Algorithms", Prentice-Hall, 1994, section 10.1. Read
//! 2026-11-21 (LibGen PDF, resumed over three requests to the full listed size, 461 pages,
//! verification only). Lemma 10.1.13 (p. 408): "Assume that the sequence X_0, ..., X_(n-1)
//! of random variables is (3d + 2)-wise independent. Then, the probability that the first d
//! elements chosen from the set L ∪ D all belong to D is O(1/l^d), for d, l > 0"; the proof
//! fixes one of the d! = O(1) labelings of D and applies Corollary 10.1.12 with t = 3d + 2,
//! which rests on Lemma 10.1.10 (p. 406), a Chebyshev tail bound for (t - d)-wise
//! independent indicators. With `m = l + d` that is Seidel and Aragon's `d`-max property; the
//! book states it for the order in which a configuration space's objects are added, drawn
//! from a pseudo-random generator, not for priorities, which is why they say "essentially".
//! The lemma is used as Seidel and Aragon state it.
//!
//! Equal priorities. Let a node be tied when another node of the treap has its priority, and let
//! `T` be the number of tied nodes. A node `y` that is not tied is an ancestor of `x` exactly when
//! its priority is above every other of the keys from `x` to `y` (Seidel and Aragon's Lemma 4.3:
//! "assuming that all priorities are distinct, xi is an ancestor of xj in T iff among all xh,
//! with h between and including i and j, the item xi has the largest priority"; its proof
//! holds in any tree heap-ordered by priority, however ties are broken: the least common
//! ancestor of `x` and `y` lies between them and is above both), so the depth of `x` is at most
//! `T` plus the number of untied `y` that hold the strict maximum of their range. Only a
//! key whose point of `q` is new to the range from `x` can be such a `y` (a key whose point is
//! met before it in the range ties with that key). Which keys these are is fixed by the keys,
//! not by the draw: on one side of `x`, let `y_k` be the `k`-th of them in the order of distance
//! from `x`. The range from `x` to `y_k` holds at least `k` distinct points of `q`, so `y_k`
//! holds its strict maximum with probability at most `c/k`, and the sum over the fixed `y_k` of
//! both sides bounds the depth by `E[T] + 2c H_n` in expectation. (The `k`-th untied ancestor
//! met is not a fixed key; the sum is over the `y_k`, each counted whether or not it is an
//! ancestor.) Two keys at distinct points of `q` tie with probability `1/p`. Keys whose points
//! are equal tie always: their number adds to `T` whatever the draw, and each use below says what
//! makes two keys one point. In all, a node's expected depth is at most
//! `T0 + n(n - 1)/p + 2c H_n`, `T0` the keys that share their point with another key of the
//! treap. Where the point is a type's 64-bit digest (settings, list cells, sets), `T0` is not
//! bounded by the draw: each step of a digest is a bijection in either argument, so a program can
//! write many distinct literals of one digest (test `a_program_can_write_many_rows_of_one_digest`
//! in `types/bdd/set/tests.rs`).
//!
//! Keys of more than a word ([`Priorities::hash`]) go to `q` through a second polynomial `g` of
//! the same draw, evaluated at a random point `r`. The key's `Hash` stream is read as 64-bit
//! words, the last completed with zero bytes, then its length in bytes as one more word; a word
//! below `p - 1` is one symbol, and a word `w` of `p - 1` or more is the two symbols `p - 1`
//! and `w - (p - 1)`. The symbols `s_1, ..., s_S` give `g = r^S + s_1 r^(S-1) + ... + s_S`.
//! Two distinct streams are two distinct sequences of symbols (no word's symbols begin
//! another's, so the words are read back from the symbols, and the length then says which
//! bytes of the last word are the stream's), so two distinct polynomials in `r` (each has
//! leading coefficient 1 at its own number of symbols), of degree at most `S`, and they agree
//! at a random `r` with probability at most `S/p` (a nonzero polynomial of degree `D` has at
//! most `D` roots). Given `g`, the keys whose `g` differ are distinct points of `q`, drawn
//! independently of `r`. So a treap of `n` keys whose streams are at most `S` symbols long
//! (at most `2(B/8 + 2)` for `B` bytes) and are distinct for distinct keys has
//! `E[T] <= n(n - 1)(S + 1)/p`, below `2^-11 (S + 1)` for `n <= 2^26`, and the expected depth
//! of every node is `O(log n)`.
//!
//! Nothing a program prints may depend on the draw (rule deterministic-checking): a treap that
//! takes these priorities shows only its keys in order, never its shape. The draw is one for
//! the process, so one set of keys still has one shape in every thread of a run. The
//! environment variable `ZED_TREAP_SEED`, a decimal number, fixes the draw, to repeat a run's
//! timing or to compare the output of two draws (test
//! `the_output_is_the_same_under_two_draws_of_the_treap_priorities`). `tools/run_tests.sh
//! --bench` sets it to 0 when it is unset, so that a benchmark's ratio is that of one draw,
//! the same on every run, rather than a random variable.
//!
//! Not proved: the operating system's random bytes are taken as uniform and independent.
//! Classified (PROOF-sweep-zed-kernel): cost only. The draw sets only the priorities, so only
//! the shape of each treap, and nothing printed or compared reads a shape (the paragraph on
//! rule deterministic-checking above; module `types::bdd::set` lists how its digests, order
//! and exclusive or avoid it; test
//! `the_output_is_the_same_under_two_draws_of_the_treap_priorities`). With biased bytes the
//! expected depth bound above may fail, and an operation may take up to `O(n)` per key
//! instead of `O(log n)`; every answer stays the same. The treaps of `treap_set` and
//! `types::bdd::set` keep stacks of their own and are dropped in a loop, so even one that is a
//! path is walked without overflowing the thread's stack. One user does recurse as deep as its
//! treap: the union and the walk of `zedc_preimage::divisors` ("Recursion as deep as the
//! treap"). There a draw far from uniform could make the run overflow its stack and stop, a
//! failure of the run, not a wrong answer. Its expected depth is `O(log n)` under the
//! assumption (paragraph "The bound" above); no tail bound on the depth is proved here.

use std::sync::OnceLock;

// The field of `p = 2^64 - 59`: its arithmetic is zed-numtheory's (DRY-num-words-2026-11-26).
use zed_numtheory::m64_59::{P, add, mul};

/// The draw of one use of treap priorities: the coefficients of `q`, highest first (the first
/// `degree + 1` of `q` are used), and the point `r` of the hash of longer keys.
#[derive(Clone, Copy, Debug)]
struct Draw {
    q: [u64; 8],
    degree: usize,
    r: u64,
}

impl Draw {
    /// `q(x mod P)`, by Horner's rule: `degree` multiplications.
    // `#[inline]` here and on the other steps of a priority (zed-numtheory's `mul` and `add` have
    // it too): the treaps that call them are in other crates, and a call across crates is not
    // inlined without it (it was one crate, zed-kernel's, until DRY-persistent-trees-2026-11-26).
    #[inline]
    fn at(&self, x: u64) -> u64 {
        let x = if x >= P { x - P } else { x };
        self.q[1..=self.degree]
            .iter()
            .fold(self.q[0], |acc, &c| add(mul(acc, x), c))
    }
}

/// The priorities of one treap's keys (module comment). Each use is a `static` of its own,
/// named by a fixed `tag`, so that two uses draw independently and `ZED_TREAP_SEED` gives each
/// the same draw on every run.
pub struct Priorities {
    tag: u64,
    degree: usize,
    /// Whether the draw is that of seed 0 when `ZED_TREAP_SEED` is unset
    /// ([`Priorities::fixed_in_unit_tests`]).
    fixed_in_unit_tests: bool,
    draw: OnceLock<Draw>,
}

impl Priorities {
    /// The priorities of the use named `tag`, drawn on first use: `q` of degree 4, 5-wise
    /// independent.
    pub const fn new(tag: u64) -> Priorities {
        Priorities {
            tag,
            degree: 4,
            fixed_in_unit_tests: false,
            draw: OnceLock::new(),
        }
    }

    /// The priorities of the use named `tag`, drawn on first use: `q` of degree 7, 8-wise
    /// independent, for the treaps whose joins need the finger bound (module comment).
    pub const fn eight_wise(tag: u64) -> Priorities {
        Priorities {
            tag,
            degree: 7,
            fixed_in_unit_tests: false,
            draw: OnceLock::new(),
        }
    }

    /// These priorities, drawn from seed 0 when `ZED_TREAP_SEED` is unset and `unit_test` is
    /// true. A crate passes its own `cfg!(test)`, which is true only in that crate's unit tests,
    /// so that a unit test of a treap's height checks one draw, the same on every run (a test
    /// asserts only what holds for the draw it checks); zed-kernel does. Every other run, the
    /// step tests included, draws from the system's random bytes when the variable is unset.
    // The flag is the caller's, not this crate's `cfg!(test)`: that is true only in the unit tests
    // of zed-collections, and zed-kernel's unit tests relied on seed 0 while this module was in
    // zed-kernel (DRY-persistent-trees-2026-11-26 moved it here).
    pub const fn fixed_in_unit_tests(mut self, unit_test: bool) -> Priorities {
        self.fixed_in_unit_tests = unit_test;
        self
    }

    #[inline]
    fn draw(&self) -> &Draw {
        self.draw
            .get_or_init(|| draw(self.tag, self.degree, self.fixed_in_unit_tests))
    }

    /// The priority of the key `x`, a number: `q(x mod P)`. The 59 numbers from `P` up share
    /// their points with `0` to `58`, so at most 118 keys tie for that reason whatever the draw.
    #[inline]
    pub fn of(&self, x: u64) -> u64 {
        self.draw().at(x)
    }

    /// The priority of a key of any size: `q(g(key))`, `g` the hash of the key's `Hash` stream
    /// at the draw's `r` (module comment). Two keys tie whatever the draw only when their
    /// streams are equal.
    pub fn hash<K: std::hash::Hash + ?Sized>(&self, key: &K) -> u64 {
        let d = self.draw();
        let mut h = Stream {
            r: d.r,
            acc: 1,
            pending: 0,
            filled: 0,
            len: 0,
        };
        key.hash(&mut h);
        d.at(h.end())
    }
}

/// `g` of a stream (module comment), read a 64-bit word at a time by Horner's rule.
// Complexity tradeoff: one multiplication modulo `p` per 8 bytes. Reading 32 bits at a time
// needs no escape, since a half is below `p`, but takes two multiplications per 8 bytes: it
// cost 4.5% of the instructions of `pncx_probe::pncx_wide_divisor_translation_scale`, whose
// one divisor of 336,000 bits is hashed digit by digit.
struct Stream {
    r: u64,
    acc: u64,
    /// The bytes of the word not yet complete, the first in the low byte.
    pending: u64,
    filled: u32,
    len: u64,
}

impl Stream {
    #[inline]
    fn symbol(&mut self, s: u64) {
        self.acc = add(mul(self.acc, self.r), s);
    }

    /// A word as symbols below `p`: itself when it is below `p - 1`, else `p - 1` and then
    /// `w - (p - 1)`, at most 59. No word's symbols begin another's, so the words are read
    /// back from the symbols.
    #[inline]
    fn word(&mut self, w: u64) {
        if w >= P - 1 {
            self.symbol(P - 1);
            self.symbol(w - (P - 1));
        } else {
            self.symbol(w);
        }
    }

    /// `g`: the last word, completed with zero bytes, then the length.
    #[inline]
    fn end(mut self) -> u64 {
        if self.filled > 0 {
            self.word(self.pending);
        }
        self.word(self.len);
        self.acc
    }
}

impl std::hash::Hasher for Stream {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        self.len += bytes.len() as u64;
        let mut rest = bytes;
        while self.filled > 0 && !rest.is_empty() {
            self.pending |= u64::from(rest[0]) << (8 * self.filled);
            self.filled = (self.filled + 1) % 8;
            rest = &rest[1..];
            if self.filled == 0 {
                let w = std::mem::take(&mut self.pending);
                self.word(w);
            }
        }
        let (words, tail) = rest.as_chunks::<8>();
        for w in words {
            self.word(u64::from_le_bytes(*w));
        }
        for &b in tail {
            self.pending |= u64::from(b) << (8 * self.filled);
            self.filled += 1;
        }
    }

    /// Not read: a priority is taken from [`Stream::end`].
    fn finish(&self) -> u64 {
        self.acc
    }
}

/// The draw of the use `tag`, `q` of degree `degree`: from `ZED_TREAP_SEED` when it is set, else
/// from the system's random bytes. A coefficient is drawn below `P` by drawing 64 bits again
/// while they are `P` or more (probability `59 / 2^64` each), so each is uniform over `0..P`.
/// The `degree + 1` coefficients are drawn first, then `r`, so a draw of degree 4 is the one a
/// seed gave before degree 7 was added.
fn draw(tag: u64, degree: usize, fixed_in_unit_tests: bool) -> Draw {
    draw_from(source(tag, fixed_in_unit_tests), degree)
}

/// [`draw`] from the words `next`.
fn draw_from(mut next: impl FnMut() -> u64, degree: usize) -> Draw {
    let mut below_p = || loop {
        let x = next();
        if x < P {
            return x;
        }
    };
    let mut q = [0; 8];
    for c in &mut q[..=degree] {
        *c = below_p();
    }
    Draw {
        q,
        degree,
        r: below_p(),
    }
}

/// The two primes of this run's fingerprints of numbers (zed-kernel `Rat::fingerprint`): `P1`
/// uniform among the primes in `[2^60, 2^61)`, and `P2 = 2Q + 1` uniform among the safe primes
/// with `Q` a prime in `[2^59, 2^60)`. They are drawn once per run, as the treap priorities are
/// (draws 21 and 22, so `ZED_TREAP_SEED` fixes them too), by drawing a uniform number of the
/// range until it is prime (`P1`), or until `Q` and `2Q + 1` both are (`P2`); rejection keeps
/// the result uniform over the accepted ones. Primality is exact: [`zed_numtheory::is_prime`],
/// Miller-Rabin with the twelve primes 2 to 37 as bases, deterministic below 2^64 (cited there,
/// Sorenson and Webster 2017).
///
/// What a fingerprint is for. A Big or Rat in a treap needs a priority and a weight that are
/// the same for equal values and, for two given unequal values, differ except with small
/// probability over the draw, whatever the values; otherwise one input with many values that
/// tie makes a treap a path. Residues modulo the fixed `2^61 - 1` cannot give that, since the
/// input can be chosen after the modulus (`2^64` and `2^64 + 2^61 - 1` share theirs). A
/// fingerprint is `(negative, |N| mod P1, D mod P1, |N| mod P2, D mod P2)` for the value `N/D`
/// in lowest terms. `N` and `D` are fixed by the value, so equal values have one fingerprint,
/// whatever forms they are held in. Nothing printed or compared reads a fingerprint; a collision
/// costs only time (module comment, rule deterministic-checking).
///
/// The bound for values with no kept power. Let `v != w` have `N_v, D_v, N_w, D_w` below
/// `2^b`. If their fingerprints agree, then `P1` divides `N_v - N_w` and `D_v - D_w`, and one
/// of the two is nonzero and below `2^b` in magnitude, so it has at most `b/60` prime factors of
/// at least `2^60`. Rosser and Schoenfeld, "Approximate formulas for some functions of prime
/// numbers", Illinois J. Math. 6 (1962) 64-94, doi:10.1215/ijm/1255631807, Corollary 3, (3.8),
/// p. 69: "3x/(5 log x) < π(2x) − π(x)   for 20½ ≦ x" (checked 2026-11-25 on the page image of
/// the publisher's PDF). At `x = 2^60`, `log x = 41.59`, so `[2^60, 2^61)` holds more than
/// `2^60 / 69.4` primes, and `Pr[P1 | N_v - N_w] < (b/60) * 69.4 * 2^-60 < 1.16 b 2^-60`. So a
/// pair collides with probability below `1.16 b 2^-60`, and among `n` keys of at most `b` bits
/// the expected number of colliding pairs is below `0.58 n^2 b 2^-60`: under `2^-10` for
/// `n = 2^20` keys of 1024 bits each.
///
/// The bound for one kept power. A value held as `c * q^f`, with `q` a wide atom and `f` of
/// any size, has digits far beyond any `b` above, so `P1` proves nothing for it. Then `P2`:
/// the units modulo `P2` form a cyclic group of order `2Q`, so the order of `q mod P2` is 1, 2,
/// `Q` or `2Q`. For two values `c q^f` and `c q^g` with `f != g` to share the `P2` residue, either
/// `q = ±1 mod P2` (so `P2` divides `q - 1` or `q + 1`, at most `bits(q)/60 + 1` primes each), or
/// `Q` divides `f - g` (at most `bits(f - g)/59` primes). Each of these is a fixed set of at most
/// `B/59 + 2` primes, `B` the bits of `q` and of `f - g`, so the chance is that over the number of
/// safe primes in the range.
///
/// Not proved: the number of safe primes. That there are infinitely many is open; their count
/// for `Q` below `x` is conjectured to be about `2 C_2 x / ((log x)(log 2x))`, `C_2 = 0.6601...`
/// the twin-prime constant (the Hardy-Littlewood conjecture; Bateman and Horn's form covers `Q`
/// and `2Q + 1` together), which gives about `2^59 / 1310` safe primes with `Q` in
/// `[2^59, 2^60)`, and so a chance near `(B/59 + 2) * 1310 * 2^-59` per pair. Observed (test
/// `fingerprint_primes_draw_rates`, seeds 0 to 255; b22-free2 on a Colab VM, 2026-11-25): 1248
/// draws of `Q` per safe prime on average, against about 1310 from the conjecture (each draw of
/// `Q` is uniform in the range, so the rate is the density); for `P1`, 40.9 draws per prime
/// against `ln 2^60.5 = 41.9` (at most 8004 draws of `Q` and 248 of `P1` at any one seed).
/// If safe primes were far rarer than conjectured, the draw would take longer and the one-atom
/// bound would weaken; no answer changes.
///
/// Not proved at all: several kept powers. Two values `prod q_i^(e_i)` and `prod q_i^(f_i)` share
/// their `P2` residue when `prod q_i^(e_i - f_i) = 1 mod P2`, a relation among several atoms with
/// huge exponents. No bound on the primes for which such a relation holds is given here: the
/// argument above needs one generator, and with several the exponents can be chosen so that the
/// relation holds for many primes at once only if the atoms are multiplicatively dependent
/// modulo many primes, which is not ruled out. Row XR-kept-form-fingerprint-several-atoms, for
/// cross-review. No input can be built to make this fail on purpose, since the primes are drawn
/// after the input is fixed; a failure would cost only time.
// Complexity tradeoff: a fixed prime costs nothing to draw but lets one input make every value
// tie; drawing a prime costs about 42 tests for `P1` and about 1310 for `Q` (about 85% of
// candidates are rejected by `is_prime`'s trial division by its twelve bases, the rest by
// Miller-Rabin), once per run: 172 µs for both primes on average over seeds 0 to 255 (same test
// and VM as above). The deterministic hashes (`value::digest`, the
// type weights) keep `2^61 - 1`, which they need to be the same on every run, and whose fold
// is cheaper than any reduction modulo a drawn prime (measured at `Rat::fingerprint`).
///
/// `unit_test` is the caller's `cfg!(test)`, as for [`Priorities::fixed_in_unit_tests`]: when
/// it is true and `ZED_TREAP_SEED` is unset, the primes are those of seed 0. The first call of a
/// process draws them; every caller of a run passes the same flag (zed-kernel is the only one).
pub fn fingerprint_primes(unit_test: bool) -> [u64; 2] {
    static PRIMES: OnceLock<[u64; 2]> = OnceLock::new();
    *PRIMES.get_or_init(|| fingerprint_primes_from(source(21, unit_test), source(22, unit_test)).0)
}

/// [`fingerprint_primes`] from the words `next1` and `next2`, with the number of draws each
/// took.
fn fingerprint_primes_from(
    mut next1: impl FnMut() -> u64,
    mut next2: impl FnMut() -> u64,
) -> ([u64; 2], [u64; 2]) {
    let mut draws = [0; 2];
    let p1 = loop {
        draws[0] += 1;
        let p = (1 << 60) | (next1() >> 4);
        if zed_numtheory::is_prime(p) {
            break p;
        }
    };
    let p2 = loop {
        draws[1] += 1;
        let q = (1 << 59) | (next2() >> 5);
        if zed_numtheory::is_prime(q) && zed_numtheory::is_prime(2 * q + 1) {
            break 2 * q + 1;
        }
    };
    ([p1, p2], draws)
}

/// The 64-bit words of the draw of `tag`.
fn source(tag: u64, fixed_in_unit_tests: bool) -> Box<dyn FnMut() -> u64> {
    let unset = (fixed_in_unit_tests || cfg!(test)).then_some(0);
    if let Some(seed) = fixed_seed().or(unset) {
        return Box::new(seeded_words(seed, tag));
    }
    use std::io::Read;
    let mut f = std::fs::File::open("/dev/urandom")
        .expect("the treap priorities read their seed from /dev/urandom");
    Box::new(move || {
        let mut w = [0u8; 8];
        f.read_exact(&mut w)
            .expect("the treap priorities read their seed from /dev/urandom");
        u64::from_le_bytes(w)
    })
}

/// splitmix64 (zed-hash's `SplitMix64`, where its source is) from the seed and the tag: the
/// same words on every run of one seed.
fn seeded_words(seed: u64, tag: u64) -> impl FnMut() -> u64 {
    let mut g = zed_hash::SplitMix64::new(seed ^ tag.wrapping_mul(0xd1b5_4a32_d192_ed03));
    move || g.next_u64()
}

/// `ZED_TREAP_SEED`, read once; `None` when it is unset. Then [`source`] takes seed 0 in the
/// unit tests of this crate and of the crates that ask for it
/// ([`Priorities::fixed_in_unit_tests`]), and the system's random bytes otherwise.
fn fixed_seed() -> Option<u64> {
    static SEED: OnceLock<Option<u64>> = OnceLock::new();
    *SEED.get_or_init(|| {
        let Ok(s) = std::env::var("ZED_TREAP_SEED") else {
            return None;
        };
        Some(
            s.trim().parse().unwrap_or_else(|_| {
                panic!("ZED_TREAP_SEED is {s:?}, not a decimal number below 2^64")
            }),
        )
    })
}

#[cfg(test)]
mod tests;

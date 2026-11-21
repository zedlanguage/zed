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
//! `priority::tests::p_is_the_largest_prime_below_2_to_the_64` (the field) and
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
//! Introduction through Randomized Algorithms", Prentice-Hall, 1994, section 10.1; the book was
//! not read, and the lemma is used as Seidel and Aragon state it. Tried 2026-11-21: LibGen by
//! title found a PDF and two DjVu copies; the PDF download broke off twice part way (curl exit
//! 18) and then the server answered 503; both DjVu copies, on the libgen.li, libgen.bz and
//! libgen.vg mirrors, answered 503 or gave no download key on every retry at 15 s, 45 s, 90 s,
//! 3 min and 5 min, and once more after; Anna's Archive by md5 met a browser check (.gd, .gl)
//! or DDoS-Guard (.pk); the book has no DOI, so Sci-Hub and Sci-Net do not apply.
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

/// The prime `2^64 - 59`, the largest below `2^64`.
pub const P: u64 = 0xffff_ffff_ffff_ffc5;

/// `a * b mod P`, for `a, b < P`. `2^64 = 59 (mod P)`, so the product `hi * 2^64 + lo` is
/// `hi * 59 + lo`; `hi < 2^64`, so that is below `2^70`. A second fold, of a high part below
/// 60, leaves it below `2^64 + 60 * 59 < 2P`, which one subtraction brings below `P`.
fn mul(a: u64, b: u64) -> u64 {
    let x = u128::from(a) * u128::from(b);
    let x = (x >> 64) * 59 + (x & u128::from(u64::MAX));
    let x = (x >> 64) * 59 + (x & u128::from(u64::MAX));
    reduce(x)
}

/// `x mod P` for `x < 2 * P`.
fn reduce(x: u128) -> u64 {
    let p = u128::from(P);
    (if x >= p { x - p } else { x }) as u64
}

/// `a + b mod P`, for `a, b < P`.
fn add(a: u64, b: u64) -> u64 {
    reduce(u128::from(a) + u128::from(b))
}

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
    draw: OnceLock<Draw>,
}

impl Priorities {
    /// The priorities of the use named `tag`, drawn on first use: `q` of degree 4, 5-wise
    /// independent.
    pub const fn new(tag: u64) -> Priorities {
        Priorities {
            tag,
            degree: 4,
            draw: OnceLock::new(),
        }
    }

    /// The priorities of the use named `tag`, drawn on first use: `q` of degree 7, 8-wise
    /// independent, for the treaps whose joins need the finger bound (module comment).
    pub const fn eight_wise(tag: u64) -> Priorities {
        Priorities {
            tag,
            degree: 7,
            draw: OnceLock::new(),
        }
    }

    fn draw(&self) -> &Draw {
        self.draw.get_or_init(|| draw(self.tag, self.degree))
    }

    /// The priority of the key `x`, a number: `q(x mod P)`. The 59 numbers from `P` up share
    /// their points with `0` to `58`, so at most 118 keys tie for that reason whatever the draw.
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
    fn symbol(&mut self, s: u64) {
        self.acc = add(mul(self.acc, self.r), s);
    }

    /// A word as symbols below `p`: itself when it is below `p - 1`, else `p - 1` and then
    /// `w - (p - 1)`, at most 59. No word's symbols begin another's, so the words are read
    /// back from the symbols.
    fn word(&mut self, w: u64) {
        if w >= P - 1 {
            self.symbol(P - 1);
            self.symbol(w - (P - 1));
        } else {
            self.symbol(w);
        }
    }

    /// `g`: the last word, completed with zero bytes, then the length.
    fn end(mut self) -> u64 {
        if self.filled > 0 {
            self.word(self.pending);
        }
        self.word(self.len);
        self.acc
    }
}

impl std::hash::Hasher for Stream {
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
fn draw(tag: u64, degree: usize) -> Draw {
    draw_from(source(tag), degree)
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

/// The 64-bit words of the draw of `tag`.
fn source(tag: u64) -> Box<dyn FnMut() -> u64> {
    if let Some(seed) = fixed_seed() {
        // splitmix64 from the seed and the tag: the same words on every run of one seed.
        let mut z = seed ^ tag.wrapping_mul(0xd1b5_4a32_d192_ed03);
        return Box::new(move || {
            z = z.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut x = z;
            x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            x ^ (x >> 31)
        });
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

/// `ZED_TREAP_SEED`, read once. In this crate's unit tests it is 0 when unset, so that a test of
/// a treap's height checks one draw, the same on every run (a test asserts only what holds for
/// the draw it checks).
fn fixed_seed() -> Option<u64> {
    static SEED: OnceLock<Option<u64>> = OnceLock::new();
    *SEED.get_or_init(|| {
        let Ok(s) = std::env::var("ZED_TREAP_SEED") else {
            return cfg!(test).then_some(0);
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

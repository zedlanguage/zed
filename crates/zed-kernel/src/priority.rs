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
//! values is a Vandermonde matrix, invertible on distinct points (Seidel and Aragon,
//! "Randomized search trees", Algorithmica 16, 1996, start of section 6).
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
//! The bound. Seidel and Aragon's Lemma 6.1 (essentially Mulmuley's, "Computational geometry",
//! 1994, section 10.1): random variables uniform over a common integer range of size at least
//! `n` that are `(3d + 2)`-wise independent have the `d`-max property, so for `d = 1` and
//! 5-wise independence there is a constant `c` with `Pr[X_1 > X_2, ..., X_m] <= c/m` for any
//! `m` of them. Their section 6 shows that the 1-max property alone gives Corollaries 4.5 and
//! 4.6 and Theorem 4.7 (i) and (ii): the expected depth of a node and the expected size of its
//! subtree are `O(log n)`, so "5-wise independence of the random priorities provably
//! suffices" for logarithmic expected search and update times (also their Theorem 3.3).
//!
//! Equal priorities. Let a node be tied when another node of the treap has its priority, and let
//! `T` be the number of tied nodes. A node `y` that is not tied is an ancestor of `x` exactly when
//! its priority is above every other of the keys from `x` to `y` (Seidel and Aragon's Lemma 4.3,
//! whose proof holds in any tree heap-ordered by priority, however ties are broken: the least
//! common ancestor of `x` and `y` lies between them and is above both), so the depth of `x` is
//! at most `T` plus the number of untied `y` that hold the strict maximum of their range. Only a
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

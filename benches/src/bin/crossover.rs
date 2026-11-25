//! The crossover benchmarks (see the crate's documentation), one per argument; `crossover all`
//! runs every one of them at once, each in a process of its own under a limit of 60 s, and
//! lists each threshold as built against its measured crossover, and each constant of a cost
//! model against the values that best fit every benchmark of it at once (the worst of their
//! work at each value), with status 1 when one has moved by more than the spread of repeated
//! runs or a benchmark failed.
//!
//! In `zed_kernel::num` (the method below the threshold, then the one above):
//!
//! - `mul [ratio]`: `MUL_LEAF` and `TOOM_COST`, num-bigint's product against the transforms,
//!   dense random factors of `w` and `ratio w` words (1, 4 and 32 in `all`).
//! - `mul-rows`: `TRANSFORM_COST` against rows, a dense factor of 8192 words by one of the same
//!   width with `k` nonzero words spread over it: rows over the nonzero words against the
//!   transforms.
//! - `wrap [n]`: `WRAP_COST`, the choice of `points` between two computed costs, a
//!   balanced product by transforms on `n / 2` points with the top words' product subtracted
//!   against on all `n`, dense random factors of `n / 4` to `n / 2` words (4096 and 8192 in
//!   `all`).
//! - `div-leaf [q d [extra [w,w,...]]]`: `DIV_LEAF` and `DIV_COST`, num-bigint's division
//!   against the division past the leaf, `(q + d) w - 1 + extra` by `d w` dense words, a
//!   quotient of about `q w` (`1 1`, `1 4`, `4 1`, `16 1` and `256 1` in `all`); for `1 1`,
//!   `extra` 1 and 2 give a quotient of `w + 1` and `w + 2` words, the last that `DIV_SAME`
//!   takes and the first past it. The sizes are the listed `w`, else the ladder.
//! - `rem-leaf [q]`: `DIV_LEAF` and `DIV_COST` in `rem`, num-bigint's `%` against the blocks
//!   of one `Divisor`, `(q + 1) w` by `w` dense words (16 and 256 in `all`).
//! - `div-rows`: `SPARSE_WORD` and `SPARSE_STEP`, long division over the divisor's nonzero
//!   words against the division by a reciprocal, `2w - 1` by `w` dense words; `div-rows step`
//!   fits `SPARSE_STEP` on the same divisors.
//! - `div-sparse [w [q]]`: `SPARSE_STEP` with `SPARSE_RUN`, the same two methods on
//!   `(q + 1) w - 1` by `w` words of which `k` are nonzero, spread evenly, from 2 (the kept
//!   power `2^(64w - 1) + 1`) to `w`; for `q` above 1 the reciprocal at every block (256, 1024
//!   and 2048 with `q` = 1, and `1024 16`, in `all`).
//! - `recip`: `RECIP_LEAF`, a reciprocal of `p` bits started from num-bigint's division at `p`
//!   bits against one Newton step from there (the leaf at `p` against at `p - 1`).
//! - `gcd-leaf`: `GCD_LEAF`, the gcd of two odd numbers of `w` words by Stein's gcd against one
//!   half gcd before it (the leaf at `64 w` bits against at `64 w - 1`).
//! - `lift-gcd`, `lift-bezout`: `LIFT_BITS`, the top level of the half gcd lifting its pair
//!   from the residues against applying its matrix to the whole numbers, in a gcd and in the
//!   Bezout coefficients of two odd numbers of `w` words.
//! - `cached`: `CACHED_COST`, a product by a factor's kept spectra against [`mul_uint`].
//! - `print-whole [from to]`: `PRINT_WHOLE`, num-bigint's printing of the whole number against
//!   the split (`to_decimal_split`), random numbers of `from` to `to` words (256 to 32,768).
//! - `print-handoff [digits...]`: `PRINT_HANDOFF`, a setting: the whole print of numbers of the
//!   given digits (160,000, 320,000 and 1,280,000) with the part handed over below each power
//!   `10^(597 2^i)`.
//! - `leaf-digits`: `LEAF_DIGITS`, a setting: reading texts of 700 to 10^6 digits with each leaf
//!   from 128 to 16,384 digits.
//! - `print-never-slower [digits...]`: `to_decimal` against num-bigint's printing at each size
//!   of COMPLEXITY.md K81 (10,000 to 1,280,000 digits by default), which must never be the
//!   slower by more than [`NEVER_SLOWER`]; exits with status 1 where it is. Not a threshold, so
//!   not in `all`.
//! - `factor-bits`: `FACTOR_BITS` and `FACTOR_INPUTS` of `num::coprime`, factoring each word
//!   input against Bernstein's trees, in a coprime base and in the inputs that share a prime,
//!   on three families of inputs at widths of 16 to 56 bits and counts of 2 to 4096; prints
//!   each method's work for the comment of `FACTOR_BITS`, not a fit, so not in `all`.
//!
//! In `zed_kernel::text`: `text-leaf`, `LEAF`, a setting: a `foldl` of 200,000 joins of pieces
//! of 1, 8 and 64 bytes, then `==`, a hash and the print, with each leaf from 16 to 1024 bytes.
//!
//! In `zed_kernel::poly` (the normal form's product `Poly::mul`, its choice between the dense
//! and the sparse product once the support product gives way): `PAIR_COST`, `SLOT_COST` and
//! `DENSE_COST` of its cost estimates, each fitted over the seven shapes below together, each
//! shape run once per constant (`[shape args] pair|slot|fixed`):
//!
//! - `poly-dense [words]`: univariate sums of 2 to 256 terms at every index, coefficients of
//!   `words` 64-bit words (1 and 4).
//! - `poly-gaps [terms]`: two sums of `terms` terms (64 and 16), one about every `g` indices
//!   at a random offset, `g` from 1 to 4096.
//! - `poly-wide [terms]`: univariate sums of `terms` terms (2 and 8), coefficients of 1 to
//!   1024 words.
//! - `poly-square [terms]`: the square of a sum of `terms` terms (256), one about every `g`
//!   indices, `g` from 1 to 512: a square is charged `SQUARE_SHARE` of its transform cost
//!   (POLY-square-choice-cost) and `t (t + 1) / 2` sparse pairs (POLY-square-sparse-half).
//!
//! And its `SUPPORT_COST`, which decides when it tries the support product, against the method
//! taken when that gives way, fitted over these two shapes together (POLY-support-bench):
//!
//! - `poly-support [words]`: the square of a sum shaped as `(x + y)^k + x`, `k` from 8 to 512,
//!   coefficients of `words` 64-bit words (1, 4 and 16).
//! - `poly-support-gaps [terms]`: the square of a sum of `terms` terms (256) in pairs `i s`,
//!   `i s + 1`, `s` a gap from 3 to 4098.
//!
//! In `zed_corpus_ref::zedrt` (the corpus's reference programs):
//!
//! - `corpus-leaf-digits`: its `LEAF_DIGITS`, as `leaf-digits`.
//! - `transform-words`: `product::TRANSFORM_WORDS`, num-bigint's product against the
//!   transform, `5^65536` (4,756 32-bit words) by a random factor of `w` 32-bit words.
//! - `kept-words`: `product::KEPT_WORDS`, a factor of `w` 32-bit words squared and multiplied
//!   by a part 1.43 times as long, with its transform kept against not.
//!
//! Each runs under 60 s (`timeout 60`), in the build the tests use (the `dev` profile), on
//! each target platform on real hardware: the thresholds measured are that platform's. Rerun
//! `crossover all` after any change to either method of a threshold, or to the code generation,
//! that changes its speed, and reset each threshold it reports moved.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::io::Read;
use std::process::{Command, ExitCode, Stdio};
use std::time::{Duration, Instant};

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use zed_benches::{Constant, Crossover, Method, Setting, Steps, conditions, least};
use zed_corpus_ref::zedrt::{self, product};
use zed_kernel::num::coprime::crossover as cx;
use zed_kernel::num::crossover as x;
use zed_kernel::num::{
    PRINT_HANDOFF, PRINT_WHOLE, mul_uint, to_decimal, to_decimal_split, to_decimal_split_at,
};
use zed_kernel::poly::crossover as px;
use zed_kernel::text::{self, Text};
use zed_tests::instances::Rng;
use zed_tests::scaling::Meter;

/// The most `to_decimal`'s instructions may be over num-bigint's at a size of
/// `print-never-slower`: 1%. Below `PRINT_WHOLE` it runs num-bigint's printing itself, whose
/// count differs between two calls on the same number by up to 0.2% (1.0004 and 1.0003
/// times at 10,000 and 80,000 digits on 2026-11-12, 0.998 to 1.001 times in `print-whole`
/// below 496 words, where the split hands the whole number to num-bigint too); from there the
/// split, which does less work at every size measured above the threshold.
const NEVER_SLOWER: f64 = 1.01;

/// The digits of the narrowest power the split divides by, `10^597` (`PRINT_LEAF` in
/// zed_kernel::num::fast).
const PRINT_LEAF_DIGITS: u32 = 597;

/// How near the sizes around a change of the faster method are halved to: 2%, a few
/// instruction counts of a step of the sizes.
const TOLERANCE: f64 = 0.02;

/// A random number of `words` 64-bit words, the top bit set.
fn random(rng: &mut Rng, words: usize) -> BigUint {
    random32(rng, 2 * words)
}

/// A random number of `words` 32-bit words, the top bit set.
fn random32(rng: &mut Rng, words: usize) -> BigUint {
    let mut digits: Vec<u32> = (0..words).map(|_| rng.next_u64() as u32).collect();
    if let Some(top) = digits.last_mut() {
        *top |= 1 << 31;
    }
    BigUint::new(digits)
}

/// A random odd number of `words` 64-bit words, the top bit set.
fn random_odd(rng: &mut Rng, words: usize) -> BigUint {
    random(rng, words) | BigUint::from(1u32)
}

/// A random number of `digits` decimal digits, the first not zero.
fn random_digits(rng: &mut Rng, digits: u32) -> BigUint {
    random_text(rng, digits as usize)
        .parse()
        .expect("decimal digits")
}

/// A random text of `digits` decimal digits, the first not zero.
fn random_text(rng: &mut Rng, digits: usize) -> String {
    (0..digits)
        .map(|i| char::from(b'0' + rng.int(i64::from(i == 0), 9) as u8))
        .collect()
}

/// The decimal digits of a number of `words` words, about.
fn digits_of_words(words: usize) -> f64 {
    words as f64 * 64.0 * std::f64::consts::LOG10_2
}

/// The 64-bit words of `x`.
fn words(x: &BigUint) -> usize {
    x.bits().div_ceil(64) as usize
}

/// The 32-bit words of `x`.
fn words32(x: &BigUint) -> u64 {
    x.bits().div_ceil(32)
}

/// Sizes from `from` to `to`, `2^(1/steps)` apart, rounded.
fn ladder(from: usize, to: usize, steps: u32) -> Vec<usize> {
    let mut sizes: Vec<usize> = (0..)
        .map(|k| (from as f64 * 2f64.powf(f64::from(k) / f64::from(steps))).round() as usize)
        .take_while(|&s| s <= to)
        .collect();
    sizes.dedup();
    sizes
}

/// The exit status of a benchmark: success when its threshold sits at the measured crossover.
fn status(holds: bool) -> ExitCode {
    match holds {
        true => ExitCode::SUCCESS,
        false => ExitCode::FAILURE,
    }
}

/// Two numbers.
type Pair = (BigUint, BigUint);

fn mul(args: &[String]) -> ExitCode {
    let ratio: usize = args.first().map_or(1, |s| s.parse().expect("a ratio"));
    let to = match ratio {
        1 => 8192,
        r if r <= 4 => 4096,
        _ => 2048,
    };
    let note = move |w: usize| format!(" by {}", ratio * w);
    let inputs = move |w: usize| {
        let mut rng = Rng::new(w as u64);
        let ones = (BigUint::from(1u32) << (64 * w)) - 1u32;
        vec![
            (random(&mut rng, ratio * w), random(&mut rng, w)),
            (ones.clone() << (64 * (ratio - 1) * w), ones),
        ]
    };
    let bench = Crossover {
        unit: "words",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "num-bigint",
            run: &|(a, b): &Pair| a * b,
        },
        above: Method {
            name: "transforms",
            run: &|(a, b): &Pair| x::mul_by_transforms(a, b),
        },
        takes_above: &|(a, b): &Pair| x::mul_method(a, b) != "num-bigint",
        constant: Some(Constant {
            name: "TOOM_COST",
            built: x::TOOM_COST,
            flip: &|(a, b): &Pair| x::toom_flip(a, b),
            below_at_most: true,
        }),
    };
    let name = format!("mul {ratio}");
    let verdict = bench.report(
        &mut Meter::new(),
        &name,
        &format!("MUL_LEAF {} words, TOOM_COST", x::MUL_LEAF),
        &ladder(256, to, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

fn mul_rows(_: &[String]) -> ExitCode {
    const LONG: usize = 8192;
    let inputs = |k: usize| {
        let mut rng = Rng::new(k as u64);
        let dense = random(&mut rng, LONG);
        let mut sparse = vec![0u64; LONG];
        for i in 0..k {
            sparse[i * LONG / k] = rng.next_u64() | 1;
        }
        sparse[LONG - 1] |= 1 << 63;
        let sparse = BigUint::from_slice(
            &sparse
                .iter()
                .flat_map(|&w| [w as u32, (w >> 32) as u32])
                .collect::<Vec<u32>>(),
        );
        vec![(sparse, dense)]
    };
    let note = |_: usize| format!(" of {LONG}");
    let bench = Crossover {
        unit: "nonzero words",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "rows",
            run: &|(a, b): &Pair| x::mul_by_rows(a, b),
        },
        above: Method {
            name: "transforms",
            run: &|(a, b): &Pair| x::mul_by_transforms(a, b),
        },
        takes_above: &|(a, b): &Pair| x::mul_method(a, b) == "transforms",
        constant: Some(Constant {
            name: "TRANSFORM_COST",
            built: x::TRANSFORM_COST,
            flip: &|(a, b): &Pair| x::transform_flip(a, b),
            below_at_most: false,
        }),
    };
    let verdict = bench.report(
        &mut Meter::new(),
        "mul-rows",
        "TRANSFORM_COST",
        &ladder(16, 1024, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// The wrapped plan of `points` against the full one (RADIX-balanced-mul-regress): balanced
/// products of `w` by `w` words from just above `n / 4` to `n / 2` words, `n` the points at
/// or above their coefficients (`n` = 4096 and 8192 in `all`). The wrapped plan transforms
/// on `n / 2` points and subtracts the product of the top words; it gains most just above
/// `n / 4` words and less as `w` nears `n / 2`, so the full plan is the method above.
/// `WRAP_COST` decides; its flip holds `WRAP_COST` as built in the top product's own cost, so
/// the fit it reports is that of the top level only (the sweep of 2026-11-22 rebuilt at each
/// value, `zed_kernel::num::fast`, `WRAP_COST`).
fn wrap(args: &[String]) -> ExitCode {
    let n: usize = args
        .first()
        .map_or(4096, |s| s.parse().expect("a power of two"));
    let inputs = |w: usize| {
        let mut rng = Rng::new(w as u64);
        let ones = (BigUint::from(1u32) << (64 * w)) - 1u32;
        vec![
            (random(&mut rng, w), random(&mut rng, w)),
            (ones.clone(), ones),
        ]
    };
    let note = |_: usize| String::new();
    let bench = Crossover {
        unit: "words",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "wrapped",
            run: &|(a, b): &Pair| x::mul_on_points(a, b, true),
        },
        above: Method {
            name: "full",
            run: &|(a, b): &Pair| x::mul_on_points(a, b, false),
        },
        takes_above: &|(a, b): &Pair| !x::wraps(a, b),
        constant: Some(Constant {
            name: "WRAP_COST",
            built: x::WRAP_COST,
            flip: &|(a, b): &Pair| x::wrap_flip(a, b),
            below_at_most: true,
        }),
    };
    let verdict = bench.report(
        &mut Meter::new(),
        &format!("wrap {n}"),
        "WRAP_COST",
        &ladder(n / 4 + n / 64, n / 2, 8),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// A dividend of `2w - 1` words and a divisor of `w`, dense and random.
fn division(w: usize) -> Vec<Pair> {
    let mut rng = Rng::new(w as u64);
    let b = random(&mut rng, w);
    let a = random(&mut rng, 2 * w - 1);
    let ones = (BigUint::from(1u32) << (64 * w)) - 1u32;
    vec![(a, b), (&ones * &ones - 1u32, ones)]
}

/// The shape of a division by `div-leaf`: a quotient of `q w` words and a divisor of `d w`, at
/// size `w`, read from the arguments (`1 1` when there are none); one of the two is 1, so the
/// size is the narrower's width, which the leaf is on.
fn division_shape(args: &[String]) -> (usize, usize) {
    let arg = |k: usize| args.get(k).map_or(1, |s| s.parse().expect("a multiple"));
    let (q, d) = (arg(0), arg(1));
    assert!(q.min(d) == 1, "div-leaf q d: one of the two is 1");
    (q, d)
}

/// `div-leaf [q d [extra [w,w,...]]]`: with `extra`, the dividend has `extra` words more, so
/// that `1 1 1` and `1 1 2` straddle `qw = bw + 1` of `DIV_SAME` by a word (`1 1` alone has
/// `qw = bw`), and with the list, only those sizes `w` (plan row
/// PERF-div-narrow-quotient-factor).
fn div_leaf(args: &[String]) -> ExitCode {
    let (q, d) = division_shape(args);
    let extra: isize = args.get(2).map_or(0, |s| s.parse().expect("extra words"));
    let listed: Option<Vec<usize>> = args
        .get(3)
        .map(|s| s.split(',').map(|w| w.parse().expect("a size")).collect());
    let aw = move |w: usize| {
        ((q + d) * w - 1)
            .checked_add_signed(extra)
            .expect("a dividend")
    };
    let note = move |w: usize| format!(" ({} by {})", aw(w), d * w);
    let inputs = move |w: usize| {
        let mut rng = Rng::new(w as u64);
        let b = random(&mut rng, d * w);
        let a = random(&mut rng, aw(w));
        let ones = |n: usize| (BigUint::from(1u32) << (64 * n)) - 1u32;
        vec![(a, b), (ones(aw(w)), ones(d * w))]
    };
    let bench = Crossover {
        unit: "words",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "num-bigint",
            run: &|(a, b): &Pair| a.div_rem(b),
        },
        above: Method {
            name: "past the leaf",
            run: &|(a, b): &Pair| x::div_rem_past_leaf(a, b),
        },
        takes_above: &|(a, b): &Pair| !x::div_by_num_bigint(a, b),
        constant: Some(Constant {
            name: "DIV_COST",
            built: x::DIV_COST,
            flip: &|(a, b): &Pair| x::div_flip(a, b),
            below_at_most: true,
        }),
    };
    let to = match q.max(d) {
        1 => 16_384,
        4 => 8192,
        _ => 2048,
    };
    let verdict = bench.report(
        &mut Meter::new(),
        &format!("div-leaf {q} {d} {extra}"),
        &format!("DIV_LEAF {} bits, DIV_COST", x::DIV_LEAF),
        &listed.unwrap_or_else(|| ladder(16, to, 2)),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// `rem-leaf [q]`: `DIV_LEAF` and `DIV_COST` in `rem`, num-bigint's `%` against the blocks of
/// one `Divisor`, `(q + 1) w` by `w` dense words, a quotient of about `q w` (16 and 256 in
/// `all`): the wide dividends `rem` reads in blocks where `div_rem` would
/// (DRY-numeric-shared-rest).
fn rem_leaf(args: &[String]) -> ExitCode {
    let q: usize = args.first().map_or(16, |s| s.parse().expect("a multiple"));
    assert!(q >= 2, "rem-leaf q: a quotient wider than the divisor");
    let note = move |w: usize| format!(" ({} by {w})", (q + 1) * w);
    let inputs = move |w: usize| {
        let mut rng = Rng::new(w as u64);
        let b = random(&mut rng, w);
        let a = random(&mut rng, (q + 1) * w);
        let ones = |n: usize| (BigUint::from(1u32) << (64 * n)) - 1u32;
        vec![(a, b), (ones((q + 1) * w), ones(w))]
    };
    let bench = Crossover {
        unit: "words",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "num-bigint",
            run: &|(a, b): &Pair| a % b,
        },
        above: Method {
            name: "blocks",
            run: &|(a, b): &Pair| x::rem_by_blocks(a, b),
        },
        takes_above: &|(a, b): &Pair| x::rem_takes_blocks(a, b),
        constant: Some(Constant {
            name: "DIV_COST",
            built: x::DIV_COST,
            flip: &|(a, b): &Pair| x::div_flip(a, b),
            below_at_most: true,
        }),
    };
    let to = match q {
        ..=16 => 2048,
        _ => 512,
    };
    let verdict = bench.report(
        &mut Meter::new(),
        &format!("rem-leaf {q}"),
        &format!(
            "DIV_LEAF {} bits, DIV_COST {} in rem",
            x::DIV_LEAF,
            x::DIV_COST
        ),
        &ladder(16, to, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// With the argument `step`, the same ladder fits `SPARSE_STEP` in place of `SPARSE_WORD`, so
/// `all` weighs the dense divisors in the joint fit of `SPARSE_STEP` with `div-sparse`.
fn div_rows(args: &[String]) -> ExitCode {
    let step = args.first().is_some_and(|a| a == "step");
    let note = |w: usize| format!(" ({} by {w})", 2 * w - 1);
    let bench = Crossover {
        unit: "words",
        note: &note,
        inputs: &division,
        below: Method {
            name: "long division",
            run: &|(a, b): &Pair| x::div_rem_sparse(a, b),
        },
        above: Method {
            name: "reciprocal",
            run: &|(a, b): &Pair| x::div_rem_by_reciprocal(a, b),
        },
        takes_above: &|(a, b): &Pair| !x::div_by_rows(a, b),
        constant: Some(match step {
            false => Constant {
                name: "SPARSE_WORD",
                built: x::SPARSE_WORD,
                flip: &|(a, b): &Pair| x::sparse_flip(a, b),
                below_at_most: true,
            },
            true => Constant {
                name: "SPARSE_STEP",
                built: x::SPARSE_STEP,
                flip: &|(a, b): &Pair| x::step_flip(a, b),
                below_at_most: true,
            },
        }),
    };
    let verdict = bench.report(
        &mut Meter::new(),
        match step {
            false => "div-rows",
            true => "div-rows step",
        },
        "SPARSE_WORD, SPARSE_STEP",
        &ladder(64, 16_384, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// A dividend of `(q + 1) w - 1` words and a divisor of `w` words of which `k` are nonzero: the
/// top word's top bit, the bottom word's bottom bit, and `k - 2` random words spread evenly
/// between them, so `k = 2` is the kept power `2^(64w - 1) + 1`.
fn sparse_division(w: usize, q: usize, k: usize) -> Vec<Pair> {
    let mut rng = Rng::new(((q - 1) << 32 | (w * 64 + k)) as u64);
    let mut words = vec![0u64; w];
    words[0] = 1;
    words[w - 1] = 1 << 63;
    for i in 1..k - 1 {
        words[i * (w - 1) / (k - 1)] |= rng.next_u64() | 1;
    }
    let b = BigUint::from_slice(
        &words
            .iter()
            .flat_map(|&d| [d as u32, (d >> 32) as u32])
            .collect::<Vec<u32>>(),
    );
    let a = random(&mut rng, (q + 1) * w - 1);
    let top = (&b << (64 * (q * w - 1))) - 1u32;
    vec![(a, b.clone()), (top, b)]
}

/// With a second argument `q` above 1 the quotient has `q` times the divisor's words, and the
/// method above is the reciprocal at every block, as `div_rem_by_reciprocal`'s blocks would each
/// choose their own way.
fn div_sparse(args: &[String]) -> ExitCode {
    let arg = |i: usize, or: usize| args.get(i).map_or(or, |s| s.parse().expect("a width"));
    let (w, q) = (arg(0, 1024), arg(1, 1));
    let note = move |_: usize| format!(" of {w} ({} by {w})", (q + 1) * w - 1);
    let inputs = move |k: usize| sparse_division(w, q, k);
    let bench = Crossover {
        unit: "nonzero words",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "long division",
            run: &|(a, b): &Pair| x::div_rem_sparse(a, b),
        },
        above: match q {
            1 => Method {
                name: "reciprocal",
                run: &|(a, b): &Pair| x::div_rem_by_reciprocal(a, b),
            },
            _ => Method {
                name: "reciprocal at each block",
                run: &|(a, b): &Pair| x::div_rem_by_levels(a, b),
            },
        },
        takes_above: &|(a, b): &Pair| !x::div_by_rows(a, b),
        constant: Some(Constant {
            name: "SPARSE_STEP",
            built: x::SPARSE_STEP,
            flip: &|(a, b): &Pair| x::step_flip(a, b),
            below_at_most: true,
        }),
    };
    let verdict = bench.report(
        &mut Meter::new(),
        &match q {
            1 => format!("div-sparse {w}"),
            _ => format!("div-sparse {w} {q}"),
        },
        &format!(
            "SPARSE_STEP, SPARSE_WORD {}, SPARSE_RUN {}",
            x::SPARSE_WORD,
            x::SPARSE_RUN
        ),
        &ladder(2, w, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

fn recip(_: &[String]) -> ExitCode {
    let note = |w: usize| format!(" ({} bits)", 64 * w);
    let inputs = |w: usize| {
        let ones = (BigUint::from(1u32) << (64 * w)) - 1u32;
        let top = BigUint::from(1u32) << (64 * w - 1);
        vec![random(&mut Rng::new(w as u64), w), ones, top]
    };
    let bench = Crossover {
        unit: "words",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "one division",
            run: &|a: &BigUint| x::reciprocal(a, a.bits()),
        },
        above: Method {
            name: "a Newton step",
            run: &|a: &BigUint| x::reciprocal(a, a.bits() - 1),
        },
        takes_above: &|a: &BigUint| a.bits() > x::RECIP_LEAF,
        constant: None,
    };
    let verdict = bench.report(
        &mut Meter::new(),
        "recip",
        &format!("RECIP_LEAF {} bits", x::RECIP_LEAF),
        &ladder(4, 1024, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// Two odd numbers of `w` words, random, and a pair of all ones and one.
fn odd_pairs(w: usize) -> Vec<Pair> {
    let mut rng = Rng::new(w as u64);
    let ones = (BigUint::from(1u32) << (64 * w)) - 1u32;
    let one_above = (BigUint::from(1u32) << (64 * w - 1)) + 1u32;
    vec![
        (random_odd(&mut rng, w), random_odd(&mut rng, w)),
        (ones, one_above),
    ]
}

fn gcd_leaf(_: &[String]) -> ExitCode {
    let note = |w: usize| format!(" ({} bits)", 64 * w);
    let bench = Crossover {
        unit: "words",
        note: &note,
        inputs: &odd_pairs,
        below: Method {
            name: "Stein",
            run: &|(a, b): &Pair| x::gcd(a, b, a.bits().max(b.bits()), x::LIFT_BITS),
        },
        above: Method {
            name: "a half gcd first",
            run: &|(a, b): &Pair| x::gcd(a, b, a.bits().max(b.bits()) - 1, x::LIFT_BITS),
        },
        takes_above: &|(a, b): &Pair| a.bits().max(b.bits()) > x::GCD_LEAF,
        constant: None,
    };
    let verdict = bench.report(
        &mut Meter::new(),
        "gcd-leaf",
        &format!("GCD_LEAF {} bits", x::GCD_LEAF),
        &ladder(32, 2048, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// The lifts of `lift-gcd` and `lift-bezout` for numbers of `bits` bits: the half gcd's top
/// level has a valuation budget of `bits / 4`, and the levels below at most half of it. The
/// first lift is above the top level's budget, which then lifts; the second between the two,
/// so that only the top level applies its matrix. The levels below lift in both.
fn lifts(bits: u64) -> (u64, u64) {
    (bits / 2, 3 * bits / 16)
}

fn lift_gcd(_: &[String]) -> ExitCode {
    let note = |w: usize| format!(" ({} bits at the top level)", 16 * w);
    let bench = Crossover {
        unit: "words",
        note: &note,
        inputs: &odd_pairs,
        below: Method {
            name: "lift",
            run: &|(a, b): &Pair| x::gcd(a, b, x::GCD_LEAF, lifts(a.bits()).0),
        },
        above: Method {
            name: "matrix",
            run: &|(a, b): &Pair| x::gcd(a, b, x::GCD_LEAF, lifts(a.bits()).1),
        },
        takes_above: &|(a, b): &Pair| a.bits().max(b.bits()) / 4 > x::LIFT_BITS,
        constant: None,
    };
    let verdict = bench.report(
        &mut Meter::new(),
        "lift-gcd",
        &format!("LIFT_BITS {} bits", x::LIFT_BITS),
        &ladder(512, 8192, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

fn lift_bezout(_: &[String]) -> ExitCode {
    let note = |w: usize| format!(" ({} bits at the top level)", 16 * w);
    let bench = Crossover {
        unit: "words",
        note: &note,
        inputs: &odd_pairs,
        below: Method {
            name: "lift",
            run: &|(a, b): &Pair| x::bezout(a, b, lifts(a.bits()).0),
        },
        above: Method {
            name: "matrix",
            run: &|(a, b): &Pair| x::bezout(a, b, lifts(a.bits()).1),
        },
        takes_above: &|(a, b): &Pair| a.bits().max(b.bits()) / 4 > x::LIFT_BITS,
        constant: None,
    };
    let verdict = bench.report(
        &mut Meter::new(),
        "lift-bezout",
        &format!("LIFT_BITS {} bits", x::LIFT_BITS),
        &ladder(512, 8192, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

fn cached(_: &[String]) -> ExitCode {
    /// The words of the factor, and the most of the numbers it multiplies.
    const FACTOR: usize = 4096;
    let factor = x::Kept::new(random(&mut Rng::new(1), FACTOR), FACTOR);
    let inputs = |w: usize| {
        let ones = (BigUint::from(1u32) << (64 * w)) - 1u32;
        vec![random(&mut Rng::new(w as u64), w), ones]
    };
    let note = |_: usize| format!(" by {FACTOR}");
    let bench = Crossover {
        unit: "words",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "mul",
            run: &|y: &BigUint| mul_uint(y, factor.value()),
        },
        above: Method {
            name: "kept spectra",
            run: &|y: &BigUint| factor.mul(y),
        },
        takes_above: &|y: &BigUint| factor.by_spectra(y),
        constant: Some(Constant {
            name: "CACHED_COST",
            built: x::CACHED_COST,
            flip: &|y: &BigUint| factor.cached_flip(y),
            below_at_most: false,
        }),
    };
    let verdict = bench.report(
        &mut Meter::new(),
        "cached",
        "CACHED_COST",
        &ladder(256, FACTOR, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

fn print_whole(args: &[String]) -> ExitCode {
    let arg = |k: usize, default: usize| {
        args.get(k)
            .map_or(default, |s| s.parse().expect("a size in words"))
    };
    let (from, to) = (arg(0, 256), arg(1, 32_768));
    let note = |w: usize| format!(" ({:.0} digits)", digits_of_words(w));
    let inputs = |w: usize| {
        let ones = (BigUint::from(1u32) << (64 * w)) - 1u32;
        vec![random(&mut Rng::new(w as u64), w), ones]
    };
    let bench = Crossover {
        unit: "words",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "num-bigint whole",
            run: &|x: &BigUint| x.to_string(),
        },
        above: Method {
            name: "split",
            run: &|x: &BigUint| to_decimal_split(x),
        },
        takes_above: &|x: &BigUint| words(x) >= PRINT_WHOLE,
        constant: None,
    };
    let verdict = bench.report(
        &mut Meter::new(),
        "print-whole",
        &format!("PRINT_WHOLE {PRINT_WHOLE} words, PRINT_HANDOFF {PRINT_HANDOFF}"),
        &ladder(from, to, 4),
        0.01,
    );
    status(verdict.holds())
}

fn print_handoff(args: &[String]) -> ExitCode {
    let digits: Vec<u32> = match args.is_empty() {
        true => vec![160_000, 320_000, 1_280_000],
        false => args
            .iter()
            .map(|s| s.parse().expect("a size in digits"))
            .collect(),
    };
    let ten = BigUint::from(10u32);
    // A handoff of `h` words hands over each part below the first power of more than `h`
    // words: 0 splits down to `10^597`, and `words(10^(597 2^i))` leaves the parts below
    // `10^(597 2^(i + 1))` to num-bigint.
    let mut handoffs = vec![0];
    let mut values = vec!["0 (below 10^597)".to_string()];
    for i in 0..8 {
        let h = words(&ten.pow(PRINT_LEAF_DIGITS << i));
        handoffs.push(h);
        values.push(format!("{h} (below 10^{})", PRINT_LEAF_DIGITS << (i + 1)));
    }
    let built = handoffs
        .iter()
        .position(|&h| h == PRINT_HANDOFF)
        .expect("PRINT_HANDOFF is a power's words");
    // One closure type for every handoff, so the closures share a `Vec` with no boxes.
    let runs: Vec<_> = handoffs
        .iter()
        .map(|&h| move |x: &BigUint| to_decimal_split_at(x, h))
        .collect();
    let inputs: Vec<BigUint> = digits
        .iter()
        .map(|&d| random_digits(&mut Rng::new(u64::from(d)), d))
        .collect();
    for x in &inputs {
        assert_eq!(
            to_decimal_split(x),
            x.to_string(),
            "the split is num-bigint's text"
        );
    }
    let setting = Setting {
        name: "print-handoff",
        constant: "PRINT_HANDOFF".into(),
        unit: "words",
        values,
        built,
        labels: digits.iter().map(|d| format!("{d} digits")).collect(),
        inputs,
        methods: runs
            .iter()
            .map(|run| Method { name: "split", run })
            .collect(),
    };
    status(setting.report(&mut Meter::new()).holds())
}

/// The leaves of `leaf-digits` and `corpus-leaf-digits`, in digits.
const LEAVES: [usize; 8] = [128, 256, 512, 1024, 2048, 4096, 8192, 16_384];

/// The texts of `leaf-digits` and `corpus-leaf-digits`, by their digits.
const TEXTS: [usize; 8] = [700, 1500, 3000, 10_000, 30_000, 100_000, 300_000, 1_000_000];

/// A setting of a reading's leaf over [`LEAVES`] on texts of [`TEXTS`] digits.
fn leaf_setting<'a>(
    name: &'static str,
    built: usize,
    runs: &'a [impl Fn(&String) -> BigUint],
) -> Setting<'a, String, BigUint> {
    Setting {
        name,
        constant: "LEAF_DIGITS".into(),
        unit: "digits",
        values: LEAVES.iter().map(usize::to_string).collect(),
        built: LEAVES
            .iter()
            .position(|&l| l == built)
            .expect("LEAF_DIGITS among the leaves"),
        labels: TEXTS.iter().map(|d| format!("{d} digits")).collect(),
        inputs: TEXTS
            .iter()
            .map(|&d| random_text(&mut Rng::new(d as u64), d))
            .collect(),
        methods: runs
            .iter()
            .map(|run| Method { name: "read", run })
            .collect(),
    }
}

fn leaf_digits(_: &[String]) -> ExitCode {
    let runs: Vec<_> = LEAVES
        .iter()
        .map(|&leaf| move |t: &String| x::read_digits(t, leaf))
        .collect();
    let setting = leaf_setting("leaf-digits", x::LEAF_DIGITS, &runs);
    status(setting.report(&mut Meter::new()).holds())
}

fn corpus_leaf_digits(_: &[String]) -> ExitCode {
    let runs: Vec<_> = LEAVES
        .iter()
        .map(|&leaf| move |t: &String| zedrt::read_digits_by(t, leaf))
        .collect();
    let setting = leaf_setting("corpus-leaf-digits", zedrt::LEAF_DIGITS, &runs);
    status(setting.report(&mut Meter::new()).holds())
}

fn transform_words(_: &[String]) -> ExitCode {
    let five = BigUint::from(5u32).pow(65_536);
    let inputs = |w: usize| {
        let ones = (BigUint::from(1u32) << (32 * w)) - 1u32;
        vec![
            (five.clone(), random32(&mut Rng::new(w as u64), w)),
            (five.clone(), ones),
        ]
    };
    let note = |_: usize| format!(" by {}", words32(&five));
    let bench = Crossover {
        unit: "32-bit words",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "num-bigint",
            run: &|(a, b): &Pair| a * b,
        },
        above: Method {
            name: "transform",
            run: &|(a, b): &Pair| product::transform_mul(a, b),
        },
        takes_above: &|(a, b): &Pair| words32(a).min(words32(b)) >= product::TRANSFORM_WORDS,
        constant: None,
    };
    let verdict = bench.report(
        &mut Meter::new(),
        "transform-words",
        &format!("TRANSFORM_WORDS {}", product::TRANSFORM_WORDS),
        &ladder(2378, 4756, 4),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// A factor, its partner 1.43 times as long, and the twiddles of their product.
type Kept = (BigUint, BigUint, Vec<product::Twiddle>);

fn kept_words(_: &[String]) -> ExitCode {
    let inputs = |w: usize| {
        let mut rng = Rng::new(w as u64);
        let (v, p) = (random32(&mut rng, w), random32(&mut rng, w * 143 / 100));
        let roots = product::twiddles(product::transform_len(v.bits(), p.bits()));
        vec![(v, p, roots)]
    };
    let note = |w: usize| format!(" by {}", w * 143 / 100);
    let bench = Crossover {
        unit: "32-bit words",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "plain",
            run: &|(v, p, roots): &Kept| {
                let f = product::Factor::plain(v.clone());
                (f.square(roots), f.times_at(p, roots, u64::MAX))
            },
        },
        above: Method {
            name: "kept",
            run: &|(v, p, roots): &Kept| {
                let f = product::Factor::new(v.clone(), p.bits(), roots);
                (f.square(roots), f.times_at(p, roots, 0))
            },
        },
        takes_above: &|(v, p, _): &Kept| words32(v).min(words32(p)) >= product::KEPT_WORDS,
        constant: None,
    };
    let verdict = bench.report(
        &mut Meter::new(),
        "kept-words",
        &format!("KEPT_WORDS {}", product::KEPT_WORDS),
        &ladder(512, 2048, 4),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// The leaves of `text-leaf`, in bytes.
const TEXT_LEAVES: [usize; 7] = [16, 32, 64, 128, 256, 512, 1024];

/// The joins of `text-leaf`.
const JOINS: usize = 200_000;

fn text_leaf(_: &[String]) -> ExitCode {
    // A `foldl` of `JOINS` joins of the pieces in turn, then `==` against the same text held
    // whole, a hash and the print: the uses whose cost depends on the blocks.
    let runs: Vec<_> = TEXT_LEAVES
        .iter()
        .map(|&leaf| {
            move |(pieces, whole): &(Vec<Text>, Text)| {
                let mut t = Text::from("");
                for p in pieces.iter().cycle().take(JOINS) {
                    t = Text::join_at(&t, p, leaf).expect("short");
                }
                let mut h = DefaultHasher::new();
                t.hash(&mut h);
                (t == *whole, h.finish(), t.to_string().len())
            }
        })
        .collect();
    let pieces = [1usize, 8, 64];
    let inputs: Vec<(Vec<Text>, Text)> = pieces
        .iter()
        .map(|&n| {
            let pieces: Vec<String> = (b'a'..=b'z')
                .map(|c| char::from(c).to_string().repeat(n))
                .collect();
            let whole: String = pieces
                .iter()
                .cycle()
                .take(JOINS)
                .map(String::as_str)
                .collect();
            (
                pieces.iter().map(|p| Text::from(p.as_str())).collect(),
                Text::from(whole),
            )
        })
        .collect();
    let setting = Setting {
        name: "text-leaf",
        constant: "text LEAF".into(),
        unit: "bytes",
        values: TEXT_LEAVES.iter().map(usize::to_string).collect(),
        built: TEXT_LEAVES
            .iter()
            .position(|&l| l == text::LEAF)
            .expect("LEAF among the leaves"),
        labels: pieces.iter().map(|n| format!("{n}-byte pieces")).collect(),
        inputs,
        methods: runs
            .iter()
            .map(|run| Method { name: "join", run })
            .collect(),
    };
    status(setting.report(&mut Meter::new()).holds())
}

/// Two sums of packed monomials, as `Poly::mul` multiplies them.
type Sums = (px::Sum, px::Sum);

/// A random signed coefficient of `words` 64-bit words, the top bit of its magnitude set.
fn coefficient(rng: &mut Rng, words: usize) -> BigInt {
    let sign = match rng.next_u64() & 1 {
        0 => Sign::Plus,
        _ => Sign::Minus,
    };
    BigInt::from_biguint(sign, random(rng, words))
}

/// A sum of a coefficient of `words` words at each of `indices`.
fn sum_at(rng: &mut Rng, indices: impl Iterator<Item = u128>, words: usize) -> px::Sum {
    px::Sum::new(indices.map(|i| (i, coefficient(rng, words))).collect())
}

/// The constant of `Poly::mul`'s choice of method that `which` names, `PAIR_COST` ("pair"),
/// `SLOT_COST` ("slot") or `DENSE_COST` ("fixed"), with `below_at_most` as the benchmark orders
/// the two methods: `sparse_first` when the sparse product is the first. A higher `PAIR_COST`
/// or a lower `SLOT_COST` or `DENSE_COST` takes the dense product sooner.
fn poly_constant(which: Option<&String>, sparse_first: bool) -> Constant<'static, Sums> {
    match which.map(String::as_str) {
        None | Some("pair") => Constant {
            name: "PAIR_COST",
            built: px::PAIR_COST,
            flip: &|(a, b): &Sums| px::pair_flip(a, b),
            below_at_most: sparse_first,
        },
        Some("slot") => Constant {
            name: "SLOT_COST",
            built: px::SLOT_COST,
            flip: &|(a, b): &Sums| px::slot_flip(a, b),
            below_at_most: !sparse_first,
        },
        Some("fixed") => Constant {
            name: "DENSE_COST",
            built: px::DENSE_COST,
            flip: &|(a, b): &Sums| px::fixed_flip(a, b),
            below_at_most: !sparse_first,
        },
        // Only a square reads it, so only `poly-square` takes it.
        Some("square") => Constant {
            name: "SQUARE_PAIR_COST",
            built: px::SQUARE_PAIR_COST,
            flip: &|(a, b): &Sums| px::square_flip(a, b),
            below_at_most: sparse_first,
        },
        Some(other) => panic!("no constant {other}: pair, slot, fixed or square"),
    }
}

/// The constants of `Poly::mul`'s choice of method as built, for the tables.
fn poly_constants() -> String {
    format!(
        "PAIR_COST {}, SLOT_COST {}, DENSE_COST {}, SQUARE_PAIR_COST {}",
        px::PAIR_COST,
        px::SLOT_COST,
        px::DENSE_COST,
        px::SQUARE_PAIR_COST
    )
}

/// The sparse product against the dense one on univariate sums of `t` terms at every index,
/// coefficients of `words` 64-bit words (1 and 4 in `all`): the dense product wins from a
/// few terms on, as its `L log L` grows as `t log t` against the sparse product's `t^2`.
fn poly_dense(args: &[String]) -> ExitCode {
    let words: usize = args.first().map_or(1, |s| s.parse().expect("words"));
    let note = move |_: usize| format!(" ({words}-word coefficients)");
    let inputs = move |t: usize| {
        let mut rng = Rng::new(t as u64);
        let n = t as u128;
        vec![
            (sum_at(&mut rng, 0..n, words), sum_at(&mut rng, 0..n, words)),
            // Sides of different spans: the second at every other index.
            (
                sum_at(&mut rng, 0..n, words),
                sum_at(&mut rng, (0..n).map(|i| 2 * i), words),
            ),
        ]
    };
    let bench = Crossover {
        unit: "terms",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "sparse",
            run: &|(a, b): &Sums| px::sparse(a, b),
        },
        above: Method {
            name: "dense",
            run: &|(a, b): &Sums| px::dense(a, b),
        },
        takes_above: &|(a, b): &Sums| px::takes_dense(a, b),
        constant: Some(poly_constant(args.get(1), true)),
    };
    let verdict = bench.report(
        &mut Meter::new(),
        &format!(
            "poly-dense {words} {}",
            args.get(1).map_or("pair", String::as_str)
        ),
        &poly_constants(),
        &ladder(2, 256, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// The dense product against the sparse one on two sums of `t` terms (64 and 16 in `all`), one
/// a gap of about `g` from the next: term `i` at `g i` plus a random offset below `g`, so no
/// common step closes the gaps. The sparse product wins from some gap on, as the dense
/// product's span grows as `t g` against its own `t^2`.
fn poly_gaps(args: &[String]) -> ExitCode {
    let t: u128 = args.first().map_or(256, |s| s.parse().expect("terms"));
    let note = move |_: usize| format!(" ({t} terms a side)");
    let inputs = move |g: usize| {
        let mut rng = Rng::new(g as u64);
        let g = g as u128;
        let side = |rng: &mut Rng| {
            let at: Vec<u128> = (0..t)
                .map(|i| g * i + u128::from(rng.next_u64()) % g)
                .collect();
            sum_at(rng, at.into_iter(), 1)
        };
        let (a, b) = (side(&mut rng), side(&mut rng));
        let (c, d) = (side(&mut rng), side(&mut rng));
        vec![(a, b), (c, d)]
    };
    let bench = Crossover {
        unit: "gap",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "dense",
            run: &|(a, b): &Sums| px::dense(a, b),
        },
        above: Method {
            name: "sparse",
            run: &|(a, b): &Sums| px::sparse(a, b),
        },
        takes_above: &|(a, b): &Sums| !px::takes_dense(a, b),
        constant: Some(poly_constant(args.get(1), false)),
    };
    let verdict = bench.report(
        &mut Meter::new(),
        &format!(
            "poly-gaps {t} {}",
            args.get(1).map_or("pair", String::as_str)
        ),
        &poly_constants(),
        &ladder(1, 4096, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// The sparse product against the dense one on univariate sums of `t` terms at every index (2
/// and 8 in `all`), coefficients of `w` 64-bit words: the sparse product's `t^2` coefficient
/// products of `w^2` words against the dense product's `t w log(t w)`.
fn poly_wide(args: &[String]) -> ExitCode {
    let t: u128 = args.first().map_or(2, |s| s.parse().expect("terms"));
    let note = move |_: usize| format!(" ({t} terms a side)");
    let inputs = move |w: usize| {
        let mut rng = Rng::new(w as u64);
        vec![
            (sum_at(&mut rng, 0..t, w), sum_at(&mut rng, 0..t, w)),
            (sum_at(&mut rng, 0..t, w), sum_at(&mut rng, 0..t + 1, w)),
        ]
    };
    let bench = Crossover {
        unit: "words",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "sparse",
            run: &|(a, b): &Sums| px::sparse(a, b),
        },
        above: Method {
            name: "dense",
            run: &|(a, b): &Sums| px::dense(a, b),
        },
        takes_above: &|(a, b): &Sums| px::takes_dense(a, b),
        constant: Some(poly_constant(args.get(1), true)),
    };
    let verdict = bench.report(
        &mut Meter::new(),
        &format!(
            "poly-wide {t} {}",
            args.get(1).map_or("pair", String::as_str)
        ),
        &poly_constants(),
        &ladder(1, 1024, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// The dense product against the sparse one on the square of a sum of `t` terms (256 in `all`),
/// one a gap of about `g` from the next as in [`poly_gaps`], `g` from 1 to 512 in eighths of a
/// doubling: the packed
/// integer is squared by transforms with one forward transform fewer than a product of two
/// numbers, which `Poly::mul`'s choice counts (`SQUARE_SHARE`), and the sparse product forms
/// only the `t (t + 1) / 2` pairs `i <= j`, which it counts too. The sparse product wins from
/// some gap on. At 64 terms the packed integer is squared by Toom in a release build, not by
/// transforms, so the share does not apply and the choice is as for two numbers. A third
/// argument gives the coefficients' 64-bit words, 1 when left out (POLY-square-cost-sizes).
fn poly_square(args: &[String]) -> ExitCode {
    let t: u128 = args.first().map_or(256, |s| s.parse().expect("terms"));
    let words: usize = args.get(2).map_or(1, |s| s.parse().expect("words"));
    let note = move |_: usize| format!(" ({t} terms of {words} words, squared)");
    let inputs = move |g: usize| {
        let mut rng = Rng::new(g as u64);
        let g = g as u128;
        let mut square = || {
            let at: Vec<u128> = (0..t)
                .map(|i| g * i + u128::from(rng.next_u64()) % g)
                .collect();
            let a = sum_at(&mut rng, at.into_iter(), words);
            (a.clone(), a)
        };
        vec![square(), square()]
    };
    let bench = Crossover {
        unit: "gap",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "dense",
            run: &|(a, b): &Sums| px::dense(a, b),
        },
        above: Method {
            name: "sparse",
            run: &|(a, b): &Sums| px::sparse(a, b),
        },
        takes_above: &|(a, b): &Sums| !px::takes_dense(a, b),
        constant: Some(poly_constant(args.get(1), false)),
    };
    let verdict = bench.report(
        &mut Meter::new(),
        &format!(
            "poly-square {t} {}{}",
            args.get(1).map_or("pair", String::as_str),
            match words {
                1 => String::new(),
                w => format!(" {w}"),
            }
        ),
        &poly_constants(),
        &ladder(1, 512, 8),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// `SUPPORT_COST` of `Poly::mul`'s choice to try the support product, for benchmarks that
/// order it second: it is tried below the flip, so a higher constant takes the first method,
/// the dense or the sparse product, sooner.
fn support_constant() -> Constant<'static, Sums> {
    Constant {
        name: "SUPPORT_COST",
        built: px::SUPPORT_COST,
        flip: &|(a, b): &Sums| px::support_flip(a, b),
        below_at_most: false,
    }
}

/// `a * b` by the support product, which these shapes give no bound.
fn support_run((a, b): &Sums) -> Vec<(u128, BigInt)> {
    px::support(a, b).expect("the support product runs")
}

/// The support product against the method `Poly::mul` takes when it gives way, on the square
/// of a sum shaped as `(x + y)^k + x` in one packed index (`k + 2` terms, at `i + (k - i) r`,
/// `r = 2k + 1`, and at 1), coefficients of `words` 64-bit words (1, 4 and 16 in `all`), `k`
/// from 8 to 512 (or the second argument) in halves of a doubling; and, checked only, the
/// product of two such sums.
/// The square's support has about `3k` indices against its `k^2 / 2` pairs, so the support
/// product wins from some `k` on, sooner at wide coefficients, whose pairs cost the sparse
/// product the more (POLY-support-bench).
fn poly_support(args: &[String]) -> ExitCode {
    let words: usize = args.first().map_or(1, |s| s.parse().expect("words"));
    // The largest `k`, 512 when left out; 1024 reaches the `k = 640` of
    // `poly::tests::the_product_takes_the_support_product_where_it_is_cheaper`.
    let top: usize = args
        .get(1)
        .map_or(512, |s| s.parse().expect("the largest k"));
    let note = move |k: usize| format!(" ({} terms of {words} words, squared)", k + 2);
    let inputs = move |k: usize| {
        let mut rng = Rng::new(k as u64);
        let k = k as u128;
        let r = 2 * k + 1;
        let mut shape = || {
            let at = (0..=k).map(|i| i + (k - i) * r).chain(std::iter::once(1));
            sum_at(&mut rng, at, words)
        };
        let a = shape();
        let (b, c) = (shape(), shape());
        vec![(a.clone(), a), (b, c)]
    };
    let bench = Crossover {
        unit: "k",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "fallback",
            run: &|(a, b): &Sums| px::fallback(a, b),
        },
        above: Method {
            name: "support",
            run: &support_run,
        },
        takes_above: &|(a, b): &Sums| px::takes_support(a, b),
        constant: Some(support_constant()),
    };
    let verdict = bench.report(
        &mut Meter::new(),
        &format!("poly-support {words}"),
        &format!("SUPPORT_COST {}", px::SUPPORT_COST),
        &ladder(8, top, 2),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// The support product against the method `Poly::mul` takes when it gives way, on the square
/// of a sum of `t` terms (256 in `all`) in pairs at `i s` and `i s + 1`, `s = g + 2`,
/// coefficients of `words` 64-bit words (1 when left out), `g` from 1 to 4096 in quarters of a
/// doubling; and, checked only, the product of that sum with one in pairs at `i s` and
/// `i s + 2`. Its support has about `1.5 t` indices whatever `g`, the dense product's span
/// grows as `t g` and the sparse product's pairs stay `t^2 / 2`, so the support product's
/// estimate falls below the dense one's from some gap on; but there the sparse square is the
/// fallback, and at 256 terms of one word it took 0.33 to 0.7 of the support product's time
/// at every gap to 4096 (POLY-support-bench, 2026-11-22). So this shape bounds
/// `SUPPORT_COST` from below only.
fn poly_support_gaps(args: &[String]) -> ExitCode {
    let t: u128 = args.first().map_or(256, |s| s.parse().expect("terms"));
    let words: usize = args.get(1).map_or(1, |s| s.parse().expect("words"));
    let note = move |_: usize| format!(" ({t} terms of {words} words, squared)");
    let inputs = move |g: usize| {
        let mut rng = Rng::new(g as u64);
        let g = g as u128;
        let mut pairs = |d: u128| {
            let at = (0..t / 2).flat_map(|i| [i * (g + 2), i * (g + 2) + d]);
            sum_at(&mut rng, at, words)
        };
        let a = pairs(1);
        let (b, c) = (pairs(1), pairs(2));
        vec![(a.clone(), a), (b, c)]
    };
    let bench = Crossover {
        unit: "gap",
        note: &note,
        inputs: &inputs,
        below: Method {
            name: "fallback",
            run: &|(a, b): &Sums| px::fallback(a, b),
        },
        above: Method {
            name: "support",
            run: &support_run,
        },
        takes_above: &|(a, b): &Sums| px::takes_support(a, b),
        constant: Some(support_constant()),
    };
    let verdict = bench.report(
        &mut Meter::new(),
        &format!(
            "poly-support-gaps {t}{}",
            match words {
                1 => String::new(),
                w => format!(" {w}"),
            }
        ),
        &format!("SUPPORT_COST {}", px::SUPPORT_COST),
        &ladder(1, 4096, 4),
        TOLERANCE,
    );
    status(verdict.holds())
}

/// `poly-support-units [words]`: on the squares of `poly-support` (`k` from 256 to 512 in
/// sixteenths of a doubling, and the `k` POLY-support-cost-ranking measured: 304, 332, 350, 354
/// and 362), the support product's work against its units: the units its choice estimates
/// before the rounds, the units its rounds spend, and the terms of the product. Where the work
/// follows the units spent but not the units estimated, the estimate misses the rounds (the
/// support's size or the number of rounds); where it follows neither, a unit's cost varies.
/// Not a fit, so not in `all`.
fn poly_support_units(args: &[String]) -> ExitCode {
    let words: usize = args.first().map_or(16, |s| s.parse().expect("words"));
    let mut meter = Meter::new();
    let mut ks = ladder(256, 512, 16);
    ks.extend([304, 332, 350, 354, 362]);
    ks.sort_unstable();
    ks.dedup();
    println!("poly-support-units {words}, {}", conditions());
    println!(
        "\n| k | terms | product terms | size estimated | size / product terms | units of folds | units estimated | units spent | spent / estimated | {} | {} / unit spent |",
        meter.unit(),
        meter.unit()
    );
    println!("|---|---|---|---|---|---|---|---|---|---|---|");
    for k in ks {
        let mut rng = Rng::new(k as u64);
        let kk = k as u128;
        let r = 2 * kk + 1;
        let at = (0..=kk).map(|i| i + (kk - i) * r).chain(std::iter::once(1));
        let a = sum_at(&mut rng, at, words);
        let u = px::support_units(&a, &a).expect("the support product runs");
        let work = meter.work(|| {
            std::hint::black_box(px::support(&a, &a));
        });
        println!(
            "| {k} | {} | {} | {:.0} | {:.3} | {:.0} | {:.0} | {:.0} | {:.3} | {} | {:.2} |",
            k + 2,
            u.terms,
            u.size,
            u.size / u.terms as f64,
            u.folds,
            u.estimated,
            u.spent,
            u.spent / u.estimated,
            work.units,
            work.units as f64 / u.spent
        );
    }
    ExitCode::SUCCESS
}

/// The first `n` primes at or above `from`, by `zed_numtheory::next_prime`.
fn primes_from(from: u64, n: usize) -> Vec<u64> {
    let mut out = Vec::with_capacity(n);
    let mut p = from;
    while out.len() < n {
        p = zed_numtheory::next_prime(p).expect("a prime below 2^64");
        out.push(p);
        p += 1;
    }
    out
}

/// `factor-bits`: `cx::FACTOR_BITS` and `cx::FACTOR_INPUTS` of `num::coprime`
/// (PERF-negated-chain-unsolved, author decision A96), the word path by factoring
/// (`zed_numtheory::coprime_base_by_factoring` and `shares_a_factor_by_factoring`) against the
/// general methods (Bernstein's trees, `cx::coprime_base_by_halves`, and
/// `cx::shares_a_factor_by_tree`) on `k` word inputs whose
/// largest has `b` bits, on both sides of each switchover. Three families of each width:
/// distinct primes of `b` bits (a primality test each); disjoint products `p_(2i) p_(2i+1)` of
/// primes of `b / 2` bits (Pollard's rho's worst case at a width, about `2^(b/4)` products
/// each); and chains `p_i p_(i+1)` of such primes (every prime shared). Where `k` primes of
/// `b / 2` bits do not exist the primes run past that width, and the printed `bits` is the
/// largest input's. Prints the instructions and bytes of each method, and exits with status 1
/// where their answers differ. Factoring costs a fixed amount an input at a width and the trees
/// more an input at more inputs, so the switch is in both: the path is taken from
/// `FACTOR_INPUTS` inputs on, up to the largest width at which it is the cheaper on every family
/// there; the measurements are in the comment of `FACTOR_BITS`. Widths past 56 bits only repeat
/// the trees' side at a higher cost (1.8 M instructions an input by factoring at 63 bits) and
/// are left out to keep the run short. Not a fit, so not in `all`. Moved here from the kernel's
/// unit tests (`num::bench::the_factor_bits_crossover_axis`, 44 s of the unit test binary,
/// TEST-kernel-unit-benches-out); `num::coprime::tests::the_factored_paths_agree` holds the two
/// methods equal on both sides of each switchover in the tests.
fn factor_bits(_: &[String]) -> ExitCode {
    let mut meter = Meter::new();
    let mut widths: Vec<u32> = vec![16, 24, 32, 40, 44, 48, 52, 56];
    widths.extend([cx::FACTOR_BITS, cx::FACTOR_BITS + 1]);
    widths.sort_unstable();
    widths.dedup();
    let fi = cx::FACTOR_INPUTS;
    let mut ks = vec![2usize, 4, 8, 13, 64, 512, fi / 2, fi];
    ks.sort_unstable();
    ks.dedup();
    let mut agree = true;
    for k in ks {
        for &b in &widths {
            let half = 1u64 << (b / 2 - 1);
            let pairs = primes_from(half, 2 * k);
            let chain = primes_from(half, k + 1);
            let families: [(&str, Vec<u64>); 3] = [
                ("distinct", primes_from(1 << (b - 1), k)),
                (
                    "pairs",
                    (0..k).map(|i| pairs[2 * i] * pairs[2 * i + 1]).collect(),
                ),
                ("chain", (0..k).map(|i| chain[i] * chain[i + 1]).collect()),
            ];
            for (family, ws) in families {
                let xs: Vec<BigUint> = ws.iter().map(|&w| BigUint::from(w)).collect();
                let bits = ws.iter().map(|w| 64 - w.leading_zeros()).max().unwrap_or(0);
                let (mut factored, mut halves) = (Vec::new(), Vec::new());
                let fb = meter.work(|| {
                    factored = zed_numtheory::coprime_base_by_factoring(&ws).0;
                });
                let hb = meter.work(|| halves = cx::coprime_base_by_halves(&xs));
                factored.sort_unstable();
                halves.sort();
                let factored: Vec<BigUint> = factored.into_iter().map(BigUint::from).collect();
                let (mut s_factored, mut s_tree) = (Vec::new(), Vec::new());
                let fs =
                    meter.work(|| s_factored = zed_numtheory::shares_a_factor_by_factoring(&ws));
                let ts = meter.work(|| s_tree = cx::shares_a_factor_by_tree(&xs));
                if factored != halves || s_factored != s_tree {
                    agree = false;
                    println!("DIFFER family={family} k={k} b={b}");
                }
                println!(
                    "bench FACTOR_BITS family={family} k={k} bits={bits} factor_side={} base: factored={}/{} halves={}/{} shares: factored={}/{} tree={}/{}",
                    bits <= cx::FACTOR_BITS && k >= fi,
                    fb.units,
                    fb.bytes,
                    hb.units,
                    hb.bytes,
                    fs.units,
                    fs.bytes,
                    ts.units,
                    ts.bytes
                );
            }
        }
    }
    println!("{}", conditions());
    status(agree)
}

fn print_never_slower(args: &[String]) -> ExitCode {
    let digits: Vec<u32> = match args.is_empty() {
        true => vec![
            10_000, 20_000, 40_000, 80_000, 160_000, 320_000, 640_000, 1_280_000,
        ],
        false => args
            .iter()
            .map(|s| s.parse().expect("a size in digits"))
            .collect(),
    };
    let mut meter = Meter::new();
    let unit = meter.unit();
    println!(
        "to_decimal against num-bigint (PRINT_WHOLE {PRINT_WHOLE} words), {}",
        conditions()
    );
    println!(
        "| digits | words | to_decimal {unit} | num-bigint {unit} | ratio | to_decimal bytes | num-bigint bytes |"
    );
    println!("|---|---|---|---|---|---|---|");
    let mut held = true;
    for d in digits {
        let x = random_digits(&mut Rng::new(u64::from(d)), d);
        assert_eq!(to_decimal(&x), x.to_string(), "{d} digits");
        let ours = least(&mut meter, || drop(std::hint::black_box(to_decimal(&x))));
        let theirs = least(&mut meter, || drop(std::hint::black_box(x.to_string())));
        let ratio = ours.units as f64 / theirs.units as f64;
        let mark = match ratio <= NEVER_SLOWER {
            true => "",
            false => " slower",
        };
        held &= ratio <= NEVER_SLOWER;
        println!(
            "| {d} | {} | {} | {} | {ratio:.4}{mark} | {} | {} |",
            words(&x),
            ours.units,
            theirs.units,
            ours.bytes,
            theirs.bytes
        );
    }
    println!("{}", conditions());
    status(held)
}

/// A benchmark: its name, its function, and its arguments in `all`.
type Bench = (
    &'static str,
    fn(&[String]) -> ExitCode,
    &'static [&'static str],
);

/// Every benchmark, with its arguments in `all`; `print-never-slower` is not a threshold.
const BENCHES: [Bench; 56] = [
    ("mul", mul, &["1"]),
    ("mul", mul, &["4"]),
    ("mul", mul, &["32"]),
    ("mul-rows", mul_rows, &[]),
    ("wrap", wrap, &["4096"]),
    ("wrap", wrap, &["8192"]),
    ("div-leaf", div_leaf, &["1", "1"]),
    ("div-leaf", div_leaf, &["1", "4"]),
    ("div-leaf", div_leaf, &["4", "1"]),
    ("div-leaf", div_leaf, &["16", "1"]),
    ("div-leaf", div_leaf, &["256", "1"]),
    ("rem-leaf", rem_leaf, &["16"]),
    ("rem-leaf", rem_leaf, &["256"]),
    ("div-rows", div_rows, &[]),
    ("div-rows", div_rows, &["step"]),
    ("div-sparse", div_sparse, &["256"]),
    ("div-sparse", div_sparse, &["1024"]),
    ("div-sparse", div_sparse, &["2048"]),
    ("div-sparse", div_sparse, &["1024", "16"]),
    ("recip", recip, &[]),
    ("gcd-leaf", gcd_leaf, &[]),
    ("lift-gcd", lift_gcd, &[]),
    ("lift-bezout", lift_bezout, &[]),
    ("cached", cached, &[]),
    ("print-whole", print_whole, &[]),
    ("print-handoff", print_handoff, &[]),
    ("leaf-digits", leaf_digits, &[]),
    ("corpus-leaf-digits", corpus_leaf_digits, &[]),
    ("transform-words", transform_words, &[]),
    ("kept-words", kept_words, &[]),
    ("text-leaf", text_leaf, &[]),
    ("poly-dense", poly_dense, &["1", "pair"]),
    ("poly-dense", poly_dense, &["4", "pair"]),
    ("poly-gaps", poly_gaps, &["64", "pair"]),
    ("poly-gaps", poly_gaps, &["16", "pair"]),
    ("poly-wide", poly_wide, &["2", "pair"]),
    ("poly-wide", poly_wide, &["8", "pair"]),
    ("poly-square", poly_square, &["256", "pair"]),
    ("poly-dense", poly_dense, &["1", "slot"]),
    ("poly-dense", poly_dense, &["4", "slot"]),
    ("poly-gaps", poly_gaps, &["64", "slot"]),
    ("poly-gaps", poly_gaps, &["16", "slot"]),
    ("poly-wide", poly_wide, &["2", "slot"]),
    ("poly-wide", poly_wide, &["8", "slot"]),
    ("poly-square", poly_square, &["256", "slot"]),
    ("poly-dense", poly_dense, &["1", "fixed"]),
    ("poly-dense", poly_dense, &["4", "fixed"]),
    ("poly-gaps", poly_gaps, &["64", "fixed"]),
    ("poly-gaps", poly_gaps, &["16", "fixed"]),
    ("poly-wide", poly_wide, &["2", "fixed"]),
    ("poly-wide", poly_wide, &["8", "fixed"]),
    ("poly-square", poly_square, &["256", "fixed"]),
    ("poly-support", poly_support, &["1"]),
    ("poly-support", poly_support, &["4"]),
    ("poly-support", poly_support, &["16"]),
    ("poly-support-gaps", poly_support_gaps, &["256"]),
];

/// The limit on each benchmark of `all`.
const LIMIT: Duration = Duration::from_secs(60);

/// Every benchmark of [`BENCHES`] at once, each a process of its own killed after [`LIMIT`];
/// each one's output is printed whole when it ends, then the table of their results.
fn all(_: &[String]) -> ExitCode {
    let exe = std::env::current_exe().expect("the binary's path");
    println!("crossover all, {}", conditions());
    let start = Instant::now();
    let mut running: Vec<_> = BENCHES
        .iter()
        .map(|&(name, _, args)| {
            let mut child = Command::new(&exe)
                .arg(name)
                .args(args)
                .stdout(Stdio::piped())
                .stderr(Stdio::null())
                .spawn()
                .expect("a benchmark process");
            let mut out = child.stdout.take().expect("piped");
            let reader = std::thread::spawn(move || {
                let mut text = String::new();
                out.read_to_string(&mut text).map(|_| text)
            });
            let label = std::iter::once(name)
                .chain(args.iter().copied())
                .collect::<Vec<_>>()
                .join(" ");
            (label, child, Some(reader))
        })
        .collect();
    let mut results = Vec::new();
    let mut fits: Vec<Steps> = Vec::new();
    let mut failed = Vec::new();
    while !running.is_empty() {
        std::thread::sleep(Duration::from_millis(100));
        let mut k = 0;
        while k < running.len() {
            let (label, child, reader) = &mut running[k];
            let ended = child.try_wait().expect("a benchmark's status");
            if ended.is_none() && start.elapsed() < LIMIT {
                k += 1;
                continue;
            }
            if ended.is_none() {
                child.kill().expect("a benchmark killed");
                child.wait().expect("a killed benchmark's status");
                failed.push(format!("{label}: killed after {} s", LIMIT.as_secs()));
            }
            let text = reader
                .take()
                .expect("one reader")
                .join()
                .expect("the reader")
                .unwrap_or_default();
            println!("\n## {label}\n\n{text}");
            fits.extend(text.lines().filter_map(Steps::parse));
            match text.lines().find(|l| l.starts_with("RESULT\t")) {
                Some(line) => results.push(line.to_string()),
                None if ended.is_some() => failed.push(format!("{label}: no result")),
                None => {}
            }
            running.swap_remove(k);
        }
    }
    println!(
        "\n| benchmark | built | measured crossover | worst ratio of the method taken | spread | verdict |"
    );
    println!("|---|---|---|---|---|---|");
    results.sort();
    let mut held = failed.is_empty();
    for line in &results {
        let fields: Vec<&str> = line.split('\t').skip(1).collect();
        held &= fields.last() != Some(&"MOVED");
        println!("| {} |", fields.join(" | "));
    }
    println!("\n| constant | built | worst work as built | best fit | spread | verdict |");
    println!("|---|---|---|---|---|---|");
    fits.sort_by(|a, b| a.name.cmp(&b.name));
    for group in fits.chunk_by(|a, b| a.name == b.name) {
        let joint = Steps::joint(group);
        held &= joint.holds();
        let mark = match joint.holds() {
            true => "at the fit",
            false => "MOVED",
        };
        println!(
            "| {} | {} | {:.4} | {} | {:.4} | {mark} |",
            joint.name,
            joint.built,
            joint.built_worst,
            joint.fit(),
            joint.spread
        );
    }
    for f in &failed {
        println!("FAILED {f}");
    }
    println!("{}", conditions());
    status(held)
}

fn main() -> ExitCode {
    // With `--exact`, where `ZED_METER_DRRUN` and `ZED_METER_ICOUNT` name DynamoRIO and its
    // client (Colab's job.sh sets both) and the hardware does not count instructions, the run
    // starts again under the client, so that its meter counts instructions, not processor time,
    // which varied 1.8 times between two Colab machines on the same fit (POLY-square-1024-wide:
    // `poly-square 1024 square 4` fitted 122 on a v5e VM and 211 to 226 on an hm3). The meter
    // does not do it here itself: it starts again only in a test binary run with one test named.
    // Elsewhere the call returns and the run measures as before.
    zed_meter_settings::start_under_dynamorio();
    let args: Vec<String> = std::env::args()
        .skip(1)
        .filter(|a| a != "--exact")
        .collect();
    let rest = args.get(1..).unwrap_or(&[]);
    let name = args.first().map_or("", String::as_str);
    if name == "all" {
        return all(rest);
    }
    if name == "print-never-slower" {
        return print_never_slower(rest);
    }
    if name == "factor-bits" {
        return factor_bits(rest);
    }
    if name == "poly-support-units" {
        return poly_support_units(rest);
    }
    match BENCHES.iter().find(|(n, _, _)| *n == name) {
        Some((_, run, _)) => run(rest),
        None => {
            let names: Vec<&str> = BENCHES.iter().map(|(n, _, _)| *n).collect();
            eprintln!(
                "usage: crossover (all | print-never-slower [digits...] | factor-bits | poly-support-units [words] | {}) [--exact]",
                names.join(" | ")
            );
            ExitCode::FAILURE
        }
    }
}

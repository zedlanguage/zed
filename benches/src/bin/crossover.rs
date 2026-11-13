//! The crossover benchmarks (see the crate's documentation), one per argument:
//!
//! - `print-whole [from to]`: `zed_kernel::num::PRINT_WHOLE`, the words from which
//!   `to_decimal` prints by halves (`to_decimal_split`) instead of by num-bigint's printing of
//!   the whole number. Both methods on random numbers of `from` to `to` words (256 to 32,768 by
//!   default), sizes `2^(1/4)` apart, then halving the interval of the change to 1%.
//! - `print-handoff [digits...]`: `zed_kernel::num::PRINT_HANDOFF`, the widest power of ten by
//!   which the split hands a part to num-bigint rather than split it further. The whole print of
//!   numbers of the given digits (160,000, 320,000 and 1,280,000 by default) with the part
//!   handed over below each power `10^(597 2^i)`; the setting is the one of least work.
//! - `print-never-slower [digits...]`: `to_decimal` against num-bigint's printing at each size
//!   of COMPLEXITY.md K81 (10,000 to 1,280,000 digits by default), which must never be the
//!   slower by more than [`NEVER_SLOWER`]; exits with status 1 where it is.
//!
//! Run each under 60 s (`timeout 60`), in the build the tests use, on each target platform on
//! real hardware: the thresholds measured are that platform's.

use std::process::ExitCode;

use num_bigint::BigUint;
use zed_benches::{Crossover, Method, Threshold, conditions, least, settings};
use zed_kernel::num::{
    PRINT_HANDOFF, PRINT_WHOLE, to_decimal, to_decimal_split, to_decimal_split_at,
};
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
const LEAF_DIGITS: u32 = 597;

/// A random number of `words` 64-bit words, the top bit set.
fn random(rng: &mut Rng, words: usize) -> BigUint {
    let mut digits: Vec<u32> = (0..2 * words).map(|_| rng.next_u64() as u32).collect();
    if let Some(top) = digits.last_mut() {
        *top |= 1 << 31;
    }
    BigUint::new(digits)
}

/// A random number of `digits` decimal digits, the first not zero.
fn random_digits(rng: &mut Rng, digits: u32) -> BigUint {
    let text: String = (0..digits)
        .map(|i| char::from(b'0' + rng.int(i64::from(i == 0), 9) as u8))
        .collect();
    text.parse().expect("digits")
}

/// The decimal digits of a number of `words` words, about.
fn digits_of_words(words: usize) -> f64 {
    words as f64 * 64.0 * std::f64::consts::LOG10_2
}

/// The words of `x`.
fn words(x: &BigUint) -> usize {
    x.bits().div_ceil(64) as usize
}

fn print_whole(args: &[String]) -> ExitCode {
    let arg = |k: usize, default: usize| {
        args.get(k)
            .map_or(default, |s| s.parse().expect("a size in words"))
    };
    let (from, to) = (arg(0, 256), arg(1, 32_768));
    let mut sizes = vec![];
    let mut k = 0;
    loop {
        let size = (from as f64 * 2f64.powf(k as f64 / 4.0)).round() as usize;
        if size > to {
            break;
        }
        sizes.push(size);
        k += 1;
    }
    let whole = |x: &BigUint| x.to_string();
    let split = |x: &BigUint| to_decimal_split(x);
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
            run: &whole,
        },
        above: Method {
            name: "split",
            run: &split,
        },
    };
    let mut meter = Meter::new();
    println!(
        "PRINT_WHOLE (now {PRINT_WHOLE} words, PRINT_HANDOFF {PRINT_HANDOFF}), {}",
        conditions()
    );
    let (points, threshold) = bench.find(&mut meter, &sizes, 0.01);
    println!("{}", bench.header(&meter));
    for p in &points {
        println!("{}", bench.row(p));
    }
    println!("crossover: {threshold:?} words");
    println!("{}", conditions());
    match threshold {
        Threshold::At(_) => ExitCode::SUCCESS,
        _ => ExitCode::FAILURE,
    }
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
    let mut handoffs = vec![(0, "below 10^597".to_string())];
    for i in 0..8 {
        let h = words(&ten.pow(LEAF_DIGITS << i));
        handoffs.push((h, format!("below 10^{}", LEAF_DIGITS << (i + 1))));
    }
    // One closure type for every handoff, so the closures share a `Vec` with no boxes.
    let runs: Vec<_> = handoffs
        .iter()
        .map(|&(h, _)| move |x: &BigUint| to_decimal_split_at(x, h))
        .collect();
    let methods: Vec<Method<'_, BigUint, String>> = runs
        .iter()
        .map(|run| Method { name: "split", run })
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
    let mut meter = Meter::new();
    println!(
        "PRINT_HANDOFF (now {PRINT_HANDOFF} words), {}",
        conditions()
    );
    let work = settings(&mut meter, &inputs, &methods);
    let unit = meter.unit();
    print!("| handoff (words) | leaves |");
    for d in &digits {
        print!(" {d} digits, {unit} | bytes |");
    }
    println!(" sum of work over the least at each size |");
    println!("|---|---|{}---|", "---|---|".repeat(digits.len()));
    let best: Vec<u64> = (0..inputs.len())
        .map(|i| work[i].iter().map(|w| w.units).min().expect("a handoff"))
        .collect();
    let mut chosen = (f64::INFINITY, 0);
    for (m, (h, leaves)) in handoffs.iter().enumerate() {
        print!("| {h} | {leaves} |");
        let mut sum = 0.0;
        for (i, row) in work.iter().enumerate() {
            print!(" {} | {} |", row[m].units, row[m].bytes);
            sum += row[m].units as f64 / best[i] as f64;
        }
        println!(" {sum:.4} |");
        if sum < chosen.0 {
            chosen = (sum, *h);
        }
    }
    println!(
        "least work: handoff {} words, {:.4} times the least at each size, summed",
        chosen.1, chosen.0
    );
    println!("{}", conditions());
    ExitCode::SUCCESS
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
    match held {
        true => ExitCode::SUCCESS,
        false => ExitCode::FAILURE,
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let rest = args.get(1..).unwrap_or(&[]);
    match args.first().map(String::as_str) {
        Some("print-whole") => print_whole(rest),
        Some("print-handoff") => print_handoff(rest),
        Some("print-never-slower") => print_never_slower(rest),
        _ => {
            eprintln!(
                "usage: crossover print-whole [from to] | print-handoff [digits...] | \
                 print-never-slower [digits...]"
            );
            ExitCode::FAILURE
        }
    }
}

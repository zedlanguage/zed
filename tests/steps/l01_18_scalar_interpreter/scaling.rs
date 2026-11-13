//! The scalar tier at the rule of low complexity (DESIGN.md Part G).

use num_bigint::{BigInt, BigUint};
use num_traits::One;
use zed_kernel::{Evaluator, Prim, Rat, Term, Value, World};

#[test]
fn a_chain_of_n_failures_merging_scales() {
    // Each `+` merged the failures so far with one more by copying them into a new set. The
    // chain is a kernel term, so that only the evaluator is timed; it nests n deep, past the
    // default thread stack.
    let chain = |n: usize| {
        (1..n).fold(Term::Lit(Value::atom("e0")), |t, i| {
            Term::Prim(Prim::Add, vec![t, Term::Lit(Value::atom(&format!("e{i}")))])
        })
    };
    let run = move |n: usize| {
        Evaluator::new(World::new())
            .run(&chain(n))
            .unwrap()
            .to_string()
    };
    zed_tests::scaling::check("n failures merged by a chain of `+`", 1000, |n| {
        run(n);
    });
    assert_eq!(run(3), "#errs({#e0, #e1, #e2})");
}

/// `n` decimal digits drawn from `seed`, the first not 0 and the last `last`.
fn digits(n: usize, seed: u64, last: char) -> String {
    let mut x = seed;
    let mut out: String = (0..n - 1)
        .map(|i| {
            // splitmix64
            x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = x;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            let d = ((z ^ (z >> 31)) % 10) as u8;
            char::from(b'0' + if i == 0 { 1 + d % 9 } else { d })
        })
        .collect();
    out.push(last);
    out
}

/// `rat(s)` of each text, timed apart from building the texts: `texts(n)` and `texts(8n)` are
/// built first.
fn check_reading(what: &str, n: usize, texts: impl Fn(usize) -> Vec<String>) {
    let built: std::collections::HashMap<usize, Vec<Term>> = [n, 8 * n]
        .into_iter()
        .map(|size| {
            let terms = texts(size)
                .into_iter()
                .map(|s| Term::Prim(Prim::CastRat, vec![Term::Lit(Value::str(&s))]))
                .collect();
            (size, terms)
        })
        .collect();
    for terms in built.values() {
        for t in terms {
            let v = zed_kernel::eval(t).unwrap();
            assert!(!v.to_string().starts_with('#'), "{what}: the text reads");
        }
    }
    zed_tests::scaling::check(what, n, |size| {
        for t in &built[&size] {
            zed_kernel::eval(t).unwrap();
        }
    });
}

#[test]
fn reading_a_rat_of_n_digits_scales() {
    // num-bigint reads decimal digits one word at a time into the whole number so far, O(n^2);
    // the kernel reads the text by halves (`num::read_decimal`), and checks lowest terms by one
    // gcd, linear when one part is a word.
    check_reading("rat(s) of an integer of n digits", 160_000, |n| {
        vec![digits(n, 1, '7'), format!("-{}r", digits(n, 2, '3'))]
    });
    check_reading(
        "rat(s) of n digits over a one-word denominator",
        160_000,
        |n| {
            vec![
                format!("{}r/2r", digits(n, 3, '1')),
                format!("-1/{}", digits(n, 4, '9')),
            ]
        },
    );
    check_reading("rat(s) of a decimal of n digits", 160_000, |n| {
        vec![
            format!("{}.{}", digits(n / 2, 5, '1'), digits(n / 2, 6, '3')),
            format!("-0.{}", digits(n, 7, '5')),
            format!("{}.25", digits(n, 8, '0')),
        ]
    });
}

/// `int(s)` reads by halves, O(n log^2 n) (COMPLEXITY.md C31), held to the limit of 10.5 every
/// scaling test meets. It passes, 11.8 times the work against the n log^2 n limit of that day,
/// 12.1 (2026-11-12, RADIX-depth), 12.0 (2026-11-13), and 11.9 with `fast::TOOM_COST` at its
/// measured 5.8 and `fast::MUL_LEAF` at 459 words (CROSSOVER-bench, 2026-11-13). It failed at
/// 15.5 (2026-11-09): the split is `log2(n / 1024)` levels deep, and the products
/// wider than `fast::MUL_LEAF` (then 512 words) are those of levels 4 and up, 4 levels at 160,000
/// digits and 7 at 1,280,000, so their number grows 1.75 times where the limit allows 1.17 for
/// each log; the ratio was 14.0 from 320,000 and 12.9 from 640,000
/// (limits 11.9 and 11.8), falling toward the limit as n grows.
#[test]
fn reading_an_int_of_n_digits_scales() {
    let built: std::collections::HashMap<usize, Term> = [160_000, 1_280_000]
        .into_iter()
        .map(|n| {
            let s = format!("-{}", digits(n, 9, '1'));
            (
                n,
                Term::Prim(Prim::CastInt, vec![Term::Lit(Value::str(&s))]),
            )
        })
        .collect();
    zed_tests::scaling::check("int(s) of n digits", 160_000, |n| {
        zed_kernel::eval(&built[&n]).unwrap();
    });
}

/// The check that a fraction of two wide parts is in lowest terms is one half gcd, O(n log^2 n)
/// in the digits (`num::fast::gcd`, COMPLEXITY.md K30 and K41), where num-bigint's Stein gcd
/// was O(n^2). At 80,000 digits, 4,153 words, both sizes are well above the gcd's leaf of 512
/// words (299 since CROSSOVER-bench), num-bigint's gcd, so both run the half gcd; the ratio of the work, 22.4 at 20,000
/// digits and 21.7 at 40,000, is 18.6 here as the leaf's share falls (2026-11-07), held to the
/// limit of 10.5 every scaling test meets (until 2026-11-13, the limit of work of order
/// n log^2 n, 12.3; COMPLEXITY.md C31). It passes, 12.3 times the work and 11.1 times the bytes
/// (2026-11-12, RADIX-depth), 12.3 and 11.6 (2026-11-13), in the band from 9 to 13; it failed
/// on the bytes, 15.2 times (2026-11-09), as the recursion's deeper levels were dear. With
/// `fast::TOOM_COST` at its measured 5.8 and `fast::DIV_COST` 9.1 the smaller run gains a little
/// more than the larger: 12.37 times the work and 12.06 the bytes (CROSSOVER-bench, 2026-11-13).
#[test]
fn reading_a_rat_of_two_wide_parts_scales() {
    check_reading("rat(s) of two parts of n digits each", 80_000, |n| {
        // A pair of random numbers is coprime with probability 6 / pi^2; seeds are tried in
        // order until one is.
        (0u64..)
            .map(|seed| (digits(n, 2 * seed + 10, '1'), digits(n, 2 * seed + 11, '3')))
            .map(|(a, b)| format!("{a}/{b}"))
            .find(|s| {
                !zed_kernel::eval(&Term::Prim(Prim::CastRat, vec![Term::Lit(Value::str(s))]))
                    .unwrap()
                    .to_string()
                    .starts_with('#')
            })
            .into_iter()
            .collect()
    });
}

/// The decimal digits of the product of `p^e` over `factors`, printed by the kernel.
fn product(factors: &[(u32, usize)]) -> String {
    let r = factors.iter().fold(Rat::int(BigInt::one()), |r, &(p, e)| {
        let power = Rat::int(BigInt::from(p)).pow(&BigUint::from(e));
        r.mul(&power.expect("memory is given"))
            .expect("memory is given")
    });
    Value::integer(r).to_string()
}

/// `0.` and the digits of `x` after zeros, `k` digits in all: the text of `x / 10^k`.
fn fraction(x: &str, k: usize) -> String {
    format!("0.{}{x}", "0".repeat(k - x.len()))
}

/// The powers of 2 and 5 a decimal of [`valuation_family`] holds in its digits.
#[derive(Clone, Copy)]
enum Powers {
    Five,
    Two,
    Both,
    None,
}

/// Texts of decimals of about n digits, by the powers of 2 and 5 their digits hold: the texts
/// `rat(s)` reads, and those of literals with an exponent, `<digits>e<exp>r` without the `r`,
/// which `Rat::decimal` reads. In `0.<5^n>`, which is `1r/2r^n`, the n factors of 5 of the
/// digits cancel against `10^n`; in `<5^m>.0` one of the m factors cancels; in `<5^m>e-n` the
/// m are moved into the kept power of 5.
fn valuation_family(powers: Powers, n: usize) -> Family {
    // `5^m` and `2^m` of about n digits.
    let (m5, m2) = (n * 10 / 7, n * 10 / 3);
    match powers {
        Powers::Five => (
            "a high power of 5",
            vec![
                fraction(&product(&[(5, n)]), n),
                format!("{}.0", product(&[(5, m5)])),
            ],
            vec![format!("{}e-{n}", product(&[(5, m5)]))],
        ),
        Powers::Two => (
            "a high power of 2",
            vec![
                fraction(&product(&[(2, n)]), n),
                format!("-{}.0", product(&[(2, m2)])),
            ],
            vec![format!("-{}e-{n}", product(&[(2, m2)]))],
        ),
        Powers::Both => {
            let both = product(&[(2, n), (5, n / 2), (7, 1)]);
            (
                "high powers of 2 and 5",
                vec![fraction(&both, both.len() + n / 4), format!("{both}.0")],
                vec![format!("{both}e{n}")],
            )
        }
        Powers::None => (
            "no high power",
            vec![format!(
                "{}.{}",
                digits(n / 2, 21, '1'),
                digits(n / 2, 22, '3')
            )],
            vec![format!("{}e-{}", digits(n, 23, '9'), digits(n, 24, '1'))],
        ),
    }
}

/// A family of [`valuation_family`]: its name, the texts `rat(s)` reads and the literals with an
/// exponent.
type Family = (&'static str, Vec<String>, Vec<String>);

/// A decimal is reduced by the powers of 2 and 5 of its digits, which can be as many as the
/// digits: each power `v` is bounded by testing `p^(2^i)`, built by squaring, while it divides,
/// read by its binary digits from the top and divided out at once, and the remaining power of
/// 10 is built by squaring, all with `num::fast`'s products and quotients, O(n log^2 v), at
/// most the order of the reading of the digits, O(M(n) log n). Each family runs through
/// `rat(s)` and through `Rat::decimal`, the reading of a literal, at 640,000 and 5,120,000
/// digits, one test a family so that libtest runs them at once. At 80,000 the divisions lie
/// where `num::fast::div_rem` takes long division, whose cost grows as the square of the width,
/// and the family with both powers grew 32.5 times to 640,000 digits; from 160,000, 13.8 to 20.8
/// times (2026-11-07). From 160,000 the family with both powers took 14.8 times the work in its
/// first runs, against the limit of 13, once `fast::DIV_COST` let num-bigint divide past
/// `DIV_LEAF` where it costs least (CROSSOVER-bench, 2026-11-13): the gain falls more at the
/// smaller size, from divisions by a power of 5 of 75 to 1189 words that num-bigint does at both
/// sizes (at 320,000 it took 14% off the smaller size's 526 M instructions and 4% off the
/// larger's 5,758 M). From 640,000 the families are 10.6 to 11.2 times the work and 8.8 to 9.6
/// times the bytes, and the step's tests take 17 s (2026-11-13, load 37).
fn check_valuation_family(powers: Powers) {
    let n = 640_000;
    let built = zed_tests::scaling::inputs(n, |m| valuation_family(powers, m));
    let what = built[&n].0;
    let cast = |s: &String| Term::Prim(Prim::CastRat, vec![Term::Lit(Value::str(s))]);
    let terms: std::collections::HashMap<usize, Vec<Term>> = built
        .iter()
        .map(|(&m, family)| (m, family.1.iter().map(cast).collect()))
        .collect();
    for t in &terms[&n] {
        let v = zed_kernel::eval(t).unwrap();
        assert!(!v.to_string().starts_with('#'), "{what}: the text reads");
    }
    zed_tests::scaling::check(
        &format!("rat(s) of a decimal of n digits with {what}"),
        n,
        |m| {
            for t in &terms[&m] {
                zed_kernel::eval(t).unwrap();
            }
        },
    );
    zed_tests::scaling::check(
        &format!("a rat literal with an exponent, of n digits with {what}"),
        n,
        |m| {
            for s in &built[&m].2 {
                Rat::decimal(s).unwrap().expect("a decimal literal");
            }
        },
    );
}

#[test]
fn reading_a_decimal_with_a_high_power_of_5_scales() {
    check_valuation_family(Powers::Five);
}

#[test]
fn reading_a_decimal_with_a_high_power_of_2_scales() {
    check_valuation_family(Powers::Two);
}

#[test]
fn reading_a_decimal_with_high_powers_of_2_and_5_scales() {
    check_valuation_family(Powers::Both);
}

#[test]
fn reading_a_decimal_with_no_high_power_scales() {
    check_valuation_family(Powers::None);
}

/// A chain of `n` bindings of `f32` arithmetic, each the one before through `*`, `+`, `/`, a
/// power with an `int` exponent, `abs`, `min` and casts to `f64` and back (FLOAT-f32).
fn f32_chain(n: usize) -> String {
    let mut src = String::from("whole(positional v: int) = v;\na0 = 0.5f32;\n");
    for i in 1..n {
        let p = i - 1;
        let step = match i % 4 {
            0 => format!("a{p} * 1.0001f32 + 0.25f32"),
            1 => format!("min(abs(a{p}) / 1.5f32, 1.0e30f32)"),
            2 => format!("a{p} ^ whole(2) - 0.125f32"),
            _ => format!("f32(f64(a{p}))"),
        };
        src.push_str(&format!("a{i} = {step};\n"));
    }
    src.push_str(&format!("x = String(a{});\n", n - 1));
    src
}

#[test]
fn checking_and_running_a_chain_of_f32_arithmetic_scales() {
    use zed_tests::step_helpers::l01_16_elaboration::value;
    let srcs: std::collections::HashMap<usize, String> =
        [100, 800].into_iter().map(|n| (n, f32_chain(n))).collect();
    assert!(value(&srcs[&100], "x").starts_with('"'));
    zed_tests::scaling::check_order("a chain of n f32 bindings", 100, 1, |n| {
        value(&srcs[&n], "x");
    });
}

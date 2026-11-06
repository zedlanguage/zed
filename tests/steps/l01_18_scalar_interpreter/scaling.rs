//! The scalar tier at the rule of low complexity (DESIGN.md Part G).

use zed_kernel::{Evaluator, Prim, Term, Value, World};

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
/// words, num-bigint's gcd, so both run the half gcd; the ratio of the work, 22.4 at 20,000
/// digits and 21.7 at 40,000, is 18.6 here as the leaf's share falls.
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

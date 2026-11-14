//! The type of a `rat` literal (COMPLEXITY.md K30, item T6-ratlit). A literal such as
//! `1e400000r` is held as its digits times a power of 2 and 5, and its type hashes, compares
//! and prints it in that form, so checking it costs the length of its text and not its
//! 400001 digits. A type prints a decimal rat as the one literal `meKr`, with `m` an integer
//! not divisible by 10, the form the type syntax writes.

use std::collections::HashMap;

use num_bigint::BigInt;
use zed_kernel::types::Type;
use zed_kernel::{Rat, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling::{check, check_order};
use zedc::zir::text::parse_type;

use zed_tests::step_helpers::l01_26_type_resolution::{info, sig};

fn dec(text: &str) -> Value {
    Value::rat(
        Rat::decimal(text)
            .expect("a test literal is small")
            .expect("a test literal is decimal"),
    )
}

fn lit(v: &Value) -> Type {
    Type::lit(v).expect("a scalar literal")
}

/// The printed type of each top-level name of `text`, sorted by name.
fn tops(text: &str) -> Vec<String> {
    let (info, _) = info(text);
    assert!(info.errors.is_empty(), "{text}: {:?}", info.errors);
    let mut out: Vec<String> = info.tops.iter().map(|(k, t)| format!("{k}: {t}")).collect();
    out.sort();
    out
}

#[test]
fn equal_literals_written_differently_have_one_type() {
    let forms = ["1000", "1e3", "1000.0", "0.1e4", "10e2", "10000e-1"];
    let types: Vec<Type> = forms.iter().map(|f| lit(&dec(f))).collect();
    // `1000r` read without an exponent is a plain rational; `1e3r` keeps `2^3 * 5^3`.
    let plain = lit(&Value::rat(Rat::int(BigInt::from(1000))));
    for t in &types {
        assert_eq!(*t, plain);
        assert_eq!(t.to_string(), "1e3r");
    }
    let all = Type::union_all(types);
    assert_eq!(all, plain);
    assert_eq!(all.to_string(), "1e3r");
    // The checker gives each binding the same literal type.
    assert_eq!(
        tops("a = 1000r;\nb = 1e3r;\nc = 0.1e4r;\nd = 10000e-1r;\n"),
        ["a: 1e3r", "b: 1e3r", "c: 1e3r", "d: 1e3r"]
    );
    // A big integer kept as a power of 2 and the same integer built have one type. The kept
    // one prints its power, which is shorter than its digits, and the built one its digits,
    // since finding the powers of digits would factor them (LIT-power-values; the follow-up
    // LIT-power-equal-print).
    let kept = Value::integer(Rat::int(BigInt::from(2)).pow(&100u32.into()).unwrap());
    let built = Value::int(BigInt::from(2).pow(100));
    assert_eq!(lit(&kept), lit(&built));
    assert_eq!(lit(&kept).to_string(), "2^100");
    assert_eq!(lit(&built).to_string(), "1267650600228229401496703205376");
}

#[test]
fn a_literal_type_prints_in_canonical_form() {
    assert_eq!(
        tops(
            "x = 1e400000r;\nfrac = 1.5e-3r;\nhalf = 0.5r;\nthird = 1r / 3r;\n\
             small = 1e-400000r;\nzero = 0e400000r;\nseven = 7r;\nwide = 25e3r;\n"
        ),
        [
            "frac: 15e-4r",
            "half: 5e-1r",
            "seven: 7r",
            "small: 1e-400000r",
            "third: rat",
            "wide: 25e3r",
            "x: 1e400000r",
            "zero: 0r",
        ]
    );
    assert_eq!(lit(&dec("-2.5e10")).to_string(), "-25e9r");
    assert_eq!(lit(&dec("-0.04")).to_string(), "-4e-2r");
    assert_eq!(lit(&dec("12.345e-400000")).to_string(), "12345e-400003r");
    // The digits are kept as written, less trailing zeros.
    assert_eq!(lit(&dec("8e-400000")).to_string(), "8e-400000r");
    assert_eq!(lit(&dec("1024e-10")).to_string(), "1024e-10r");
    assert_eq!(lit(&dec("-0e-400000")).to_string(), "0r");
    // The printed type reads back as the same type.
    for f in [
        "1e400000",
        "8e-400000",
        "1024e-10",
        "1e-400000",
        "-2.5e10",
        "1.5e-3",
        "0e400000",
        "0.5",
        "7",
    ] {
        let t = lit(&dec(f));
        assert_eq!(parse_type(&t.to_string()), Ok(t.clone()), "{f}");
    }
}

#[test]
fn literal_types_order_by_value_across_rat_and_int() {
    let rats = [
        "1e400000",
        "1e-400000",
        "-1e400000",
        "0.5",
        "1e400001",
        "999e399997",
    ];
    let t = Type::union_all(rats.iter().map(|f| lit(&dec(f))));
    assert_eq!(
        t.to_string(),
        "(| -1e400000r 1e-400000r 5e-1r 999e399997r 1e400000r 1e400001r)"
    );
    assert!(lit(&dec("1e400000")).subtype(&Type::rat()));
    assert!(!lit(&dec("1e400000")).subtype(&Type::int()));
    assert!(lit(&dec("1e400000")).subtype(&t));
    assert!(!lit(&dec("2e400000")).subtype(&t));
    // In the natural order a number of any kind sits by its value, `int` before `rat`.
    let big = Value::integer(Rat::decimal("1e400000").unwrap().unwrap());
    let mut vs = vec![
        dec("1e400000"),
        big.clone(),
        Value::Int(i64::MAX),
        dec("1e-400000"),
        Value::Int(0),
        dec("1e400001"),
    ];
    vs.sort();
    assert_eq!(
        vs,
        [
            Value::Int(0),
            dec("1e-400000"),
            Value::Int(i64::MAX),
            big.clone(),
            dec("1e400000"),
            dec("1e400001"),
        ]
    );
    // An int literal and a rat literal of one value are different types.
    assert!(lit(&big).subtype(&Type::int()));
    assert!((lit(&big) & lit(&dec("1e400000"))).is_empty());
}

/// Random exact numbers: their kept form and the plain rational built from their digits print
/// alike and have one type.
#[test]
fn kept_and_built_forms_of_random_numbers_print_alike() {
    let mut rng = Rng::new(0x7a7);
    for _ in 0..400 {
        let mantissa = rng.int(-99_999, 99_999);
        let point = rng.below(4);
        let exp = rng.int(-60, 60);
        let mut text = mantissa.abs().to_string();
        if point > 0 && point < text.len() {
            text.insert(text.len() - point, '.');
        }
        let sign = if mantissa < 0 { "-" } else { "" };
        let kept = Rat::decimal(&format!("{sign}{text}e{exp}"))
            .unwrap()
            .unwrap();
        let n: BigInt = kept.numer_text().unwrap().parse().unwrap();
        let d: BigInt = kept.denom_text().unwrap().parse().unwrap();
        let built = Rat::new(n, d).unwrap();
        assert_eq!(kept, built);
        let (a, b) = (lit(&Value::rat(kept)), lit(&Value::rat(built)));
        assert_eq!(a, b, "{sign}{text}e{exp}");
        assert_eq!(a.to_string(), b.to_string());
        assert_eq!(parse_type(&a.to_string()), Ok(a));
    }
}

#[test]
fn a_computed_power_prints_its_digits() {
    // The checker gives no computed constant a literal type, but a kept power that is not a
    // power of 10 can reach one through the kernel; its type prints the digits it must.
    let two = Rat::int(BigInt::from(2));
    let p = two.pow(&40u32.into()).unwrap();
    assert_eq!(lit(&Value::rat(p.clone())).to_string(), "1099511627776r");
    let q = Rat::int(BigInt::from(1)).div(&p).unwrap().unwrap();
    assert_eq!(
        lit(&Value::rat(q)).to_string(),
        "9094947017729282379150390625e-40r"
    );
    let three = Rat::int(BigInt::from(3)).pow(&5u32.into()).unwrap();
    let r = three.mul(&Rat::decimal("1e7").unwrap().unwrap()).unwrap();
    assert_eq!(lit(&Value::rat(r)).to_string(), "243e7r");
    // A quotient that is not a decimal has no literal; its type prints the quotient.
    let third = Rat::int(BigInt::from(-1))
        .div(&Rat::int(BigInt::from(3)))
        .unwrap()
        .unwrap();
    assert_eq!(lit(&Value::rat(third)).to_string(), "-1r/3r");
}

/// `x = 1eNr` with literals near it, checked and printed. Built before timing, by size.
fn programs(sizes: &[String]) -> HashMap<usize, String> {
    sizes
        .iter()
        .enumerate()
        .map(|(i, n)| {
            let text = format!(
                "x = 1e{n}r;\ny = 10e{n}r;\nz = 1.0e{n}r;\nlt = x < y;\neq = x == z;\n\
                 small = 1e-{n}r;\n"
            );
            (i, text)
        })
        .collect()
}

fn check_program(text: &str, n: &str) {
    let (info, _) = info(text);
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(info.tops["x"].to_string(), format!("1e{n}r"));
    assert_eq!(info.tops["small"].to_string(), format!("1e-{n}r"));
    let x = lit(&dec(&format!("1e{n}")));
    let z = lit(&dec(&format!("1.0e{n}")));
    let y = lit(&dec(&format!("10e{n}")));
    assert_eq!(z, x);
    assert!(z.subtype(&(x.clone() | y.clone())));
    assert_eq!((x | y).to_string().len(), 2 * n.len() + 11);
}

/// Small instance of `bench::a_rat_literal_costs_its_exponent_and_not_its_digits` and
/// `bench::a_rat_literal_costs_the_length_of_its_text` (TEST-bench-move-l0123, author P169):
/// literals of the exponents 400000 and 10^29, which fits no machine word, checked, compared
/// and printed.
#[test]
fn literals_of_a_large_exponent_are_checked_compared_and_printed() {
    let ns = ["400000".to_string(), format!("1{}", "0".repeat(29))];
    let texts = programs(&ns);
    for (i, n) in ns.iter().enumerate() {
        check_program(&texts[&i], n);
    }
}

/// A literal type hashes a `rat` by its residues modulo `2^61 - 1`, but compares, orders and
/// tests membership on the exact value: two literals of equal residues stay two types.
#[test]
fn literals_of_equal_residues_are_different_types() {
    let two_61 = "2305843009213693952";
    let two = || Rat::int(BigInt::from(2));
    let pairs = [
        (dec("1"), dec(two_61)),
        // `2^61` kept as a power of 2 and not built.
        (dec("1"), Value::rat(two().pow(&61u32.into()).unwrap())),
        // `1/2` and `1/2^62`: the denominators agree modulo `2^61 - 1`.
        (
            dec("0.5"),
            Value::rat(
                Rat::int(BigInt::from(1))
                    .div(&two().pow(&62u32.into()).unwrap())
                    .unwrap()
                    .unwrap(),
            ),
        ),
    ];
    for (a, b) in &pairs {
        let (Value::Rat(x), Value::Rat(y)) = (a, b) else {
            unreachable!("rat literals")
        };
        assert_eq!(x.residues(), y.residues(), "{a} and {b} share residues");
        let (ta, tb) = (lit(a), lit(b));
        assert_ne!(ta, tb);
        assert!(!ta.subtype(&tb) && !tb.subtype(&ta));
        assert!((ta.clone() & tb.clone()).is_empty());
        let both = ta.clone() | tb.clone();
        assert!(ta.subtype(&both) && tb.subtype(&both));
        assert_ne!(both, ta);
        assert_eq!(both, Type::union_all([tb.clone(), ta.clone()]));
    }
    // `1 < 2^61` always holds, so no value reaches the second branch and it adds nothing.
    assert_eq!(
        tops(&format!(
            "a = 1r;\nb = {two_61}r;\nc = if a < b {{ a }} else {{ b }};\n"
        )),
        [
            "a: 1r".to_string(),
            format!("b: {two_61}r"),
            "c: 1r".to_string()
        ]
    );
    // A test that may go either way keeps both, as two types.
    assert_eq!(
        sig(
            &format!(
                "a = 1r;\nb = {two_61}r;\nc(positional p: bool) = if p {{ a }} else {{ b }};\n"
            ),
            "c"
        ),
        format!("(bool) -> 1r | {two_61}r")
    );
}

mod bench;

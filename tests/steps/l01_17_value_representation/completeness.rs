//! Cases of DESIGN.md step L1.17 that the other files of this step leave out, one test per
//! construct. COMPLETENESS.md beside this file lists every case and the test that covers it.

use std::cmp::Ordering;
use std::hash::{DefaultHasher, Hash, Hasher};
use zed_kernel::{Text, Value};
use zed_tests::step_helpers::l01_16_elaboration::{elab, value, with_prelude};

/// Functions that pass their argument on, so the checker does not read the operand.
const PASS: &str = "whole(positional v: int) = v;\nreal(positional v: f64) = v;\n\
                    text(positional v: String) = v;\n";

/// The value of `x = <expr>;` after [`PASS`], printed.
fn x(expr: &str) -> String {
    value(&format!("{PASS}x = {expr};\n"), "x")
}

/// The values of `exprs`, each bound after [`PASS`] and evaluated.
fn values(exprs: &[&str]) -> Vec<Value> {
    exprs
        .iter()
        .map(|e| {
            let u = elab(&format!("{PASS}x = {e};\n")).unwrap();
            zed_kernel::eval(&with_prelude(u.get("x").unwrap())).unwrap()
        })
        .collect()
}

/// `2^2^100` is a value: past a word an integer keeps its powers of primes, so its order,
/// equality and remainders come without its digits.
#[test]
fn two_to_two_to_the_hundred_is_a_value() {
    assert_eq!(x("2^2^100 > 0"), "true");
    assert_eq!(x("2^2^100 == 2^(2^100)"), "true");
    assert_eq!(x("2^2^100 < 2^(2^100 + 1)"), "true");
    assert_eq!(x("2^2^100 mod 3"), "1");
    assert_eq!(x("2^2^100 mod 2"), "0");
    assert_eq!(x("-(2^2^100) < 0"), "true");
}

/// `x^n` on a `rat` takes any `int` `n`: exact, a negative `n` inverting, `#divByZero` only for
/// `0r` to a negative power.
#[test]
fn a_rat_power_in_a_program_takes_either_sign() {
    let cases = [
        ("(2r/3r) ^ whole(-2)", "9r/4r"),
        ("(-2r/3r) ^ whole(3)", "-8r/27r"),
        ("(-2r/3r) ^ whole(-3)", "-27r/8r"),
        ("(2r/3r) ^ whole(0)", "1r"),
        ("rat(whole(0)) ^ whole(0)", "1r"),
        ("rat(whole(0)) ^ whole(3)", "0r"),
        ("rat(whole(0)) ^ whole(-1)", "#divByZero"),
        ("rat(whole(-3)) ^ whole(-1)", "-1r/3r"),
        ("2r ^ whole(-64)", "1r/18446744073709551616r"),
    ];
    for (e, want) in cases {
        assert_eq!(x(e), want, "{e}");
    }
}

/// `0r`, `1r` and `-1r` to any power stay small, read from the sign and parity of `n`.
#[test]
fn powers_of_zero_one_and_minus_one_as_rats_stay_small() {
    let cases = [
        ("1r ^ whole(-(2^100))", "1r"),
        ("(-1r) ^ whole(2^100)", "1r"),
        ("(-1r) ^ whole(2^100 + 1)", "-1r"),
        ("(-1r) ^ whole(-(2^100) - 1)", "-1r"),
        ("0r ^ whole(2^100)", "0r"),
        ("rat(whole(0)) ^ whole(-(2^100))", "#divByZero"),
    ];
    for (e, want) in cases {
        assert_eq!(x(e), want, "{e}");
    }
}

/// A decimal literal base meets an `int` exponent at `rat`, its one carrier there.
#[test]
fn a_decimal_literal_to_an_int_power_is_a_rat() {
    assert_eq!(x("0.5 ^ whole(3)"), "1r/8r");
    assert_eq!(x("1.5 ^ whole(0)"), "1r");
    assert_eq!(x("2.5 ^ whole(-1)"), "2r/5r");
}

/// A `rat` is kept reduced with a positive denominator, whatever the signs of the parts.
#[test]
fn a_rat_is_reduced_with_a_positive_denominator() {
    let cases = [
        ("rat(whole(6)) / rat(whole(-4))", "-3r/2r"),
        ("rat(whole(-6)) / rat(whole(-4))", "3r/2r"),
        ("rat(whole(0)) / rat(whole(-5))", "0r"),
        ("-(0r)", "0r"),
        ("rat(whole(2^64)) / rat(whole(2^62))", "4r"),
        ("1r/3r - 1r/3r", "0r"),
    ];
    for (e, want) in cases {
        assert_eq!(x(e), want, "{e}");
    }
}

/// `<`, `<=`, `>`, `>=` compare two numbers of one kind or two values of one non-number kind;
/// two tuples compare component by component.
#[test]
fn comparisons_within_one_kind() {
    let cases = [
        ("\"a\" < \"b\"", "true"),
        ("\"b\" <= \"ab\"", "false"),
        ("false < true", "true"),
        ("true >= true", "true"),
        ("(1, \"a\") < (1, \"b\")", "true"),
        ("(2, \"a\") < (1, \"b\")", "false"),
        ("(1, 2) <= (1, 2)", "true"),
        ("(1, (2, 3)) > (1, (2, 2))", "true"),
        ("1r/3r < 1r/2r", "true"),
        ("-(2^70) < -(2^69)", "true"),
        ("(1, real(0.0f64 / 0.0)) < (1, 1.0f64)", "false"),
    ];
    for (e, want) in cases {
        assert_eq!(x(e), want, "{e}");
    }
}

/// Comparing values of two kinds, numbers of two kinds included, is a type error, as is
/// `r + n` with `r` a `rat` and `n` an `int`.
#[test]
fn comparisons_and_sums_across_kinds_are_type_errors() {
    for e in [
        "whole(1) < 1r",
        "1r <= real(1.0f64)",
        "f32(1) > real(1.0f64)",
        "\"a\" < whole(1)",
        "true < whole(1)",
        "(whole(1), 2) < (1, 2r)",
        "(1, \"a\") < (1, 2)",
    ] {
        let src = format!("{PASS}x = {e};\n");
        assert!(elab(&src).is_err(), "{src} is accepted");
    }
    let src = "f(positional r: rat, positional n: int) = r + n;\n";
    assert!(elab(src).is_err(), "{src} is accepted");
}

/// The natural order ranks equal values `int`, then `rat`, then `f32`, then `f64`, and a float
/// by the dyadic rational it is.
#[test]
fn equal_numbers_order_by_kind_and_floats_by_their_exact_value() {
    let mut vs = values(&["1.0f64", "f32(1)", "1r", "1"]);
    vs.sort();
    assert_eq!(vs, values(&["1", "1r", "f32(1)", "1.0f64"]));
    // f64(1/3) lies below 1/3 and f32(1/3) above it.
    let mut vs = values(&[
        "f32(text(\"0.3333333333\"))",
        "1r/3r",
        "f64(text(\"0.3333333333333333\"))",
    ]);
    vs.sort();
    let shown: Vec<String> = vs.iter().map(|v| v.to_string()).collect();
    assert_eq!(shown, ["0.3333333333333333", "1r/3r", "0.33333334f32"]);
    let mut vs = values(&[
        "f64(text(\"inf\"))",
        "f32(text(\"inf\"))",
        "f32(text(\"-inf\"))",
        "f64(text(\"-inf\"))",
        "2^2^100",
    ]);
    vs.sort();
    assert_eq!(
        vs,
        values(&[
            "f32(text(\"-inf\"))",
            "f64(text(\"-inf\"))",
            "2^2^100",
            "f32(text(\"inf\"))",
            "f64(text(\"inf\"))",
        ])
    );
}

/// `==` and `!=` compare atoms as data, IEEE 754 at an `f32` inside them as at an `f64`.
#[test]
fn equality_of_atoms_and_f32_inside_values() {
    let cases = [
        ("#a == #b", "false"),
        ("#a != #a", "false"),
        ("#a(1) == #a(1)", "true"),
        ("#a(1) == #a(2)", "false"),
        ("#a(1) == #b(1)", "false"),
        ("#a(x: 1) == #a(x: 1)", "true"),
        (
            "(f32(text(\"nan\")), 1) == (f32(text(\"nan\")), 1)",
            "false",
        ),
        ("(f32(text(\"-0\")), 1) == (f32(text(\"0\")), 1)", "true"),
        ("#at(f32(text(\"-0\"))) != #at(f32(text(\"0\")))", "false"),
    ];
    for (e, want) in cases {
        assert_eq!(x(e), want, "{e}");
    }
}

/// An atom's payload may hold a function, by position or by name; building one is no error.
/// The same for a tuple waits on row FAIL-values-function-in-tuple.
#[test]
fn building_an_atom_that_holds_a_function_is_no_error() {
    let f = "f(positional v: int) = v;\n";
    for e in ["#box(f)", "#pair(fst: f, snd: 1)", "#box(#inner(f))"] {
        let src = format!("{f}x = {e};\n");
        assert!(elab(&src).is_ok(), "{src}: {:?}", elab(&src).err());
    }
}

/// The join of `parts` as a balanced tree of joins.
fn balanced(parts: &[Text]) -> Text {
    match parts {
        [] => Text::from(""),
        [p] => p.clone(),
        _ => {
            let (a, b) = parts.split_at(parts.len() / 2);
            Text::join(&balanced(a), &balanced(b)).expect("a length that fits")
        }
    }
}

fn hash_of(t: &Text) -> u64 {
    let mut h = DefaultHasher::new();
    t.hash(&mut h);
    h.finish()
}

/// A string joined from many blocks, as a left fold, a right fold or a balanced tree of joins,
/// is equal to, ordered with and hashed as the same text in one block: the shape of its joins
/// never enters its identity (DESIGN.md sec:order, ropes are a representation).
#[test]
fn a_joined_string_is_compared_ordered_and_hashed_by_its_text_alone() {
    // 40 parts of 300 bytes each, longer than a block, so each join keeps them apart.
    let parts: Vec<String> = (0..40).map(|i| format!("{i:03}é").repeat(60)).collect();
    let texts: Vec<Text> = parts.iter().map(|p| Text::from(p.as_str())).collect();
    let join = |a: &Text, b: &Text| Text::join(a, b).expect("a length that fits");
    let left = texts
        .iter()
        .skip(1)
        .fold(texts[0].clone(), |a, b| join(&a, b));
    let right = texts
        .iter()
        .rev()
        .skip(1)
        .fold(texts[39].clone(), |b, a| join(a, &b));
    let tree = balanced(&texts);
    let flat = Text::from(parts.concat().as_str());
    for t in [&left, &right, &tree] {
        assert_eq!(t, &flat);
        assert_eq!(t.cmp(&flat), Ordering::Equal);
        assert_eq!(hash_of(t), hash_of(&flat));
        assert_eq!(t.char_count(), flat.char_count());
    }
    // One digit changed in the last part, then in the first, orders as the flat texts do.
    for at in [parts.concat().len() - 3, 0] {
        let mut other = parts.concat().into_bytes();
        other[at] = b'~';
        let other = String::from_utf8(other).unwrap();
        let joined_other = balanced(&[Text::from(&other[..at]), Text::from(&other[at..])]);
        assert_ne!(tree, joined_other);
        assert_eq!(
            tree.cmp(&joined_other),
            parts.concat().as_str().cmp(other.as_str())
        );
        assert_eq!(left.cmp(&joined_other), right.cmp(&joined_other));
    }
    // A text orders before every longer text it begins, in blocks or not.
    let longer = join(&tree, &Text::from("~"));
    assert_eq!(left.cmp(&longer), Ordering::Less);
    assert_eq!(longer.cmp(&right), Ordering::Greater);
    assert_ne!(left, longer);
    // A short text joined before a long one whose first block has room joins that block.
    let short_first = join(&Text::from("ab"), &tree);
    let joined = join(&Text::from("é"), &short_first);
    let mut want = String::from("éab");
    want.push_str(&parts.concat());
    assert_eq!(joined, Text::from(want.as_str()));
    assert_eq!(joined.char_count(), want.chars().count());
    assert_eq!(hash_of(&joined), hash_of(&Text::from(want.as_str())));
}

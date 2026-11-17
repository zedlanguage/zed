//! The rounding words `round`, `round(x, ties: #away)`, `floor`, `ceil`, `trunc` and
//! `awayFromZero` (step L1.18, plan row CAST-round-whole; DESIGN.md sec:facets, "Rounding to a
//! whole number", whose table the first test holds at every value). `round` breaks a tie to
//! the even neighbor, the IEEE 754 rule, and `ties: #away` away from zero; `ties:` takes only
//! the two atoms written in place. Each word gives an `int`; at a float the NaN gives `#NaN`
//! and an infinity `#overflow`. Every value here is written out, not computed by the code
//! under test.

use num_bigint::BigInt;
use zed_kernel::Rat;
use zed_kernel::num::Rounding;

use zed_tests::step_helpers::l01_16_elaboration::term;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};

use super::x;

/// The six calls of the DESIGN table's columns, in its order, on the operand `a`.
fn columns(a: &str) -> [String; 6] {
    [
        format!("round({a})"),
        format!("round({a}, ties: #away)"),
        format!("floor({a})"),
        format!("ceil({a})"),
        format!("trunc({a})"),
        format!("awayFromZero({a})"),
    ]
}

/// The table of DESIGN.md sec:facets, "Rounding to a whole number": `x`, then `round(x)`,
/// `round(x, ties: #away)`, `floor(x)`, `ceil(x)`, `trunc(x)` and `awayFromZero(x)`.
const TABLE: [(&str, [&str; 6]); 5] = [
    ("0.5", ["0", "1", "0", "1", "0", "1"]),
    ("1.5", ["2", "2", "1", "2", "1", "2"]),
    ("2.5", ["2", "3", "2", "3", "2", "3"]),
    ("-2.5", ["-2", "-3", "-3", "-2", "-2", "-3"]),
    ("2.4", ["2", "2", "2", "3", "2", "3"]),
];

#[test]
fn every_value_of_the_design_table() {
    for (a, want) in TABLE {
        // A bare decimal takes `f64`; with a suffix it is a `rat` or an `f32`. Each value of
        // the table is exact in all three, so all three give the table's whole numbers.
        for operand in [a.to_string(), format!("{a}r"), format!("{a}f32")] {
            for (call, w) in columns(&operand).iter().zip(want) {
                assert_eq!(x(call), w, "{call}");
            }
        }
    }
}

#[test]
fn ties_away_from_zero_is_written_with_ties_away_and_ties_even_is_the_default() {
    assert_eq!(x("round(2.5)"), "2");
    assert_eq!(x("round(-2.5)"), "-2");
    assert_eq!(x("round(0.5)"), "0");
    assert_eq!(x("round(-0.5)"), "0");
    assert_eq!(x("round(3.5)"), "4");
    assert_eq!(x("round(2.5, ties: #even)"), "2");
    assert_eq!(x("round(2.5, ties: #away)"), "3");
    assert_eq!(x("round(-2.5, ties: #away)"), "-3");
    assert_eq!(x("round(-0.5, ties: #away)"), "-1");
    assert_eq!(x("awayFromZero(-2.1)"), "-3");
    assert_eq!(x("awayFromZero(2.1)"), "3");
}

/// The largest `f64` below one half is not a tie under either rule, so both give 0; the naive
/// `trunc(x + copySign(0.5, x))` gives 1 there, since the sum rounds up to 1.0 (DESIGN.md
/// sec:facets, the list of new machine functions).
#[test]
fn the_largest_double_below_one_half_rounds_to_zero() {
    assert_eq!(x("round(0.49999999999999994)"), "0");
    assert_eq!(x("round(0.49999999999999994, ties: #away)"), "0");
    assert_eq!(x("round(-0.49999999999999994, ties: #away)"), "0");
    assert_eq!(x("round(0.49999999999999994r)"), "0");
    // The sum the naive way computes is 1.0 at `f64`.
    assert_eq!(x("0.49999999999999994 + 0.5"), "1.0");
}

/// DESIGN.md step L1.18: on `7r/2r`, `round` 4 and `round(…, ties: #away)` 4, `floor` 3,
/// `ceil` 4, `trunc` 3 and `awayFromZero` 4; and the same mirrored below zero.
#[test]
fn a_rat_rounds_by_each_rule() {
    for (call, want) in columns("7r/2r").iter().zip(["4", "4", "3", "4", "3", "4"]) {
        assert_eq!(x(call), want, "{call}");
    }
    for (call, want) in columns("-7r/2r")
        .iter()
        .zip(["-4", "-4", "-4", "-3", "-3", "-4"])
    {
        assert_eq!(x(call), want, "{call}");
    }
    // A third is no tie, and 2/3 rounds up under both tie rules.
    for (call, want) in columns("2r/3r").iter().zip(["1", "1", "0", "1", "0", "1"]) {
        assert_eq!(x(call), want, "{call}");
    }
}

#[test]
fn a_whole_number_is_its_own_rounding() {
    for call in columns("7") {
        assert_eq!(x(&call), "7", "{call}");
    }
    for call in columns("-3.0") {
        assert_eq!(x(&call), "-3", "{call}");
    }
    for call in columns("12r") {
        assert_eq!(x(&call), "12", "{call}");
    }
    // `-0.0` is the whole number 0, which has no sign.
    for call in columns("-0.0") {
        assert_eq!(x(&call), "0", "{call}");
    }
}

#[test]
fn the_nan_and_the_infinities_have_no_whole_number() {
    for (op, want) in [("0.0", "#NaN"), ("1.0", "#overflow"), ("-1.0", "#overflow")] {
        for call in columns(&format!("({op}f64 / 0.0)")) {
            assert_eq!(x(&call), want, "{call}");
        }
    }
}

/// A wide `rat` and a wide float round exactly: 2^70 + 1/2 is a tie between 2^70, even, and
/// 2^70 + 1, and 1e300 is a whole number of 301 digits.
#[test]
fn wide_numbers_round_exactly() {
    let p = "1180591620717411303424";
    let q = "1180591620717411303425";
    assert_eq!(x(&format!("round({p}r + 1r/2r)")), p);
    assert_eq!(x(&format!("round({p}r + 1r/2r, ties: #away)")), q);
    assert_eq!(x(&format!("floor(-{p}r - 1r/3r)")), format!("-{q}"));
    let e300 = x("round(1e300)");
    assert_eq!(e300, x("int(1e300)"));
    assert_eq!(e300.len(), 301);
}

/// The kernel's rule at each operand by exact integer arithmetic: for `N/D` with `D` in
/// `2..=9` and `N` in `-40..=40`, each word's result agrees with the definition read from the
/// quotient and remainder.
#[test]
fn the_kernel_agrees_with_the_definitions_on_small_rationals() {
    for d in 2i64..=9 {
        for n in -40i64..=40 {
            let r = Rat::new(BigInt::from(n), BigInt::from(d)).expect("a nonzero denominator");
            let q = n.div_euclid(d);
            let rem2 = 2 * n.rem_euclid(d);
            let exact = n.rem_euclid(d) == 0;
            let neg = n < 0;
            let up = |cond: bool| if exact || !cond { q } else { q + 1 };
            let nearest = |tie: bool| match rem2.cmp(&d) {
                std::cmp::Ordering::Less => up(false),
                std::cmp::Ordering::Greater => up(true),
                std::cmp::Ordering::Equal => up(tie),
            };
            let want = [
                (Rounding::TiesEven, nearest(q % 2 != 0)),
                (Rounding::TiesAway, nearest(!neg)),
                (Rounding::Floor, q),
                (Rounding::Ceil, up(true)),
                (Rounding::Trunc, up(neg)),
                (Rounding::AwayFromZero, up(!neg)),
            ];
            for (rule, w) in want {
                let got = r.round_whole(rule).expect("a small rational");
                assert_eq!(got, Rat::int(BigInt::from(w)), "{n}/{d} by {rule:?}");
            }
        }
    }
}

#[test]
fn each_word_gives_an_int_and_a_float_may_give_nan_or_overflow() {
    assert_eq!(
        sig("f(positional x: f64) = round(x);", "f"),
        "f64 -> int | #NaN | #overflow"
    );
    assert_eq!(
        sig("f(positional x: f32) = trunc(x);", "f"),
        "f32 -> int | #NaN | #overflow"
    );
    assert_eq!(
        sig("f(positional x: f64) = round(x, ties: #away);", "f"),
        "f64 -> int | #NaN | #overflow"
    );
    assert_eq!(sig("f(positional x: rat) = floor(x);", "f"), "rat -> int");
    assert_eq!(sig("f(positional x: int) = ceil(x);", "f"), "int -> int");
    // An operand the text gives, finite and not NaN, gives an `int` alone.
    assert_eq!(sig("f() = round(2.5f64);", "f"), "() -> int");
    assert_eq!(sig("f() = round(2.5);", "f"), "() -> int");
    assert_eq!(sig("f() = awayFromZero(-2.1f32);", "f"), "() -> int");
}

#[test]
fn ties_takes_a_constant_even_or_away_alone() {
    for (src, arg) in [
        (
            "f(positional x: f64, t: #even | #away) = round(x, ties: t);",
            "t",
        ),
        ("f(positional x: f64) = round(x, ties: #up);", "#up"),
        ("f(positional x: f64) = round(x, ties: 1);", "1"),
    ] {
        let errs = type_errors(src);
        let want = format!(
            "`ties:` takes the constant `#even` or `#away`, and `{arg}` is not one of them."
        );
        assert!(
            errs.len() == 1 && errs[0].starts_with(&want) && errs[0].ends_with(&format!("[{arg}]")),
            "{src}: {errs:?}"
        );
    }
    assert_eq!(
        type_errors("f(positional x: f64) = round(x, ties: #away);"),
        Vec::<String>::new()
    );
}

/// `round(x, ties: #away)` elaborates to its own primitive and `ties: #even` to `round`.
#[test]
fn the_tie_rule_picks_the_primitive() {
    assert_eq!(
        term("x = round(2.5, ties: #away);\n", "x"),
        "roundTiesAway(2.5)"
    );
    assert_eq!(term("x = round(2.5, ties: #even);\n", "x"), "round(2.5)");
}

/// The table's row at 2.5 through `zedc run`, from a function and in place: each call is an
/// `int`, so the line needs no `else`.
#[test]
fn zedc_run_prints_the_row_at_two_and_a_half() {
    let src = "f() = round(2.5);\nmain(m: MainArgs) {\n  m.stdout <- \"${f()} \
               ${round(2.5, ties: #away)} ${floor(2.5)} ${ceil(2.5)} ${trunc(-2.5)} \
               ${awayFromZero(-2.5)}\";\n}\n";
    let out = zed_tests::step_helpers::l01_19a_command_line::run("round-row", src, &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "2 3 2 3 -2 -3\n", "")
    );
}

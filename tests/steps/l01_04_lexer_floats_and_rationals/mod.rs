//! Step L1.4: float literals, which need a leading digit, and exact `r` rationals.

use zedc::lex::{ErrorKind, Tok, lex};

fn toks(text: &str) -> Vec<Tok> {
    lex(text)
        .unwrap_or_else(|e| panic!("{text:?}: {e}"))
        .into_iter()
        .map(|t| t.tok)
        .collect()
}

fn float(s: &str) -> Tok {
    Tok::Float(s.into())
}

fn rat(s: &str) -> Tok {
    Tok::Rat(s.into())
}

#[test]
fn floats_as_programs_write_them() {
    // A half, a tolerance, a billion, Avogadro's number grouped, a large exponent.
    assert_eq!(
        toks("0.5 1.5e-3 1e9 6.022_140_76e23 2E+10 1e400"),
        [
            float("0.5"),
            float("1.5e-3"),
            float("1e9"),
            float("6.02214076e23"),
            float("2E+10"),
            float("1e400")
        ]
    );
}

#[test]
fn rationals_are_decimal_and_keep_their_text() {
    // A third is `1r/3r` once `/` lexes (step L1.6); `0.1r` is one tenth exactly.
    assert_eq!(
        toks("3r 0.1r 2.5e-3r 1_000r"),
        [rat("3"), rat("0.1"), rat("2.5e-3"), rat("1000")]
    );
}

#[test]
fn a_digit_must_follow_the_dot_so_member_access_and_ranges_start_with_the_integer() {
    // Each number ends before the `.`, which is an operator (step L1.6); `.5` is no float.
    for (text, at) in [
        ("5.double", 1),
        ("1..10", 1),
        ("1.e5", 1),
        (".5", 0),
        ("12.", 2),
    ] {
        let e = lex(text).unwrap_err();
        assert_eq!(
            (e.kind, e.span.start),
            (ErrorKind::Unexpected('.'), at),
            "{text}"
        );
    }
}

#[test]
fn integers_are_unchanged() {
    assert_eq!(
        toks("10 0x1E"),
        [
            Tok::Int {
                radix: 10,
                digits: "10".into()
            },
            Tok::Int {
                radix: 16,
                digits: "1E".into()
            }
        ]
    );
}

#[test]
fn golden_malformed_floats_and_rationals() {
    let cases = [
        "1e", "1e+", "1.5e", "1.5f", "3R", "0x10r", "1.5_", "2.5ms", "1e3x", "1rr",
    ];
    let out: Vec<String> = cases
        .iter()
        .map(|c| {
            let e = lex(c).unwrap_err();
            format!("{c:<6} [{}..{}] {e}", e.span.start, e.span.end)
        })
        .collect();
    insta::assert_snapshot!(out.join("\n"));
}

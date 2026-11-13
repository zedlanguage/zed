//! An int power whose exponent is shown to be at least 0 is accepted, and a rejected power
//! offers only repairs that check (POW-nonneg-power). A base of int[1..] to an exponent of
//! int[0..] is at least 1, so `2^(2^k)` under `k >= 0` has a non-negative exponent; the note on
//! a name a test narrows shows its narrowed type, `int[0..]`, not `int`; and each repair a
//! rejection offers, in a note or as the headline's Try, is written into the program, which
//! then checks.

use zed_tests::scaling;
use zedc::run::load;

/// `src` with a `main` added, so that `load` checks its functions.
fn program(src: &str) -> String {
    format!("{src}main(m: MainArgs) {{\n  m.stdout <- \"a\";\n}}\n")
}

/// Asserts that `src` checks.
fn checks(src: &str) {
    let src = program(src);
    load(src.as_bytes()).unwrap_or_else(|e| panic!("{src}\n{e}"));
}

/// The rendered diagnostics of `src`, which must be rejected.
fn rejected(src: &str) -> String {
    super::rejected(&program(src))
}

/// The repair the headline of `out` ends with, as in "Try `r` instead".
fn tried(out: &str) -> Option<&str> {
    let first = out.lines().next()?;
    let (_, rest) = first.split_once(" Try `")?;
    Some(&rest[..rest.find("` instead")?])
}

/// Every repair the notes of `out` offer, as "repair: `r`".
fn repairs(out: &str) -> Vec<&str> {
    out.lines()
        .filter_map(|l| l.split_once(": repair: `")?.1.strip_suffix('`'))
        .collect()
}

/// `src` with its one `power` replaced by the repair `r`, the branch left open filled with 0,
/// as a block where it binds a name and in parentheses otherwise, as in `domain_repairs`.
fn repaired(src: &str, power: &str, r: &str) -> String {
    assert_eq!(src.matches(power).count(), 1, "{src}");
    let r = r.replace('…', "0");
    match r.contains(';') {
        true => src.replace(power, &format!("{{ {r} }}")),
        false => src.replace(power, &format!("({r})")),
    }
}

#[test]
fn a_power_of_a_power_of_a_tested_exponent_checks() {
    // The program of the plan row, rejected before as "Int power with an exponent that may
    // be negative".
    checks("q(k: int) = if k >= 0 { 2^(2^k) } else { 0 };\n");
    // Towers, and powers of 1 and 0, whose exponent is still at least 0.
    for body in [
        "2^(2^(2^k))",
        "3^(2^k - 1)",
        "2^(1^k)",
        "2^(0^k)",
        "0^(2^k) + 1^(2^k) + (-2)^(2^k)",
    ] {
        checks(&format!(
            "q(k: int) = if k >= 0 {{ {body} }} else {{ 0 }};\n"
        ));
    }
}

#[test]
fn a_power_at_least_its_bernoulli_bound_checks() {
    // A base of at least b to an exponent of at least n is read as at least 1 + n(b - 1):
    // `3^(2^k)` is at least 3, and `5^(2^k + 1)` at least 9.
    checks("q(k: int) = if k >= 0 { 2^(3^(2^k) - 3) } else { 0 };\n");
    checks("q(k: int) = if k >= 0 { 2^(5^(2^k + 1) - 9) } else { 0 };\n");
    // One past the bound is rejected: `3^1 - 4` is -1 at k = 0.
    let out = rejected("q(k: int) = if k >= 0 { 2^(3^(2^k) - 4) } else { 0 };\n");
    assert!(
        out.contains("Int power with an exponent that may be negative"),
        "{out}"
    );
}

#[test]
fn an_exponent_that_may_be_negative_is_still_rejected() {
    for (body, negative) in [
        // -1 at k = 0.
        ("2^(2^k - 2)", false),
        // `(-2)^k` is negative at odd k.
        ("2^((-2)^k)", false),
        ("2^(0 - 2^k)", true),
    ] {
        let out = rejected(&format!(
            "q(k: int) = if k >= 0 {{ {body} }} else {{ 0 }};\n"
        ));
        let head = match negative {
            true => "Int power with a negative exponent",
            false => "Int power with an exponent that may be negative",
        };
        assert!(out.contains(head), "{body}\n{out}");
    }
}

#[test]
fn a_name_a_test_narrows_is_shown_with_its_narrowed_type() {
    let out = rejected("q(k: int) = if k >= 0 { 2^(2^k - 2) } else { 0 };\n");
    assert!(out.contains("`k` is int[0..] here"), "{out}");
    assert!(!out.contains("`k` is int here"), "{out}");
    let out = rejected("q(k: int) = if k > 0 { 2^(k - 5) } else { 0 };\n");
    assert!(out.contains("`k` is int[1..] here"), "{out}");
    // With no test, the declared type.
    let out = rejected("q(k: int) = 2^(k - 5);\n");
    assert!(out.contains("`k` is int here"), "{out}");
}

/// Programs of one rejected int power, written as `power` once in the program, each with the
/// repairs it offers in order.
const OFFERED: [(&str, &str, &[&str]); 9] = [
    (
        "q(k: int) = 2^(k - 5);\n",
        "2^(k - 5)",
        &[
            "exponent = k - 5; if exponent >= 0 { 2^exponent } else { … }",
            "2r^(k - 5)",
        ],
    ),
    (
        "q(k: int) = 1 + 2^(k - 5);\n",
        "2^(k - 5)",
        &[
            "exponent = k - 5; if exponent >= 0 { 2^exponent } else { … }",
            "2r^(k - 5)",
        ],
    ),
    (
        "q(k: int) {\n  y = 2^(k - 5);\n  return y + 1;\n}\n",
        "2^(k - 5)",
        &[
            "exponent = k - 5; if exponent >= 0 { 2^exponent } else { … }",
            "2r^(k - 5)",
        ],
    ),
    (
        "q(k: int) = 2^k;\n",
        "2^k",
        &["if k >= 0 { 2^k } else { … }", "2r^k"],
    ),
    // `n + 2r^k` adds a `rat` to an int: not offered.
    (
        "q(n: int, k: int) = n + 2^k;\n",
        "2^k",
        &["if k >= 0 { 2^k } else { … }"],
    ),
    // The inner power of the tower, written with its parentheses; the outer one is accepted,
    // and is again once the inner one is tested.
    (
        "q(k: int) = 2^(2^k);\n",
        "(2^k)",
        &["if k >= 0 { (2^k) } else { … }"],
    ),
    (
        "q(k: int) = if k >= 0 { 2^(2^k - 2) } else { 0 };\n",
        "2^(2^k - 2)",
        &[
            "exponent = 2^k - 2; if exponent >= 0 { 2^exponent } else { … }",
            "2r^(2^k - 2)",
        ],
    ),
    ("c = 2^-3;\n", "2^-3", &["2.0f64^-3", "2^-3.0f64", "2r^-3"]),
    // Each repair changes the value to a `rat` or a float, which `+ k` does not take.
    ("q(k: int) = 2^-3 + k;\n", "2^-3", &[]),
];

#[test]
fn each_offered_power_repair_checks_where_it_is_written() {
    for (src, power, want) in OFFERED {
        let out = rejected(src);
        let offered = repairs(&out);
        assert_eq!(offered, want, "{src}\n{out}");
        assert_eq!(tried(&out), want.first().copied(), "{src}\n{out}");
        if want.is_empty() {
            assert!(
                out.contains("No fix is offered: each one the checker tried is rejected too."),
                "{out}"
            );
        }
        for r in offered {
            checks(&repaired(src, power, r));
        }
    }
}

#[test]
#[ignore = "REPAIR-past-binding: a repair that changes the type of a value bound to a name is \
            checked at the binding, not at the name's uses"]
fn a_repair_is_checked_at_the_uses_of_the_name_it_binds() {
    let src = "q(n: int, k: int) {\n  y = 2^k;\n  return y + n;\n}\n";
    let out = rejected(src);
    for r in repairs(&out) {
        checks(&repaired(src, "2^k", r));
    }
}

/// A chain of `n` bindings under `k >= 0`, each a power of 2 to the one before, and each
/// exponent shown to be at least 1 by the power that gives it.
fn tower(n: usize) -> String {
    let mut src = String::from("q(k: int) {\n  y0 = if k >= 0 { 2^k } else { 1 };\n");
    for i in 1..n {
        src += &format!("  y{i} = 2^y{p};\n", p = i - 1);
    }
    src + &format!("  return y{};\n}}\n", n - 1)
}

#[test]
fn a_chain_of_powers_scales() {
    let made = scaling::inputs(64, |n| program(&tower(n)));
    scaling::check("checking a chain of n powers of powers", 64, |n| {
        let src = &made[&n];
        load(src.as_bytes()).unwrap_or_else(|e| panic!("{src}\n{e}"));
    });
}

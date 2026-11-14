//! An int power whose exponent is shown to be at least 0 is accepted, and a rejected power
//! offers only repairs that check (POW-nonneg-power). A base of int[1..] to an exponent of
//! int[0..] is at least 1, so `2^(2^k)` under `k >= 0` has a non-negative exponent; the note on
//! a name a test narrows shows its narrowed type, `int[0..]`, not `int`; and each repair a
//! rejection offers, in a note or as the headline's Try, is written into the program, which
//! then checks. A test's narrowing of an exponent reaches the power, and a power is read at
//! least at its least power: under `k > 0`, `2^(2^k - 2)` checks (POW-scope-exponent). That least
//! power is exact at every level of a tower: under `k > 0`, `5^(2^k + 1) - 10` is at least
//! 5^3 - 10 = 115, and the headline of one past it shows the derived `int[-1..]`
//! (POW-tower-exact-test).

use zedc::run::load;

/// `src` with a `main` added, so that `load` checks its functions.
pub(super) fn program(src: &str) -> String {
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
fn a_power_at_least_its_least_power_checks() {
    // A base of at least b to an exponent of at least n is at least b^n, read exactly:
    // `3^(2^k)` is at least 3, and `5^(2^k + 1)` at least 25 (POW-scope-exponent; the bound by
    // Bernoulli's inequality before it, 1 + n(b - 1), gave 9).
    checks("q(k: int) = if k >= 0 { 2^(3^(2^k) - 3) } else { 0 };\n");
    checks("q(k: int) = if k >= 0 { 2^(5^(2^k + 1) - 25) } else { 0 };\n");
    // One past the bound is rejected: `3^1 - 4` is -1 at k = 0, and `5^2 - 26` too.
    for body in ["2^(3^(2^k) - 4)", "2^(5^(2^k + 1) - 26)"] {
        let out = rejected(&format!(
            "q(k: int) = if k >= 0 {{ {body} }} else {{ 0 }};\n"
        ));
        assert!(
            out.contains("Int power with an exponent that may be negative"),
            "{body}\n{out}"
        );
    }
}

#[test]
fn a_test_s_narrowing_of_an_exponent_reaches_the_power() {
    // `k` is int[1..] in the arm, so `2^k - 2` and `3^k - 3` are at least 0 (POW-scope-exponent).
    for (test, body) in [
        ("k > 0", "2^(2^k - 2)"),
        ("k >= 1", "2^(3^k - 3)"),
        ("k >= 3", "2^(2^k - 8)"),
        ("k > 0 && k < 5", "2^(2^k - 2) + 2^(16 - 2^k)"),
        ("k >= 1", "{ e = 2^k - 2; 2^e }"),
        ("k > 0", "2^(2^(2^k - 2) - 1)"),
    ] {
        checks(&format!(
            "q(k: int) = if {test} {{ {body} }} else {{ 0 }};\n"
        ));
    }
    // One below the least power, or one bound too few, is still rejected.
    for (test, body) in [
        ("k > 0", "2^(2^k - 3)"),
        ("k >= 1", "2^(3^k - 4)"),
        ("k >= 3", "2^(2^k - 9)"),
        ("k > 0 && k < 5", "2^(2^k - 2) + 2^(15 - 2^k)"),
        ("k > 0", "2^(2^(2^k - 2) - 2)"),
        ("k > 0", "2^((0 - 2)^k)"),
    ] {
        let out = rejected(&format!(
            "q(k: int) = if {test} {{ {body} }} else {{ 0 }};\n"
        ));
        assert!(
            out.contains("Int power with an exponent that may be negative"),
            "{test}: {body}\n{out}"
        );
    }
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
fn a_repair_is_checked_at_the_uses_of_the_name_it_binds() {
    let src = "q(n: int, k: int) {\n  y = 2^k;\n  return y + n;\n}\n";
    let out = rejected(src);
    // `2r^k` makes `y + n` add a rat to an int: not offered.
    assert_eq!(repairs(&out), ["if k >= 0 { 2^k } else { … }"], "{out}");
    for r in repairs(&out) {
        checks(&repaired(src, "2^k", r));
    }
}

/// Programs of one rejected power bound to a name, each with the repairs it offers, checked at
/// each use of the name.
const BOUND: [(&str, &[&str]); 9] = [
    // A use outside any construct takes every type.
    (
        "q(k: int) {\n  y = 2^k;\n  return y;\n}\n",
        &["if k >= 0 { 2^k } else { … }", "2r^k"],
    ),
    // Both arguments are uses of `y`: `2r^k` makes both rat at once.
    (
        "q(k: int) {\n  y = 2^k;\n  return y * y;\n}\n",
        &["if k >= 0 { 2^k } else { … }", "2r^k"],
    ),
    (
        "q(k: int) {\n  y = 2^k;\n  return (y + 1) * y;\n}\n",
        &["if k >= 0 { 2^k } else { … }", "2r^k"],
    ),
    // Through a second name, and through a construct bound to a name.
    (
        "q(n: int, k: int) {\n  y = 2^k;\n  z = y;\n  return z + n;\n}\n",
        &["if k >= 0 { 2^k } else { … }"],
    ),
    (
        "q(n: int, k: int) {\n  y = 2^k;\n  a = y * 2;\n  return a + n;\n}\n",
        &["if k >= 0 { 2^k } else { … }"],
    ),
    // One use takes a rat and the other does not.
    (
        "q(n: int, k: int) {\n  y = 2^k;\n  a = y + 1;\n  return y + n;\n}\n",
        &["if k >= 0 { 2^k } else { … }"],
    ),
    // A component of a tuple display bound to a name.
    (
        "q(n: int, k: int) {\n  y, w = (2^k, 1);\n  return y + n;\n}\n",
        &["if k >= 0 { 2^k } else { … }"],
    ),
    (
        "q(k: int) {\n  y, w = (2^k, 1);\n  return y + 1;\n}\n",
        &["if k >= 0 { 2^k } else { … }", "2r^k"],
    ),
    // An argument of a call whose parameter is an int.
    (
        "f(a: int) = a + 1;\nq(k: int) {\n  y = 2^k;\n  return f(a: y);\n}\n",
        &["if k >= 0 { 2^k } else { … }"],
    ),
];

#[test]
fn a_repair_of_a_bound_value_is_checked_at_every_use() {
    for (src, want) in BOUND {
        let out = rejected(src);
        assert_eq!(repairs(&out), want, "{src}\n{out}");
        for r in want {
            checks(&repaired(src, "2^k", r));
        }
    }
}

/// Programs of one int power to a negative literal bound to a name in a body, written as
/// `2^-1` once in the program, each with the repairs it offers: those a power outside every
/// function offers, `c = 2^-3` above, less those a use of the name does not take
/// (REPAIR-block-pow-negative). The binding gives the power's class its carrier, int, which
/// takes no repair; before, each was checked against it and none was offered.
const NEGATIVE_BOUND: [(&str, &[&str]); 10] = [
    (
        "g() = { z = 2^-1; z };\n",
        &["2.0f64^-1", "2^-1.0f64", "2r^-1"],
    ),
    (
        "g() {\n  z = 2^-1;\n  return z;\n}\n",
        &["2.0f64^-1", "2^-1.0f64", "2r^-1"],
    ),
    // The power's class holds the `1` too, which takes each repair's carrier.
    (
        "g() {\n  z = 2^-1 + 1;\n  return z * z;\n}\n",
        &["2.0f64^-1", "2^-1.0f64", "2r^-1"],
    ),
    (
        "g() = { z = { w = 2^-1; w }; z };\n",
        &["2.0f64^-1", "2^-1.0f64", "2r^-1"],
    ),
    // `z + n` takes none: each repair adds a rat or a float to an int.
    ("g(n: int) {\n  z = 2^-1;\n  return z + n;\n}\n", &[]),
    // Through a second name.
    (
        "g(n: int) {\n  z = 2^-1;\n  w = z;\n  return w + n;\n}\n",
        &[],
    ),
    // A component of a tuple display bound to a name.
    (
        "g() {\n  z, w = (2^-1, 3);\n  return z;\n}\n",
        &["2.0f64^-1", "2^-1.0f64", "2r^-1"],
    ),
    (
        "g(n: int) {\n  z, w = (2^-1, n);\n  return z + n;\n}\n",
        &[],
    ),
    // A use of the name in a call whose parameter is an int.
    (
        "f(a: int) = a + 1;\ng() {\n  z = 2^-1;\n  return f(a: z);\n}\n",
        &[],
    ),
    // A value the power's class is only part of carries no repair to the name's uses.
    ("g() {\n  y = (2^-1, 1);\n  return y;\n}\n", &[]),
];

#[test]
fn a_bound_power_to_a_negative_literal_offers_the_repairs_of_one_outside_every_function() {
    for (src, want) in NEGATIVE_BOUND {
        let out = rejected(src);
        assert_eq!(repairs(&out), want, "{src}\n{out}");
        assert_eq!(tried(&out), want.first().copied(), "{src}\n{out}");
        if want.is_empty() {
            assert!(
                out.contains("No fix is offered: each one the checker tried is rejected too."),
                "{out}"
            );
        }
        for r in want {
            checks(&repaired(src, "2^-1", r));
        }
    }
}

/// A use that takes a rat and no float keeps `2r^-1` alone, in a body as outside every
/// function; the use is rejected too, as `z` is an int.
#[test]
fn a_use_of_a_bound_power_keeps_the_repairs_it_takes() {
    for src in [
        "z = 2^-1;\nc = z * 2r;\n",
        "g() {\n  z = 2^-1;\n  return z * 2r;\n}\n",
        "g() {\n  z, w = (2^-1, 3);\n  return z * 2r;\n}\n",
    ] {
        let out = rejected(src);
        assert_eq!(repairs(&out), ["2r^-1"], "{src}\n{out}");
        assert_eq!(tried(&out), Some("2r^-1"), "{src}\n{out}");
        checks(&repaired(src, "2^-1", "2r^-1"));
    }
}

/// Programs of `2^-1` used beside an operand of a fixed carrier other than `int`, each with
/// the repairs it offers: those whose type the operand takes. Numbers of two carriers meet in
/// no operator (no implicit conversion), so `2r^-1` makes `z` a `rat`, which `z * 2.0f64` then
/// rejects as `rat * f64`; it was kept before, since the check of the use with the repair in
/// place rejected the literal `2.0f64` again, at the same place, which read as the use's own
/// error (REPAIR-pow-use-f64-drops-rat). Beside an `f32`, every repair gives an `f64` or a
/// `rat`, and none is offered.
const USE_AT_A_CARRIER: [(&str, &[&str]); 12] = [
    ("z = 2^-1;\nc = z * 2.0f64;\n", &["2.0f64^-1", "2^-1.0f64"]),
    (
        "g() {\n  z = 2^-1;\n  return z * 2.0f64;\n}\n",
        &["2.0f64^-1", "2^-1.0f64"],
    ),
    (
        "g() = { z = 2^-1; z * 2.0f64 };\n",
        &["2.0f64^-1", "2^-1.0f64"],
    ),
    (
        "g() {\n  z, w = (2^-1, 3);\n  return 2.0f64 * z;\n}\n",
        &["2.0f64^-1", "2^-1.0f64"],
    ),
    (
        "g() {\n  z = 2^-1;\n  return z < 2.0f64;\n}\n",
        &["2.0f64^-1", "2^-1.0f64"],
    ),
    ("z = 2^-1;\nc = z + 1.5f32;\n", &[]),
    ("g() {\n  z = 2^-1;\n  return z + 1.5f32;\n}\n", &[]),
    (
        "g() {\n  z = 2^-1;\n  w = z;\n  return w + 1.5f32;\n}\n",
        &[],
    ),
    // A name of type `f64`: a parameter, and a name bound to an `f64` literal.
    (
        "g(x: f64) {\n  z = 2^-1;\n  return z * x;\n}\n",
        &["2.0f64^-1", "2^-1.0f64"],
    ),
    (
        "g() {\n  x = 1.5f64;\n  z = 2^-1;\n  return z * x;\n}\n",
        &["2.0f64^-1", "2^-1.0f64"],
    ),
    ("g(x: f32) {\n  z = 2^-1;\n  return x - z;\n}\n", &[]),
    // A `rat` operand keeps `2r^-1` alone.
    ("g(x: rat) {\n  z = 2^-1;\n  return z * x;\n}\n", &["2r^-1"]),
];

#[test]
fn a_use_beside_a_fixed_carrier_keeps_the_repairs_of_that_carrier() {
    for (src, want) in USE_AT_A_CARRIER {
        let out = rejected(src);
        assert_eq!(repairs(&out), want, "{src}\n{out}");
        assert_eq!(tried(&out), want.first().copied(), "{src}\n{out}");
        if want.is_empty() {
            assert!(
                out.contains("No fix is offered: each one the checker tried is rejected too."),
                "{out}"
            );
        }
        for r in want {
            checks(&repaired(src, "2^-1", r));
        }
        // Each repair dropped is rejected where it is written.
        for r in ["2.0f64^-1", "2^-1.0f64", "2r^-1"] {
            if !want.contains(&r) {
                let src = program(&repaired(src, "2^-1", r));
                assert!(load(src.as_bytes()).is_err(), "{src}");
            }
        }
    }
}

/// A function of `n` names each bound to a power to a negative literal and used twice, and one
/// name bound to a sum of `n` such powers, one class with `n` powers among its uses.
pub(super) fn negative_bound(n: usize) -> String {
    let mut src = String::from("q(n: int) {\n  y = 2^-1");
    for _ in 1..n {
        src += " + 2^-1";
    }
    src += ";\n";
    for i in 0..n {
        src += &format!("  z{i} = 2^-1;\n  a{i} = z{i} * z{i};\n  b{i} = z{i} + n;\n");
    }
    src + "  return y;\n}\n"
}

/// Asserts that `src` is rejected.
pub(super) fn is_rejected(src: &str) {
    assert!(load(src.as_bytes()).is_err(), "{src}");
}

/// Asserts that `src` checks, as [`checks`] does with the program around it.
pub(super) fn checks_whole(src: &str) {
    load(src.as_bytes()).unwrap_or_else(|e| panic!("{src}\n{e}"));
}

#[test]
fn checking_bound_powers_and_their_repairs_at_uses() {
    for n in [1, 3] {
        is_rejected(&program(&negative_bound(n)));
        is_rejected(&program(&bound_uses(n)));
        checks_whole(&program(&tower(n)));
        checks_whole(&program(&narrowed_tower(n)));
    }
}

/// A function of `n` rejected powers each bound to a name used twice, as one argument of an
/// int sum and as both arguments of a product, and one rejected power bound to a name used `n`
/// times: each repair is checked at every use.
pub(super) fn bound_uses(n: usize) -> String {
    let mut src = String::from("q(n: int, k: int) {\n  y = 2^k;\n");
    for i in 0..n {
        src += &format!("  b{i} = 2^k;\n  c{i} = b{i} + n;\n  d{i} = b{i} * b{i};\n");
        src += &format!("  a{i} = y + {i};\n");
    }
    src + "  return y;\n}\n"
}


/// A chain of `n` bindings under `k >= 0`, each a power of 2 to the one before, and each
/// exponent shown to be at least 1 by the power that gives it.
pub(super) fn tower(n: usize) -> String {
    let mut src = String::from("q(k: int) {\n  y0 = if k >= 0 { 2^k } else { 1 };\n");
    for i in 1..n {
        src += &format!("  y{i} = 2^y{p};\n", p = i - 1);
    }
    src + &format!("  return y{};\n}}\n", n - 1)
}


/// A tower of `n` powers under `k > 0`, each exponent one less than a power of 2 and so at least
/// 0 only where the test's narrowing of `k` reaches it: `2^(2^(2^k - 1) - 1) ...`.
pub(super) fn narrowed_tower(n: usize) -> String {
    let mut e = String::from("2^k - 1");
    for _ in 1..n {
        e = format!("2^({e}) - 1");
    }
    format!("q(k: int) = if k > 0 {{ {e} }} else {{ 0 }};\n")
}


/// Asserts that `src` is rejected with an int power whose headline shows `power`, its code
/// annotated with the types the checker derived, as `2 : int ^ (2^k - 3) : int[-1..]`.
fn rejected_with(src: &str, power: &str) {
    let out = rejected(src);
    let want = format!("Int power with an exponent that may be negative: `{power}`.");
    assert!(out.lines().any(|l| l.contains(&want)), "{src}\n{out}");
}

#[test]
fn the_least_power_of_a_tower_under_a_test_is_exact() {
    // Under `k > 0`, `2^k + 1` is at least 3, so `5^(2^k + 1)` is at least 5^3 = 125, read at
    // the corners exactly, and `5^(2^k + 1) - 10` is at least 115 (POW-tower-exact-test). The
    // bound by Bernoulli's inequality, 1 + 3(5 - 1) = 13, would make it at least 3, and the
    // bound under `k >= 0`, 5^2 = 25, at least 15: each is below 115 - 116.
    let arm = |body: &str| format!("q(k: int) = if k > 0 {{ {body} }} else {{ 0 }};\n");
    for body in [
        "2^(5^(2^k + 1) - 10)",
        "2^(5^(2^k + 1) - 10 - 115)",
        "2^(5^(2^k + 1) - 125)",
    ] {
        checks(&arm(body));
    }
    // One past the least power, the exponent shows its derived least value, -1.
    for (body, power) in [
        (
            "2^(5^(2^k + 1) - 10 - 116)",
            "2 : int ^ (5^(2^k + 1) - 10 - 116) : int[-1..]",
        ),
        (
            "2^(5^(2^k + 1) - 126)",
            "2 : int ^ (5^(2^k + 1) - 126) : int[-1..]",
        ),
        (
            "2^(5^(2^k + 1) - 135)",
            "2 : int ^ (5^(2^k + 1) - 135) : int[-10..]",
        ),
    ] {
        rejected_with(&arm(body), power);
    }
}

#[test]
fn the_least_power_of_a_neighboring_tower_is_exact() {
    let arm = |body: &str| format!("q(k: int) = if k > 0 {{ {body} }} else {{ 0 }};\n");
    // One level deeper: `2^(2^k)` is at least 4, so `5^(2^(2^k) + 1)` is at least 5^5 = 3125.
    checks(&arm("2^(5^(2^(2^k) + 1) - 3125)"));
    rejected_with(
        &arm("2^(5^(2^(2^k) + 1) - 3126)"),
        "2 : int ^ (5^(2^(2^k) + 1) - 3126) : int[-1..]",
    );
    // An inner exponent of at least 0 gives an inner power of at least 5^0 = 1.
    checks(&arm("2^(5^(2^k - 2) - 1)"));
    // An inner exponent that may be negative, `2^k - 3` at k = 1, is rejected, and so is the
    // outer power, whose exponent `5^(2^k - 3) - 10` is not shown to be at least 0.
    let src = arm("2^(5^(2^k - 3) - 10)");
    rejected_with(&src, "5 : int ^ (2^k - 3) : int[-1..]");
    rejected_with(&src, "2 : int ^ (5^(2^k - 3) - 10) : int");
}

/// A tower of `n` powers under `k > 0`, each level `5^(e + 1) - 123` of the level `e` below it,
/// from `2^k`, and `2^(e - 2)` of the top level `e`: each level is at least 2, since
/// `5^(2 + 1) - 123 = 2`, read exactly at every level, where a bound below the least power
/// rejects it (Bernoulli's 1 + 3(5 - 1) = 13 gives -110).
pub(super) fn least_power_tower(n: usize, minus: usize) -> String {
    let mut e = String::from("2^k");
    for _ in 0..n {
        e = format!("5^({e} + 1) - 123");
    }
    format!("q(k: int) = if k > 0 {{ 2^({e} - {minus}) }} else {{ 0 }};\n")
}

#[test]
fn a_tower_at_its_least_power_checks() {
    // The top level is at least 2 and no more: `- 2` checks and `- 3` is rejected.
    for n in [1, 2, 3] {
        checks(&least_power_tower(n, 2));
        let out = rejected(&least_power_tower(n, 3));
        assert!(
            out.lines()
                .next()
                .is_some_and(|l| l.contains("- 123 - 3) : int[-1..]`.")),
            "{out}"
        );
    }
}

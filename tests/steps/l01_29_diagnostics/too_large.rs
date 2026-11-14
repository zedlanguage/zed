//! A power whose result the operands' types prove larger than the target's address space is
//! rejected at compile time (plan row CONST-too-large, QUESTIONS A100; DESIGN
//! sec:checking_in_zed and the sec:diagnostics row "Number too large for any memory of the
//! target"). The least size is `k * ⌊log₂ |x|⌋ + 1` bits for `x ^ k`, from the least `|x|`
//! and `|k|` the types allow, and nothing is built. Before, `b ^ (2^64)` with
//! `b = 2^64 + 13` compiled and the run stopped with "Number too large for memory".

use zed_tests::scaling;
use zedc::build::Build;
use zedc::run::load_for;

/// The program `src` built for Linux x86_64: its rendered diagnostics, or `None` when it
/// compiles.
fn built(src: &str) -> Option<String> {
    let build = Build::default().for_target("x86_64-linux");
    load_for(src.as_bytes(), &build).err()
}

/// The rendered diagnostics of `src`, which the checker rejects.
fn rejected(src: &str) -> String {
    built(src).unwrap_or_else(|| panic!("accepted:\n{src}"))
}

/// `main` pushing `String(<power>)` to standard output, after `b = 2^64 + 13;`.
fn pushed(power: &str) -> String {
    format!(
        "main(m: MainArgs) {{\n    b = 2^64 + 13;\n    m.stdout <- String({power}) else \"\";\n}}\n"
    )
}

#[test]
fn a_power_past_the_address_space_is_rejected_with_its_least_size() {
    // A100's first program: `64 * 2^64 + 1` bits, at least 128 EiB.
    let src = "main(m: MainArgs) {\n    b = 2^64 + 13;\n    m.stdout <- String(b ^ (2^64));\n}\n";
    assert_eq!(
        rejected(src),
        r#"3:24: Number too large for any memory of the target: `b ^ (2^64)` needs at least 128 EiB; Linux x86_64 addresses 16 EiB. Try `m.stdout <- String(b ^ (2^60))` instead.
  [1] 2:5: the base x, `b`, is at least 2^64 in magnitude, so ⌊log₂ |x|⌋ is 64
      2 |     b = 2^64 + 13;
        |     ^^^^^^^^^^^^^^
  [2] 3:28: the exponent k, `(2^64)`, is at least 2^64
      3 |     m.stdout <- String(b ^ (2^64));
        |                        ^^^^^^^^^^ [3, 4]
        |                            ^^^^^^ [2]
  [3] 3:24: so `b ^ (2^64)` has at least 2^64 * 64 + 1 bits: |k| * ⌊log₂ |x|⌋ + 1 at the least |x| and |k|
  [4] 3:24: or read the exponent from the input: the run then stops if no memory holds the result
  fixes, each checked here:
    m.stdout <- String(b ^ (2^60));    needs at least 8 EiB"#
    );
}

#[test]
fn a_power_in_a_branch_not_taken_is_rejected() {
    // A100's third program: the bound holds whether or not the branch runs.
    let src = "main(m: MainArgs) {\n    k = int(m.args[0] else \"\") else 0;\n    \
               m.stdout <- if k > 5 { String((2^64 + 13) ^ (2^64)) } else { \"few\" };\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "3:35: Number too large for any memory of the target: `(2^64 + 13) ^ (2^64)` \
             needs at least 128 EiB; Linux x86_64 addresses 16 EiB."
        ),
        "{out}"
    );
}

#[test]
fn a_power_whose_size_depends_on_the_input_compiles() {
    // A100's second program, `grow`: `2^k` may be 0 or 1, so nothing is proved.
    let src = "grow(k: int) {\n    return if k >= 0 { 2r^(2^k) } else { 0r };\n}\n\
               main(m: MainArgs) {\n    k = int(m.args[0] else \"\") else 0;\n    \
               m.stdout <- String(grow(k: k)) else \"\";\n}\n";
    assert_eq!(built(src), None);
    // An exponent read from the input, 2^64 when there is none: the types allow 0, so the
    // run decides (sites.rs, `a_power_too_large_is_named_as_written_with_its_size`).
    for base in ["b", "rat(b)"] {
        let src = format!(
            "main(m: MainArgs) {{\n    b = 2^64 + 13;\n    \
             k = 2^64 + (int(m.args[0] else \"\") else 0);\n    \
             m.stdout <- if k >= 0 {{ String({base} ^ k) }} else {{ \"\" }};\n}}\n"
        );
        assert_eq!(built(&src), None, "{base}");
    }
}

#[test]
fn the_bound_is_exact_at_the_address_space() {
    // `b` has 65 bits, so `b ^ k` has at least `64 * k + 1` bits; 2^64 bytes are 2^67 bits.
    // `k = 2^61 - 1` gives `2^67 - 63` bits, which fit; `k = 2^61` gives `2^67 + 1`.
    for power in [
        "b ^ (2^61 - 1)",
        "rat(b) ^ (2^61 - 1)",
        "b ^ (2^60)",
        "b ^ 1000",
    ] {
        assert_eq!(built(&pushed(power)), None, "{power}");
    }
    for (power, col) in [("b ^ (2^61)", 24), ("rat(b) ^ (2^61)", 24)] {
        let out = rejected(&pushed(power));
        let head = format!(
            "3:{col}: Number too large for any memory of the target: `{power}` needs more \
             than 16 EiB; Linux x86_64 addresses 16 EiB."
        );
        assert!(out.starts_with(&head), "{power}:\n{out}");
    }
}

#[test]
fn a_base_that_builds_nothing_proves_nothing() {
    // A base within 64 bits is kept as prime powers, as is a power of 2 however large: the
    // result is a list of exponents, not a number of `k` words.
    for power in [
        "(2^64 - 1) ^ (2^64)",
        "2 ^ (2^70)",
        "(2^(2^70)) ^ (2^64)",
        "3 ^ (2^100)",
    ] {
        let src = format!("main(m: MainArgs) {{\n    m.stdout <- String({power} > 0);\n}}\n");
        assert_eq!(built(&src), None, "{power}");
    }
}

#[test]
fn a_negative_exponent_is_bounded_by_its_magnitude() {
    let out = rejected(&pushed("rat(b) ^ -(2^64)"));
    assert_eq!(
        out,
        r#"3:24: Number too large for any memory of the target: `rat(b) ^ -(2^64)` needs at least 128 EiB; Linux x86_64 addresses 16 EiB. Try `m.stdout <- String(rat(b) ^ -(2^60)) else ""` instead.
  [1] 3:24: the numerator p of the base `rat(b)` is at least 2^64 in magnitude, so ⌊log₂ |p|⌋ is 64
      3 |     m.stdout <- String(rat(b) ^ -(2^64)) else "";
        |                        ^^^^^^ [1]
        |                        ^^^^^^^^^^^^^^^^ [3, 4]
        |                                 ^^^^^^^ [2]
  [2] 3:33: the exponent k, `-(2^64)`, is at most -2^64
  [3] 3:24: so `rat(b) ^ -(2^64)` has at least 2^64 * 64 + 1 bits from the base's numerator: |k| * ⌊log₂ |p|⌋ + 1 at the least |p| and |k|
  [4] 3:24: or read the exponent from the input: the run then stops if no memory holds the result
  fixes, each checked here:
    m.stdout <- String(rat(b) ^ -(2^60)) else "";    needs at least 8 EiB"#
    );
}

/// `n` bindings, each a power past the address space.
fn powers(n: usize) -> String {
    (0..n)
        .map(|i| format!("x{i} = (2^64 + 13) ^ (2^64 + {i});\n"))
        .collect()
}

#[test]
fn rejecting_many_powers_scales() {
    // The bound is O(1) words per power: one division and one comparison.
    scaling::check("n powers past the address space, each rejected", 200, |n| {
        let out = rejected(&powers(n));
        assert_eq!(
            out.matches("Number too large for any memory of the target")
                .count(),
            n
        );
    });
}

/// `main` binding `b = 5 * 2^100 + 1` (103 bits) and `x` to `rat`, then the lines `body`
/// (plan row CONST-too-large-rat-names).
fn with_x(x: &str, body: &str) -> String {
    format!("main(m: MainArgs) {{\n    b = 5 * 2^100 + 1;\n    x = {x};\n{body}}}\n")
}

#[test]
fn a_rat_base_fixed_through_a_name_and_a_division_is_rejected() {
    // The row's program. Before, it compiled and the run stopped with "Number too large for
    // memory" (103 EiB). Both parts of `b / (b + 1)` have 103 bits, so `x ^ (2^62)` has at
    // least `2 * (2^62 * 102 + 1)` bits, 102 EiB.
    let src = with_x(
        "rat(b) / rat(b + 1)",
        "    m.stdout <- String(x ^ (2^62)) else \"\";\n",
    );
    assert_eq!(
        rejected(&src),
        r#"4:24: Number too large for any memory of the target: `x ^ (2^62)` needs at least 102 EiB; Linux x86_64 addresses 16 EiB. Try `m.stdout <- String(x ^ (2^59)) else ""` instead.
  [1] 3:5: the numerator p of the base `x` is at least 2^102 in magnitude, so ⌊log₂ |p|⌋ is 102; the denominator p of the base `x` is at least 2^102 in magnitude, so ⌊log₂ |p|⌋ is 102
      3 |     x = rat(b) / rat(b + 1);
        |     ^^^^^^^^^^^^^^^^^^^^^^^^
  [2] 4:28: the exponent k, `(2^62)`, is at least 2^62
      4 |     m.stdout <- String(x ^ (2^62)) else "";
        |                        ^^^^^^^^^^ [3, 4]
        |                            ^^^^^^ [2]
  [3] 4:24: so `x ^ (2^62)` has at least 2^62 * 102 + 1 bits from the base's numerator and 2^62 * 102 + 1 bits from the base's denominator: |k| * ⌊log₂ |p|⌋ + 1 at the least |p| and |k|
  [4] 4:24: or read the exponent from the input: the run then stops if no memory holds the result
  fixes, each checked here:
    m.stdout <- String(x ^ (2^59)) else "";    needs at least 12 EiB"#
    );
}

/// `with_x(x, …)` pushing `String(<power>)` to standard output.
fn x_pushed(x: &str, power: &str) -> String {
    with_x(x, &format!("    m.stdout <- String({power}) else \"\";\n"))
}

#[test]
fn both_parts_of_a_rat_base_count() {
    // With both parts of 103 bits, `x ^ k` has at least `k * 204 + 2` bits: `2^59` fits
    // (12.75 EiB) and `2^60` does not (25.5 EiB). With the denominator 7, only the numerator
    // is built, `k * 102 + 1` bits: `2^60` fits (12.75 EiB) and `2^61` does not.
    let both = "rat(b) / rat(b + 1)";
    let one = "rat(b) / 7";
    for (x, power) in [
        (both, "x ^ (2^59)"),
        (one, "x ^ (2^60)"),
        (one, "x ^ -(2^60)"),
    ] {
        assert_eq!(built(&x_pushed(x, power)), None, "{x}; {power}");
    }
    for (x, power, need) in [
        (both, "x ^ (2^60)", "at least 25 EiB"),
        (one, "x ^ (2^61)", "at least 25 EiB"),
        (one, "x ^ -(2^61)", "at least 25 EiB"),
    ] {
        let out = rejected(&x_pushed(x, power));
        let head = format!(
            "4:24: Number too large for any memory of the target: `{power}` needs {need}; \
             Linux x86_64 addresses 16 EiB."
        );
        assert!(out.starts_with(&head), "{x}; {power}:\n{out}");
    }
    let out = rejected(&x_pushed(one, "x ^ (2^61)"));
    assert!(
        out.contains(
            "the numerator p of the base `x` is at least 2^102 in magnitude, so ⌊log₂ |p|⌋ \
             is 102\n"
        ) && !out.contains("denominator"),
        "{out}"
    );
}

#[test]
fn a_rat_base_is_read_through_names_and_operations() {
    // A name bound to a name, a negation, a sum, a product and a quotient of `rat`s: each is
    // the kernel's value, so a quotient whose parts reduce is read reduced.
    for (x, body) in [
        (
            "rat(b) / rat(b + 1)",
            "    y = x;\n    z = -y;\n    m.stdout <- String(z ^ (2^62)) else \"\";\n",
        ),
        (
            "rat(b) * rat(b)",
            "    m.stdout <- String(x ^ (2^60)) else \"\";\n",
        ),
        (
            "rat(b) + 1 / 3",
            "    m.stdout <- String((x - 1) ^ (2^62)) else \"\";\n",
        ),
        (
            "rat(b) / rat(b + 1)",
            "    y = x / 7;\n    m.stdout <- String(y ^ (2^62)) else \"\";\n",
        ),
    ] {
        let out = rejected(&with_x(x, body));
        assert!(
            out.contains("Number too large for any memory of the target"),
            "{x}; {body}:\n{out}"
        );
    }
    // `3b / b` is 3, which builds nothing, and `b / 2b` is 1/2.
    for x in ["rat(3 * b) / rat(b)", "rat(b) / rat(2 * b)"] {
        assert_eq!(built(&x_pushed(x, "x ^ (2^64)")), None, "{x}");
    }
    // `b` is 0 mod 3 (`2^100` is 1 mod 3), so `b / 3` is an integer of 101 bits.
    let out = rejected(&x_pushed("rat(b) / 3", "x ^ (2^62)"));
    assert!(
        out.contains(
            "the numerator p of the base `x` is at least 2^100 in magnitude, so ⌊log₂ |p|⌋ \
             is 100\n"
        ) && !out.contains("denominator"),
        "{out}"
    );
}

#[test]
fn a_rat_base_the_text_does_not_fix_proves_nothing() {
    // A parameter, a value read from the input and a division by zero fix no value.
    let src = "f(x: rat) {\n    return x ^ (2^62);\n}\n\
               main(m: MainArgs) {\n    b = 5 * 2^100 + 1;\n    \
               m.stdout <- String(f(x: rat(b) / rat(b + 1))) else \"\";\n}\n";
    assert_eq!(built(src), None);
    let src = with_x(
        "rat(b) / rat(int(m.args[0] else \"\") else 1)",
        "    m.stdout <- String(x ^ (2^62)) else \"\";\n",
    );
    assert_eq!(built(&src), None);
    let src = with_x(
        "rat(b) / rat(b - b)",
        "    m.stdout <- String(x ^ (2^62)) else \"\";\n",
    );
    let out = built(&src).unwrap_or_default();
    assert!(!out.contains("Number too large"), "{out}");
}

/// `n` names after `x`, each `b` over the one before, so each is `x` or `1 / x` and has
/// parts of 103 bits, and a power of each past the address space.
fn chain(n: usize) -> String {
    let body: String = (0..n)
        .map(|i| {
            let prev = if i == 0 {
                "x".to_string()
            } else {
                format!("y{}", i - 1)
            };
            format!("    y{i} = rat(b) / {prev};\n    p{i} = y{i} ^ (2^62);\n")
        })
        .collect();
    with_x("rat(b) / rat(b + 1)", &body)
}

#[test]
fn reading_a_chain_of_names_and_divisions_scales() {
    // Each name is read once, however many powers read it: the chain of `n` names costs `n`
    // divisions of 103-bit numbers and `n` rejections.
    scaling::check(
        "a chain of n names and divisions, a power of each rejected",
        200,
        |n| {
            let out = rejected(&chain(n));
            assert_eq!(
                out.matches("Number too large for any memory of the target")
                    .count(),
                n
            );
        },
    );
}

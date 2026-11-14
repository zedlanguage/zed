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
        |                        ^^^^^^^^^^ [3, 4, 5]
        |                            ^^^^^^ [2]
  [3] 3:24: so `b ^ (2^64)` has at least 2^64 * 64 + 1 bits: |k| * ⌊log₂ |x|⌋ + 1 at the least |x| and |k|
  [4] 3:24: or read the exponent from the input: the run then stops if no memory holds the result
  [5] 3:24: or delete `b ^ (2^64)` if its result is not used
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
        |                        ^^^^^^^^^^^^^^^^ [3, 4, 5]
        |                                 ^^^^^^^ [2]
  [2] 3:33: the exponent k, `-(2^64)`, is at most -2^64
  [3] 3:24: so `rat(b) ^ -(2^64)` has at least 2^64 * 64 + 1 bits from the base's numerator: |k| * ⌊log₂ |p|⌋ + 1 at the least |p| and |k|
  [4] 3:24: or read the exponent from the input: the run then stops if no memory holds the result
  [5] 3:24: or delete `rat(b) ^ -(2^64)` if its result is not used
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
        |                        ^^^^^^^^^^ [3, 4, 5]
        |                            ^^^^^^ [2]
  [3] 4:24: so `x ^ (2^62)` has at least 2^62 * 102 + 1 bits from the base's numerator and 2^62 * 102 + 1 bits from the base's denominator: |k| * ⌊log₂ |p|⌋ + 1 at the least |p| and |k|
  [4] 4:24: or read the exponent from the input: the run then stops if no memory holds the result
  [5] 4:24: or delete `x ^ (2^62)` if its result is not used
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

// Products and quotients (plan row CONST-too-large-products). `b = 2^64 + 13` has 65 bits,
// so `b ^ (2^60)` has at least `2^66 + 1` bits, 8 EiB, and a product of two such factors at
// least `2^67 + 1`, past the 2^67 bits of the address space. Before, only `^` was bounded,
// and the row's program compiled; its run stopped with "Number too large for memory".

#[test]
fn a_product_past_the_address_space_is_rejected_with_its_least_size() {
    // The row's program: the first `*` is past the address space, and the second, whose
    // operand already is, is not reported again.
    let src = pushed("(b ^ (2^60)) * (b ^ (2^60)) * (b ^ (2^60))");
    assert_eq!(
        rejected(&src),
        r#"3:24: Number too large for any memory of the target: `(b ^ (2^60)) * (b ^ (2^60))` needs more than 16 EiB; Linux x86_64 addresses 16 EiB.
  [1] 3:24: `(b ^ (2^60))` has at least 2^66 + 1 bits
      3 |     m.stdout <- String((b ^ (2^60)) * (b ^ (2^60)) * (b ^ (2^60))) else "";
        |                        ^^^^^^^^^^^^ [1]
        |                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^ [3, 4, 5]
        |                                       ^^^^^^^^^^^^ [2]
  [2] 3:39: `(b ^ (2^60))` has at least 2^66 + 1 bits
  [3] 3:24: so `(b ^ (2^60)) * (b ^ (2^60))` has at least 2^67 + 1 bits: the bit lengths of the least |x| and |y| added, less one
  [4] 3:24: or read a factor from the input: the run then stops if no memory holds the result
  [5] 3:24: or delete `(b ^ (2^60)) * (b ^ (2^60))` if its result is not used"#
    );
}

#[test]
fn the_product_bound_is_exact_at_the_address_space() {
    // `b ^ (2^60)` times `b ^ k` has at least `2^66 + 64 * k + 1` bits: `k = 2^60 - 1` gives
    // `2^67 - 63`, which fit, and `k = 2^60` gives `2^67 + 1`.
    for product in [
        "(b ^ (2^60)) * (b ^ (2^60 - 1))",
        "(b ^ (2^60)) * (b ^ (2^59))",
        "(b ^ (2^60)) * b",
        "rat(b ^ (2^60)) * (rat(b) ^ (2^60 - 1))",
    ] {
        assert_eq!(built(&pushed(product)), None, "{product}");
    }
    for product in [
        "(b ^ (2^60)) * (b ^ (2^60))",
        "(b ^ (2^60 - 1)) * (b ^ (2^60 + 1))",
        "-(b ^ (2^60)) * (b ^ (2^60))",
        "(rat(b) ^ (2^60)) * (rat(b) ^ (2^60))",
    ] {
        let out = rejected(&pushed(product));
        let head = format!(
            "3:24: Number too large for any memory of the target: `{product}` needs more \
             than 16 EiB; Linux x86_64 addresses 16 EiB."
        );
        assert!(out.starts_with(&head), "{product}:\n{out}");
    }
}

#[test]
fn a_chain_of_names_and_products_is_rejected_where_it_passes() {
    // `x` has `2^65 + 1` bits, `y` `2^66 + 1`, `y * x` `2^66 + 2^65 + 1`, and `y * x * x`
    // `2^67 + 1`: the third `*` is rejected, through the names, and `y` is not.
    let src = "main(m: MainArgs) {\n    b = 2^64 + 13;\n    x = b ^ (2^59);\n    \
               y = x * x;\n    z = y * x * x;\n    m.stdout <- String(z) else \"\";\n}\n";
    let out = rejected(src);
    assert_eq!(
        out.matches("Number too large for any memory of the target")
            .count(),
        1,
        "{out}"
    );
    assert!(
        out.starts_with(
            "5:9: Number too large for any memory of the target: `y * x * x` needs more than \
             16 EiB; Linux x86_64 addresses 16 EiB."
        ) && out.contains("[2] 3:5: `x` has at least 2^65 + 1 bits\n"),
        "{out}"
    );
}

#[test]
fn a_quotient_past_the_address_space_is_rejected() {
    // `x / y` is `x` times the denominator of `y`, `2^67 + 1` bits; the numerator of `y` is 1,
    // so nothing cancels.
    let src = "main(m: MainArgs) {\n    b = 2^64 + 13;\n    x = rat(b) ^ (2^60);\n    \
               y = 1 / (rat(b) ^ (2^60));\n    m.stdout <- String(x / y) else \"\";\n}\n";
    assert_eq!(
        rejected(src),
        r#"5:24: Number too large for any memory of the target: `x / y` needs more than 16 EiB; Linux x86_64 addresses 16 EiB.
  [1] 3:5: `x` has at least 2^66 + 1 bits
      3 |     x = rat(b) ^ (2^60);
        |     ^^^^^^^^^^^^^^^^^^^^
  [2] 4:5: `y` has a denominator of at least 2^66 + 1 bits
      4 |     y = 1 / (rat(b) ^ (2^60));
        |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
  [3] 5:24: so `x / y` has at least 2^67 + 1 bits: the bit lengths of the least numerator of x and denominator of y added, less one
      5 |     m.stdout <- String(x / y) else "";
        |                        ^^^^^
  [4] 5:24: or read a factor from the input: the run then stops if no memory holds the result
  [5] 5:24: or delete `x / y` if its result is not used"#
    );
}

#[test]
fn a_product_or_quotient_that_may_cancel_or_build_nothing_proves_nothing() {
    // `x / x` is 1 and `x * (1 / x)` is 1: the kernel reduces by a gcd the text does not
    // prove 1, so the factors' sizes bound nothing (GMP's `mpq_div` cancels it before it
    // multiplies). A factor kept as prime powers, a factor that may be 0 and one the text
    // does not fix prove nothing either.
    let src = |x: &str, out: &str| {
        format!(
            "main(m: MainArgs) {{\n    b = 2^64 + 13;\n    \
             k = int(m.args[0] else \"\") else 0;\n    x = {x};\n    \
             m.stdout <- String(({out}) + rat(k)) else \"\";\n}}\n"
        )
    };
    for (x, out) in [
        ("rat(b) ^ (2^60)", "x / x"),
        ("rat(b) ^ (2^59)", "(x * x) / (x * x)"),
        ("rat(b) ^ (2^60)", "x * (1 / x)"),
        ("rat(3) ^ (2^100)", "x * x * x"),
        ("rat(2) ^ (2^70)", "x * (rat(b) ^ (2^60))"),
        ("rat(b) ^ (2^60)", "x * (rat(b) ^ k)"),
        ("rat(b) ^ (2^60)", "x * rat(k) * x"),
        ("rat(b) ^ (2^60)", "x * (x - x)"),
        // The roots `b` and `c` of the two numerators are each the other's denominator: the
        // product is `(b / c) ^ (2^60 - 1)` and fits.
        (
            "rat(b) ^ (2^60) / rat(2^64 + 15)",
            "x * (rat(2^64 + 15) ^ (2^60) / rat(b))",
        ),
        // `x` keeps 3 as a power, and `3^41`, of 65 bits, is a power of 3: the kernel moves
        // the factors of 3 out of the result's coefficient, which then has `2^66 + 1` bits.
        (
            "rat(3) ^ (2^70) * (rat(b) ^ (2^60))",
            "x * (rat(3^41) ^ (2^60))",
        ),
    ] {
        let program = src(x, out);
        assert_eq!(built(&program), None, "{x}; {out}");
    }
}

// Plan row CONST-too-large-products-unproved: products and quotients the bound left to the run
// before, each a test that failed then (the program compiled). `b = 2^64 + 13` and
// `c = 2^64 + 15` share no factor, so `b ^ (2^60)` has `2^66 + 1` bits and nothing cancels
// between it and a power of `c`.

/// `main` with `b`, `c`, the bindings `lets` and `String(<out>)` pushed to standard output.
fn bc_pushed(lets: &str, out: &str) -> String {
    format!(
        "main(m: MainArgs) {{\n    b = 2^64 + 13;\n    c = 2^64 + 15;\n{lets}    \
         m.stdout <- String({out}) else \"\";\n}}\n"
    )
}

#[test]
fn a_product_of_rats_whose_wide_parts_share_no_factor_is_rejected() {
    // (a) The numerator of `x` is `b ^ (2^60)` and its denominator `c`: `x * x` and `x / z`
    // multiply a power of `b` by a power of `c` across the fraction, and the gcd of the fixed
    // bases, 1, proves nothing cancels.
    let lets = "    x = rat(b) ^ (2^60) / rat(c);\n    z = rat(c) / (rat(b) ^ (2^60));\n";
    for out in ["x * x", "x / z", "x * (rat(b) ^ (2^60) / rat(c))"] {
        let src = bc_pushed(lets, out);
        let got = rejected(&src);
        assert!(
            got.starts_with(&format!(
                "6:24: Number too large for any memory of the target: `{out}` needs more than \
                 16 EiB; Linux x86_64 addresses 16 EiB."
            )),
            "{out}:\n{got}"
        );
    }
    assert_eq!(
        rejected(&bc_pushed(lets, "x * x")),
        r#"6:24: Number too large for any memory of the target: `x * x` needs more than 16 EiB; Linux x86_64 addresses 16 EiB.
  [1] 4:5: `x` has a numerator of at least 2^66 + 1 bits and a denominator of at least 65 bits
      4 |     x = rat(b) ^ (2^60) / rat(c);
        |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [2] 4:5: `x` has a numerator of at least 2^66 + 1 bits and a denominator of at least 65 bits
  [3] 6:24: so `x * x` has a numerator of at least 2^67 + 1 bits and a denominator of at least 129 bits: for each part, the bit lengths of the least parts it multiplies added, less one: numerator by numerator and denominator by denominator, where neither numerator shares a factor with the other operand's denominator
      6 |     m.stdout <- String(x * x) else "";
        |                        ^^^^^
  [4] 6:24: or read a factor from the input: the run then stops if no memory holds the result
  [5] 6:24: or delete `x * x` if its result is not used"#
    );
}

#[test]
fn a_product_whose_operand_keeps_prime_powers_is_rejected_where_none_divides_the_other() {
    // (b) `2^(2^70)` is kept as a power of 2 and builds nothing, so `x` holds `b ^ (2^60)` as
    // its coefficient and 2 as a kept prime; `b` is odd, so the kernel moves nothing out of
    // the product's coefficient, `2^67 + 1` bits.
    for (lets, out) in [
        ("    x = 2^(2^70) * (b ^ (2^60));\n", "x * (b ^ (2^60))"),
        ("", "(2^(2^70) * (b ^ (2^60))) * (b ^ (2^60))"),
        (
            "    x = rat(2) ^ (2^70) * (rat(b) ^ (2^60));\n",
            "x * (rat(b) ^ (2^60) / rat(2) ^ (2^70))",
        ),
        (
            "    x = rat(3) ^ (2^70) / (rat(c) ^ (2^60));\n",
            "x / (rat(c) ^ (2^60))",
        ),
    ] {
        let got = rejected(&bc_pushed(lets, out));
        let line = if lets.is_empty() { 4 } else { 5 };
        assert!(
            got.starts_with(&format!(
                "{line}:24: Number too large for any memory of the target: `{out}` needs more \
                 than 16 EiB; Linux x86_64 addresses 16 EiB."
            )),
            "{out}:\n{got}"
        );
    }
}

#[test]
fn a_power_of_a_base_the_types_bound_is_rejected() {
    // (c) `x * x` has `2^66 + 1` bits, so its square has at least `2 * 2^66 + 1`, past the
    // address space; the base is not a number the text fixes, but its least size is proved.
    let lets = "    x = b ^ (2^59);\n";
    for out in [
        "(x * x) ^ 2",
        "(b ^ (2^60)) ^ 2",
        "(rat(b) ^ (2^60) / rat(c)) ^ -2",
    ] {
        let got = rejected(&bc_pushed(lets, out));
        assert!(
            got.starts_with(&format!(
                "5:24: Number too large for any memory of the target: `{out}` needs more than \
                 16 EiB; Linux x86_64 addresses 16 EiB."
            )),
            "{out}:\n{got}"
        );
    }
    assert_eq!(
        rejected(&bc_pushed(lets, "(x * x) ^ 2")),
        r#"5:24: Number too large for any memory of the target: `(x * x) ^ 2` needs more than 16 EiB; Linux x86_64 addresses 16 EiB.
  [1] 5:24: the base x, `(x * x)`, is at least 2^(2^66) in magnitude, so ⌊log₂ |x|⌋ is at least 2^66
      5 |     m.stdout <- String((x * x) ^ 2) else "";
        |                        ^^^^^^^ [1]
        |                        ^^^^^^^^^^^ [3, 4, 5]
        |                                  ^ [2]
  [2] 5:34: the exponent k, `2`, is at least 2
  [3] 5:24: so `(x * x) ^ 2` has at least 2 * 2^66 + 1 bits: |k| * ⌊log₂ |x|⌋ + 1 at the least |x| and |k|
  [4] 5:24: or read the exponent from the input: the run then stops if no memory holds the result
  [5] 5:24: or delete `(x * x) ^ 2` if its result is not used"#
    );
    // Within the address space, or with a base whose size the text does not prove.
    for out in [
        "(x * x) ^ 1",
        "x ^ 3",
        "(rat(x) / rat(x)) ^ 2",
        "(x * (int(m.args[0] else \"\") else 0)) ^ 2",
        "rat(x * x) ^ (int(m.args[0] else \"\") else 0)",
    ] {
        assert_eq!(built(&bc_pushed(lets, out)), None, "{out}");
    }
}

#[test]
fn a_product_in_a_branch_not_taken_is_rejected() {
    let src = "main(m: MainArgs) {\n    k = int(m.args[0] else \"\") else 0;\n    \
               b = 2^64 + 13;\n    \
               m.stdout <- if k > 5 { String((b ^ (2^60)) * (b ^ (2^60))) } else { \"few\" };\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "4:35: Number too large for any memory of the target: `(b ^ (2^60)) * (b ^ (2^60))` \
             needs more than 16 EiB; Linux x86_64 addresses 16 EiB."
        ),
        "{out}"
    );
}

/// `n` names, each 7 times the one before, from `x = b ^ (2^59)`, and a product of each with
/// `x` three times, past the address space.
fn product_chain(n: usize) -> String {
    let body: String = (0..n)
        .map(|i| {
            let prev = if i == 0 {
                "x".to_string()
            } else {
                format!("y{}", i - 1)
            };
            format!("    y{i} = {prev} * 7;\n    p{i} = y{i} * x * x * x;\n")
        })
        .collect();
    format!("main(m: MainArgs) {{\n    b = 2^64 + 13;\n    x = b ^ (2^59);\n{body}}}\n")
}

#[test]
fn bounding_a_chain_of_products_scales() {
    // Each name is read once, however many products read through it: the chain of `n` names
    // costs O(n) reads of bit lengths and `n` rejections, each at the third `*` of its line.
    scaling::check(
        "a chain of n names and products, a product of each rejected",
        200,
        |n| {
            let out = rejected(&product_chain(n));
            assert_eq!(
                out.matches("Number too large for any memory of the target")
                    .count(),
                n
            );
        },
    );
}

/// `n` names, each the one before times `rat(b)`, from `x = rat(b) ^ (2^59) / rat(c)`, and
/// for each a product with `x` three times and the square of a product with `x`, both past
/// the address space.
fn rat_product_chain(n: usize) -> String {
    let body: String = (0..n)
        .map(|i| {
            let prev = if i == 0 {
                "x".to_string()
            } else {
                format!("y{}", i - 1)
            };
            format!(
                "    y{i} = {prev} * rat(b);\n    p{i} = y{i} * x * x * x;\n    \
                 q{i} = (y{i} * x) ^ 2;\n"
            )
        })
        .collect();
    format!(
        "main(m: MainArgs) {{\n    b = 2^64 + 13;\n    c = 2^64 + 15;\n    \
         x = rat(b) ^ (2^59) / rat(c);\n{body}}}\n"
    )
}

#[test]
fn bounding_a_chain_of_rat_products_scales() {
    // Plan row CONST-too-large-products-unproved, cases (a) and (c): each name keeps `b` as
    // the root of its numerator and `c` as that of its denominator, so each `*` costs at most
    // six gcds of 65-bit numbers, not a gcd of the whole chain's product: O(n) in all, and
    // `2n` rejections.
    scaling::check(
        "a chain of n rat names, a product and a power of each rejected",
        200,
        |n| {
            let out = rejected(&rat_product_chain(n));
            assert_eq!(
                out.matches("Number too large for any memory of the target")
                    .count(),
                2 * n
            );
        },
    );
}

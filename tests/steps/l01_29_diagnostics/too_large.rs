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

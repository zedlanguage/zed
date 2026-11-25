//! An operation that builds a number larger than the target's address space is rejected at
//! compile time (plan rows CONST-too-large and CONST-too-large-kept-powers, QUESTIONS A100;
//! DESIGN sec:checking_in_zed and the sec:diagnostics row "Number too large for any memory of
//! the target"), and nothing is built. Before, `String(b ^ (2^64))` with `b = 2^64 + 13`
//! compiled and the run stopped with "Number too large for memory".
//!
//! Since KEPT-power-form (DESIGN.md steps L1.17b and L1.17c) a power of a base wider than 64
//! bits is kept as a wide atom with its exponent, as a power of a smaller base is kept as prime
//! powers: `b ^ (2^64)` alone, a product of such powers and a comparison of them build
//! nothing and compile. What writes the power out is rejected: printing it, sized by a lower
//! bound on its digits, and a sum, sized by its part above the atoms its operands share.
//! Before, the power itself was rejected, at `k * ⌊log₂ |x|⌋ + 1` bits for `x ^ k`. Left to
//! plan row CONST-kept-sizes: a sum or print of `x ^ k` whose base only the types bound, and
//! the repair that makes an operand smaller.

use zedc::build::Build;
use zedc::run::load_for;

/// The program `src` built for Linux x86_64: its rendered diagnostics, or `None` when it
/// compiles.
///
/// These tests are of the bound of the address space, 2^64 bytes. Since zed 21e7335 (plan row
/// CONST-default-memory-limit) a `main` without `@limits(memory: …)` also rejects a build of
/// 1 GiB or more, so a program here that declares no limit is given the largest one,
/// `@limits(memory: 2^64)`, which leaves the address space as the only bound, as it was when
/// these tests were written. It is written on `main`'s line so that every line and column the
/// tests expect stays as it was. The default limit is tested in
/// `l01_29_diagnostics::main_limits::without_a_memory_limit_a_build_of_1_gib_or_more_is_rejected`.
pub(super) fn built(src: &str) -> Option<String> {
    let build = Build::default().for_target("x86_64-linux");
    let src = match src.contains("@limits") {
        true => src.to_owned(),
        false => src.replacen(
            "main(m: MainArgs)",
            "@limits(memory: 2^64) main(m: MainArgs)",
            1,
        ),
    };
    load_for(src.as_bytes(), &build).err()
}

/// The rendered diagnostics of `src`, which the checker rejects.
pub(super) fn rejected(src: &str) -> String {
    built(src).unwrap_or_else(|| panic!("accepted:\n{src}"))
}

/// `main` pushing `String(<power>)` to standard output, after `b = 2^64 + 13;`.
fn pushed(power: &str) -> String {
    format!("main(m: MainArgs) {{\n    b = 2^64 + 13;\n    m.stdout <- String({power});\n}}\n")
}

#[test]
fn a_power_of_a_wide_base_is_kept_and_printing_it_is_rejected_with_its_least_size() {
    // A100's first program, `String(b ^ (2^64))`: its text has at least
    // 355,393,490,465,494,856,472 digits, `⌊2^64 * log₁₀ b⌋ + 1`, 308 EiB (DESIGN.md step
    // L1.17c). The power alone is the atom `b` with the exponent `2^64`, and a comparison of it
    // reads its logarithm: both build nothing.
    assert_eq!(built(&pushed("b ^ (2^64) > 0")), None);
    assert_eq!(
        built("main(m: MainArgs) {\n    x = (2^64 + 13) ^ (2^64);\n}\n"),
        None
    );
    assert_eq!(rejected(&pushed("b ^ (2^64)")), PRINTED);
}

/// The rejection of `String(b ^ (2^64))`.
const PRINTED: &str = r#"3:17: Number too large for any memory of the target: `String(b ^ (2^64))` needs at least 308 EiB; Linux x86_64 addresses 16 EiB.
  [1]  3:24: this `^` gives int
       3 |     m.stdout <- String(b ^ (2^64));
         |                 ^^^^^^^^^^^^^^^^^^ [12, 13, 14]
         |                        ^ [2]  ^^ [11]
         |                            ^^^^^^ [9]
         |                             ^ [10]
         |                        ^--------^ [1]
  [2]  3:24: `b` is int here
  [3]  2:9: `b` is defined as this expression, int
       2 |     b = 2^64 + 13;
         |         ^ [6]  ^^ [8]
         |         ^^^^ [5]
         |         ^^^^^^^^^ [3, 4]
         |           ^^ [7]
  [4]  2:9: this `+` adds integer literals alone, so it is a literal too; nothing here gives it a carrier, so it is an `int`
  [5]  2:9: this `^` takes a power of integer literals alone, so it is a literal too; nothing here gives it a carrier, so it is an `int`
  [6]  2:9: this literal, 2, is 2
  [7]  2:11: this literal, 64, is 64
  [8]  2:16: this literal, 13, is 13
  [9]  3:28: this `^` gives 2^64
  [10] 3:29: this literal, 2, is 2
  [11] 3:31: this literal, 64, is 64
  [12] 3:17: `String(b ^ (2^64))` asks for at least 2^71 bits: printing a number writes all of its digits, a byte each
  [13] 3:17: or read an operand from the input: the run then stops if no memory holds what it writes out
  [14] 3:17: or delete `String(b ^ (2^64))` if its result is not used"#;

#[test]
fn a_sum_that_writes_out_a_power_of_a_wide_base_is_rejected_with_its_least_size() {
    // DESIGN.md step L1.17c: `b ^ (2^64) + 1` builds the power, `2^64 * 64` bits and more,
    // 128 EiB.
    let out = rejected(&pushed("b ^ (2^64) + 1 > 0"));
    assert!(
        out.starts_with(
            "3:24: Number too large for any memory of the target: `b ^ (2^64) + 1` needs at \
             least 128 EiB; Linux x86_64 addresses 16 EiB."
        ) && out.contains("a sum writes out in full its part above the powers"),
        "{out}"
    );
    // The atom both operands share is not written out: `b ^ (2^64) + b ^ (2^64)` is
    // `2 * b ^ (2^64)`, and `b ^ (2^64) - b ^ (2^64)` is 0.
    for same in [
        "b ^ (2^64) + b ^ (2^64) > 0",
        "b ^ (2^64) - b ^ (2^64) == 0",
    ] {
        assert_eq!(built(&pushed(same)), None, "{same}");
    }
}

/// `main` reading `k` from the input and, under `test`, writing whether `sum` is positive.
fn k_sum(test: &str, sum: &str) -> String {
    format!(
        "main(m: MainArgs) {{\n    k = int(m.args[0] else #outOfBounds -> \"\") else \
         #invalid -> 0;\n    m.stdout <- if {test} {{ String({sum} > 0) }} else {{ \"\" }};\n}}\n"
    )
}

#[test]
fn a_sum_beside_an_int_bounded_away_from_0_is_rejected() {
    // Plan row CONST-build-typed-operands: `k` comes from the input, but in `1..=5` (or
    // `-5..=-1`) it shares at most `2^2` with `2^(2^70)`, so the sum writes out at least
    // `2^70 - 21` bits whatever `k` is (`Rat::sum_least_beside`). Before, it compiled and the
    // run stopped with "Number too large for memory".
    for (test, sum) in [
        ("k >= 1 && k <= 5", "2^(2^70) + k"),
        ("k >= 1 && k <= 5", "k + 2^(2^70)"),
        ("k >= -5 && k <= -1", "2^(2^70) - k"),
        ("k >= 1 && k <= 5", "3^(2^70) + k"),
    ] {
        let out = rejected(&k_sum(test, sum));
        assert!(
            out.contains(&format!(
                "Number too large for any memory of the target: `{sum}` needs at least"
            )) && out.contains("or let `k` be 0 here"),
            "{sum}:\n{out}"
        );
    }
    // Where `k` may be 0 the sum may be `2^(2^70)` itself, which builds nothing; where `k`
    // has no bound it may share any power of 2; a fixed power of `2^60` bits is within the
    // address space: all are left to the run.
    for (test, sum) in [
        ("k >= 0 && k <= 5", "2^(2^70) + k"),
        ("k >= 1", "2^(2^70) + k"),
        ("k >= 1 && k <= 5", "2^(2^60) + k"),
    ] {
        assert_eq!(built(&k_sum(test, sum)), None, "{test}: {sum}");
    }
}

#[test]
fn a_power_in_a_branch_not_taken_is_rejected() {
    // A100's third program, printed and summed: the bound holds whether or not the branch
    // runs.
    for (write, head) in [
        (
            "String((2^64 + 13) ^ (2^64))",
            "3:28: Number too large for any memory of the target: `String((2^64 + 13) ^ \
             (2^64))` needs at least 308 EiB; Linux x86_64 addresses 16 EiB.",
        ),
        (
            "String((2^64 + 13) ^ (2^64) + 1 > 0)",
            "3:35: Number too large for any memory of the target: `(2^64 + 13) ^ (2^64) + 1` \
             needs at least 128 EiB; Linux x86_64 addresses 16 EiB.",
        ),
    ] {
        let src = format!(
            "main(m: MainArgs) {{\n    k = int(m.args[0] else #outOfBounds -> \"\") else \
             #invalid -> 0;\n    m.stdout <- if k > 5 {{ {write} }} else {{ \"few\" }};\n}}\n"
        );
        let out = rejected(&src);
        assert!(out.starts_with(head), "{out}");
    }
}

#[test]
fn a_power_whose_size_depends_on_the_input_compiles() {
    // A100's second program, `grow`: `2^k` may be 0 or 1, so nothing is proved.
    let src = "grow(k: int) {\n    return if k >= 0 { 2r^(2^k) } else { 0r };\n}\n\
               main(m: MainArgs) {\n    k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n    \
               m.stdout <- String(grow(k: k));\n}\n";
    assert_eq!(built(src), None);
    // An exponent read from the input, 2^64 when there is none: the types allow 0, so the
    // run decides (sites.rs, `a_power_too_large_is_named_as_written_with_its_size`).
    for base in ["b", "rat(b)"] {
        let src = format!(
            "main(m: MainArgs) {{\n    b = 2^64 + 13;\n    \
             k = 2^64 + (int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0);\n    \
             m.stdout <- if k >= 0 {{ String({base} ^ k) }} else {{ \"\" }};\n}}\n"
        );
        assert_eq!(built(&src), None, "{base}");
    }
}

#[test]
fn the_bound_is_exact_at_the_address_space() {
    // `b` has 65 bits, so the sum writes out `b ^ k`, at least `64 * k` bits, beside a bit
    // for each of the two coefficients, 1 and 1 (`Rat::sum_least`); 2^64 bytes are 2^67 bits.
    // `k = 2^61 - 1` gives `2^67 - 62` bits, which fit; `k = 2^61` gives `2^67 + 2`.
    for power in [
        "b ^ (2^61 - 1)",
        "rat(b) ^ (2^61 - 1)",
        "b ^ (2^60)",
        "b ^ 1000",
    ] {
        let sum = format!("{power} + 1 > 0");
        assert_eq!(built(&pushed(&sum)), None, "{sum}");
    }
    for power in ["b ^ (2^61)", "rat(b) ^ (2^61)"] {
        let out = rejected(&pushed(&format!("{power} + 1 > 0")));
        let head = format!(
            "3:24: Number too large for any memory of the target: `{power} + 1` needs more \
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
    // `1 / b ^ (2^64)` keeps the atom `b` with the exponent `-(2^64)`: its text writes the
    // denominator's digits, and a sum writes the denominator out.
    assert_eq!(built(&pushed("rat(b) ^ -(2^64) > 0")), None);
    for (write, head) in [
        (
            "rat(b) ^ -(2^64)",
            "3:17: Number too large for any memory of the target: `String(rat(b) ^ -(2^64))` \
             needs at least 308 EiB; Linux x86_64 addresses 16 EiB.",
        ),
        (
            "rat(b) ^ -(2^64) + 1 > 0",
            "3:24: Number too large for any memory of the target: `rat(b) ^ -(2^64) + 1` needs \
             at least 128 EiB; Linux x86_64 addresses 16 EiB.",
        ),
    ] {
        let out = rejected(&pushed(write));
        assert!(out.starts_with(head), "{write}:\n{out}");
    }
}

/// The base of a too-large power written as a cast of a name says where its value came from,
/// through a chain of names (row MSG-too-large-cast-origin; DESIGN.md sec:diagnostics, row
/// "Number too large for any memory of the target": the least `|x|` and `k` "each with where it
/// came from, the literal or the declaration"). Before, no note pointed at a binding.
#[test]
fn a_cast_base_names_the_bindings_it_reads() {
    let src = "main(m: MainArgs) {\n    a = 2^64 + 13;\n    b = a;\n    m.stdout <- String(rat(b) ^ (2^64));\n}\n";
    let out = rejected(src);
    assert!(
        out.contains("4:17: Number too large for any memory of the target"),
        "{out}"
    );
    // Since KEPT-power-form the notes are the derivation of the operand's type, which reads
    // through both names to their expressions (the wording "bound here to" of the old power
    // bound is left to plan row CONST-kept-sizes).
    assert!(
        out.contains("3:9: `b` is defined as this expression"),
        "{out}"
    );
    assert!(
        out.contains("2:9: `a` is defined as this expression"),
        "{out}"
    );
}

/// `n` bindings, each a sum that writes out a power past the address space.
pub(super) fn powers(n: usize) -> String {
    (0..n)
        .map(|i| format!("x{i} = (2^64 + 13) ^ (2^64 + {i}) + 1;\n"))
        .collect()
}

/// `main` binding `b = 5 * 2^100 + 1` (103 bits) and `x` to `rat`, then the lines `body`
/// (plan row CONST-too-large-rat-names).
fn with_x(x: &str, body: &str) -> String {
    format!("main(m: MainArgs) {{\n    b = 5 * 2^100 + 1;\n    x = {x};\n{body}}}\n")
}

#[test]
fn a_rat_base_fixed_through_a_name_and_a_division_is_rejected() {
    // The row's program. Before, it compiled and the run stopped with "Number too large for
    // memory" (103 EiB). Both parts of `b / (b + 1)` have 103 bits and are kept as atoms, so
    // `x ^ (2^62)` alone builds nothing, and printing it writes the digits of both parts.
    let src = |out: &str| with_x("rat(b) / rat(b + 1)", &format!("    m.stdout <- {out};\n"));
    assert_eq!(built(&src("String(x ^ (2^62) > 0)")), None);
    assert_eq!(rejected(&src("String(x ^ (2^62))")), RAT_PRINTED);
}

/// The rejection of `String(x ^ (2^62))` for `x = rat(b) / rat(b + 1)`.
/// Both parts have about `2^62 * 30.8` digits, 246 EiB together; the least bound says 245.
const RAT_PRINTED: &str = r#"4:17: Number too large for any memory of the target: `String(x ^ (2^62))` needs at least 245 EiB; Linux x86_64 addresses 16 EiB.
  [1]  4:24: this `^` gives rat
       4 |     m.stdout <- String(x ^ (2^62));
         |                 ^^^^^^^^^^^^^^^^^^ [22, 23, 24]
         |                        ^ [2]  ^^ [21]
         |                            ^^^^^^ [19]
         |                             ^ [20]
         |                        ^--------^ [1]
  [2]  4:24: `x` is rat here
  [3]  3:9: `x` is defined as this expression, rat
       3 |     x = rat(b) / rat(b + 1);
         |         ^^^^^^ [5]   ^^^^^ [16]
         |         ^^^^^^^^^^^^^^^^^^^ [3, 4]
         |             ^ [6]    ^ [17]
         |                          ^ [18]
         |                  ^--------^ [15]
  [4]  3:9: this `/` gives rat
  [5]  3:9: this call of `rat` gives rat \ 0r
  [6]  3:13: `b` is int here
  [7]  2:9: `b` is defined as this expression, int
       2 |     b = 5 * 2^100 + 1;
         |         ^ [10]      ^ [14]
         |         ^^^^^^^^^^^^^ [7, 8]
         |             ^ [12]
         |             ^^^^^ [11]
         |               ^^^ [13]
         |         ^-------^ [9]
  [8]  2:9: this `+` adds integer literals alone, so it is a literal too; nothing here gives it a carrier, so it is an `int`
  [9]  2:9: this `*` multiplies integer literals alone, so it is a literal too; nothing here gives it a carrier, so it is an `int`
  [10] 2:9: this literal, 5, is 5
  [11] 2:13: this `^` takes a power of integer literals alone, so it is a literal too; nothing here gives it a carrier, so it is an `int`
  [12] 2:13: this literal, 2, is 2
  [13] 2:15: this literal, 100, is 100
  [14] 2:21: this literal, 1, is 1
  [15] 3:18: this call of `rat` gives rat \ 0r
  [16] 3:22: this `+` gives int
  [17] 3:22: `b` is int here
  [18] 3:26: this literal, 1, is 1
  [19] 4:28: this `^` gives 4611686018427387904
  [20] 4:29: this literal, 2, is 2
  [21] 4:31: this literal, 62, is 62
  [22] 4:17: `String(x ^ (2^62))` asks for at least 2^70 bits: printing a number writes all of its digits, a byte each
  [23] 4:17: or read an operand from the input: the run then stops if no memory holds what it writes out
  [24] 4:17: or delete `String(x ^ (2^62))` if its result is not used"#;

/// The `else` a push of a value that may be `#divByZero` ends with: DESIGN.md sec:failure
/// (QUESTIONS A113), every `else` names the atoms it takes, and a value with no atom takes
/// none, so the other pushes end with no `else`.
const DZ: &str = " else #divByZero -> \"\"";

/// `with_x(x, …)` pushing `String(<power>)` to standard output, then `tail`.
fn x_pushed(x: &str, power: &str, tail: &str) -> String {
    with_x(x, &format!("    m.stdout <- String({power}){tail};\n"))
}

#[test]
fn both_parts_of_a_rat_base_count() {
    // A sum with 1 writes out both parts of `x ^ k`. With both parts of 103 bits, kept as
    // atoms of 102 and 103 bits beside the prime 2, that is at least `k * 203` bits: `2^59`
    // fits (12.7 EiB) and `2^60` does not (25.4 EiB). With the denominator 7, only the
    // numerator is written out, `k * 102` bits: `2^60` fits (12.75 EiB) and `2^61` does not
    // (25.5 EiB and a few bits, which the message rounds to 26). A
    // negative power of `x` may divide by zero, as the types do not prove `x` is not 0.
    let both = "rat(b) / rat(b + 1)";
    let one = "rat(b) / 7";
    for (x, power, tail) in [
        (both, "x ^ (2^59)", ""),
        (one, "x ^ (2^60)", ""),
        (one, "x ^ -(2^60)", DZ),
    ] {
        let sum = format!("{power} + 1 > 0");
        assert_eq!(built(&x_pushed(x, &sum, tail)), None, "{x}; {sum}");
    }
    for (x, power, tail, eib) in [
        (both, "x ^ (2^60)", "", 25),
        (one, "x ^ (2^61)", "", 26),
        (one, "x ^ -(2^61)", DZ, 26),
    ] {
        let out = rejected(&x_pushed(x, &format!("{power} + 1 > 0"), tail));
        let head = format!(
            "4:24: Number too large for any memory of the target: `{power} + 1` needs at least \
             {eib} EiB; Linux x86_64 addresses 16 EiB."
        );
        assert!(out.starts_with(&head), "{x}; {power}:\n{out}");
    }
}

#[test]
fn a_rat_base_is_read_through_names_and_operations() {
    // A name bound to a name, a negation, a sum, a product and a quotient of `rat`s: each is
    // the kernel's value, so a quotient whose parts reduce is read reduced.
    for (x, body) in [
        (
            "rat(b) / rat(b + 1)",
            "    y = x;\n    z = -y;\n    m.stdout <- String(z ^ (2^62) + 1 > 0);\n",
        ),
        (
            "rat(b) * rat(b)",
            "    m.stdout <- String(x ^ (2^60) + 1 > 0);\n",
        ),
        (
            "rat(b) + 1 / 3",
            "    m.stdout <- String((x - 1) ^ (2^62) + 1 > 0);\n",
        ),
        (
            "rat(b) / rat(b + 1)",
            "    y = x / 7;\n    m.stdout <- String(y ^ (2^62) + 1 > 0);\n",
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
        assert_eq!(built(&x_pushed(x, "x ^ (2^64)", "")), None, "{x}");
    }
    // `b` is 0 mod 3 (`2^100` is 1 mod 3), so `b / 3` is an integer of 101 bits, and
    // `x ^ (2^62) + 1` writes out at least `2^62 * 100` bits, 50 EiB.
    let out = rejected(&x_pushed("rat(b) / 3", "x ^ (2^62) + 1 > 0", ""));
    assert!(
        out.contains("`x ^ (2^62) + 1` needs at least 50 EiB"),
        "{out}"
    );
}

#[test]
fn a_rat_base_the_text_does_not_fix_proves_nothing() {
    // A parameter, a value read from the input and a division by zero fix no value.
    let src = "f(x: rat) {\n    return x ^ (2^62);\n}\n\
               main(m: MainArgs) {\n    b = 5 * 2^100 + 1;\n    \
               m.stdout <- String(f(x: rat(b) / rat(b + 1)));\n}\n";
    assert_eq!(built(src), None);
    let src = with_x(
        "rat(b) / rat(int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 1)",
        "    m.stdout <- String(x ^ (2^62)) else #divByZero -> \"\";\n",
    );
    assert_eq!(built(&src), None);
    let src = with_x(
        "rat(b) / rat(b - b)",
        "    m.stdout <- String(x ^ (2^62)) else #divByZero -> \"\";\n",
    );
    let out = built(&src).unwrap_or_default();
    assert!(!out.contains("Number too large"), "{out}");
}

/// `n` names after `x`, each `b` over the one before, so each is `x` or `1 / x` and has
/// parts of 103 bits, and a sum that writes out a power of each past the address space.
pub(super) fn chain(n: usize) -> String {
    let body: String = (0..n)
        .map(|i| {
            let prev = if i == 0 {
                "x".to_string()
            } else {
                format!("y{}", i - 1)
            };
            format!("    y{i} = rat(b) / {prev};\n    p{i} = y{i} ^ (2^62) + 1;\n")
        })
        .collect();
    with_x("rat(b) / rat(b + 1)", &body)
}

// Products and quotients (plan row CONST-too-large-products). `b = 2^64 + 13` has 65 bits,
// so `b ^ (2^60)` written out has at least `2^66` bits, 8 EiB, and a product of two such
// factors at least `2^67`, the 2^67 bits of the address space. Since KEPT-power-form a product
// of powers of `b` is the atom `b` with the sum of the exponents and builds nothing; a sum
// with 1 writes it out. Before, the product itself was rejected.

#[test]
fn a_product_of_kept_powers_builds_nothing_and_a_sum_that_writes_it_out_is_rejected() {
    // The row's program: the product compiles, and its sum with 1 is rejected once, at the
    // sum.
    let product = "(b ^ (2^60)) * (b ^ (2^60)) * (b ^ (2^60))";
    assert_eq!(built(&pushed(&format!("{product} > 0"))), None);
    let out = rejected(&pushed(&format!("{product} + 1 > 0")));
    assert!(
        out.starts_with(&format!(
            "3:24: Number too large for any memory of the target: `{product} + 1` needs at \
             least 24 EiB; Linux x86_64 addresses 16 EiB."
        )) && out.matches("Number too large").count() == 1,
        "{out}"
    );
    // Row CONST-too-large-products-fix (d501ac3f6) rejected `(b ^ (2^60)) * (b ^ (2^60)) > 0`
    // with the first power lowered as a repair; that product is now kept and compiles.
    assert_eq!(built(&pushed("(b ^ (2^60)) * (b ^ (2^60)) > 0")), None);
}

#[test]
fn the_product_bound_is_exact_at_the_address_space() {
    // `b ^ (2^60)` times `b ^ k` is `b ^ (2^60 + k)`, and its sum with 1 writes out at least
    // `64 * (2^60 + k) + 2` bits: `k = 2^60 - 1` gives `2^67 - 62`, which fit, and `k = 2^60`
    // gives `2^67 + 2`.
    for product in [
        "(b ^ (2^60)) * (b ^ (2^60 - 1))",
        "(b ^ (2^60)) * (b ^ (2^59))",
        "(b ^ (2^60)) * b",
        "rat(b ^ (2^60)) * (rat(b) ^ (2^60 - 1))",
    ] {
        let sum = format!("{product} + 1 > 0");
        assert_eq!(built(&pushed(&sum)), None, "{sum}");
    }
    for product in [
        "(b ^ (2^60)) * (b ^ (2^60))",
        "(b ^ (2^60 - 1)) * (b ^ (2^60 + 1))",
        "-(b ^ (2^60)) * (b ^ (2^60))",
        "(rat(b) ^ (2^60)) * (rat(b) ^ (2^60))",
    ] {
        assert_eq!(built(&pushed(&format!("{product} > 0"))), None, "{product}");
        let out = rejected(&pushed(&format!("{product} + 1 > 0")));
        let head = format!(
            "3:24: Number too large for any memory of the target: `{product} + 1` needs more \
             than 16 EiB; Linux x86_64 addresses 16 EiB."
        );
        assert!(out.starts_with(&head), "{product}:\n{out}");
    }
}

#[test]
fn a_chain_of_names_and_products_is_rejected_where_it_passes() {
    // `x` is `b ^ (2^59)`, `y` `b ^ (2^60)` and `z` `b ^ (2^61)`: none is written out, and
    // `z + 1` writes out `2^67 + 2` bits, past the address space, through the names, while
    // `y + 1` fits.
    let src = "main(m: MainArgs) {\n    b = 2^64 + 13;\n    x = b ^ (2^59);\n    \
               y = x * x;\n    z = y * x * x;\n    u = y + 1;\n    v = z + 1;\n}\n";
    let out = rejected(src);
    assert_eq!(
        out.matches("Number too large for any memory of the target")
            .count(),
        1,
        "{out}"
    );
    assert!(
        out.starts_with(
            "7:9: Number too large for any memory of the target: `z + 1` needs more than \
             16 EiB; Linux x86_64 addresses 16 EiB."
        ),
        "{out}"
    );
}

#[test]
fn a_quotient_past_the_address_space_is_rejected() {
    // `x / y` is `b ^ (2^61)`: kept, and its sum with 1 writes out `2^67 + 2` bits.
    let src = |out: &str| {
        format!(
            "main(m: MainArgs) {{\n    b = 2^64 + 13;\n    x = rat(b) ^ (2^60);\n    \
             y = 1 / (rat(b) ^ (2^60));\n    m.stdout <- String({out}) else #divByZero -> \"\";\n}}\n"
        )
    };
    assert_eq!(built(&src("x / y > 0")), None);
    let out = rejected(&src("x / y + 1 > 0"));
    assert!(
        out.starts_with(
            "5:24: Number too large for any memory of the target: `x / y + 1` needs more than \
             16 EiB; Linux x86_64 addresses 16 EiB."
        ),
        "{out}"
    );
}

#[test]
fn a_product_or_quotient_that_may_cancel_or_build_nothing_proves_nothing() {
    // `x / x` is 1 and `x * (1 / x)` is 1: the kernel reduces by a gcd the text does not
    // prove 1, so the factors' sizes bound nothing (GMP's `mpq_div` cancels it before it
    // multiplies). A factor kept as prime powers, a factor that may be 0 and one the text
    // does not fix prove nothing either.
    let src = |x: &str, out: &str, tail: &str| {
        format!(
            "main(m: MainArgs) {{\n    b = 2^64 + 13;\n    \
             k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n    x = {x};\n    \
             m.stdout <- String(({out}) + rat(k)){tail};\n}}\n"
        )
    };
    for (x, out, tail) in [
        ("rat(b) ^ (2^60)", "x / x", DZ),
        ("rat(b) ^ (2^59)", "(x * x) / (x * x)", DZ),
        ("rat(b) ^ (2^60)", "x * (1 / x)", DZ),
        ("rat(3) ^ (2^100)", "x * x * x", ""),
        ("rat(2) ^ (2^70)", "x * (rat(b) ^ (2^60))", ""),
        ("rat(b) ^ (2^60)", "x * (rat(b) ^ k)", ""),
        ("rat(b) ^ (2^60)", "x * rat(k) * x", ""),
        ("rat(b) ^ (2^60)", "x * (x - x)", ""),
        // The roots `b` and `c` of the two numerators are each the other's denominator: the
        // product is `(b / c) ^ (2^60 - 1)` and fits.
        (
            "rat(b) ^ (2^60) / rat(2^64 + 15)",
            "x * (rat(2^64 + 15) ^ (2^60) / rat(b))",
            "",
        ),
        // `x` keeps 3 as a power, and `3^41`, of 65 bits, is a power of 3: the kernel moves
        // the factors of 3 out of the result's coefficient, which then has `2^66 + 1` bits.
        (
            "rat(3) ^ (2^70) * (rat(b) ^ (2^60))",
            "x * (rat(3^41) ^ (2^60))",
            "",
        ),
    ] {
        let program = src(x, out, tail);
        assert_eq!(built(&program), None, "{x}; {out}");
    }
}

// Plan row CONST-too-large-products-unproved: products and quotients the bound left to the run
// before, each a test that failed then (the program compiled). `b = 2^64 + 13` and
// `c = 2^64 + 15` share no factor, so `b ^ (2^60)` has `2^66 + 1` bits and nothing cancels
// between it and a power of `c`.

/// `main` with `b`, `c`, the bindings `lets` and `String(<out>)` pushed to standard output,
/// then `tail`.
fn bc_pushed(lets: &str, out: &str, tail: &str) -> String {
    format!(
        "main(m: MainArgs) {{\n    b = 2^64 + 13;\n    c = 2^64 + 15;\n{lets}    \
         m.stdout <- String({out}){tail};\n}}\n"
    )
}

/// `out` and its sum with 1 compared with 0, in `bc_pushed`: the product alone compiles and
/// the sum is rejected at `line`.
fn product_kept_sum_rejected(lets: &str, out: &str, tail: &str, line: usize) {
    let product = format!("{out} > 0");
    assert_eq!(built(&bc_pushed(lets, &product, tail)), None, "{lets}{out}");
    let got = rejected(&bc_pushed(lets, &format!("{out} + 1 > 0"), tail));
    assert!(
        got.starts_with(&format!(
            "{line}:24: Number too large for any memory of the target: `{out} + 1` needs "
        )) && got.contains("Linux x86_64 addresses 16 EiB.")
            && got.matches("Number too large").count() == 1,
        "{lets}{out}:\n{got}"
    );
}

#[test]
fn a_product_of_rats_whose_wide_parts_share_no_factor_is_kept() {
    // (a) The numerator of `x` is `b ^ (2^60)` and its denominator `c`: `x * x` and `x / z`
    // are `b ^ (2^61) / c ^ 2`, kept as the atoms `b` and `c`, and a sum with 1 writes them
    // out.
    let lets = "    x = rat(b) ^ (2^60) / rat(c);\n    z = rat(c) / (rat(b) ^ (2^60));\n";
    for (out, tail) in [
        ("x * x", ""),
        ("x / z", DZ),
        ("x * (rat(b) ^ (2^60) / rat(c))", ""),
    ] {
        product_kept_sum_rejected(lets, out, tail, 6);
    }
}

#[test]
fn a_product_whose_operand_keeps_prime_powers_is_kept() {
    // (b) `2^(2^70)` is kept as a power of 2 and builds nothing, so `x` holds `b ^ (2^60)` and
    // 2 as kept atoms, and so does each product below; a sum with 1 writes them out.
    for (lets, out, tail) in [
        ("    x = 2^(2^70) * (b ^ (2^60));\n", "x * (b ^ (2^60))", ""),
        ("", "(2^(2^70) * (b ^ (2^60))) * (b ^ (2^60))", ""),
        (
            "    x = rat(2) ^ (2^70) * (rat(b) ^ (2^60));\n",
            "x * (rat(b) ^ (2^60) / rat(2) ^ (2^70))",
            DZ,
        ),
        (
            "    x = rat(3) ^ (2^70) / (rat(c) ^ (2^60));\n",
            "x / (rat(c) ^ (2^60))",
            DZ,
        ),
    ] {
        let line = if lets.is_empty() { 4 } else { 5 };
        product_kept_sum_rejected(lets, out, tail, line);
    }
}

#[test]
fn a_power_of_a_kept_product_is_kept() {
    // (c) `(x * x) ^ 2` is `b ^ (2^61)`: kept, and a sum with 1 writes out `2^67 + 2` bits.
    let lets = "    x = b ^ (2^59);\n";
    for (out, tail) in [
        ("(x * x) ^ 2", ""),
        ("(b ^ (2^60)) ^ 2", ""),
        ("(rat(b) ^ (2^60) / rat(c)) ^ -2", DZ),
    ] {
        product_kept_sum_rejected(lets, out, tail, 5);
    }
    // Compared with 0: the products and powers below build nothing, and a base the text does
    // not fix is left to the run (the size its types bound is plan row CONST-kept-sizes).
    // Printing `(x * x) ^ 1` would write about 19 EiB of digits and is rejected.
    for (out, tail) in [
        ("(x * x) ^ 1", ""),
        ("x ^ 3", ""),
        ("(rat(x) / rat(x)) ^ 2", DZ),
        (
            "(x * (int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0)) ^ 2",
            "",
        ),
        (
            "rat(x * x) ^ (int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0)",
            DZ,
        ),
    ] {
        let out = format!("{out} > 0");
        assert_eq!(built(&bc_pushed(lets, &out, tail)), None, "{out}");
    }
}

#[test]
fn a_product_in_a_branch_not_taken_is_rejected() {
    let src = "main(m: MainArgs) {\n    k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n    \
               b = 2^64 + 13;\n    \
               m.stdout <- if k > 5 { String((b ^ (2^60)) * (b ^ (2^60)) + 1 > 0) } else { \"few\" };\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "4:35: Number too large for any memory of the target: `(b ^ (2^60)) * (b ^ (2^60)) \
             + 1` needs more than 16 EiB; Linux x86_64 addresses 16 EiB."
        ),
        "{out}"
    );
}

/// `n` names, each 7 times the one before, from `x = b ^ (2^59)`, and a sum with 1 of a
/// product of each with `x` three times, past the address space.
pub(super) fn product_chain(n: usize) -> String {
    let body: String = (0..n)
        .map(|i| {
            let prev = if i == 0 {
                "x".to_string()
            } else {
                format!("y{}", i - 1)
            };
            format!("    y{i} = {prev} * 7;\n    p{i} = y{i} * x * x * x + 1;\n")
        })
        .collect();
    format!("main(m: MainArgs) {{\n    b = 2^64 + 13;\n    x = b ^ (2^59);\n{body}}}\n")
}

/// `n` names, each the one before times `rat(b)`, from `x = rat(b) ^ (2^59) / rat(c)`, and
/// for each a sum with 1 of a product with `x` three times and of the square of a product
/// with `x`, both past the address space.
pub(super) fn rat_product_chain(n: usize) -> String {
    let body: String = (0..n)
        .map(|i| {
            let prev = if i == 0 {
                "x".to_string()
            } else {
                format!("y{}", i - 1)
            };
            format!(
                "    y{i} = {prev} * rat(b);\n    p{i} = y{i} * x * x * x + 1;\n    \
                 q{i} = (y{i} * x) ^ 2 + 1;\n"
            )
        })
        .collect();
    format!(
        "main(m: MainArgs) {{\n    b = 2^64 + 13;\n    c = 2^64 + 15;\n    \
         x = rat(b) ^ (2^59) / rat(c);\n{body}}}\n"
    )
}

// Plan row CONST-too-large-coprime-base: a part that is a product of powers of different
// numbers, as the numerator `b ^ (2^59) * c ^ (2^59)`. Before KEPT-power-form such a product
// was bounded where no root of one part shared a prime with a root of the part it must not
// cancel against; since, the kernel keeps `b` and `c` as atoms, the product is exact and
// builds nothing, and a sum with 1 writes it out. `d = 2^64 + 17` shares no factor with `b` or
// `c`.

#[test]
fn a_product_through_a_part_with_several_roots_is_kept() {
    // `x` has the atoms `b` and `c`, each to `2^60`, over `d`, so `x * x` writes out at least
    // `2^68` bits in a sum. At `2^59` the least size is `2^67` bits exactly, `64 * 2^60` for
    // each atom (the bound counts `⌊log₂ b⌋ = 64` bits a factor, not the 0.6 bits that 13 adds
    // over `2^60` factors), which is not past the address space: the bound is a lower one.
    for (lets, out, tail) in [
        (
            "    d = 2^64 + 17;\n    x = rat(b) ^ (2^60) * (rat(c) ^ (2^60)) / rat(d);\n",
            "x * x",
            "",
        ),
        // The kept prime 2 against the roots `b` and `c`, both odd.
        (
            "    x = rat(2) ^ (2^70) * (rat(b) ^ (2^60) * (rat(c) ^ (2^60)));\n",
            "x * x",
            "",
        ),
        // A power of `x`, by a negative exponent and by 2.
        (
            "    d = 2^64 + 17;\n    x = (rat(b) ^ (2^60) * (rat(c) ^ (2^60)) / rat(d)) ^ -1;\n",
            "x * x",
            DZ,
        ),
        (
            "    d = 2^64 + 17;\n    x = rat(b) ^ (2^60) * (rat(c) ^ (2^60)) / rat(d);\n",
            "x ^ 2",
            "",
        ),
    ] {
        let line = 4 + lets.matches('\n').count();
        product_kept_sum_rejected(lets, out, tail, line);
    }
}

#[test]
fn a_part_with_several_roots_that_cancels_builds_nothing() {
    // `x / (rat(c) ^ (2^59))` cancels `c ^ (2^59)` exactly: its value is `b ^ (2^59)`, and the
    // products and powers of it below build nothing.
    let x = "    x = rat(b) ^ (2^59) * (rat(c) ^ (2^59));\n";
    for out in [
        "x * (x / (rat(c) ^ (2^59))) > 0",
        "(x / (rat(c) ^ (2^59))) ^ 2 > 0",
        "(x / (rat(c) ^ (2^59))) * (x / (rat(c) ^ (2^59))) > 0",
    ] {
        assert_eq!(built(&bc_pushed(x, out, DZ)), None, "{out}");
    }
    // The kept prime 2 and the root `2^64 + 16 = 2^4 * (2^60 + 1)`: the kernel moves the
    // factors of 2 into the kept prime, and `x * x` builds nothing.
    let x = "    x = rat(2) ^ (2^70) * (rat(b) ^ (2^59) * (rat(2^64 + 16) ^ (2^59)));\n";
    assert_eq!(built(&bc_pushed(x, "x * x > 0", "")), None);
}

/// The fourth powers of the first `n` primes above 2^16: numbers of 65 to 72 bits, pairwise
/// coprime.
pub(super) fn coprime_fourth_powers(n: usize) -> Vec<u128> {
    let mut out = Vec::with_capacity(n);
    let mut q: u128 = 1 << 16;
    while out.len() < n {
        q += 1;
        if (2..)
            .take_while(|d| d * d <= q)
            .all(|d| !q.is_multiple_of(d))
        {
            out.push(q.pow(4));
        }
    }
    out
}

/// The lines that bind `e` before a chain of roots: `2^60` when `fixed`, else `2^60` or `2^61`
/// by the input, which the text does not fix, so no name of the chain is fixed and each is
/// bounded by its roots (`Ck::least_built` in zedc-check). The benches time the chains with
/// `fixed` false: folding a fixed chain exactly holds `i` words at link `i`, O(n^2) in all
/// (plan row FOLD-growing-chains).
pub(super) fn exponent(fixed: bool) -> &'static str {
    match fixed {
        true => "    e = 2^60;\n",
        false => {
            "    k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n    \
             e = if k > 0 { 2^60 } else { 2^61 };\n"
        }
    }
}

/// Plan row CONST-coprime-base-shared-primes: `n` names from `y0 = rat(r0) ^ e` ([`exponent`]),
/// each the one before times `rat(2 r_i)` or divided by `rat(r_i)`, in turn, for `r_i` of
/// [`coprime_fourth_powers`], and `y * y + 1` for the last name `y`, which writes out
/// `r0 ^ (2 e)`, past the address space. Every numerator factor is even, so they all share
/// the prime 2, which the kernel keeps as a prime power.
pub(super) fn even_chain(n: usize, fixed: bool) -> String {
    let r = coprime_fourth_powers(n);
    let body: String = (1..n)
        .map(|i| match i % 2 == 0 {
            true => format!("    y{i} = y{} * rat({});\n", i - 1, 2 * r[i]),
            false => format!("    y{i} = y{} / rat({});\n", i - 1, r[i]),
        })
        .collect();
    format!(
        "main(m: MainArgs) {{\n{}    y0 = rat({}) ^ e;\n{body}    \
         m.stdout <- String(y{} * y{} + 1 > 0);\n}}\n",
        exponent(fixed),
        r[0],
        n - 1,
        n - 1
    )
}

/// Plan row CONST-coprime-check-many-sets: `x` of `k` factors, `k = isqrt(n)`, the first to
/// `2^60`; `u_i` and `v_j` for `i, j < k`, each `1 / (b_1 ... b_k)` for `k` factors of its own;
/// `w_i_j = x * (u_i * v_j)` for each pair, in turn; and `w * w + 1` for the last `w`, which
/// writes out `r0 ^ (2^61)`, past the address space. The factors are
/// [`coprime_fourth_powers`].
pub(super) fn pool_products(n: usize) -> String {
    let k = n.isqrt().max(1);
    let r = coprime_fourth_powers(3 * k * k);
    let over = |rs: &[u128]| -> String { rs.iter().map(|b| format!(" / rat({b})")).collect() };
    let mut s = format!("main(m: MainArgs) {{\n    x = rat({}) ^ (2^60)", r[0]);
    s.extend(r[1..k].iter().map(|b| format!(" * rat({b})")));
    s += ";\n";
    for i in 0..k {
        let u = over(&r[k * (1 + i)..k * (2 + i)]);
        let v = over(&r[k * (1 + k + i)..k * (2 + k + i)]);
        s += &format!("    u{i} = rat(1){u};\n    v{i} = rat(1){v};\n");
    }
    for i in 0..k {
        for j in 0..k {
            s += &format!("    w{i}_{j} = x * (u{i} * v{j});\n");
        }
    }
    let w = format!("w{}_{}", k - 1, k - 1);
    s + &format!("    m.stdout <- String({w} * {w} + 1 > 0);\n}}\n")
}

#[test]
fn products_of_one_value_and_unions_from_one_pool_are_exact() {
    // Each `w` is the kernel's exact product, its factors kept: the products build nothing,
    // and the one sum, `w * w + 1`, is rejected once.
    for n in [1, 4, 9, 10] {
        rejected_times(&pool_products(n), 1);
    }
}

#[test]
fn a_product_through_parts_that_share_a_prime_is_exact() {
    // The numerator's factors all share 2, which the kernel moves into the kept prime 2: the
    // products build nothing, and the one sum, `y * y + 1`, is rejected once. With the exponent
    // the input picks, no name is fixed and the sum is left to the run.
    for n in [3, 4, 5, 8, 9] {
        rejected_times(&even_chain(n, true), 1);
        let src = even_chain(n, false);
        assert_eq!(built(&src), None, "{src}");
    }
}

// Plan row CONST-too-large-kept-powers: the size checked is the size of what each operation
// builds, by the list of DESIGN's numbers section. A number is kept as `n/d · ∏ p^e`, so a
// power of a base within 64 bits costs its exponents and compiles; an operation that writes
// it out in full (printing, a sum's part above the shared powers, a power of it, the listed
// `div` and `mod` cases) is rejected where the text fixes its operands and what it builds
// passes the address space. Before, every operation on a kept power compiled and the run
// stopped with "Number too large for memory".

/// `main` binding `x = <x>;` and writing `out` to standard output.
fn x_out(x: &str, out: &str) -> String {
    format!("main(m: MainArgs) {{\n  x = {x};\n  m.stdout <- {out};\n}}\n")
}

#[test]
fn a_kept_power_and_the_operations_that_keep_it_compile() {
    for (x, out) in [
        ("2^(2^70)", "String(x > 0)"),
        ("3^(2^70)", "String(x > 0)"),
        ("2^(2^70) * 3^(2^70)", "String(x > 0)"),
        ("2r^(2^70) / 2r^(2^70 - 1)", "String(x)"),
        ("2^2^200", "String(x < 3^3^150)"),
        (
            "2^(2^70)",
            "String(x == x) ++ String(x + x > 0) ++ String(x * 3 > 0)",
        ),
        ("2^2^100", "String(5 mod x)"),
        // The corners: a base of 1, -1 or 0 builds nothing, whatever the exponent.
        ("1^(2^70)", "String(x)"),
        ("(-1)^(2^70)", "String(x)"),
        ("0^(2^70)", "String(x)"),
    ] {
        let src = x_out(x, out);
        assert_eq!(built(&src), None, "{src}");
    }
}

#[test]
fn printing_a_kept_power_is_rejected_where_the_power_is_not() {
    // The contrasting pair: `x = 2^(2^70);` compiles, `String(x)` writes its 2^70 * log10(2)
    // digits, about 3.6 × 10^20 bytes.
    assert_eq!(built(&x_out("2^(2^70)", "\"kept\"")), None);
    assert_eq!(
        rejected(&x_out("2^(2^70)", "String(x)")),
        r#"3:15: Number too large for any memory of the target: `String(x)` needs at least 308 EiB; Linux x86_64 addresses 16 EiB.
  [1]  3:22: `x` is int here
       3 |   m.stdout <- String(x);
         |               ^^^^^^^^^ [8, 9, 10]
         |                      ^ [1]
  [2]  2:7: `x` is defined as this expression, int
       2 |   x = 2^(2^70);
         |       ^ [4]
         |       ^^^^^^^^ [2, 3]
         |         ^^^^^^ [5]
         |          ^ [6]
         |            ^^ [7]
  [3]  2:7: this `^` takes a power of integer literals alone, so it is a literal too; nothing here gives it a carrier, so it is an `int`
  [4]  2:7: this literal, 2, is 2
  [5]  2:9: this `^` gives 2^70
  [6]  2:10: this literal, 2, is 2
  [7]  2:12: this literal, 70, is 70
  [8]  3:15: `String(x)` asks for at least 2^71 bits: printing a number writes all of its digits, a byte each
  [9]  3:15: or read an operand from the input: the run then stops if no memory holds what it writes out
  [10] 3:15: or delete `String(x)` if its result is not used"#
    );
}

#[test]
fn each_operation_that_writes_a_kept_power_out_is_rejected() {
    for (x, out, head, why) in [
        (
            "2^(2^70)",
            "String(x + 1 > 0)",
            "3:22: Number too large for any memory of the target: `x + 1` needs at least 128 \
             EiB",
            "`x + 1` asks for at least 2^70 bits: a sum writes out in full its part above the \
             powers of primes its operands share",
        ),
        (
            // Printing the sum would build more again; the sum, the one cause, is reported.
            "2^(2^70)",
            "String(x + 1)",
            "3:22: Number too large for any memory of the target: `x + 1` needs at least 128 \
             EiB",
            "a sum writes out in full",
        ),
        (
            "2^(2^70)",
            "String(x - 1 > 0)",
            "3:22: Number too large for any memory of the target: `x - 1` needs at least 128 \
             EiB",
            "a sum writes out in full",
        ),
        (
            "2^2^100",
            "String(x div 3)",
            "3:22: Number too large for any memory of the target: `x div 3` needs at least \
             2^97 bytes",
            "`div` writes out the divisor, and the dividend less its remainder",
        ),
        (
            "2^2^100",
            "String((-5 mod x))",
            "3:22: Number too large for any memory of the target: `(-5 mod x)` needs at least \
             2^97 bytes",
            "`mod` writes out the modulus",
        ),
        (
            "3^2^2^70",
            "String(x > 0)",
            "2:7: Number too large for any memory of the target: `3^2^2^70` needs at least \
             128 EiB",
            "a power writes out its exponent in full unless the base is 0, 1 or -1",
        ),
    ] {
        let src = x_out(x, out);
        let out = rejected(&src);
        assert!(out.starts_with(head) && out.contains(why), "{src}\n{out}");
        assert_eq!(out.matches("Number too large").count(), 1, "{src}\n{out}");
    }
}

#[test]
fn the_largest_sum_within_the_address_space_compiles() {
    // `2^k + 1` builds `k + 1` bits, 2^67 bits, 16 EiB, at `k = 2^67 - 1`, and one bit more
    // at `k = 2^67`.
    let src = |k: &str| x_out(&format!("2^({k}) + 1"), "String(x > 0)");
    assert_eq!(built(&src("2^67 - 1")), None);
    let out = rejected(&src("2^67"));
    assert!(
        out.starts_with(
            "2:7: Number too large for any memory of the target: `2^(2^67) + 1` needs more \
             than 16 EiB"
        ),
        "{out}"
    );
}

/// `main` under a 1 MiB memory limit writing `out` to standard output.
fn limited(out: &str) -> String {
    format!("@limits(memory: 1048576)\nmain(m: MainArgs) {{\n  m.stdout <- {out};\n}}\n")
}

#[test]
fn a_build_past_the_memory_limit_is_rejected_and_the_largest_within_it_compiles() {
    // `2^(2^23 - 1) + 1` builds `2^23` bits, 1 MiB; `2^(2^23) + 1` one bit more.
    assert_eq!(built(&limited("String(2^(2^23 - 1) + 1 > 0)")), None);
    let out = rejected(&limited("String(2^(2^23) + 1 > 0)"));
    assert!(
        out.starts_with(
            "3:22: Number too large for the memory limit of `main`: `2^(2^23) + 1` needs at \
             least 1 MiB; `@limits(memory: 1048576)`. Try `@limits(memory: 2^21)` instead."
        ) && out.contains("`2^(2^23) + 1` asks for at least 8388609 bits"),
        "{out}"
    );
    // Printing writes a byte a digit: `2^(2^20)` has 315653 digits, `2^(2^24)` 5050446.
    assert_eq!(built(&limited("String(2^(2^20))")), None);
    // `5^1300000` has 908660 digits, within 1 MiB; the kernel's bound from above on its text,
    // at 3 bits a factor 5, puts it at 1.1 MiB, which the check must not claim it needs.
    assert_eq!(built(&limited("String(5^1300000)")), None);
    // `5^3600000 + 1` builds 8358942 bits, within 2^23; at 3 bits a factor 5 it would be past.
    assert_eq!(built(&limited("String(5^3600000 + 1 > 0)")), None);
    let out = rejected(&limited("String(2^(2^24))"));
    assert!(
        out.starts_with(
            "3:15: Number too large for the memory limit of `main`: `String(2^(2^24))` needs \
             at least 4.8 MiB; `@limits(memory: 1048576)`. Try `@limits(memory: 2^23)` instead."
        ),
        "{out}"
    );
    // Printing a sum past the limit is reported at the sum alone, the one cause.
    let out = rejected(&limited("String(2^(2^24) + 1)"));
    assert_eq!(out.matches("Number too large").count(), 1, "{out}");
    assert!(
        out.starts_with(
            "3:22: Number too large for the memory limit of `main`: `2^(2^24) + 1` needs at \
             least 2 MiB"
        ),
        "{out}"
    );
}

/// `n` bindings, each a kept power and a sum that writes it out past the address space.
pub(super) fn kept_sums(n: usize) -> String {
    let body: String = (0..n)
        .map(|i| format!("  x{i} = 2^(2^70 + {i});\n  y{i} = x{i} + 1;\n"))
        .collect();
    format!("main(m: MainArgs) {{\n{body}}}\n")
}

/// `src` is rejected with `count` diagnostics "Number too large for any memory of the target".
pub(super) fn rejected_times(src: &str, count: usize) {
    let out = rejected(src);
    assert_eq!(
        out.matches("Number too large for any memory of the target")
            .count(),
        count,
        "{out}"
    );
}

/// The chains and lists of `bench::too_large` at 1, 2 and 5 links or bindings, each rejected
/// once per power, product or sum past the address space (the bench times 200 and 1600, and 800
/// and 6400 kept sums).
#[test]
fn chains_and_lists_past_the_address_space() {
    for n in [1, 2, 5] {
        rejected_times(&powers(n), n);
        rejected_times(&chain(n), n);
        rejected_times(&product_chain(n), n);
        rejected_times(&rat_product_chain(n), 2 * n);
        rejected_times(&kept_sums(n), n);
        rejected_times(&bounded_sums(n), n);
    }
}

/// `n` bindings, each a kept power and, under a test that bounds `k` from the input to
/// `1..=5`, its sum with `k`, past the address space (plan row CONST-build-typed-operands).
pub(super) fn bounded_sums(n: usize) -> String {
    let body: String = (0..n)
        .map(|i| {
            format!(
                "  x{i} = 2^(2^70 + {i});\n  \
                 y{i} = if k >= 1 && k <= 5 {{ x{i} + k }} else {{ 0 }};\n"
            )
        })
        .collect();
    format!(
        "main(m: MainArgs) {{\n  k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> \
         0;\n{body}}}\n"
    )
}

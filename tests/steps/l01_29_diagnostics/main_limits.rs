//! The limits written before `main` at compile time (plan row MAIN-limits; DESIGN.md sec:ports,
//! "`main` may limit its own run", and the sec:diagnostics row "Number too large for the memory
//! limit of `main`"): `@limits` and `@kill` stand only before `main`, each argument is a
//! positive constant, and a power whose result the types prove larger than the memory limit is
//! rejected, as one larger than the target's address space is (too_large.rs). The runs that hit
//! each limit are in l01_36a_executables/limits_binary.rs, since a limit holds for a whole
//! process.

use zedc::build::Build;
use zedc::run::load_for;

/// The program `src` built for Linux x86_64: its rendered diagnostics, or `None` when it
/// compiles.
fn built(src: &str) -> Option<String> {
    let build = Build::default().for_target("x86_64-linux");
    load_for(src.as_bytes(), &build).err()
}

/// The rendered diagnostics of `src`, which the checker rejects.
pub(super) fn rejected(src: &str) -> String {
    built(src).unwrap_or_else(|| panic!("accepted:\n{src}"))
}

#[test]
fn limits_before_a_function_other_than_main_are_rejected() {
    for (annot, word) in [
        ("@limits(memory: 1048576)", "@limits"),
        ("@kill(#kill)", "@kill"),
    ] {
        let src = format!(
            "{annot}\nf(x: int) = x;\nmain(m: MainArgs) {{\n    m.stdout <- String(f(1));\n}}\n"
        );
        let out = rejected(&src);
        assert!(
            out.starts_with(&format!("1:1: `{word}` stands before `main`")),
            "{out}"
        );
    }
    // Before `main`, the same annotation is accepted.
    let src =
        "@limits(memory: 1048576)\n@kill(#kill)\nmain(m: MainArgs) {\n    m.stdout <- \"hi\";\n}\n";
    assert_eq!(built(src), None);
}

#[test]
fn each_argument_of_a_limit_is_a_positive_constant() {
    let src = "n = 0;\n@limits(memory: n, cpu: 1r/2r)\n@timeout(-1)\n@kill(#term, grace: 0)\n\
               main(m: MainArgs) {\n    m.stdout <- \"hi\";\n}\n";
    assert_eq!(
        rejected(src),
        "2:17: `memory: n` leaves the run no memory: the memory limit of `main` is a number of \
         bytes above 0, as `memory: 1048576` for 1 MiB.\n\
         3:10: `-1` is not a time the run can have: a limit of `main` is a number of seconds \
         above 0 and below 2^64 nanoseconds, as `60r`.\n\
         4:21: `grace: 0` is not a time the run can have: a limit of `main` is a number of \
         seconds above 0 and below 2^64 nanoseconds, as `grace: 60r`."
    );
    // Names bound to constants, `int` and `rat` seconds.
    let src = "n = 1048576;\nd = 1r/2r;\n@limits(memory: n, cpu: d)\n@timeout(1r/2r)\n\
               @kill(#term, grace: 2)\nmain(m: MainArgs) {\n    m.stdout <- \"hi\";\n}\n";
    assert_eq!(built(src), None);
}

#[test]
fn a_power_past_the_memory_limit_is_rejected_and_one_within_it_compiles() {
    let src = "@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n    \
               m.stdout <- String(b ^ (2^20) > 0);\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "4:24: Number too large for the memory limit of `main`: `b ^ (2^20)` needs at least \
             8 MiB; `@limits(memory: 1048576)`. Try `m.stdout <- String(b ^ (2^16) > 0)` instead."
        ),
        "{out}"
    );
    assert!(
        out.contains("the memory limit of `main` lets the run hold 1 MiB")
            && out.ends_with(
                "  fixes, each checked here:\n    m.stdout <- String(b ^ (2^16) > 0);    needs at \
                 least 512 KiB\n    @limits(memory: 2^24)                  lets the run hold 16 MiB"
            ),
        "{out}"
    );
    // Without the limit, 8 MiB fits the address space; under it, 2^16 fits the limit. The
    // power is compared, not printed: printing `b ^ (2^16)` writes about 1.26 million digits,
    // 1.2 MiB, past the limit (plan row CONST-too-large-kept-powers).
    assert_eq!(built(&src.replace("@limits(memory: 1048576)\n", "")), None);
    assert_eq!(built(&src.replace("2^20", "2^16")), None);
}

#[test]
fn a_product_past_the_memory_limit_is_rejected_and_one_within_it_compiles() {
    // Plan row CONST-too-large-products-unproved (d): `x` has `2^22 + 1` bits, 512 KiB, within
    // the limit, and `x * x` at least `2^23 + 1`, past it. Before, only powers were judged
    // against the limit, and this compiled.
    let src = "@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n    \
               x = b ^ (2^16);\n    m.stdout <- String(x * x > 0);\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "5:24: Number too large for the memory limit of `main`: `x * x` needs at least 1 \
             MiB; `@limits(memory: 1048576)`. Try `@limits(memory: 2^21)` instead."
        ),
        "{out}"
    );
    assert!(
        out.contains("4:5: `x` has at least 4194305 bits\n")
            && out.contains(
                "5:24: so `x * x` has at least 8388609 bits: the bit lengths of the least |x| \
                 and |y| added, less one\n"
            )
            && out.contains("1:1: the memory limit of `main` lets the run hold 1 MiB\n")
            && out.contains(
                "5:24: or read a factor from the input: the run then stops at the memory limit \
                 of `main` if the result passes it\n"
            )
            && out.ends_with(
                "  fixes, each checked here:\n    @limits(memory: 2^21)    lets the run hold 2 MiB"
            ),
        "{out}"
    );
    // Without the limit, 1 MiB fits the address space; under it, `x * b` fits the limit. The
    // product is compared, not printed: printing `x * b` writes about 1.2 MiB of digits.
    assert_eq!(built(&src.replace("@limits(memory: 1048576)\n", "")), None);
    assert_eq!(built(&src.replace("x * x", "x * b")), None);
}

#[test]
fn a_product_through_a_part_with_several_roots_past_the_memory_limit_is_rejected() {
    // Plan row CONST-too-large-coprime-base: the numerator of `x`, `b ^ (2^15) * c ^ (2^15)`,
    // has the roots `b` and `c` and at least `2^22 + 1` bits, so `x * x` has at least
    // `2^23 + 1`, past 1 MiB; the check that `b` and `c` share no prime with `d` is decided
    // after the walk, and the product is then judged against the limit.
    let src = "@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n    \
               c = 2^64 + 15;\n    d = 2^64 + 17;\n    \
               x = rat(b) ^ (2^15) * (rat(c) ^ (2^15)) / rat(d);\n    \
               m.stdout <- String(x * x > 0) else \"\";\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "7:24: Number too large for the memory limit of `main`: `x * x` needs at least 1 \
             MiB; `@limits(memory: 1048576)`."
        ),
        "{out}"
    );
    // A power of `x` is decided after the walk too, then judged against the limit.
    let out = rejected(&src.replace("x * x", "x ^ 2"));
    assert!(
        out.starts_with(
            "7:24: Number too large for the memory limit of `main`: `x ^ 2` needs at least 1 \
             MiB; `@limits(memory: 1048576)`."
        ),
        "{out}"
    );
    // A negated value keeps the roots of what it negates: `d` still shares no prime with `b`
    // and `c`.
    let out = rejected(&src.replace("d = 2^64 + 17", "d = -(2^64 + 17)"));
    assert!(
        out.starts_with(
            "7:24: Number too large for the memory limit of `main`: `x * x` needs at least 1 \
             MiB; `@limits(memory: 1048576)`."
        ),
        "{out}"
    );
    // Without the limit it fits the address space. `x / (rat(c) ^ (2^15))` cancels the power
    // of `c`, so a product through it proves nothing and is left to the run.
    assert_eq!(built(&src.replace("@limits(memory: 1048576)\n", "")), None);
    assert_eq!(
        built(&src.replace("x * x", "x * (x / (rat(c) ^ (2^15)))")),
        None
    );
}

/// `n` powers of about 8 MiB each under a 1 MiB limit.
pub(super) fn powers(n: usize) -> String {
    let mut s = String::from("@limits(memory: 1048576)\nmain(m: MainArgs) {\n");
    for i in 0..n {
        s.push_str(&format!(
            "    m.stdout <- String((2^64 + 13) ^ (2^20 + {i}));\n"
        ));
    }
    s + "}\n"
}

/// Each of the `n` powers of [`powers`]`(n)` is rejected. Each power is sized once in the
/// walk and compared with the limit once after it: O(1) words per power.
pub(super) fn powers_past_the_memory_limit_rejected(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(
        out.matches("Number too large for the memory limit of `main`")
            .count(),
        n
    );
}

#[test]
fn rejecting_many_powers_past_the_memory_limit() {
    for n in [1, 3] {
        powers_past_the_memory_limit_rejected(&powers(n), n);
    }
}

/// `main` with the memory limit `memory`, which writes one string.
fn with_memory_limit(memory: &str) -> String {
    format!("@limits(memory: {memory})\nmain(m: MainArgs) {{\n    m.stdout <- \"a\";\n}}\n")
}

#[test]
fn the_largest_memory_limit_is_the_address_space_and_a_larger_one_names_it() {
    // FAIL-check-memory-limit-2-63 (found by TEST-complete-crates): the rejection of a limit
    // past the address space said "write at most `2^63`", and `2^63` was rejected with the same
    // message. The address space of Linux x86_64 is 2^64 bytes, 16 EiB (DESIGN.md
    // sec:checking_in_zed, "Linux x86_64 addresses 16 EiB"), so every limit up to it compiles,
    // and the rejection of one past it names it; a repair is code the checker accepts
    // (sec:diagnostics).
    for fits in ["1", "2^63 - 1", "2^63", "2^64 - 1", "2^64"] {
        assert_eq!(built(&with_memory_limit(fits)), None, "memory: {fits}");
    }
    for past in ["2^64 + 1", "2^65", "2^(2^70)"] {
        let out = built(&with_memory_limit(past)).unwrap_or_else(|| panic!("memory: {past}"));
        assert!(
            out.contains(&format!(
                "`memory: {past}` is more memory than Linux x86_64 addresses: write at most \
                 `2^64`."
            )),
            "memory: {past}\n{out}"
        );
        let at_most = out
            .split("write at most `")
            .nth(1)
            .and_then(|rest| rest.split('`').next())
            .unwrap_or_else(|| panic!("no largest limit named: {out}"));
        assert_eq!(
            built(&with_memory_limit(at_most)),
            None,
            "memory: {at_most}"
        );
    }
}

#[test]
fn a_repair_that_raises_the_memory_limit_past_2_to_the_63_compiles() {
    // `b ^ (2^60)`, `b = 2^64 + 13`, needs a little more than 2^63 bytes, within the address
    // space: the repair of the limit is the least power of two that holds it, `2^64`, which is
    // the address space itself and must compile (FAIL-check-memory-limit-2-63).
    let src = "@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n    \
               m.stdout <- String(b ^ (2^60) > 0);\n}\n";
    let out = rejected(src);
    assert!(out.contains("@limits(memory: 2^64)"), "{out}");
    assert_eq!(
        built(&src.replace("@limits(memory: 1048576)", "@limits(memory: 2^64)")),
        None
    );
}

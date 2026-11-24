//! The limits written before `main` at compile time (plan row MAIN-limits; DESIGN.md sec:ports,
//! "`main` may limit its own run", and the sec:diagnostics row "Number too large for the memory
//! limit of `main`"): `@limits` and `@kill` stand only before `main`, each argument is a
//! positive constant, and an operation that the operands prove to build more than the memory
//! limit is rejected, as one larger than the target's address space is (too_large.rs). The runs
//! that hit each limit are in l01_36a_executables/limits_binary.rs, since a limit holds for a whole
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
    // Since KEPT-power-form (DESIGN.md step L1.17c) `b ^ (2^20)` is kept and builds nothing;
    // its sum with 1 writes out `2^20 * 64 + 2` bits, 8 MiB, past the limit. Before, the power
    // itself was rejected, with a smaller exponent as a repair (now plan row CONST-kept-sizes).
    let src = "@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n    \
               m.stdout <- String(b ^ (2^20) + 1 > 0);\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "4:24: Number too large for the memory limit of `main`: `b ^ (2^20) + 1` needs at \
             least 8 MiB; `@limits(memory: 1048576)`. Try `@limits(memory: 2^24)` instead."
        ),
        "{out}"
    );
    assert!(
        out.contains("the memory limit of `main` lets the run hold 1 MiB")
            && out.ends_with(
                "  fixes, each checked here:\n    @limits(memory: 2^24)    lets the run hold 16 MiB"
            ),
        "{out}"
    );
    // Without the limit, 8 MiB fits the address space; under it, 2^16 fits the limit, and the
    // power alone builds nothing.
    assert_eq!(built(&src.replace("@limits(memory: 1048576)\n", "")), None);
    assert_eq!(built(&src.replace("2^20", "2^16")), None);
    assert_eq!(built(&src.replace(" + 1 > 0", " > 0")), None);
}

#[test]
fn a_product_past_the_memory_limit_is_rejected_and_one_within_it_compiles() {
    // Plan row CONST-too-large-products-unproved (d): `x` is `b ^ (2^16)` and `x * x`
    // `b ^ (2^17)`, both kept; the sum with 1 writes out `2^23 + 2` bits, past 1 MiB. Before,
    // the product itself was rejected.
    let src = "@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n    \
               x = b ^ (2^16);\n    m.stdout <- String(x * x + 1 > 0);\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "5:24: Number too large for the memory limit of `main`: `x * x + 1` needs at least 1 \
             MiB; `@limits(memory: 1048576)`. Try `@limits(memory: 2^21)` instead."
        ),
        "{out}"
    );
    assert!(
        out.contains("1:1: the memory limit of `main` lets the run hold 1 MiB\n")
            && out.contains(
                "5:24: or read an operand from the input: the run then stops at the memory limit \
                 of `main` if the result passes it\n"
            )
            && out.ends_with(
                "  fixes, each checked here:\n    @limits(memory: 2^21)    lets the run hold 2 MiB"
            ),
        "{out}"
    );
    // Without the limit, 1 MiB fits the address space; under it, `x * b + 1` fits the limit,
    // and the product alone builds nothing.
    assert_eq!(built(&src.replace("@limits(memory: 1048576)\n", "")), None);
    assert_eq!(built(&src.replace("x * x", "x * b")), None);
    assert_eq!(built(&src.replace(" + 1 > 0", " > 0")), None);
}

#[test]
fn a_product_through_a_part_with_several_roots_past_the_memory_limit_is_rejected() {
    // Plan row CONST-too-large-coprime-base: `x` keeps `b` and `c` as atoms, each to `2^15`,
    // over `d`, so `x * x + 1` writes out at least `2^23` bits, past 1 MiB.
    let src = "@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n    \
               c = 2^64 + 15;\n    d = 2^64 + 17;\n    \
               x = rat(b) ^ (2^15) * (rat(c) ^ (2^15)) / rat(d);\n    \
               m.stdout <- String(x * x + 1 > 0);\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "7:24: Number too large for the memory limit of `main`: `x * x + 1` needs at least 1 \
             MiB; `@limits(memory: 1048576)`."
        ),
        "{out}"
    );
    // A power of `x`, and a negated `d`.
    let out = rejected(&src.replace("x * x", "x ^ 2"));
    assert!(
        out.starts_with(
            "7:24: Number too large for the memory limit of `main`: `x ^ 2 + 1` needs at least 1 \
             MiB; `@limits(memory: 1048576)`."
        ),
        "{out}"
    );
    let out = rejected(&src.replace("d = 2^64 + 17", "d = -(2^64 + 17)"));
    assert!(
        out.starts_with(
            "7:24: Number too large for the memory limit of `main`: `x * x + 1` needs at least 1 \
             MiB; `@limits(memory: 1048576)`."
        ),
        "{out}"
    );
    // Without the limit it fits the address space. `x / (rat(c) ^ (2^15))` cancels the power
    // of `c`, so `x * (x / (rat(c) ^ (2^15))) + 1` writes out about `3 * 2^21` bits, 768 KiB,
    // within the limit. That quotient may divide by zero, and the push names the atom
    // (DESIGN.md sec:failure, QUESTIONS A113).
    assert_eq!(built(&src.replace("@limits(memory: 1048576)\n", "")), None);
    assert_eq!(
        built(&src.replace(
            "x * x + 1 > 0)",
            "x * (x / (rat(c) ^ (2^15))) + 1 > 0) else #divByZero -> \"\""
        )),
        None
    );
}

/// `n` sums with 1 of powers, each writing out about 8 MiB, under a 1 MiB limit.
pub(super) fn powers(n: usize) -> String {
    let mut s = String::from("@limits(memory: 1048576)\nmain(m: MainArgs) {\n");
    for i in 0..n {
        s.push_str(&format!(
            "    m.stdout <- String((2^64 + 13) ^ (2^20 + {i}) + 1 > 0);\n"
        ));
    }
    s + "}\n"
}

/// Each of the `n` sums of [`powers`]`(n)` is rejected. Each is sized once in the walk, one
/// kernel step refused before it allocates, and compared with the limit once after it: O(1)
/// words per sum.
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
    // `b ^ (2^60) + 1`, `b = 2^64 + 13`, writes out a little more than 2^63 bytes, within the
    // address space: the repair of the limit is the least power of two that holds it, `2^64`,
    // which is the address space itself and must compile (FAIL-check-memory-limit-2-63).
    let src = "@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n    \
               m.stdout <- String(b ^ (2^60) + 1 > 0);\n}\n";
    let out = rejected(src);
    assert!(out.contains("@limits(memory: 2^64)"), "{out}");
    assert_eq!(
        built(&src.replace("@limits(memory: 1048576)", "@limits(memory: 2^64)")),
        None
    );
}

#[test]
fn a_time_of_a_power_too_large_to_build_is_judged_by_its_size() {
    // A positive time below 1 ns is rounded up to 1 ns, however small: `1r / 2 ^ (2^40)` has a
    // denominator of 2^40 + 1 bits, 128 GiB, which the checker holds factored and must not build
    // to round it (limits.rs `seconds`). One past 2^64 nanoseconds is rejected, however large.
    let main = "main(m: MainArgs) {\n    m.stdout <- \"hi\";\n}\n";
    for tiny in ["1r / 2 ^ (2^40)", "1r / (3 ^ (2^40))"] {
        assert_eq!(built(&format!("@timeout({tiny})\n{main}")), None, "{tiny}");
    }
    // `rat(..)`: `/` takes no `int`s, and `3 ^ (2^40) / 7` was rejected for that as well.
    for huge in ["2 ^ (2^40)", "rat(3 ^ (2^40)) / 7"] {
        let out = rejected(&format!("@timeout({huge})\n{main}"));
        assert!(
            out.contains(
                "is not a time the run can have: a limit of `main` is a number of seconds \
                          above 0 and below 2^64 nanoseconds"
            ),
            "{huge}: {out}"
        );
    }
}

/// Row PROOF-seconds-unbuildable-in-range: a time between the ends whose two sides are powers
/// too large to build. `rat(3 ^ (2^40)) / 2 ^ b` with `b = 1742684699131`, the whole part of
/// `2^40 * log2(3)` (bc at scale 80: `...131.8380069509`), is `2^0.8380069509...`, about 1.79 s,
/// while `3 ^ (2^40)` has 1.7 * 10^12 bits, 218 GB. Its nanoseconds are
/// `ceil(1787578937.2732...)` (bc at scale 80). Red before: the rounding divided the sides and
/// the system refused the memory, so the time was rejected as "not a time the run can have".
#[test]
fn a_time_in_range_whose_sides_are_too_large_to_build_is_rounded_up() {
    let main = "main(m: MainArgs) {\n    m.stdout <- \"hi\";\n}\n";
    let src = format!("@timeout(rat(3 ^ (2^40)) / 2 ^ 1742684699131)\n{main}");
    let build = Build::default().for_target("x86_64-linux");
    let program = load_for(src.as_bytes(), &build).unwrap_or_else(|e| panic!("{src}: {e}"));
    assert_eq!(
        program.limits().timeout,
        Some(std::time::Duration::from_nanos(1_787_578_938))
    );
}

/// Plan row CONST-default-memory-limit (DESIGN.md sec:checking_in_zed, "The default memory
/// limit", zed 21e7335; headline as reworded in zed c79c154): without `@limits(memory: …)`
/// before `main`, an operation the operands prove to build 1 GiB or more is rejected at compile
/// time, whether or not its branch is taken;
/// a declared limit at least the build accepts it, in any unit of information.
/// `(2^64 + 13) ^ (2^27) + 1` writes out at least `2^27 * 64 + 2` bits, 2^30 bytes and two
/// bits, so its headline rounds to 1 GiB; `(2^64 + 13) ^ (2^20) + 1` at least 8 MiB. Since
/// KEPT-power-form the power alone is kept and builds nothing (DESIGN.md step L1.17c).
#[test]
fn without_a_memory_limit_a_build_of_1_gib_or_more_is_rejected() {
    let main = |limit: &str, body: &str| {
        format!("{limit}main(m: MainArgs) {{\n    b = 2^64 + 13;\n    {body}\n}}\n")
    };
    let push = "m.stdout <- String(b ^ (2^27) + 1 > 0);";
    let out = rejected(&main("", push));
    assert!(
        out.contains(
            "Number too large for the default memory limit: `b ^ (2^27) + 1` needs at least 1 \
             GiB; without `@limits(memory: …)` before `main`, no operation may make a value of 1 \
             GiB or more"
        ),
        "{out}"
    );
    // The repair is a limit before `main`, the least power of two that holds the build.
    assert!(out.contains("@limits(memory: 2^31)"), "{out}");
    assert_eq!(built(&main("@limits(memory: 2^31)\n", push)), None);
    assert_eq!(
        built(&main("", "m.stdout <- String(b ^ (2^27) > 0);")),
        None
    );
    // In a branch that is not taken, the same.
    let branch = "m.stdout <- if m.args.len() > 9 { String(b ^ (2^27) + 1 > 0) } else { \"\" };";
    let out = rejected(&main("", branch));
    assert!(out.contains("the default memory limit"), "{out}");
    // A declared limit at least the build accepts it, and one below the build rejects it.
    // Written in bytes: zedc does not take `with units("GiB")` before step L12, which gives
    // `2 with units("GiB")` and `4 with units("GB")` here.
    for limit in [
        "@limits(memory: 2147483648)\n",
        "@limits(memory: 4000000000)\n",
    ] {
        assert_eq!(built(&main(limit, push)), None, "{limit}");
    }
    let out = rejected(&main("@limits(memory: 2^30)\n", push));
    assert!(out.contains("the memory limit of `main`"), "{out}");
    // Below 1 GiB the default accepts: 8 MiB, and `2^26 * 64 + 2` bits, 512 MiB and two bits.
    for power in ["b ^ (2^20)", "b ^ (2^26)"] {
        let body = format!("m.stdout <- String({power} + 1 > 0);");
        assert_eq!(built(&main("", &body)), None, "{power}");
    }
    // A size that depends on the input is left to the run, which the default does not limit.
    let input = "k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n    \
                 m.stdout <- if k >= 0 { String(b ^ (2^k)) } else { \"\" };";
    assert_eq!(built(&main("", input)), None);
    // The program of 8376989a7, whose run asked for about 51 GB: `3 ^ (2 ^ 40)` has a base of
    // 64 bits or fewer, so it is kept as a power and builds nothing, and a comparison builds
    // only where the two numbers agree to within their width, which an `x` read from the input
    // does not prove (DESIGN.md sec:checking_in_zed). So the default limit does not reject it.
    let compare = "x = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n    \
                   m.stdout <- String(x < 3 ^ (2 ^ 40));";
    assert_eq!(built(&main("", compare)), None);
}

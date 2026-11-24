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

/// Row CONST-repair-build-trial: the smaller power a repair offers is checked with the builds
/// around it. Printed, `b ^ (2^16)` needs about 1.2 MiB of digits under the 1 MiB limit, so the
/// repair offers `2^15`, whose power needs 256 KiB and whose digits about 616 KiB, and the
/// program with that repair compiles.
#[test]
fn a_smaller_power_offered_is_checked_with_the_print_around_it() {
    let src = "@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n    \
               m.stdout <- String(b ^ (2^20));\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "4:24: Number too large for the memory limit of `main`: `b ^ (2^20)` needs at least \
             8 MiB; `@limits(memory: 1048576)`. Try `m.stdout <- String(b ^ (2^15))` instead."
        ),
        "{out}"
    );
    assert!(!out.contains("2^16"), "{out}");
    assert_eq!(built(&src.replace("2^20", "2^15")), None);
    assert!(built(&src.replace("2^20", "2^16")).is_some());
    // A power of the power: `(b ^ (2^16)) ^ 2` needs 1 MiB, so the inner repair is `2^15`.
    let src = "@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n    \
               m.stdout <- String((b ^ (2^20)) ^ 2 > 0);\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "4:24: Number too large for the memory limit of `main`: `(b ^ (2^20))` needs at \
             least 8 MiB; `@limits(memory: 1048576)`. Try `m.stdout <- String((b ^ (2^15)) ^ 2 > 0)` \
             instead."
        ),
        "{out}"
    );
    assert!(!out.contains("2^16"), "{out}");
    assert_eq!(built(&src.replace("2^20", "2^15")), None);
    assert!(built(&src.replace("2^20", "2^16")).is_some());
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

/// Row CONST-too-large-products-fix: a product past the limit whose larger operand is a power
/// the walk sized is repaired by that power's exponent lowered, as the power's own repair is.
/// Each factor `b ^ (2^16)` has `2^22 + 1` bits, so the product has at least `2^23 + 1`, past
/// 1 MiB; with `2^15` in the first, at least `2^21 + 2^22 + 1` bits, 768 KiB.
#[test]
fn a_product_past_the_memory_limit_offers_a_smaller_power_operand() {
    let src = "@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n    \
               m.stdout <- String((b ^ (2^16)) * (b ^ (2^16)) > 0);\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "4:24: Number too large for the memory limit of `main`: `(b ^ (2^16)) * (b ^ \
             (2^16))` needs at least 1 MiB; `@limits(memory: 1048576)`. Try `m.stdout <- \
             String((b ^ (2^15)) * (b ^ (2^16)) > 0)` instead."
        ),
        "{out}"
    );
    assert!(
        out.contains("needs at least 768 KiB\n") && out.contains("@limits(memory: 2^21)"),
        "{out}"
    );
    assert_eq!(
        built(&src.replacen("2^16", "2^15", 1)),
        None,
        "{}",
        src.replacen("2^16", "2^15", 1)
    );
    // An operand that is no power, as a name bound to one, has no such repair
    // (a_product_past_the_memory_limit_is_rejected_and_one_within_it_compiles).
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
               m.stdout <- String(x * x > 0);\n}\n";
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
    // of `c`, so a product through it proves nothing and is left to the run. That quotient may
    // divide by zero, and the push names the atom (DESIGN.md sec:failure, QUESTIONS A113).
    assert_eq!(built(&src.replace("@limits(memory: 1048576)\n", "")), None);
    assert_eq!(
        built(&src.replace(
            "x * x > 0)",
            "x * (x / (rat(c) ^ (2^15))) > 0) else #divByZero -> \"\""
        )),
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

/// `main` under a limit of 1 MiB writing `n` products of two powers each past it together, each
/// in a `String` and a comparison, as in
/// [`a_product_past_the_memory_limit_offers_a_smaller_power_operand`].
pub(super) fn products(n: usize) -> String {
    // Each operand has about `64 * 2^16` bits, 4.2 Mbit, within the 1 MiB limit, and each
    // product about 8.4 Mbit, past it. The repair's trial sizes each shrunk product from its
    // operands' bit lengths instead of multiplying them (PERF-product-limit-built-to-measure);
    // before, 98% of the run was the kernel's transform multiplication (perf, DWARF,
    // b22-checkrest12, 2026-11-24), about 130 ms a line, which held the benchmark at n = 4
    // (PERF-products-bench-native-cost) until the operands were cut to `2^12`.
    let mut s = String::from("@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n");
    for i in 0..n {
        s.push_str(&format!(
            "    m.stdout <- String((b ^ (2^16)) * (b ^ (2^16 + {i})) > 0);\n"
        ));
    }
    s + "}\n"
}

/// Each of the `n` products of [`products`]`(n)` is rejected with a smaller power operand
/// offered. Each repair is sized against the operations above the power, a fixed number per
/// product here, each a multiplication or comparison of numbers of at most about 8.4 Mbit.
pub(super) fn products_past_the_memory_limit_rejected(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(
        out.matches("Number too large for the memory limit of `main`")
            .count(),
        n,
        "{out}"
    );
    assert_eq!(
        out.matches("Try `m.stdout <- String((b ^ ").count(),
        n,
        "{out}"
    );
}

#[test]
fn rejecting_many_products_past_the_memory_limit() {
    for n in [1, 3] {
        products_past_the_memory_limit_rejected(&products(n), n);
    }
}

/// The exponent of the first power in the repair offered for `expr` in `main` under a memory
/// limit of `limit` bytes, `b = 2^64 + 13`: `K` of "Try `m.stdout <- String((b ^ (2^K))`".
fn product_repair(limit: u32, expr: &str) -> String {
    let src = format!(
        "@limits(memory: {limit})\nmain(m: MainArgs) {{\n    b = 2^64 + 13;\n    \
         m.stdout <- String({expr});\n}}\n"
    );
    let out = rejected(&src);
    let k = out
        .split("Try `m.stdout <- String(")
        .nth(1)
        .and_then(|t| t.split("b ^ (2^").nth(1))
        .and_then(|t| t.split(')').next())
        .unwrap_or_else(|| panic!("no repair offered:\n{src}\n{out}"));
    k.to_string()
}

/// Row PERF-product-limit-built-to-measure: the repair of a product of two powers sizes the
/// product from its operands' bit lengths where only an order with a machine-word `int` reads
/// it, and builds it otherwise. Both give the same repair: each case below is compared with
/// the same product read through `+ 0`, which the size from the operands does not cover, so
/// the product is built and measured. `b ^ (2^11) * b ^ (2^12)` has `64 * 6144 + 1 = 393217`
/// bits, one past the room of 49152 bytes and within that of 49153, so the two limits offer
/// `2^10` and `2^11`, the product's size deciding each by one bit. Negative control: the same
/// reads at the two limits are offered different repairs, so a least size one bit too small
/// (`a + b - 2`) would offer `2^11` at 49152 and fail; and `> 2^64 + 13` and `== 0`, which the size from the operands does not cover,
/// are built on both sides and must agree with the rest.
#[test]
fn a_product_sized_from_its_operands_gives_the_repair_building_gives() {
    let p = "(b ^ (2^12)) * (b ^ (2^12))";
    for (limit, k) in [(49152, "10"), (49153, "11")] {
        for read in [
            format!("{p} > 0"),
            format!("{p} < 7"),
            format!("{p} >= -1"),
            format!("{p} <= 0"),
            format!("0 < {p}"),
            format!("{p} > 2^64 + 13"),
            format!("{p} == 0"),
        ] {
            let sized = product_repair(limit, &read);
            let built = product_repair(limit, &read.replacen(p, &format!("{p} + 0"), 1));
            assert_eq!(sized, built, "limit {limit}: {read}");
            assert_eq!(sized, k, "limit {limit}: {read}");
        }
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
/// `(2^64 + 13) ^ (2^27)` has at least `2^27 * 64 + 1` bits, 2^30 bytes and one bit, so its
/// headline rounds up to 1 GiB; `(2^64 + 13) ^ (2^20)` has at least 8 MiB.
#[test]
fn without_a_memory_limit_a_build_of_1_gib_or_more_is_rejected() {
    let main = |limit: &str, body: &str| {
        format!("{limit}main(m: MainArgs) {{\n    b = 2^64 + 13;\n    {body}\n}}\n")
    };
    let push = "m.stdout <- String(b ^ (2^27));";
    let out = rejected(&main("", push));
    assert!(
        out.contains(
            "Number too large for the default memory limit: `b ^ (2^27)` needs at least 1 GiB; \
             without `@limits(memory: …)` before `main`, no operation may make a value of 1 GiB \
             or more"
        ),
        "{out}"
    );
    // The repair is a limit before `main`, the least power of two that holds the build.
    assert!(out.contains("@limits(memory: 2^31)"), "{out}");
    assert_eq!(built(&main("@limits(memory: 2^31)\n", push)), None);
    // In a branch that is not taken, the same.
    let branch = "m.stdout <- if m.args.len() > 9 { String(b ^ (2^27)) } else { \"\" };";
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
    // Below 1 GiB the default accepts: 8 MiB, and the most a 65-bit base allows,
    // `2^26 * 64 + 1` bits, 512 MiB and one bit.
    for power in ["b ^ (2^20)", "b ^ (2^26)"] {
        let body = format!("m.stdout <- String({power});");
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

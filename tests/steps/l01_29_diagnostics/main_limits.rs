//! The limits written before `main` at compile time (plan row MAIN-limits; DESIGN.md sec:ports,
//! "`main` may limit its own run", and the sec:diagnostics row "Number too large for the memory
//! limit of `main`"): `@limits` and `@kill` stand only before `main`, each argument is a
//! positive constant, and a power whose result the types prove larger than the memory limit is
//! rejected, as one larger than the target's address space is (too_large.rs). The runs that hit
//! each limit are in l01_36a_executables/limits_binary.rs, since a limit holds for a whole
//! process.

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
               m.stdout <- String(b ^ (2^20));\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with(
            "4:24: Number too large for the memory limit of `main`: `b ^ (2^20)` needs at least \
             8 MiB; `@limits(memory: 1048576)`. Try `m.stdout <- String(b ^ (2^16))` instead."
        ),
        "{out}"
    );
    assert!(
        out.contains("the memory limit of `main` lets the run hold 1 MiB")
            && out.ends_with(
                "  fixes, each checked here:\n    m.stdout <- String(b ^ (2^16));    needs at \
                 least 512 KiB\n    @limits(memory: 2^24)              lets the run hold 16 MiB"
            ),
        "{out}"
    );
    // Without the limit, 8 MiB fits the address space; under it, 2^16 fits the limit.
    assert_eq!(built(&src.replace("@limits(memory: 1048576)\n", "")), None);
    assert_eq!(built(&src.replace("2^20", "2^16")), None);
}

#[test]
fn a_product_past_the_memory_limit_is_rejected_and_one_within_it_compiles() {
    // Plan row CONST-too-large-products-unproved (d): `x` has `2^22 + 1` bits, 512 KiB, within
    // the limit, and `x * x` at least `2^23 + 1`, past it. Before, only powers were judged
    // against the limit, and this compiled.
    let src = "@limits(memory: 1048576)\nmain(m: MainArgs) {\n    b = 2^64 + 13;\n    \
               x = b ^ (2^16);\n    m.stdout <- String(x * x);\n}\n";
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
    // Without the limit, 1 MiB fits the address space; under it, `x * b` fits the limit.
    assert_eq!(built(&src.replace("@limits(memory: 1048576)\n", "")), None);
    assert_eq!(built(&src.replace("x * x", "x * b")), None);
}

/// `n` powers of about 8 MiB each under a 1 MiB limit.
fn powers(n: usize) -> String {
    let mut s = String::from("@limits(memory: 1048576)\nmain(m: MainArgs) {\n");
    for i in 0..n {
        s.push_str(&format!(
            "    m.stdout <- String((2^64 + 13) ^ (2^20 + {i}));\n"
        ));
    }
    s + "}\n"
}

#[test]
fn rejecting_many_powers_past_the_memory_limit_scales() {
    // Each power is sized once in the walk and compared with the limit once after it: O(1)
    // words per power.
    scaling::check(
        "n powers past the memory limit of main, each rejected",
        100,
        |n| {
            let out = rejected(&powers(n));
            assert_eq!(
                out.matches("Number too large for the memory limit of `main`")
                    .count(),
                n
            );
        },
    );
}

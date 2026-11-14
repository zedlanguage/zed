//! The need a function whose parameter has no type passes to its callers (CHK-need-bound) is
//! read under the tests of the arm its use is in (DESIGN.md step L1.39): only what the arm
//! leaves unproven passes on, and an arm no value reaches passes on nothing. Found by
//! TEST-complete-reduced, fixed by FAIL-check-generic-need-ignores-arm (`Ck::ints_as_int`).

use zedc::run::load;

fn check(src: &str) -> Option<String> {
    let src = format!("{src}main(m: MainArgs) {{\n  m.stdout <- \"\";\n}}\n");
    load(src.as_bytes()).err()
}

#[test]
fn a_generic_function_passes_on_only_what_its_arm_leaves_unproven() {
    for src in [
        // The arm's test proves the domain of `popCount`: no need is left.
        "g(positional n) = if n >= 0 { popCount(n) } else { 0 };\nf(positional n: int) = g(n);\n",
        "g(positional n) = if n >= 0 { popCount(n) } else { 0 };\nf(positional n: int) = g(-5);\n",
        // The same through a lambda whose parameter has no type.
        "g = n -> if n >= 0 { popCount(n) } else { 0 };\nf(positional n: int) = g(n);\n",
        "g = n -> if n >= 0 && n <= 7 { bitNot(n, width: 3) } else { 0 };\nf(positional n: int) = g(100);\n",
        // An arm no value reaches.
        "g(positional n) = if n > 3 && n < 2 { popCount(n - n - 1) } else { 0 };\nf(positional n: int) = g(n);\n",
        "g = n -> if n > 3 && n < 2 { popCount(n - n - 1) } else { 0 };\nf(positional n: int) = g(n);\n",
    ] {
        if let Some(out) = check(src) {
            panic!("rejected:\n{src}{out}");
        }
    }
    // The control: with no test, the need passes on and `g(-5)` is rejected.
    let src = "g(positional n) = popCount(n);\nf(positional n: int) = g(-5);\n";
    let out = check(src).expect("rejected");
    assert!(out.contains("`g` takes `n` in int[0..]"), "{out}");
}

/// The neighbors of the fix: a need on ints is read with the parameters it reads taken as
/// int, under the tests of its arm; what the arm leaves unproven still passes on or is
/// rejected.
#[test]
fn a_generic_need_reads_the_arm_with_its_parameters_as_ints() {
    for src in [
        // Two parameters, each tested.
        "g(positional n, positional m) = if n >= 0 && m >= 0 { popCount(n + m) } else { 0 };\nf(positional n: int) = g(n, -1);\n",
        // A nested arm: the outer test proves the domain.
        "g(positional n) = if n >= 1 { if n < 10 { popCount(n) } else { 1 } } else { 0 };\nf(positional n: int) = g(-3);\n",
        // An `||` whose two ways each prove it.
        "g(positional n) = if n >= 5 || n == 0 { popCount(n) } else { 0 };\nf(positional n: int) = g(-3);\n",
        // The `else` arm of a test that fails below 0.
        "g(positional n) = if n < 0 { 0 } else { popCount(n) };\nf(positional n: int) = g(-3);\n",
    ] {
        if let Some(out) = check(src) {
            panic!("rejected:\n{src}{out}");
        }
    }
    for (src, says) in [
        // The arm leaves `n - 1` at -1.
        (
            "g(positional n) = if n >= 0 { popCount(n - 1) } else { 0 };\nf(positional n: int) = g(n);\n",
            "cannot show",
        ),
        // A test on another parameter says nothing of `n`: the need passes on.
        (
            "g(positional n, positional m) = if m >= 0 { popCount(n) } else { 0 };\nf(positional n: int) = g(-5, 1);\n",
            "`g` takes `n` in int[0..]",
        ),
        // The arm holds the ints below 0 only.
        (
            "g(positional n) = if n < 0 { popCount(n) } else { 0 };\nf(positional n: int) = g(-5);\n",
            "`g` takes `n` in int[0..]",
        ),
    ] {
        let out = check(src).unwrap_or_else(|| panic!("accepted:\n{src}"));
        assert!(out.contains(says), "{src}{out}");
    }
}

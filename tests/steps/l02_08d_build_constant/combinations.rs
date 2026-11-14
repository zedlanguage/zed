//! Completeness of step L2.8d (plan row TEST-complete-ports, COMPLETENESS.md beside this
//! file): each read of `build` in each position an expression takes, each target literal, and
//! each way the build's options are given. A read is a literal of the build, so staging keeps
//! the string of the branch the build takes and drops the other's.

use zedc::build::Build;
use zedc::run::load_for;

use super::lowered;

/// The build for x86_64 Linux of a package that declares `fast` and `slow`, with `on` on.
fn build(on: &[&str]) -> Build {
    Build::new("x86_64-linux", &["fast".into(), "slow".into()], on).unwrap()
}

#[test]
fn a_read_in_each_position_is_replaced_by_its_literal() {
    // Each program writes "KEEP" where the build for x86_64 Linux with `fast` on takes the
    // branch and "CUT" where it does not; staged, only "KEEP" is left.
    let main =
        |defs: &str, expr: &str| format!("{defs}main(m: MainArgs) {{\n  m.stdout <- {expr};\n}}\n");
    let cases = [
        (
            "if_condition",
            main("", "if build.options.fast { \"KEEP\" } else { \"CUT\" }"),
        ),
        (
            "negated",
            main("", "if !build.options.slow { \"KEEP\" } else { \"CUT\" }"),
        ),
        (
            "conjunction",
            main(
                "",
                "if build.options.fast && !build.options.slow { \"KEEP\" } else { \"CUT\" }",
            ),
        ),
        (
            "disjunction",
            main(
                "",
                "if build.options.slow || build.options.fast { \"KEEP\" } else { \"CUT\" }",
            ),
        ),
        (
            "target_not_equal",
            main(
                "",
                "if build.target != \"x86_64-linux\" { \"CUT\" } else { \"KEEP\" }",
            ),
        ),
        (
            "target_literal_on_the_left",
            main(
                "",
                "if \"x86_64-linux\" == build.target { \"KEEP\" } else { \"CUT\" }",
            ),
        ),
        (
            "helper_body",
            main(
                "pick() = if build.options.fast { \"KEEP\" } else { \"CUT\" };\n",
                "pick()",
            ),
        ),
        (
            "helper_argument",
            main(
                "pick(on: bool) = if on { \"KEEP\" } else { \"CUT\" };\n",
                "pick(on: build.options.fast)",
            ),
        ),
        (
            "bound_to_a_name",
            "main(m: MainArgs) {\n  on = build.options.fast;\n  \
             m.stdout <- if on { \"KEEP\" } else { \"CUT\" };\n}\n"
                .to_string(),
        ),
        (
            "nested_if",
            main(
                "",
                "if build.target == \"x86_64-linux\" { if build.options.slow { \"CUT\" } \
                 else { \"KEEP\" } } else { \"CUT\" }",
            ),
        ),
    ];
    let b = build(&["fast"]);
    let mut wrong = Vec::new();
    for (name, src) in &cases {
        let zir = lowered(src, &b, true);
        if !zir.contains("KEEP") || zir.contains("CUT") {
            wrong.push(format!("{name}:\n{zir}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn every_target_is_a_target_literal_on_either_side() {
    for t in [
        "x86_64-linux",
        "aarch64-linux",
        "riscv64-linux",
        "x86_64-macos",
        "aarch64-macos",
        "x86_64-windows",
        "aarch64-windows",
    ] {
        for src in [
            format!("f() = build.target == \"{t}\";\nmain(m: MainArgs) {{}}\n"),
            format!("f() = \"{t}\" != build.target;\nmain(m: MainArgs) {{}}\n"),
        ] {
            let p = load_for(src.as_bytes(), &Build::default());
            assert!(p.is_ok(), "{src}: {:?}", p.err());
        }
    }
}

#[test]
fn each_build_of_two_options_takes_its_own_branch() {
    let src = "main(m: MainArgs) {\n  m.stdout <- if build.options.fast { \
               if build.options.slow { \"both\" } else { \"fast only\" } } \
               else { if build.options.slow { \"slow only\" } else { \"neither\" } };\n}\n";
    let all = ["both", "fast only", "slow only", "neither"];
    for (on, kept) in [
        (&[][..], "neither"),
        (&["fast"][..], "fast only"),
        (&["slow"][..], "slow only"),
        (&["fast", "slow"][..], "both"),
        (&["slow", "fast"][..], "both"),
    ] {
        let zir = lowered(src, &build(on), true);
        for s in all {
            assert_eq!(zir.contains(s), s == kept, "{on:?}, {s}:\n{zir}");
        }
    }
}

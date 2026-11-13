//! The build modes (DESIGN.md Part F, "Build modes"; plan row BUILD-modes): the table names
//! the debug build and the optimized build, each preserving the program's values, and every
//! "X build" of DESIGN.md that names a kind of build is a name the bullet defines. The `sync`
//! tool checks DESIGN.md so (`zed_tools::spec_checks::build_modes`); this file tests that search
//! on small texts. A program gives the same expected outputs in each way this implementation
//! builds it, with and without the unit item `@log(#off);`.
//!
//! The implementation does not yet have the two modes (the log modes come with step L7.3, and
//! what a debug build optimizes is author question A25), so the run test covers the two
//! builds it has: the interpreter, `zedc run`, and the native executable, `zedc build`. There
//! is no log port before step L7.3, so the program writes no log line with or without the
//! item: the test compares the two builds against fixed outputs, and shows that both accept
//! the item and that it changes no output; it cannot yet show that logging off drops a line.

use std::path::Path;

use zed_tests::scaling;

use zed_tests::step_helpers::l01_36a_executables::{Ran, built, dir, executable, interpreter};
use zed_tools::spec_checks::{before_build, undefined_builds};

/// The places in `design` outside the "Build modes" bullet where a word names a kind of build
/// the bullet does not define.
fn undefined(design: &str) -> Vec<String> {
    undefined_builds(design).expect("the fixture has the bullet")
}

/// A small DESIGN.md: the bullet, then `rest`.
fn fixture(rest: &str) -> String {
    "# Zed\n\n- **Build modes.** A *debug build* or an *optimized build*.\n\n\
     | | Debug build | Optimized build |\n|---|---|---|\n| Values | x | the same |\n\n\
     A *counting build* counts.\n\n- **Next.** Text.\n"
        .to_string()
        + rest
}

#[test]
fn a_kind_of_build_the_bullet_does_not_define_is_named_with_its_line() {
    let ok = fixture("A debug build, the build, the step builds it, a counting build.\n");
    assert_eq!(undefined(&ok), Vec::<String>::new());
    let bad = fixture("Line.\nIn a release build and in fast builds, rebuild.\n");
    assert_eq!(
        undefined(&bad),
        ["13: \"release build\"", "13: \"fast build\""]
    );
}

#[test]
fn build_stage_and_build_dependent_are_not_kinds_of_build() {
    let text = fixture("A demanded build-stage term, a build-dependent string.\n");
    assert_eq!(undefined(&text), Vec::<String>::new());
}

/// The temperature conversion of step L1.21's programs; `@log(#off);` before it when `off`.
fn program(off: bool) -> String {
    let src = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("steps/l01_21_test_runner/zed/fahrenheit.zed"),
    )
    .unwrap();
    if off {
        format!("@log(#off);\n\n{src}")
    } else {
        src
    }
}

#[test]
fn a_run_gives_the_same_outputs_in_each_build_with_and_without_the_log_off_item() {
    let d = dir("build_modes");
    let cases: [(&[u8], &str); 4] = [
        (b"21\n", "69F\n"),
        (b" -40 \n", "-40F\n"),
        (b"twenty\n", "not a whole number: twenty\n"),
        (b"", "not a whole number: \n"),
    ];
    for off in [false, true] {
        let name = if off { "off" } else { "on" };
        let src = d.join(format!("{name}.zed"));
        std::fs::write(&src, program(off)).unwrap();
        let exe = d.join(name);
        built(&src, &exe);
        for (input, expected) in cases {
            let want = Ran {
                status: 0,
                stdout: expected.into(),
                stderr: String::new(),
            };
            assert_eq!(interpreter(&src, &[], input), want, "zedc run, {name}");
            assert_eq!(executable(&exe, &[], input), want, "zedc build, {name}");
        }
    }
}

#[test]
fn finding_the_kinds_of_build_is_linear() {
    let texts: Vec<(usize, String)> = [3000, 24000]
        .into_iter()
        .map(|n| {
            let rest: String = (0..n)
                .map(|i| format!("Line {i}: a debug build, the build, a counting build.\n"))
                .collect();
            (n, fixture(&rest))
        })
        .collect();
    scaling::check_order("finding the kinds of build in n lines", 3000, 1, |n| {
        let (_, text) = texts.iter().find(|(m, _)| *m == n).unwrap();
        assert!(undefined(text).is_empty());
        assert_eq!(before_build(text).len(), 3 * n + 5);
    });
}

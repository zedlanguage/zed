//! The build modes (DESIGN.md Part F, "Build modes"; plan row BUILD-modes): the table names
//! the debug build and the optimized build, each preserving the program's values, and every
//! "X build" of DESIGN.md that names a kind of build is a name the bullet defines. The `sync`
//! tool checks DESIGN.md so (`zed_tools::spec_checks::build_modes`), and m0_03
//! `sync::the_prose_checks_pass_on_the_spec` runs that check on the spec; this file tests the
//! search on small texts. A program gives the same expected outputs in each way this implementation
//! builds it, with and without the unit item `@log(#off);`.
//!
//! The implementation does not yet have the two modes (the log modes come with step L7.3, and
//! what a debug build optimizes is author question A25), so the run test covers the two
//! builds it has: the interpreter, `zedc run`, and the native executable, `zedc build`. There
//! is no log port before step L7.3, so the program writes no log line with or without the
//! item: the test compares the two builds against fixed outputs, and shows that both accept
//! the item and that it changes no output; it cannot yet show that logging off drops a line.

use std::path::Path;

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

/// A plan step's id before the verb "builds" names the step, not a kind of build, whatever
/// the form of its number (plan row FAIL-sync-build-modes-step-number: spec 92ceb14's "step
/// L1.24 builds the interval lattice" was read as a "24 build"). A number that is not a step id
/// before "build" is still named.
#[test]
fn a_step_id_before_builds_is_not_a_kind_of_build() {
    let steps = fixture(
        "Run once step L1.24 builds the interval lattice.\nStep L1.36b builds the note, \
         L10.4d builds it, M0.3 builds the table and L1.29d-package builds the package.\n\
         The compilers of step S.5 build it; with row S.2-forms builds an `Ast`; L4 builds.\n",
    );
    assert_eq!(undefined(&steps), Vec::<String>::new());
    let bad = fixture("A 1.24 build, a release build, e.g. build, a L1x.2 build.\n");
    assert_eq!(
        undefined(&bad),
        [
            "12: \"1.24 build\"",
            "12: \"release build\"",
            "12: \"l1x.2 build\""
        ]
    );
}

/// The pronoun "which" before the verb "builds" is its subject, not a kind of build (spec
/// 2a73c74, sec:strings: "a format string, which builds the string at run time"; found by
/// SPEC-copies-out, whose test runs these checks on the spec in place).
#[test]
fn which_before_builds_is_not_a_kind_of_build() {
    let text = fixture("A format string, which builds the string at run time.\n");
    assert_eq!(undefined(&text), Vec::<String>::new());
}

/// The branch `main` before the verb "builds" is its subject, not a kind of build (spec
/// 5cf7f90, step S.11: "Main builds the shim from source"; SYNC-copies-refresh-2).
#[test]
fn main_before_builds_is_not_a_kind_of_build() {
    let text = fixture("Main builds the shim from source with the pinned toolchain.\n");
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

/// A DESIGN.md of `n` lines after the bullet, each naming three kinds of build it defines
/// and a step `L1.i` that builds.
pub(super) fn lines_of_builds(n: usize) -> String {
    let rest: String = (0..n)
        .map(|i| {
            format!("Line {i}: a debug build, the build, a counting build; step L1.{i} builds.\n")
        })
        .collect();
    fixture(&rest)
}

/// Asserts every kind of build the text `text` of [`lines_of_builds`]`(n)` names defined, and
/// found before the word `build` `4n + 5` times.
pub(super) fn kinds_found(text: &str, n: usize) {
    assert!(undefined(text).is_empty());
    assert_eq!(before_build(text).len(), 4 * n + 5);
}

/// The kinds of build in a few lines are found; the time is held linear in `bench/modes.rs`.
#[test]
fn finding_the_kinds_of_build_in_a_few_lines() {
    for n in [0, 1, 2, 9] {
        kinds_found(&lines_of_builds(n), n);
    }
}

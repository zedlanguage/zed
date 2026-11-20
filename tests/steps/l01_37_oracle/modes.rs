//! The oracle runs each source in a debug build and an optimized build (DESIGN.md "Build modes",
//! zed 806bc8c; plan row TEST-oracle-both-modes) and compares both with the interpreter. Until
//! the optimizer exists both modes run the same code (`zedc::build::Mode`), so these tests check
//! the harness: that it runs both modes, and that a change to either mode's output alone makes
//! the check fail (the negative control).

use super::scaling::bump;
use zed_tests::oracle::{native, native_by, program, unit};
use zedc::build::Mode;
use zedc::run::Through;

/// A unit of two bindings, the second reading the first.
const UNIT: &str = "x = 1;\ny = x + 1;\n";

/// A program that writes a line (`<-` on `stdout` adds the newline) and gives the exit status 7.
const STATUS: &str = "main(m: MainArgs) -> int {\n  m.stdout <- \"hi\";\n  7\n}\n";

/// The native engines of [`native`], with every integer of the result one more in the engines
/// of `changed`, and the others as they are.
fn changing(changed: Option<Mode>) -> impl Fn(Mode, bool) -> Box<Through<'static>> {
    move |mode, fuse| {
        let run = zed_native::through(mode, fuse);
        if Some(mode) == changed {
            Box::new(move |t, ev| run(t, ev).map(bump))
        } else {
            Box::new(run)
        }
    }
}

/// The mismatches the oracle reports on [`UNIT`]'s bindings and [`STATUS`]'s wave, with the
/// engines of `changed` giving other outputs.
fn mismatches(changed: Option<Mode>) -> Vec<String> {
    let ((binds, (wave, want)), runs) = native_by(changing(changed), |engines| {
        (unit(UNIT, engines), program(STATUS, b"", engines))
    });
    // The two bindings run together once, and the wave once, under each of four engines. Each
    // engine compares the two bindings and the table checks, of which this unit has none, so
    // they run nothing and agree.
    assert_eq!(runs, 8, "native runs, each leaving no cell live");
    assert_eq!((binds.compared, wave.compared), (12, 4));
    assert_eq!(
        want.as_deref(),
        Some(r#"port `m.stdout` writes "hi\n", and the exit status 7"#)
    );
    binds
        .mismatches
        .into_iter()
        .chain(wave.mismatches)
        .collect()
}

/// The mismatches [`mismatches`] reports when the engines of `mode` give other outputs.
fn expected(mode: &str) -> Vec<String> {
    let differences = [
        ("binding `x`", "the value 1", "the value 2"),
        ("binding `y`", "the value 2", "the value 3"),
        (
            "the wave",
            r#"port `m.stdout` writes "hi\n", and the exit status 7"#,
            r#"port `m.stdout` writes "hi\n", and the exit status 8"#,
        ),
    ];
    let mut all = Vec::new();
    for (what, want, got) in differences {
        for plan in ["fused", "unfused"] {
            let e = format!("native ({mode}, {plan})");
            all.push(format!(
                "{what}: the interpreter gives {want}, and {e} gives {got}"
            ));
        }
    }
    all
}

#[test]
fn the_oracle_runs_a_debug_and_an_optimized_build_of_each_plan() {
    let (names, runs) = native(|engines| {
        engines
            .iter()
            .map(|(n, _)| n.to_string())
            .collect::<Vec<_>>()
    });
    assert_eq!(
        names,
        [
            "native (debug, fused)",
            "native (debug, unfused)",
            "native (optimized, fused)",
            "native (optimized, unfused)",
        ]
    );
    assert_eq!(runs, 0);
}

#[test]
fn both_builds_agree_with_the_interpreter() {
    assert_eq!(mismatches(None), Vec::<String>::new());
}

/// The negative control: an optimized build whose output differs from the interpreter's, while
/// the debug build's does not, fails the oracle, and the report names the optimized engines
/// alone. The exit status is compared too: the wave's writes are the same in every engine here,
/// and only its status differs.
#[test]
fn an_optimized_build_that_differs_fails_the_oracle() {
    assert_eq!(mismatches(Some(Mode::Optimized)), expected("optimized"));
}

/// The same with the debug build's output changed: either mode alone is enough.
#[test]
fn a_debug_build_that_differs_fails_the_oracle() {
    assert_eq!(mismatches(Some(Mode::Debug)), expected("debug"));
}

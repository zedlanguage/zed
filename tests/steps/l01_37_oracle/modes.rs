//! The oracle runs one build mode, the one the test run asks for through the environment
//! variable `ZED_BUILD_MODE` (`debug` or `optimized`, unset meaning `optimized`;
//! `zed_tests::oracle::mode`). Every rewrite carries a certificate that it keeps the semantics
//! (DESIGN.md sec:optimizer, "Certificates"; step L3.21), so the two builds are proved equal
//! and only the asked-for one runs (author, 2026-11-20, correcting A25; plan row
//! TEST-oracle-both-modes). The oracle also compares `main`'s exit status.

use std::cell::RefCell;
use std::process::Command;

use super::scaling::bump;
use zed_tests::oracle::{MODE_VARIABLE, mode, mode_of, native, native_by, program, unit};
use zedc::build::Mode;
use zedc::run::Through;

/// A unit of two bindings, the second reading the first.
const UNIT: &str = "x = 1;\ny = x + 1;\n";

/// A program that writes a line (`<-` on `stdout` adds the newline) and gives the exit status 7.
const STATUS: &str = "main(m: MainArgs) -> int {\n  m.stdout <- \"hi\";\n  7\n}\n";

/// The names of the two engines of `mode`.
fn engines_of(mode: Mode) -> [String; 2] {
    ["fused", "unfused"].map(|plan| format!("native ({}, {plan})", mode.name()))
}

#[test]
fn the_setting_names_the_build_mode_and_unset_is_optimized() {
    assert_eq!(mode_of(None), Ok(Mode::Optimized));
    assert_eq!(mode_of(Some("debug")), Ok(Mode::Debug));
    assert_eq!(mode_of(Some("optimized")), Ok(Mode::Optimized));
}

/// The negative control of the setting: a value that names no mode is an error naming the
/// variable, the value and the two values it may take, not a silent default.
#[test]
fn a_setting_that_names_no_mode_is_an_error() {
    let want = "ZED_BUILD_MODE=\"fast\" names no build mode: write `debug` or `optimized`, or \
                leave it unset for `optimized`";
    assert_eq!(mode_of(Some("fast")), Err(want.to_string()));
    // Case and spaces count: only the two exact words are modes.
    for wrong in ["", "Debug", "optimized ", "release"] {
        assert!(mode_of(Some(wrong)).is_err(), "{wrong:?}");
    }
}

/// Each mode runs exactly its own two engines, one per plan, each run counted: the engine maker
/// is asked for that mode alone, once per plan, and [`STATUS`] runs once under each.
#[test]
fn each_mode_runs_its_own_two_engines_alone() {
    for m in Mode::ALL {
        let asked = RefCell::new(Vec::new());
        let ((names, wave), runs) = native_by(
            m,
            |mode, fuse| {
                asked.borrow_mut().push((mode, fuse));
                Box::new(zed_native::through(mode, fuse))
            },
            |engines| {
                let names: Vec<String> = engines.iter().map(|(n, _)| n.to_string()).collect();
                (names, program(STATUS, b"", engines).0)
            },
        );
        assert_eq!(asked.into_inner(), [(m, true), (m, false)]);
        assert_eq!(names, engines_of(m));
        assert_eq!((runs, wave.compared), (2, 2));
        assert_eq!(wave.mismatches, Vec::<String>::new());
    }
}

/// The engines of this run's mode, as [`native`] gives them, and its runs of [`STATUS`],
/// printed for [`the_variable_picks_the_mode_of_a_test_run`], which runs this test in a child
/// process under each setting.
#[test]
fn the_engines_of_this_run_are_those_of_its_mode() {
    let (names, runs) = native(|engines| {
        program(STATUS, b"", engines);
        engines
            .iter()
            .map(|(n, _)| n.to_string())
            .collect::<Vec<_>>()
    });
    assert_eq!(names, engines_of(mode()));
    assert_eq!(runs, 2);
    println!("engines: {}; runs: {runs}", names.join(", "));
}

/// Runs [`the_engines_of_this_run_are_those_of_its_mode`] in a child process of this test binary
/// with [`MODE_VARIABLE`] set to `setting`, or removed: whether it passed, and its output.
fn child(setting: Option<&str>) -> (bool, String) {
    let mut c = Command::new(std::env::current_exe().unwrap());
    c.args([
        "--exact",
        "modes::the_engines_of_this_run_are_those_of_its_mode",
        "--nocapture",
        "--test-threads=1",
    ]);
    match setting {
        Some(s) => c.env(MODE_VARIABLE, s),
        None => c.env_remove(MODE_VARIABLE),
    };
    let out = c.output().unwrap();
    let text =
        String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr);
    (out.status.success(), text)
}

/// The variable picks the mode of a whole test run, read where [`native`] reads it: each value
/// runs that mode's two engines and no others, unset runs the optimized build, and a value that
/// names no mode fails the run with the error (the negative control).
#[test]
fn the_variable_picks_the_mode_of_a_test_run() {
    for (setting, m) in [
        (Some("debug"), Mode::Debug),
        (Some("optimized"), Mode::Optimized),
        (None, Mode::Optimized),
    ] {
        let (passed, text) = child(setting);
        assert!(passed, "{setting:?}: {text}");
        let want = format!("engines: {}; runs: 2", engines_of(m).join(", "));
        assert!(text.contains(&want), "{setting:?}: {text}");
    }
    let (passed, text) = child(Some("fast"));
    assert!(!passed, "{text}");
    assert!(
        text.contains("ZED_BUILD_MODE=\"fast\" names no build mode"),
        "{text}"
    );
}

/// The engines of `mode`, with every integer of the result one more when `changed`.
fn changing(changed: bool) -> impl Fn(Mode, bool) -> Box<Through<'static>> {
    move |mode, fuse| {
        let run = zed_native::through(mode, fuse);
        if changed {
            Box::new(move |t, ev| run(t, ev).map(bump))
        } else {
            Box::new(run)
        }
    }
}

/// The mismatches the oracle reports on [`UNIT`]'s bindings and [`STATUS`]'s wave in the
/// optimized build, its engines giving other outputs when `changed`.
fn mismatches(changed: bool) -> Vec<String> {
    let ((binds, (wave, want)), runs) = native_by(Mode::Optimized, changing(changed), |engines| {
        (unit(UNIT, engines), program(STATUS, b"", engines))
    });
    // The two bindings run together once, and the wave once, under each of the two engines.
    // Each engine compares the two bindings and the table checks, of which this unit has none,
    // so they run nothing and agree.
    assert_eq!(runs, 4, "native runs, each leaving no cell live");
    assert_eq!((binds.compared, wave.compared), (6, 2));
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

#[test]
fn the_engines_agree_with_the_interpreter() {
    assert_eq!(mismatches(false), Vec::<String>::new());
}

/// A build whose outputs differ from the interpreter's fails the oracle, and the exit status
/// is compared too: the wave's writes are the same in every engine here, and only its status
/// differs, 8 for 7.
#[test]
fn a_build_that_differs_fails_the_oracle_on_its_exit_status_too() {
    let differences = [
        ("binding `x`", "the value 1", "the value 2"),
        ("binding `y`", "the value 2", "the value 3"),
        (
            "the wave",
            r#"port `m.stdout` writes "hi\n", and the exit status 7"#,
            r#"port `m.stdout` writes "hi\n", and the exit status 8"#,
        ),
    ];
    let mut want = Vec::new();
    for (what, interpreter, got) in differences {
        for e in engines_of(Mode::Optimized) {
            want.push(format!(
                "{what}: the interpreter gives {interpreter}, and {e} gives {got}"
            ));
        }
    }
    assert_eq!(mismatches(true), want);
}

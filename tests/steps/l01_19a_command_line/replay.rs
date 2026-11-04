//! The arguments in the record and in a test table: `--record` saves them, `zedc replay`
//! reads them from the record whatever its own command line holds, and a row of `main`'s
//! table gives them as a `String`, one argument per line.

use std::ffi::OsString;

use zedc::run::{Record, load};

use super::{ECHO, dir, program, run_words, zedc};
use crate::l01_21_test_runner::checks;

#[test]
fn a_replay_sees_the_recorded_arguments_not_its_own() {
    let prog = program("replay", ECHO);
    let rec = dir("replay").join("wave.rec").into_os_string();
    let rec_s = rec.to_str().unwrap();
    let out = zedc(&run_words(&prog, &["--record", rec_s, "--", "a", "b c"]));
    assert_eq!((out.status, out.stdout.as_str()), (0, "a\nb c\n"));
    let replay = |more: &[&str]| {
        let mut words = vec![OsString::from("replay"), prog.clone(), rec.clone()];
        words.extend(more.iter().map(OsString::from));
        zedc(&words)
    };
    for more in [&[][..], &["--", "other", "words", "here"][..]] {
        let out = replay(more);
        assert_eq!(
            (out.status, out.stdout.as_str()),
            (0, "a\nb c\n"),
            "{more:?}"
        );
    }
}

#[test]
fn a_record_made_with_no_arguments_replays_with_none() {
    let prog = program("replay_none", ECHO);
    let rec = dir("replay_none").join("wave.rec").into_os_string();
    let out = zedc(&run_words(&prog, &["--record", rec.to_str().unwrap()]));
    assert_eq!((out.status, out.stdout.as_str()), (0, ""));
    let words = [OsString::from("replay"), prog, rec, "--".into(), "x".into()];
    let out = zedc(&words);
    assert_eq!((out.status, out.stdout.as_str()), (0, ""));
}

#[test]
fn the_record_holds_the_arguments_only_of_a_program_that_reads_them() {
    let echo = load(ECHO.as_bytes()).unwrap();
    let args = ["x".to_string(), "".to_string()];
    let wave = echo
        .run_args(&Default::default(), &args, |_| unreachable!())
        .unwrap();
    assert_eq!(wave.record.args, args);
    assert_eq!(echo.replay(&wave.record).unwrap().writes, wave.writes);
    let hello = load(b"main() -> (stdout: Lines) {\n  stdout <- \"hi\";\n}\n").unwrap();
    let wave = hello
        .run_args(&Default::default(), &args, |_| unreachable!())
        .unwrap();
    assert_eq!(wave.record, Record::default());
}

#[test]
fn the_arguments_of_a_record_round_trip() {
    let record = Record {
        args: vec![
            "plain".into(),
            "".into(),
            "two\nlines".into(),
            "--".into(),
            "é 7".into(),
        ],
        ..Record::default()
    };
    let bytes = record.to_bytes();
    assert!(bytes.starts_with(b"zed record 1\narg 5\nplain\narg 0\n\n"));
    assert_eq!(Record::from_bytes(&bytes), Ok(record));
    // A record from before this step, with no `arg` entries, holds no arguments.
    let old = Record::from_bytes(b"zed record 1\nlines 5 2\nstdinab\n").unwrap();
    assert!(old.args.is_empty());
}

#[test]
fn a_main_row_gives_the_arguments_one_per_line() {
    let src = "main(args: CommandLine) -> (stdout: Lines) {\n  \
               stdout <- \"${args[1] else \"-\"}+${args[2] else \"-\"}\";\n}\n\
               test { \"a\\nb c\\n\" -> \"a+b c\\n\", \"only\" -> \"only+-\\n\", \"\" -> \"-+-\\n\", \
               3 -> \"\" }\n";
    assert_eq!(
        checks(src),
        [
            "4:8: ok",
            "4:33: ok",
            "4:55: ok",
            "4:70: `3 -> \"\"` of `main`: the `CommandLine` port `args` is given as a String, \
             one argument per line, not 3",
        ]
    );
}

#[test]
fn two_command_line_ports_see_one_command_line() {
    let src = "main(a: CommandLine, b: CommandLine) -> (stdout: Lines) {\n  \
               stdout <- (a[1] else \"-\") ++ (b[1] else \"-\");\n}\n\
               test { (\"x\", \"x\") -> \"xx\\n\", (\"x\", \"y\") -> \"\" }\n";
    assert_eq!(
        checks(src),
        [
            "4:8: ok",
            "4:30: `(\"x\", \"y\") -> \"\"` of `main`: the `CommandLine` ports `a` and `b` are \
             given different arguments; a run has one command line",
        ]
    );
    let out = super::run("two", src, &["--", "z"]);
    assert_eq!(out.stdout, "zz\n");
}

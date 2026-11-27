//! The arguments in the record and in a test table: `--record` saves them, `zedc replay`
//! reads them from the record whatever its own command line holds, and a row of `main`'s
//! table gives them as a `String`, one argument per line.

use std::ffi::OsString;

use zedc::run::{Record, load};

use super::{ECHO, dir, program, run_words, zedc};
use zed_tests::step_helpers::l01_21_test_runner::checks;

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
    let hello = load(b"main(m: MainArgs) {\n  m.stdout <- \"hi\";\n}\n").unwrap();
    let wave = hello
        .run_args(&Default::default(), &args, |_| unreachable!())
        .unwrap();
    let only_the_program = Record {
        program: Some(hello.address().unwrap()),
        ..Record::default()
    };
    assert_eq!(wave.record, only_the_program);
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
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- \"${m.args[0] else #outOfBounds -> \"-\"}+${m.args[1] else #outOfBounds -> \"-\"}\";\n}\n\
               test { { args: \"a\\nb c\\n\" } -> \"a+b c\\n\", { args: \"only\" } -> \"only+-\\n\", \
               \"\" -> \"-+-\\n\" }\n";
    assert_eq!(checks(src), ["4:8: ok", "4:43: ok", "4:75: ok"]);
    // Arguments given as anything but a String are refused when the unit is checked (plan row
    // PORT-main-key-values-unchecked), before any row runs; until then `{ args: 3 }` failed
    // only its own row, when it ran.
    let src = src.replace(
        "\"\" -> \"-+-\\n\" }",
        "\"\" -> \"-+-\\n\", { args: 3 } -> \"\" }",
    );
    let got = checks(&src);
    // Each of the four rows as not run, and the rejection, at the key item of the last row,
    // after that row's start.
    assert_eq!(got.len(), 5, "{got:?}");
    assert!(got[4].contains("`main::args` does not take 3"), "{got:?}");
    assert!(
        (got.iter().take(4)).all(|g| g.ends_with("not run, since the unit is rejected")),
        "{got:?}"
    );
}

#[test]
fn a_main_rows_arguments_end_at_each_line_end() {
    // The String's lines are read as a `Lines` input's: `\n`, `\r\n` and a lone `\r` each end
    // one (author, 2026-11-13, QUESTIONS A90).
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- \"${m.args[0] else #outOfBounds -> \"-\"}+${m.args[1] else #outOfBounds -> \"-\"}\";\n}\n\
               test { { args: \"a\\rb\\r\\nc\" } -> \"a+b\\n\", { args: \"a\\r\\r\\n\" } -> \"a+\\n\", { args: \"a\\r\" } -> \"a+-\\n\" }\n";
    assert_eq!(checks(src), ["4:8: ok", "4:42: ok", "4:73: ok"]);
}

//! The environment in the record: `--record` saves each name the wave read and what the read
//! gave, and `zedc replay` gives the program those, whatever its own environment holds.

use std::ffi::OsString;
use std::sync::Arc;

use zed_kernel::Value;
use zedc::run::{Environment, Record, load};

use super::{TWO, dir_program, run_words, vars, zedc};
use zed_tests::step_helpers::l01_19a_command_line::dir;

#[test]
fn a_replay_gives_the_recorded_values_with_the_variables_unset() {
    let prog = dir_program("replay", TWO);
    let rec = dir("l01_19c_replay").join("wave.rec").into_os_string();
    let out = zedc(
        &run_words(&prog, &["--record", rec.to_str().unwrap()]),
        vars(&[("ZED_A", b"recorded")]),
    );
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "recorded|-\n"),
        "{}",
        out.stderr
    );
    let words = [OsString::from("replay"), prog, rec];
    for env in [vec![], vars(&[("ZED_A", b"other"), ("ZED_B", b"set now")])] {
        let out = zedc(&words, env);
        assert_eq!(
            (out.status, out.stdout.as_str()),
            (0, "recorded|-\n"),
            "{}",
            out.stderr
        );
    }
}

#[test]
fn the_record_holds_the_names_read_and_what_each_gave() {
    let two = load(TWO.as_bytes()).unwrap();
    let env = Arc::new(Environment::new(vars(&[
        ("ZED_A", b"a"),
        ("PATH", b"/bin"),
    ])));
    let wave = two
        .run_args(&Default::default(), &[], |_| Arc::clone(&env) as _)
        .unwrap();
    let read = &wave.record.files["env"];
    assert_eq!(
        read.iter().collect::<Vec<_>>(),
        [
            (&Value::str("ZED_A"), &Value::str("a")),
            (&Value::str("ZED_B"), &Value::atom("notFound")),
        ]
    );
    let back = Record::from_bytes(&wave.record.to_bytes()).unwrap();
    assert_eq!(back, wave.record);
    assert_eq!(two.replay(&back).unwrap().writes, wave.writes);
}

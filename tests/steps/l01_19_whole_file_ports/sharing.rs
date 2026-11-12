//! A wave's record shares the bytes of each `Lines` input it was given (T11-unit-share): the
//! record holds the same `Arc<[u8]>` as the input, and a replay's record the same as the record
//! it replays, so neither copies the input.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::Lookup;
use zed_tests::scaling::{check, inputs};
use zedc::run::{Program, load};
use zedc::testing::test;

/// Writes the last of its `n` lines, so the wave reads the whole input.
fn last_line(n: usize) -> Program {
    let src = format!(
        "main(m: MainArgs) {{\n  m.stdout <- m.stdin[{}] else \"\";\n}}\n",
        n - 1
    );
    load(src.as_bytes()).unwrap()
}

/// `n` lines, `line 0` to `line n-1`.
fn lines(n: usize) -> Arc<[u8]> {
    let text: String = (0..n).map(|i| format!("line {i}\n")).collect();
    Arc::from(text.as_bytes())
}

fn no_files(_: &str) -> Arc<dyn Lookup> {
    unreachable!("no `Files` port")
}

#[test]
fn the_record_holds_the_input_it_was_given_and_its_replay_the_same() {
    let p = last_line(3);
    let input = BTreeMap::from([("m.stdin".to_string(), lines(3))]);
    let wave = p.run(&input, no_files).unwrap();
    assert_eq!(
        wave.writes,
        [("m.stdout".to_string(), b"line 2\n".to_vec())]
    );
    assert!(Arc::ptr_eq(
        &wave.record.lines["m.stdin"],
        &input["m.stdin"]
    ));
    let again = p.replay(&wave.record).unwrap();
    assert_eq!(again.writes, wave.writes);
    assert!(Arc::ptr_eq(
        &again.record.lines["m.stdin"],
        &input["m.stdin"]
    ));
}

#[test]
fn a_record_read_back_from_bytes_replays_the_same_wave() {
    // A record read from its bytes holds bytes of its own, and a replay of it shares those.
    let p = last_line(2);
    let input = BTreeMap::from([("m.stdin".to_string(), lines(2))]);
    let wave = p.run(&input, no_files).unwrap();
    let back = zedc::run::Record::from_bytes(&wave.record.to_bytes()).unwrap();
    assert_eq!(back, wave.record);
    let again = p.replay(&back).unwrap();
    assert_eq!(again.writes, wave.writes);
    assert!(Arc::ptr_eq(
        &again.record.lines["m.stdin"],
        &back.lines["m.stdin"]
    ));
}

#[test]
fn a_wave_over_n_lines_and_its_replay_share_the_input_and_scale() {
    let waves = inputs(20_000, |n| {
        let input = BTreeMap::from([("m.stdin".to_string(), lines(n))]);
        (last_line(n), input)
    });
    check("a wave over n lines and its replay", 20_000, |n| {
        let (p, input) = &waves[&n];
        let wave = p.run(input, no_files).unwrap();
        let again = p.replay(&wave.record).unwrap();
        assert_eq!(again.writes, wave.writes);
        assert!(Arc::ptr_eq(
            &again.record.lines["m.stdin"],
            &input["m.stdin"]
        ));
    });
}

#[test]
fn rows_still_run_when_the_program_is_refused() {
    // The builder gives each `main` the parameters of the fields its body reads, so two `main`s
    // that read different fields have different parameter types: the unit is accepted,
    // `run::program` refuses it as a program, and the table of `next` still runs.
    let text = "main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n\
                main(m: MainArgs) {\n  m.stdout <- m.args[0] else \"\";\n}\n\
                next(positional x) = x + 1\ntest {\n  1 -> 2,\n  2 -> 4\n}\n";
    let outcomes: Vec<(usize, Option<String>)> = test(text)
        .into_iter()
        .map(|o| (o.line, o.failure))
        .collect();
    let (line, refusal) = &outcomes[0];
    assert_eq!(*line, 4);
    assert!(
        refusal
            .as_deref()
            .is_some_and(|r| r.starts_with("this file declares 2 functions named `main`")),
        "{refusal:?}"
    );
    assert_eq!(
        outcomes[1..],
        [
            (9, None),
            (10, Some("`2 -> 4` of `next`: the result is 3".to_string())),
        ]
    );
}

#[test]
fn a_second_main_is_a_duplicate_and_no_row_runs() {
    // Two `main`s that read the same fields (here none) have the same parameter types: the
    // resolver rejects the unit at the second, and no row runs. (A `main`
    // with a header it may not have rejects the whole unit the same way:
    // `a_main_with_a_wrong_header_reports_once_and_runs_no_row` in step L1.21.)
    let text = "main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n\
                main() {\n}\n\
                next(positional x) = x + 1\ntest {\n  1 -> 2,\n  2 -> 4\n}\n";
    let outcomes: Vec<(usize, Option<String>)> = test(text)
        .into_iter()
        .map(|o| (o.line, o.failure))
        .collect();
    let (line, rejection) = &outcomes[0];
    assert_eq!(*line, 4);
    assert!(
        rejection
            .as_deref()
            .is_some_and(|r| r.starts_with("`main` is already declared in this scope")),
        "{rejection:?}"
    );
    let not_run = |case: &str| {
        Some(format!(
            "`{case}` of `next`: not run, since the unit is rejected"
        ))
    };
    assert_eq!(
        outcomes[1..],
        [(8, not_run("1 -> 2")), (9, not_run("2 -> 4"))]
    );
}

#[test]
fn zedc_run_reading_a_file_of_n_lines_on_stdin_scales() {
    let dir = std::env::temp_dir().join("zed-l01-19-sharing-scaling");
    std::fs::create_dir_all(&dir).unwrap();
    let program = dir.join("first.zed");
    std::fs::write(
        &program,
        "main(m: MainArgs) {\n  m.stdout <- m.stdin[0] else \"\";\n}\n",
    )
    .unwrap();
    let files = inputs(20_000, |n| {
        let path = dir.join(format!("input-{n}.txt"));
        std::fs::write(&path, &*lines(n)).unwrap();
        path
    });
    check("zedc run reading a file of n lines on stdin", 20_000, |n| {
        let args = ["run".to_string(), program.display().to_string()];
        let mut input = std::fs::File::open(&files[&n]).unwrap();
        let mut out = Vec::new();
        let status = zedc::run::command(&args, &mut input, &mut out, &mut std::io::sink());
        assert_eq!((status, out), (0, b"line 0\n".to_vec()));
    });
    std::fs::remove_file(&program).unwrap();
    for path in files.values() {
        std::fs::remove_file(path).unwrap();
    }
}

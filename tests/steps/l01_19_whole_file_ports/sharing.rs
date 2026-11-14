//! A wave's record shares the bytes of each `Lines` input it was given (T11-unit-share): the
//! record holds the same `Arc<[u8]>` as the input, and a replay's record the same as the record
//! it replays, so neither copies the input.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::Lookup;
use zedc::run::{Program, load};
use zedc::testing::test;

/// Writes the last of its `n` lines, so the wave reads the whole input.
pub(super) fn last_line(n: usize) -> Program {
    let src = format!(
        "main(m: MainArgs) {{\n  m.stdout <- m.stdin[{}] else \"\";\n}}\n",
        n - 1
    );
    load(src.as_bytes()).unwrap()
}

/// `n` lines, `line 0` to `line n-1`.
pub(super) fn lines(n: usize) -> Arc<[u8]> {
    let text: String = (0..n).map(|i| format!("line {i}\n")).collect();
    Arc::from(text.as_bytes())
}

pub(super) fn no_files(_: &str) -> Arc<dyn Lookup> {
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

/// Runs `program` and replays its record: the replay writes what the run wrote, and its
/// record shares the input's bytes, copying none of them.
pub(super) fn replays_sharing_the_input(program: &Program, input: &BTreeMap<String, Arc<[u8]>>) {
    let wave = program.run(input, no_files).unwrap();
    let again = program.replay(&wave.record).unwrap();
    assert_eq!(again.writes, wave.writes);
    assert!(Arc::ptr_eq(
        &again.record.lines["m.stdin"],
        &input["m.stdin"]
    ));
}

/// `bench::a_wave_over_n_lines_and_its_replay_share_the_input_and_scale` at a small size.
#[test]
fn a_wave_and_its_replay_share_the_input() {
    let input = BTreeMap::from([("m.stdin".to_string(), lines(3))]);
    replays_sharing_the_input(&last_line(3), &input);
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

/// The program `zedc run` runs on a file of lines: it writes the first.
pub(super) const FIRST_LINE: &str = "main(m: MainArgs) {\n  m.stdout <- m.stdin[0] else \"\";\n}\n";

/// `zedc run program` with the file `input` on standard input: it writes `line 0`.
pub(super) fn runs_on_the_file(program: &std::path::Path, input: &std::path::Path) {
    let args = ["run".to_string(), program.display().to_string()];
    let mut input = std::fs::File::open(input).unwrap();
    let mut out = Vec::new();
    let status = zedc::run::command(&args, &mut input, &mut out, &mut std::io::sink());
    assert_eq!((status, out), (0, b"line 0\n".to_vec()));
}

/// `bench::zedc_run_reading_a_file_of_n_lines_on_stdin_scales` at a small size.
#[test]
fn zedc_run_reads_a_file_of_lines_on_stdin() {
    let dir = super::dir("sharing_file_stdin");
    let program = dir.join("first.zed");
    std::fs::write(&program, FIRST_LINE).unwrap();
    let input = dir.join("input.txt");
    std::fs::write(&input, &*lines(3)).unwrap();
    runs_on_the_file(&program, &input);
}

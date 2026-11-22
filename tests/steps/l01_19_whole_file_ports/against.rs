//! Step L1.19d: `zedc replay old.zed <record> --program new.zed` replays a record of `old.zed`
//! against an edited program: each recorded input is checked against the ports of `new.zed`,
//! both programs run on the recorded inputs, and each output port's first differing line and
//! line counts are reported.

use std::path::PathBuf;

use zedc::run::Record;

use super::{Outcome, dir, zedc};

/// A program that writes its standard input to standard output, line by line.
const CAT: &str = "main(m: MainArgs) {\n  m.stdout <- m.stdin;\n}\n";

/// `CAT` with only its body changed: each line equal to `from` is written as `to`.
fn cat_changing(from: &str, to: &str) -> String {
    format!(
        "main(m: MainArgs) {{\n  m.stdout <- m.stdin.map(l -> l else #ioError -> \"\")\
         .map(l -> if l == \"{from}\" {{ \"{to}\" }} else {{ l }});\n}}\n"
    )
}

/// The files of one test in the directory `name`: `old.zed` holding `old`, `new.zed` holding
/// `new`, and `wave.rec`, the record of a run of `old.zed` on standard input `stdin`. Gives
/// the three paths.
fn recorded(name: &str, old: &str, new: &str, stdin: &str) -> [String; 3] {
    let d = dir(name);
    let path = |f: &str| -> PathBuf { d.join(f) };
    let (o, n, r) = (path("old.zed"), path("new.zed"), path("wave.rec"));
    std::fs::write(&o, old).unwrap();
    std::fs::write(&n, new).unwrap();
    let [o, n, r] = [o, n, r].map(|p| p.to_str().unwrap().to_string());
    let out = zedc(&["run", &o, "--record", &r], stdin);
    assert_eq!(out.status, 0, "{}", out.stderr);
    [o, n, r]
}

/// `zedc replay old rec --program new`, with nothing on standard input: a replay reads none.
fn against(old: &str, rec: &str, new: &str) -> Outcome {
    zedc(&["replay", old, rec, "--program", new], "")
}

#[test]
fn an_edit_of_a_body_reports_the_first_differing_line_with_both_texts() {
    let [old, new, rec] = recorded("against_body", CAT, &cat_changing("b", "B"), "a\nb\nc\n");
    let out = against(&old, &rec, &new);
    assert_eq!(
        (out.status, out.stdout, out.stderr.as_str()),
        (
            0,
            format!(
                "m.stdout: the line at key 1 differs: {old} writes \"b\", and {new} writes \
                 \"B\"; {old} writes 3 lines, and {new} 3.\n"
            ),
            ""
        )
    );
}

#[test]
fn an_edit_that_changes_no_output_reports_no_difference() {
    let [old, new, rec] = recorded("against_same", CAT, &cat_changing("z", "Z"), "a\nb\nc\n");
    let out = against(&old, &rec, &new);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (
            0,
            "m.stdout: no difference: both write the same 3 lines.\n",
            ""
        )
    );
}

#[test]
fn outputs_that_differ_only_in_their_last_line_are_reported_at_its_key() {
    let [old, new, rec] = recorded("against_last", CAT, &cat_changing("c", "C"), "a\nb\nc\n");
    let out = against(&old, &rec, &new);
    assert_eq!(
        out.stdout,
        format!(
            "m.stdout: the line at key 2 differs: {old} writes \"c\", and {new} writes \"C\"; \
             {old} writes 3 lines, and {new} 3.\n"
        )
    );
}

#[test]
fn an_output_that_is_a_prefix_of_the_other_is_reported_by_the_line_counts() {
    // The first two lines of the input, as one string with a line end inside, which is written
    // as two lines.
    let line =
        |k: u32| format!("${{m.stdin[{k}] else #ioError -> \"\" else #outOfBounds -> \"\"}}");
    let shorter = format!(
        "main(m: MainArgs) {{\n  m.stdout <- \"{}\\n{}\";\n}}\n",
        line(0),
        line(1)
    );
    let shorter = shorter.as_str();
    let [old, new, rec] = recorded("against_prefix", CAT, shorter, "a\nb\nc\n");
    let out = against(&old, &rec, &new);
    assert_eq!(
        (out.status, out.stdout, out.stderr.as_str()),
        (
            0,
            format!(
                "m.stdout: the lines both write are the same, and one writes more: {old} \
                 writes 3 lines, and {new} 2.\n"
            ),
            ""
        )
    );
    // And the other way round: the record of the shorter, replayed against the longer.
    let [old, new, rec] = recorded("against_prefix_back", shorter, CAT, "a\nb\nc\n");
    assert_eq!(
        against(&old, &rec, &new).stdout,
        format!(
            "m.stdout: the lines both write are the same, and one writes more: {old} writes 2 \
             lines, and {new} 3.\n"
        )
    );
}

#[test]
fn programs_with_no_output_port_compare_no_lines_and_report_their_exit_statuses() {
    let old = "main(m: MainArgs) -> int {\n  (m.stdin.count) mod 256\n}\n";
    let new = "main(m: MainArgs) -> int {\n  (m.stdin.count + 1) mod 256\n}\n";
    let d = dir("against_no_port");
    let (o, n, r) = (d.join("old.zed"), d.join("new.zed"), d.join("wave.rec"));
    std::fs::write(&o, old).unwrap();
    std::fs::write(&n, new).unwrap();
    let [o, n, r] = [o, n, r].map(|p| p.to_str().unwrap().to_string());
    // `old.zed` ends with 3, the count of its lines, so its run is not an error.
    let run = zedc(&["run", &o, "--record", &r], "a\nb\nc\n");
    assert_eq!((run.status, run.stderr.as_str()), (3, ""));
    let out = against(&o, &r, &n);
    assert_eq!(
        (out.status, out.stdout, out.stderr.as_str()),
        (
            0,
            format!(
                "neither program has an output port, so no lines are compared.\nthe exit \
                 status: {o} ends with 3, and {n} with 4.\n"
            ),
            ""
        )
    );
}

#[test]
fn a_port_only_one_program_writes_is_reported_with_its_count_of_lines() {
    let both = "main(m: MainArgs) {\n  m.stdout <- m.stdin;\n  m.stderr <- \"done\";\n}\n";
    let [old, new, rec] = recorded("against_one_port", CAT, both, "a\nb\n");
    let out = against(&old, &rec, &new);
    assert_eq!(
        out.stdout,
        format!(
            "m.stdout: no difference: both write the same 2 lines.\nm.stderr: only {new} has \
             this port, and {old} does not write it; {new} writes 1 line to it.\n"
        )
    );
    // The other way round, the port is `old.zed`'s alone.
    let [old, new, rec] = recorded("against_one_port_back", both, CAT, "a\nb\n");
    assert_eq!(
        against(&old, &rec, &new).stdout,
        format!(
            "m.stdout: no difference: both write the same 2 lines.\nm.stderr: only {old} has \
             this port, and {new} does not write it; {old} writes 1 line to it.\n"
        )
    );
}

#[test]
fn a_record_of_a_third_program_is_still_refused() {
    let [_, new, rec] = recorded("against_third", CAT, &cat_changing("b", "B"), "a\n");
    let third = dir("against_third").join("third.zed");
    std::fs::write(
        &third,
        "main(m: MainArgs) {\n  m.stdout <- m.stdin;\n  m.stderr <- \"x\";\n}\n",
    )
    .unwrap();
    let third = third.to_str().unwrap();
    let out = against(third, &rec, &new);
    assert_eq!(out.status, 2);
    assert!(
        out.stderr.starts_with(&format!(
            "{rec}: this record was written by a run of a different program:"
        )),
        "{}",
        out.stderr
    );
    assert_eq!(out.stdout, "");
}

#[test]
fn lines_recorded_for_a_port_the_new_program_reads_as_the_environment_are_rejected() {
    let env = "main(m: MainArgs) {\n  m.stdout <- m.env[\"ZED_L119D_UNSET\"] else #notFound -> \"none\";\n}\n";
    let edited = "main(m: MainArgs) {\n  m.stdout <- m.env[\"ZED_L119D_UNSET\"] else #notFound -> \"unset\";\n}\n";
    let [old, new, rec] = recorded("against_env", env, edited, "");
    // The record of `old.zed`, changed to hold lines for its environment port: the address
    // is still `old.zed`'s, so only the check against `new.zed`'s ports can refuse it.
    let mut record = Record::from_bytes(&std::fs::read(&rec).unwrap()).unwrap();
    record
        .lines
        .insert("m.env".into(), b"HOME=/root\nPATH=/bin\n".to_vec().into());
    std::fs::write(&rec, record.to_bytes()).unwrap();
    let out = against(&old, &rec, &new);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr),
        (
            2,
            "",
            format!(
                "wave 0 of the record {rec} holds, for the port `m.env`, the lines of a `Lines` \
                 input, 2 lines, the first \"HOME=/root\", and {new} reads `m.env` as the \
                 environment, `(String) ->? String`, which that value does not fit. Read \
                 `m.env` in {new} as the run that wrote the record read it, or make a record \
                 of {new} with `zedc run {new} --record <out>`.\n"
            )
        )
    );
    // Without `--program` the record is checked against `old.zed` alone, as step L1.19b does.
    assert_eq!(zedc(&["replay", &old, &rec], "").stdout, "none\n");
}

#[test]
fn a_port_the_new_program_reads_with_nothing_recorded_and_a_recorded_port_it_drops_are_named() {
    let args = "main(m: MainArgs) {\n  m.stdout <- m.args[0] else #outOfBounds -> \"none\";\n}\n";
    let [old, new, rec] = recorded("against_ports", CAT, args, "a\n");
    let out = against(&old, &rec, &new);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr),
        (
            2,
            "",
            format!(
                "{new} reads the port `m.args`, and the record {rec} holds nothing for it: the \
                 run that wrote the record did not read `m.args`, and a replay reads only what \
                 the record holds. Remove the read of `m.args` from {new}, or make a record \
                 that holds it with `zedc run {new} --record <out>`.\nthe record {rec} holds \
                 the input of the port `m.stdin`, and {new} does not read `m.stdin`, so a \
                 replay of {new} would not use it and its outputs could not be compared with \
                 those of the recorded run. Read `m.stdin` in {new}, or replay {rec} without \
                 `--program`.\n"
            )
        )
    );
}

#[test]
fn program_is_an_option_of_replay_alone_given_once_with_its_file() {
    let [old, new, rec] = recorded("against_usage", CAT, CAT, "a\n");
    let reason = |o: Outcome| {
        (
            o.status,
            o.stderr.split("\n\n").next().unwrap_or("").to_string(),
        )
    };
    assert_eq!(
        reason(zedc(&["replay", &old, &rec, "--program"], "")),
        (
            2,
            "`--program` needs the file of the program to replay the record against after it: \
             write `--program <new.zed>`."
                .to_string()
        )
    );
    assert_eq!(
        reason(zedc(
            &["replay", &old, &rec, "--program", &new, "--program", &new],
            ""
        )),
        (
            2,
            "`--program` is given twice, and a record replays against one other program at a \
             time. Keep one `--program <new.zed>`."
                .to_string()
        )
    );
    assert_eq!(
        reason(zedc(&["replay", &old, &rec, "--bogus"], "")),
        (
            2,
            "`--bogus` is not understood here: after the record comes only `--program \
             <new.zed>`, which replays the record against another program. A replay gives the \
             program the arguments the record holds."
                .to_string()
        )
    );
    // `zedc run` takes no `--program`.
    let run = reason(zedc(&["run", &old, "--program", &new], ""));
    assert_eq!(run.0, 2);
    assert!(
        run.1.starts_with(
            "`--program` is not understood here: before `--` comes only `--record <out>`"
        ),
        "{}",
        run.1
    );
    // The same program on both sides reports no difference.
    assert_eq!(
        against(&old, &rec, &new).stdout,
        "m.stdout: no difference: both write the same 1 line.\n"
    );
}

/// The files of the benchmark at size `n`: `CAT` recorded on `n` lines, and the edit that
/// changes the last of them, so the comparison reads every line of both outputs.
pub(super) fn long_record(n: usize) -> [String; 3] {
    let stdin: String = (0..n).map(|i| format!("line {i}\n")).collect();
    let last = format!("line {}", n - 1);
    recorded(
        &format!("against_long_{n}"),
        CAT,
        &cat_changing(&last, "changed"),
        &stdin,
    )
}

/// Replays the record of [`long_record`]`(n)` against its edit and checks the report.
pub(super) fn replays_long(files: &[String; 3], n: usize) {
    let [old, new, rec] = files;
    let out = against(old, rec, new);
    assert_eq!(
        out.stdout,
        format!(
            "m.stdout: the line at key {k} differs: {old} writes \"line {k}\", and {new} writes \
             \"changed\"; {old} writes {n} lines, and {new} {n}.\n",
            k = n - 1
        )
    );
}

/// Small instance of `bench::comparing_the_outputs_of_n_and_8n_lines_scales`.
#[test]
fn a_long_record_is_compared_to_its_last_line() {
    replays_long(&long_record(50), 50);
}

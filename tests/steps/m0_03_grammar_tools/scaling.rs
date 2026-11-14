//! The inputs of the tool benchmarks in `bench/scaling.rs` (how the tools scale with the size of
//! the spec or the program), and what each benchmark asserts besides its ratio, checked here at
//! small sizes (TEST-bench-move-rest, P170).

use zed_tools::spec::Spec;
use zed_tools::{
    audit, cases, check as check_tool, fence_layers, fences, fuzz, layer, progress, ring, sync,
};

use super::{Dir, design, fence, spec_dir};
use zed_tests::step_helpers::m0_03_grammar_tools::KERNEL;

/// `n` functions, each with its own name.
pub(super) fn functions(n: usize) -> String {
    (0..n)
        .map(|i| format!("f{i}(x: int) -> int = x * {i};\n"))
        .collect()
}

/// `n` fences of one function each.
pub(super) fn many_fences(n: usize) -> String {
    (0..n)
        .map(|i| fence(&format!("f{i}(x: int) -> int = x * {i};")))
        .collect()
}

/// `check` passes the spec in `d`.
pub(super) fn check_passes(d: &Dir) {
    assert_eq!(check_tool::run(&[d.root()], &mut String::new()), Ok(true));
}

/// `fences` passes the spec in `d`.
pub(super) fn fences_pass(d: &Dir) {
    assert_eq!(fences::run(&[d.root()], &mut String::new()), Ok(true));
}

/// `fence_layers` lays out at least `at_least` fences of the `DESIGN.md` in `d`.
pub(super) fn lays_out_fences(d: &Dir, at_least: usize) {
    let spec = Spec::open(&d.root()).expect("the spec reads");
    let laid = fence_layers::of_document(&d.at("DESIGN.md"), &spec).expect("they lay out");
    assert!(laid.len() >= at_least);
}

/// A rejection table of `m` rows, each with a gloss in parentheses.
pub(super) fn rejection_table(m: usize) -> String {
    let rows: String = (0..m)
        .map(|i| format!("| Row {i} (gloss) | a | b |\n"))
        .collect();
    format!("| Rejection | W | M |\n|---|---|---|\n{rows}")
}

/// `rejection_rows` names each of the `m` rows of `table`.
pub(super) fn reads_each_row(table: &str, m: usize) {
    assert_eq!(fence_layers::rejection_rows(table).len(), m);
}

/// A directory named `{name}_{m}` whose `cases.txt` holds `m` cases and whose `leftrec.txt` is
/// empty.
pub(super) fn cases_dir(name: &str, m: usize) -> Dir {
    let d = Dir::new(&format!("{name}_{m}"));
    d.write(
        "cases.txt",
        &"Expr ::: a + b * c ::: (a + (b * c))\n".repeat(m),
    );
    d.write("leftrec.txt", "");
    d
}

/// `cases` passes the cases in `d` against `spec`.
pub(super) fn cases_pass(spec: &Spec, d: &Dir) {
    assert_eq!(
        cases::run_files(spec, &d.root(), &mut String::new()),
        Ok(true)
    );
}

/// A directory named `{name}_{m}` holding `p.zed`, a program of layer L1 of `m` functions.
pub(super) fn program_dir(name: &str, m: usize) -> Dir {
    let d = Dir::new(&format!("{name}_{m}"));
    d.write("p.zed", &format!("// layer L1\n{}", functions(m)));
    d
}

/// `ring` runs on the program in `d` against the spec in `spec`.
pub(super) fn ring_runs(spec: &Dir, d: &Dir) {
    assert!(ring::run(&[spec.root(), d.at("p.zed")], &mut String::new()).is_ok());
}

/// `layer` runs on the program in `d` against the spec in `spec`.
pub(super) fn layer_runs(spec: &Dir, d: &Dir) {
    assert!(layer::run(&[spec.root(), d.at("p.zed")], &mut String::new()).is_ok());
}

/// `audit` runs on the program in `d` against the spec in `spec`.
pub(super) fn audit_runs(spec: &Dir, d: &Dir) {
    assert!(audit::run(&[spec.root(), d.at("p.zed")], &mut String::new()).is_ok());
}

/// What a program needs, `m` alternatives and `2m` words, and a checklist that lists them all,
/// `m` of each that are not needed, and the `m` words `v{i}` in both the row L1 and the row L2.
pub(super) fn checklist(m: usize) -> (audit::Needs, String) {
    let needs = audit::Needs {
        program: "p.zed".into(),
        alts: (0..m).map(|i| (1, format!("R{i}"), 0)).collect(),
        words: (0..m)
            .flat_map(|i| [(format!("w{i}"), 1), (format!("v{i}"), 1)])
            .collect(),
    };
    let alts: String = (0..m).map(|i| format!(" `R{i}#0` `S{i}#0`")).collect();
    let words: String = (0..m).map(|i| format!(" `w{i}` `x{i}` `v{i}`")).collect();
    let wrong: String = (0..m).map(|i| format!(" `v{i}`")).collect();
    let list = format!(
        "## Part A\n\n| Layer | Alternatives | Words |\n|---|---|---|\n| L1 |{alts} |{words} |\n\
         | L2 | — |{wrong} |\n"
    );
    (needs, list)
}

/// The audit fails [`checklist`]`(m)`, naming the `2m` entries not needed and the `m` in the row
/// of another layer.
pub(super) fn compares_checklist(
    spec: &Spec,
    table: &layer::WordTable,
    needs: &audit::Needs,
    list: &str,
    m: usize,
) {
    let mut out = String::new();
    let outcome = audit::compare(spec, table, needs, "ZED0.md", list, &mut out);
    assert_eq!(outcome, Ok(false));
    assert!(out.contains(&format!(", {} not needed `", 2 * m)), "{out}");
    assert!(
        out.contains(&format!(
            "checklist: {} needed entries listed, {m} in the row of another layer `",
            3 * m
        )),
        "{out}"
    );
}

/// A Part A of `m` lines the audit cannot read, each for three reasons, and one line it cannot
/// read for `m` reasons.
pub(super) fn unreadable(m: usize) -> String {
    let bad: String = (0..m)
        .map(|i| format!("| L{i}–L{} | R{i}#0 | `w{i} |\n", i + 1))
        .collect();
    let long: String = (0..m).map(|i| format!(" x{i} `R{i}#0`")).collect();
    format!(
        "## Part A\n\n| Layer | Alternatives | Words |\n|---|---|---|\n{bad}| L1 |{long} | — |\n"
    )
}

/// The audit fails [`unreadable`]`(m)`, naming its `m + 1` lines and the `m` reasons of the
/// last.
pub(super) fn reads_unreadable(
    spec: &Spec,
    table: &layer::WordTable,
    needs: &audit::Needs,
    list: &str,
    m: usize,
) {
    let mut out = String::new();
    let outcome = audit::compare(spec, table, needs, "ZED0.md", list, &mut out);
    assert_eq!(outcome, Ok(false));
    assert!(
        out.contains(&format!("checklist: {} lines of Part A", m + 1)),
        "{out}"
    );
    assert!(out.contains(&format!(", for {m} reasons: ")), "{out}");
}

/// The ring the fuzz benchmark's first pass runs at.
pub(super) const LAST_RING: u32 = 22;

/// The fuzz's first pass at [`LAST_RING`] over `m` programs accepts some.
pub(super) fn first_pass_accepts(spec: &Spec, m: usize) {
    let accepted = fuzz::first_pass(spec, LAST_RING.., m, 1, &mut String::new());
    assert!(accepted.expect("the first pass runs") > 0);
}

/// A plan of `m` steps of L1 and its table of `m` rows marked done.
pub(super) fn progress_plan(m: usize) -> (String, String) {
    let steps: String = (1..=m).map(|i| format!("L1.{i}. Step {i}.\n")).collect();
    let done: String = (1..=m)
        .map(|i| format!("| L1.{i} | done | x |\n"))
        .collect();
    (
        format!("## (sec:steps) The steps, layer by layer\n\n### L1\n\n{steps}"),
        done,
    )
}

/// `progress` renders `plan` with `done`.
pub(super) fn renders_progress(plan: &str, done: &str) {
    assert!(progress::render(plan, done, None).is_ok());
}

/// The `DESIGN.md` fences of `sync`'s benchmark: `m` `zed` fences, `m` `text` fences and the
/// kernel.
pub(super) fn sync_body(m: usize) -> String {
    let texts: String = (0..m)
        .map(|i| format!("- Item {i}:\n\n  ```text\n  report {i}\n  ```\n\n"))
        .collect();
    format!("{}\n{texts}{KERNEL}", many_fences(m))
}

/// The directories `sync` copies into under `d`.
pub(super) fn sync_targets(d: &Dir) {
    for sub in ["zed/fences", "zed/grammar"] {
        std::fs::create_dir_all(d.at(sub)).expect("a copy directory");
    }
}

/// `sync` lays out and copies the fences of the spec in `d` into its `zed/`.
pub(super) fn syncs(d: &Dir) {
    let spec = Spec::open(&d.root()).expect("the spec reads");
    let mut out = String::new();
    let outcome = sync::sync_into(&spec, &d.at("zed"), false, &mut out);
    assert_eq!(outcome, Ok(true), "{out}");
}

/// Each benchmark of `bench/scaling.rs` at small sizes, through the same assertions: `check`,
/// `fences`, `fence_layers`, `rejection_rows`, `cases`, `ring`, `layer`, `audit`, the
/// checklist's comparison and reading, the fuzz's first pass, `progress` and `sync`.
#[test]
fn each_tool_benchmark_passes_at_small_sizes() {
    let empty = spec_dir("small_scale_tools", &design(""), "");
    let spec = Spec::open(&empty.root()).expect("the spec reads");
    let table = layer::WordTable::read(&spec.design).expect("the table reads");
    let no_needs = audit::Needs {
        program: "p.zed".into(),
        ..Default::default()
    };
    for m in [1, 2, 9] {
        let d = spec_dir(
            &format!("small_scale_fences_{m}"),
            &design(&many_fences(m)),
            "",
        );
        check_passes(&d);
        fences_pass(&d);
        lays_out_fences(&d, m);
        let long = spec_dir(
            &format!("small_scale_long_{m}"),
            &design(&fence(&functions(m))),
            "",
        );
        check_passes(&long);
        reads_each_row(&rejection_table(m), m);
        cases_pass(&spec, &cases_dir("small_scale_cases", m));
        let p = program_dir("small_scale_p", m);
        ring_runs(&empty, &p);
        layer_runs(&empty, &p);
        audit_runs(&empty, &p);
        let (needs, list) = checklist(m);
        compares_checklist(&spec, &table, &needs, &list, m);
        // One reason is written without a count, so the line of m reasons needs m of 2 or more.
        let r = m.max(2);
        reads_unreadable(&spec, &table, &no_needs, &unreadable(r), r);
        first_pass_accepts(&spec, m);
        let (plan, done) = progress_plan(m);
        renders_progress(&plan, &done);
        let s = spec_dir(&format!("small_scale_sync_{m}"), &design(&sync_body(m)), "");
        sync_targets(&s);
        syncs(&s);
    }
}

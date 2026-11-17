//! Step M0.8: the bootstrap subset's checklist, Parts A and B of the step in DESIGN.md, read in
//! place (feature `spec`). The `audit` tool checks Part A against corpus program 31 with the
//! spec's grammar; the other tests keep the recorded result consistent: the layer the step says
//! completes the audited needs is the highest layer of Part A, program 31 is labeled at that
//! layer, and every need of Part B lies within the bootstrap subset of the author's order of
//! 2026-11-05.

mod cases;

#[cfg(feature = "spec")]
const PROGRAM_31: &str = include_str!("../../../zed/corpus/31-typechecker/main.zed");

/// The text of step M0.8 of DESIGN.md: from its first line up to step M0.9.
#[cfg(feature = "spec")]
fn checklist() -> &'static str {
    let design = zed_tests::spec::design();
    let start = design.find("\nM0.8. ").expect("DESIGN.md has step M0.8") + 1;
    let end = start
        + design[start..]
            .find("\nM0.9. ")
            .expect("DESIGN.md has step M0.9 after M0.8");
    &design[start..end]
}

/// The layers in the first column of every table row, after the header rows.
fn table_layers(text: &str) -> Vec<u32> {
    text.lines()
        .filter(|l| l.starts_with("| L"))
        .filter_map(|l| {
            l[3..]
                .split(|c: char| !c.is_ascii_digit())
                .next()?
                .parse()
                .ok()
        })
        .collect()
}

/// The layer number at the start of `s`, after an optional `L`.
fn layer(s: &str) -> u32 {
    s.trim_start_matches('L')
        .split(|c: char| !c.is_ascii_digit())
        .next()
        .unwrap()
        .parse()
        .unwrap()
}

/// The layer number that follows the first occurrence of `before` in the step.
#[cfg(feature = "spec")]
fn layer_after(before: &str) -> u32 {
    layer(
        checklist()
            .split(before)
            .nth(1)
            .unwrap_or_else(|| panic!("step M0.8 says `{before}`")),
    )
}

/// The highest layer in the third column of Part B's rows: the last layer of a range
/// such as `L7–L24`.
fn part_b_layers(text: &str) -> Vec<u32> {
    let part = text.split("**Part B").nth(1).unwrap();
    part.lines()
        .filter(|l| l.starts_with("| ") && !l.starts_with("| Need") && !l.starts_with("|---"))
        .map(|l| layer(l.split(" | ").nth(2).unwrap().rsplit('–').next().unwrap()))
        .collect()
}

#[cfg(feature = "spec")]
#[test]
fn part_a_lists_exactly_what_the_audit_of_program_31_finds() {
    // Part A names alternatives by their index in the grammar, so a grammar change moves them;
    // the audit names each entry missing, not needed or in the wrong row, and exits 1 if any.
    let program = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../zed/corpus/31-typechecker/main.zed"
    );
    let args = [
        zed_tests::spec::root(),
        program.to_string(),
        "--checklist".to_string(),
        zed_tests::spec::design_path(),
    ];
    let mut out = String::new();
    let outcome = zed_tools::audit::run(&args, &mut out);
    assert!(outcome.is_ok(), "{out}");
    assert!(out.contains("checklist: 131 needed, 0 missing\n"), "{out}");
}

#[cfg(feature = "spec")]
#[test]
fn the_completing_layer_is_the_highest_item_and_program_31_is_labeled_there() {
    // "The audit of 2026-11-03 found that L6 completes what program 31 and the compiler's Rust
    // need": the audit of program 31 is Part A.
    let audited = layer_after("found that L");
    let a = table_layers(checklist());
    assert_eq!(a, [1, 2, 3, 4, 5, 6]);
    assert_eq!(a.iter().max(), Some(&audited));
    assert_eq!(
        PROGRAM_31.lines().next(),
        Some(format!("// layer L{audited}").as_str())
    );
}

#[cfg(feature = "spec")]
#[test]
fn every_part_b_need_lies_within_the_bootstrap_subset() {
    // "The bootstrap subset is: L1–L18 in full; the language parts of L19–L22 (...);
    // saturation and extraction (steps L23.1–L23.5b); the strategy catalog (steps L24.1 ...);
    // ...; one back-end path, ZIR to MLIR to LLVM IR to x86-64 (steps L28.1a, ...)". The
    // language parts end at the highest layer of a step the sentence names before the back end.
    let full = layer_after("The bootstrap subset is: L1–L");
    let back_end = layer_after("to x86-64 (steps L");
    let subset = checklist()
        .split("The bootstrap subset is:")
        .nth(1)
        .and_then(|s| s.split("After step S.6").next())
        .expect("step M0.8 lists the bootstrap subset before what follows step S.6");
    let language = cases::steps_named(subset)
        .into_iter()
        .filter_map(|s| s.strip_prefix('L'))
        .map(layer)
        .filter(|&l| l < back_end)
        .max()
        .expect("the subset names steps before the back end");
    assert_eq!((full, language, back_end), (18, 24, 28));
    let b = part_b_layers(checklist());
    assert_eq!(b.len(), 20);
    assert!(b.iter().all(|&l| (1..=language).contains(&l)), "{b:?}");
    assert_eq!(b.iter().max(), Some(&language));
}

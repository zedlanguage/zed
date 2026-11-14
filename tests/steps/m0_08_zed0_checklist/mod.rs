//! Step M0.8: the Zed₀ checklist (`zed/compiler/ZED0.md`). The audit against corpus program
//! 31 needs the spec's grammar tools and runs by hand (the `audit` tool); this test
//! keeps the recorded result consistent: the layer the checklist says completes the audited
//! needs is the highest layer of Part A, program 31 is labeled at that layer, and every need
//! of Part B lies within the core that Zed₀ is by the author's order of 2026-11-05.

mod cases;

const CHECKLIST: &str = include_str!("../../../zed/compiler/ZED0.md");
const PROGRAM_31: &str = include_str!("../../../zed/corpus/31-typechecker.zed");

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

/// The layer number that follows the first occurrence of `before` in the checklist.
fn layer_after(before: &str) -> u32 {
    layer(CHECKLIST.split(before).nth(1).unwrap())
}

/// The highest layer in the third column of Part B's rows: the last layer of a range
/// such as `L7–L24`.
fn part_b_layers(text: &str) -> Vec<u32> {
    let part = text.split("## Part B").nth(1).unwrap();
    part.lines()
        .filter(|l| l.starts_with("| ") && !l.starts_with("| Need") && !l.starts_with("|---"))
        .map(|l| layer(l.split(" | ").nth(2).unwrap().rsplit('–').next().unwrap()))
        .collect()
}

#[test]
fn the_completing_layer_is_the_highest_item_and_program_31_is_labeled_there() {
    // "the audit found that L6 completes that much": the audit of program 31 is Part A.
    let audited = layer_after("the audit found that L");
    let a = table_layers(CHECKLIST);
    assert_eq!(a, [1, 2, 3, 4, 5, 6]);
    assert_eq!(a.iter().max(), Some(&audited));
    assert_eq!(
        PROGRAM_31.lines().next(),
        Some(format!("// layer L{audited}").as_str())
    );
}

#[test]
fn every_part_b_need_lies_within_the_core_that_zed0_is() {
    // "L1–L18 in full, the language parts of L19–L24 and the back end ... of L28".
    let full =
        layer_after("**Zed₀ is the whole core, not\nthe smallest subset that compiles**: L1–L");
    let language = layer_after("the language parts of L19–L");
    let back_end = layer_after("x86-64 of L");
    assert_eq!((full, language, back_end), (18, 24, 28));
    let b = part_b_layers(CHECKLIST);
    assert_eq!(b.len(), 20);
    assert!(b.iter().all(|&l| (1..=language).contains(&l)), "{b:?}");
    assert_eq!(b.iter().max(), Some(&language));
}

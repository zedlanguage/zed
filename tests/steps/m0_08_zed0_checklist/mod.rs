//! Step M0.8: the Zed₀ checklist (`zed/compiler/ZED0.md`). The audit against corpus program
//! 31 needs the spec's grammar tools and runs by hand (`tools/bin/audit.dart`); this test
//! keeps the recorded result consistent: the layer the checklist names as completing Zed₀ is
//! the highest layer of any item in it, and program 31 is labeled at that layer.

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

/// The layers in the third column of Part B's rows.
fn part_b_layers(text: &str) -> Vec<u32> {
    let part = text.split("## Part B").nth(1).unwrap();
    part.lines()
        .filter(|l| l.starts_with("| ") && !l.starts_with("| Need") && !l.starts_with("|---"))
        .map(|l| {
            let col = l.split(" | ").nth(2).unwrap();
            col.trim_start_matches('L')
                .split(|c: char| !c.is_ascii_digit())
                .next()
                .unwrap()
                .parse()
                .unwrap()
        })
        .collect()
}

#[test]
fn the_completing_layer_is_the_highest_item_and_program_31_is_labeled_there() {
    let stated: u32 = CHECKLIST
        .split("**The layer that completes it is L")
        .nth(1)
        .and_then(|s| s.split("**").next())
        .and_then(|s| s.parse().ok())
        .unwrap();
    let a = table_layers(CHECKLIST);
    let b = part_b_layers(CHECKLIST);
    assert_eq!(a, [1, 2, 3, 4, 5, 6]);
    assert_eq!(b.len(), 9);
    assert_eq!(a.iter().chain(&b).max(), Some(&stated));
    assert_eq!(
        PROGRAM_31.lines().next(),
        Some(format!("// layer L{stated}").as_str())
    );
}

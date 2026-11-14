//! Completeness cases for the recorded checklist (TEST-complete-m0, author P189): each claim of
//! DESIGN.md step M0.8 that `zed/compiler/ZED0.md` records is checked against the file. The case
//! list is `COMPLETENESS.md`.

use super::{CHECKLIST, layer, part_b_layers, table_layers};

/// The rows of Part A: each layer and its two cells, grammar alternatives and defined words.
fn part_a() -> Vec<(u32, Vec<String>, Vec<String>)> {
    let part = CHECKLIST
        .split("## Part A")
        .nth(1)
        .and_then(|p| p.split("## Part B").next())
        .expect("ZED0.md has Parts A and B");
    let entries = |cell: &str| {
        cell.split('`')
            .skip(1)
            .step_by(2)
            .map(str::to_string)
            .collect::<Vec<_>>()
    };
    part.lines()
        .filter(|l| {
            l.strip_prefix("| L")
                .is_some_and(|r| r.starts_with(|c: char| c.is_ascii_digit()))
        })
        .map(|l| {
            let cells: Vec<&str> = l.split(" | ").collect();
            assert_eq!(cells.len(), 3, "a row of Part A has three cells: {l}");
            (layer(&cells[0][2..]), entries(cells[1]), entries(cells[2]))
        })
        .collect()
}

/// The words of `text` that name a step, such as `L1.19a` and `S.1c`, with the punctuation
/// after them removed.
fn steps_named(text: &str) -> Vec<&str> {
    text.split(|c: char| !(c.is_ascii_alphanumeric() || c == '.'))
        .map(|w| w.trim_end_matches('.'))
        .filter(|w| {
            let mut parts = w.splitn(2, '.');
            let (Some(stage), Some(step)) = (parts.next(), parts.next()) else {
                return false;
            };
            let stage_ok = stage == "S"
                || (stage.len() > 1
                    && stage.starts_with('L')
                    && stage[1..].bytes().all(|b| b.is_ascii_digit()));
            stage_ok && step.starts_with(|c: char| c.is_ascii_digit())
        })
        .collect()
}

#[test]
fn part_a_has_grammar_at_l1_l2_l3_l6_and_words_up_to_l5() {
    // DESIGN.md M0.8: "Program 31's units need grammar alternatives of L1, L2, L3 and L6
    // (`loop`, `until`, boundary `with`) and defined words up to L5".
    let rows = part_a();
    assert_eq!(
        rows.iter().map(|r| r.0).collect::<Vec<_>>(),
        table_layers(CHECKLIST),
        "Part A is the only table read by its first cell"
    );
    let with_grammar: Vec<u32> = rows
        .iter()
        .filter(|r| !r.1.is_empty())
        .map(|r| r.0)
        .collect();
    assert_eq!(with_grammar, [1, 2, 3, 6]);
    let with_words: Vec<u32> = rows
        .iter()
        .filter(|r| !r.2.is_empty())
        .map(|r| r.0)
        .collect();
    assert_eq!(with_words.iter().max(), Some(&5), "{with_words:?}");
    let l6 = &rows.iter().find(|r| r.0 == 6).expect("a row L6").1;
    for alt in ["Loop#0", "Until#0", "Boundary#0"] {
        assert!(l6.iter().any(|a| a == alt), "{alt} in row L6: {l6:?}");
    }
    // Each entry is a rule and its alternative index, `Rule#i`, and is listed once.
    let mut all: Vec<&String> = rows.iter().flat_map(|r| &r.1).collect();
    for a in &all {
        let (rule, i) = a.split_once('#').unwrap_or_else(|| panic!("{a} is Rule#i"));
        assert!(rule.starts_with(|c: char| c.is_ascii_uppercase()), "{a}");
        assert!(i.parse::<u32>().is_ok(), "{a}");
    }
    let n = all.len();
    all.sort();
    all.dedup();
    assert_eq!(all.len(), n, "a grammar alternative listed twice");
}

#[test]
fn every_step_design_names_for_the_subset_is_recorded() {
    // DESIGN.md M0.8, the steps the audits added before row S and in it.
    let named = steps_named(CHECKLIST);
    for step in [
        "L1.19a", "L1.36a", "L1.39c", "L3.15a", "L5.8a", "L6.13", "L6.13a", "L6.13b", "L6.13c",
        "S.1a", "S.1b", "S.1c", "S.1d", "S.1e", "S.1f", "S.3a",
    ] {
        assert!(named.contains(&step), "ZED0.md records step {step}");
    }
    // The reader of step names: a prefix is not the step, and a sentence's full stop is not
    // part of it.
    assert_eq!(
        steps_named("steps L6.13 to L6.13c. L6 S.1a, x.1 L.1"),
        ["L6.13", "L6.13c", "S.1a"]
    );
}

#[test]
fn part_b_places_each_need_design_names_at_its_layer() {
    // DESIGN.md M0.8: "the `Files` port and the string functions (L1), the named bit functions
    // for BLAKE3 addresses (L1), `rekey` (L4), indexed definitions, the definedness `fix` and
    // `.fold` on a recursive union (L6), and the back-end port (step S.1a)".
    let part = CHECKLIST.split("## Part B").nth(1).unwrap();
    let rows: Vec<&str> = part
        .lines()
        .filter(|l| l.starts_with("| ") && !l.starts_with("| Need") && !l.starts_with("|---"))
        .collect();
    assert_eq!(rows.len(), part_b_layers(CHECKLIST).len());
    let layer_of = |what: &str| {
        let row = rows
            .iter()
            .find(|r| r.contains(what))
            .unwrap_or_else(|| panic!("Part B names {what}"));
        layer(row.split(" | ").nth(2).unwrap())
    };
    for (what, at) in [
        ("the `Files` port", 1),
        ("the `String` functions", 1),
        ("bit words", 1),
        ("`rekey`", 4),
        ("indexed definitions", 6),
        ("the definedness `fix`", 6),
        ("`.fold` on a recursive union", 6),
        ("step S.1a", 1),
    ] {
        assert_eq!(layer_of(what), at, "{what}");
    }
    // Every row has four cells, none empty.
    for r in &rows {
        let cells: Vec<&str> = r.trim_matches('|').split(" | ").collect();
        assert_eq!(cells.len(), 4, "{r}");
        assert!(cells.iter().all(|c| !c.trim().is_empty()), "{r}");
    }
}

#[test]
fn the_readers_of_layers_take_the_first_number() {
    assert_eq!(layer("L7–L24"), 7);
    assert_eq!(layer("7"), 7);
    assert_eq!(layer("L1 (port header)"), 1);
    assert_eq!(layer("L28.1a"), 28);
    assert_eq!(
        table_layers("| L1 | a |\n| L12x | b |\n| Lx | c |\n|---|\n"),
        [1, 12]
    );
    assert_eq!(table_layers(""), Vec::<u32>::new());
    let b =
        "## Part B\n| Need | F | Layer | W |\n|---|\n| a | b | L7–L24 | c |\n| d | e | L3 | f |\n";
    assert_eq!(part_b_layers(b), [24, 3]);
}

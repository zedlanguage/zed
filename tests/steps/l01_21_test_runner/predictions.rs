//! The M0(d) prediction suite (DESIGN.md, Part G, deliverable M0(d)): twenty short programs in
//! `zed/fences/predictions/`, each with the output its comment derives from the spec, written
//! and committed before the program first ran. A program runs once the layer its first line
//! labels is enabled. A program with `// ✗` marks predicts a rejection: its marks must hold, and
//! the load error must name the word after the first mark. A failed prediction is a defect of
//! the surface or of the compiler, never a reason to edit the expected output unexplained.

use std::path::PathBuf;

use zed_tests::oracle::{self, ENABLED, native, program};
use zedc::run;

use super::checks;

/// Enabled programs that zedc rejects though the spec accepts them, each with the plan item that
/// fixes the compiler and a part of the rejection it gives now. The expected output stays as
/// predicted; when the item lands the program loads, this test fails, and the entry goes.
const PENDING: [(&str, &str, &str); 2] = [
    // DESIGN.md line 1807: a type name at L1 is a prelude type, and the string type is
    // `Utf8String` (sec:order); zedc still calls it `String`.
    (
        "02-greet.zed",
        "STR-types",
        "The type `Utf8String` is not defined",
    ),
    // DESIGN.md line 1850: a `div` or `mod` whose divisor's type holds no zero adds no
    // `#divByZero`, and line 639: `int[0..=255] + int[0..=255]` is `int[0..=510]`; zedc gives
    // `0 - 2` the type `int`, so `7 div (0 - 2)` keeps `#divByZero`. The checker takes integer
    // facts from forward transfer at L1.40b.
    ("03-euclid.zed", "L1.40b", "String | #divByZero"),
];

fn suite() -> Vec<(PathBuf, u32)> {
    oracle::labeled(&PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../zed/fences/predictions"))
}

#[test]
fn the_suite_is_twenty_programs_with_five_groupings_a_float_sum_and_a_join() {
    let suite = suite();
    let texts: Vec<String> = suite
        .iter()
        .map(|(p, _)| std::fs::read_to_string(p).unwrap())
        .collect();
    assert_eq!(texts.len(), 20);
    let with = |word: &str| texts.iter().filter(|t| t.contains(word)).count();
    assert!(with(".group(") + with(" into (") + with(".rekey(") >= 5);
    assert_eq!(with(".join("), 1);
    assert!(suite.iter().any(|(p, _)| p.ends_with("09-float-sum.zed")));
    let mut per_layer = [0; 7];
    for (_, layer) in &suite {
        per_layer[*layer as usize] += 1;
    }
    assert_eq!(per_layer, [0, 6, 2, 4, 5, 2, 1]);
}

#[test]
fn every_enabled_prediction_holds() {
    let enabled: Vec<_> = suite().into_iter().filter(|(_, l)| *l <= ENABLED).collect();
    assert_eq!(enabled.len(), 6);
    let mut failed = Vec::new();
    let ((), runs) = native(|engines| {
        for (path, _) in &enabled {
            let at = path.display();
            let text = std::fs::read_to_string(path).unwrap();
            let pending = PENDING.iter().find(|(name, ..)| path.ends_with(name));
            if let Some((_, item, why)) = pending {
                match run::load(text.as_bytes()) {
                    Err(e) if e.contains(why) => {}
                    Err(e) => failed.push(format!("{at}: pending {item}, rejected otherwise: {e}")),
                    Ok(_) => failed.push(format!("{at}: loads; remove its {item} entry")),
                }
                continue;
            }
            if let Some((_, mark)) = text.split_once("// ✗") {
                let got = checks(&text);
                if got.is_empty() || got.iter().any(|c| !c.ends_with(": ok")) {
                    failed.push(format!("{at}: the marks give {got:?}"));
                }
                let word = mark.split_whitespace().next().unwrap_or_default();
                match run::load(text.as_bytes()) {
                    Err(e) if e.contains(word) => {}
                    Err(e) => failed.push(format!("{at}: rejected without `{word}`: {e}")),
                    Ok(_) => failed.push(format!("{at}: loaded, and `{word}` was predicted")),
                }
                continue;
            }
            let input = std::fs::read(path.with_extension("in")).unwrap();
            let out = std::fs::read(path.with_extension("out")).unwrap();
            let (r, got) = program(&text, &input, engines);
            failed.extend(r.mismatches.into_iter().map(|m| format!("{at}: {m}")));
            let out = zed_kernel::Value::str(&String::from_utf8_lossy(&out));
            let want = format!("port `m.stdout` writes {out}");
            match (got, run::load(text.as_bytes())) {
                (Some(got), _) if got == want => {}
                (Some(got), _) => failed.push(format!("{at}: predicted {want}, and got {got}")),
                (None, Err(e)) => failed.push(format!("{at}: predicted {want}, and rejected: {e}")),
                (None, Ok(_)) => unreachable!("`program` gives the writes of a program that loads"),
            }
        }
    });
    assert_eq!(failed, Vec::<String>::new());
    // Four programs run, each under two engines; the pending two load no program.
    assert_eq!(runs, 8, "native runs, each leaving no cell live");
}

//! The formatter's standing rule (DESIGN.md, step L1.13) over the documentation's fences and
//! the corpus:
//! every unit that builds is formatted, and the result builds to the same statements, keeps
//! its comments, and formats to itself.

use zed_tests::fences;

#[test]
fn every_unit_that_builds_formats_to_a_fixed_point() {
    let mut formatted = 0;
    for f in fences::all().iter().filter(|f| !f.notation) {
        if super::build(&f.text).is_ok() {
            let r = std::panic::catch_unwind(|| super::fmt(&f.text));
            assert!(r.is_ok(), "fence at {}:\n{}", f.at, f.text);
            formatted += 1;
        }
    }
    // 23 at step L1.13; later steps build more.
    assert!(formatted >= 23, "formatted {formatted}");
}

#[test]
fn every_corpus_program_that_builds_formats_to_a_fixed_point() {
    let dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../zed/corpus");
    let mut formatted = Vec::new();
    let mut differ = Vec::new();
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "zed") {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        if super::build(&text).is_ok() {
            let name = path.file_name().unwrap().to_string_lossy().into_owned();
            if super::fmt(&text) != text {
                differ.push(name.clone());
            }
            formatted.push(name);
        }
    }
    // One at step L1.13; later steps build more.
    assert!(!formatted.is_empty(), "no corpus program builds");
    // The corpus is written in the formatter's layout, except where it is laid out by hand in a
    // way the formatter does not reproduce: 10-regex-matcher.zed wraps its `hhmm` record display
    // (it builds from step L2.2, its `import`); from step L3.1, which builds `for`, `><`, `::`
    // and displays, the others align the `=` of consecutive bindings and their trailing
    // comments, 11-csv-split.zed and 23-join-zoo.zed also wrap long lines, and 23-join-zoo.zed
    // writes a `match` on one line. From step L6.1, which builds `loop`, indexed definitions and
    // their `with`, the programs that use them also break long `if` chains and definitions by
    // hand, align, write a `loop` or a `match` on one line, or keep parentheses the grammar
    // does not need; 15-spreadsheet.zed, 24-weighted-pick.zed and 28-precedence-climbing.zed
    // write a `while` guard after the step, where the formatter writes it first. From the
    // AXIOMS-fmt fix, which builds `asc` and `desc` keys, 22-top-k.zed builds; it aligns a `=` and
    // writes a block of two statements on one line. From the CORPUS-parse fix, which wrote its
    // empty family `#bad -> ({})`, 19-bank-ledger.zed builds; it breaks an `if` chain by hand,
    // aligns `=` and writes a `while` guard after the step.
    differ.sort();
    assert_eq!(
        differ,
        [
            "01-word-count.zed",
            "02-histogram.zed",
            "03-edit-distance.zed",
            "04-running-variance.zed",
            "05-max-prefix-sum.zed",
            "06-matrix-multiply.zed",
            "08-utf8-percent.zed",
            "10-regex-matcher.zed",
            "11-csv-split.zed",
            "12-cyk-table.zed",
            "13-union-find.zed",
            "15-spreadsheet.zed",
            "17-sensor-pipeline.zed",
            "19-bank-ledger.zed",
            "22-top-k.zed",
            "23-join-zoo.zed",
            "24-weighted-pick.zed",
            "26-heat-stencil.zed",
            "27-parent-chain.zed",
            "28-precedence-climbing.zed",
            "31-typechecker.zed",
        ]
    );
}

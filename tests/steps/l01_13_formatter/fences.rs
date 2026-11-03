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
    // writes a `match` on one line.
    differ.sort();
    assert_eq!(
        differ,
        [
            "01-word-count.zed",
            "02-histogram.zed",
            "04-running-variance.zed",
            "05-max-prefix-sum.zed",
            "06-matrix-multiply.zed",
            "10-regex-matcher.zed",
            "11-csv-split.zed",
            "13-union-find.zed",
            "17-sensor-pipeline.zed",
            "23-join-zoo.zed",
            "29-late-dedup.zed",
        ]
    );
}

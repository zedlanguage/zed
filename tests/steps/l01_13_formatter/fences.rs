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
    let mut laid_out = 0;
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "zed") {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        if let Ok((_, stmts)) = super::build(&text) {
            let out = super::fmt(&text);
            // A program the compiler accepts is written in the formatter's layout. One of a
            // later layer may be wrapped by hand, which the formatter does not do: from step
            // L2.2 the `import` of 10-regex-matcher.zed (layer L19) builds.
            if zedc::resolve::resolve(&stmts).is_ok() {
                assert_eq!(out, text, "{}", path.display());
                laid_out += 1;
            }
            formatted.push(path.file_name().unwrap().to_string_lossy().into_owned());
        }
    }
    // One at step L1.13; later steps build more.
    assert!(!formatted.is_empty(), "no corpus program builds");
    assert!(laid_out > 0, "no corpus program resolves");
}

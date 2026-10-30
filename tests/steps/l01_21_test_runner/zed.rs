use std::path::PathBuf;

use zedc::testing::test;

/// The units of every step's `zed/` folder, by path.
fn units() -> Vec<PathBuf> {
    let steps = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("steps");
    let mut out = Vec::new();
    for step in std::fs::read_dir(steps).unwrap() {
        let dir = step.unwrap().path().join("zed");
        if let Ok(entries) = std::fs::read_dir(&dir) {
            out.extend(entries.map(|e| e.unwrap().path()));
        }
    }
    out.sort();
    out
}

#[test]
fn every_zed_test_of_every_step_passes() {
    let mut passed = 0;
    for path in units() {
        let text = std::fs::read_to_string(&path).unwrap();
        for o in test(&text) {
            let at = format!("{}:{}:{}", path.display(), o.line, o.col);
            assert_eq!(o.failure, None, "{at}");
            passed += 1;
        }
    }
    // The four units of this step hold 22 rows; a runner that skipped them would pass the
    // loop above.
    assert!(passed >= 22, "{passed} checks ran");
}

//! Every table row of every corpus unit, waves included, run through ZIR: each closed term
//! the runner evaluates is lowered, validated and raised back, and the row still passes.

use std::cell::Cell;
use std::path::PathBuf;

use zedc::testing::{test, test_through};
use zedc::zir::lower::{lower, raise};
use zedc::zir::validate;

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
fn every_row_passes_through_zir() {
    let (lowered, ported) = (Cell::new(0), Cell::new(0));
    let through = |t: &zed_kernel::Term, ev: &mut zed_kernel::Evaluator| {
        let g = lower(t)?;
        validate(&g)?;
        lowered.set(lowered.get() + 1);
        ported.set(ported.get() + usize::from(!g.args.is_empty()));
        ev.run(&raise(&g)?).map_err(|e| e.to_string())
    };
    let mut rows = 0;
    for path in units() {
        let text = std::fs::read_to_string(&path).unwrap();
        let want = test(&text);
        let got = test_through(&text, &through);
        assert_eq!(got, want, "{}", path.display());
        rows += got.len();
    }
    // The seven corpus units hold 41 checks, which evaluate 58 closed terms; the 11 waves
    // among them lower to port regions. A runner that skipped the map would pass the
    // comparison above.
    assert_eq!(rows, 41);
    assert_eq!((lowered.get(), ported.get()), (58, 11));
}

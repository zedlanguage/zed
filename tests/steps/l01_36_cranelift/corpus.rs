//! Every table row of every corpus unit, run natively: each closed term the runner evaluates
//! is lowered, planned, compiled by the JIT and run, and the row still passes; each run
//! allocates and writes counts exactly as the counting machine of L1.34 does.

use std::cell::Cell;
use std::path::PathBuf;

use zed_kernel::{Evaluator, Term};
use zedc::testing::{test, test_through};
use zedc::zir::lower::lower;
use zedc::zir::memory::{plan, run};

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
fn every_row_passes_natively_with_the_machines_counts() {
    for fuse in [true, false] {
        let (runs, cells, writes) = (Cell::new(0), Cell::new(0), Cell::new(0));
        let through = |t: &Term, ev: &mut Evaluator| {
            let g = lower(t)?;
            let p = plan(&g, fuse);
            // The machine runs in a copy of the world as it was before the native run.
            let mut copy = Evaluator::new(ev.world.clone());
            let o = zed_native::run(&g, &p, ev)?;
            let (v, s) = run(&g, &p, &mut copy)?;
            assert_eq!(o.value, v, "{t:?}");
            let native = (o.stats.increments, o.stats.decrements, o.stats.allocations);
            assert_eq!(native, (s.increments, s.decrements, s.allocations), "{t:?}");
            assert_eq!(
                (o.stats.frees, o.stats.peak, o.stats.shared),
                (s.frees, s.peak, s.shared)
            );
            runs.set(runs.get() + 1);
            cells.set(cells.get() + o.stats.allocations);
            writes.set(writes.get() + o.stats.increments + o.stats.decrements);
            Ok(o.value)
        };
        let mut rows = 0;
        for path in units() {
            let text = std::fs::read_to_string(&path).unwrap();
            let want = test(&text);
            let got = test_through(&text, &through);
            assert_eq!(got, want, "{} (fuse {fuse})", path.display());
            rows += got.len();
        }
        assert_eq!(rows, 41);
        let want = if fuse { 129 } else { 139 };
        assert_eq!((runs.get(), cells.get(), writes.get()), (58, 125, want));
    }
}

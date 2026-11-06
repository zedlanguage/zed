//! Every table row of every corpus unit, waves included, run through ZIR: each closed term
//! the runner evaluates is lowered, validated and raised back, and the row still passes.

use std::cell::Cell;
use std::path::PathBuf;

use zedc::testing::{test, test_through};
use zedc::zir::canon::canonicalize;
use zedc::zir::lower::{lower, raise};
use zedc::zir::{binary, text, validate};

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
    let (lowered, ported, unread) = (Cell::new(0), Cell::new(0), Cell::new(0));
    let through = |t: &zed_kernel::Term, ev: &mut zed_kernel::Evaluator| {
        let g = lower(t)?;
        validate(&g)?;
        // The text form of a lowered graph reads back as that graph: the printer writes no
        // name (atom, field, binder, port, facet kind, evidence key) the reader refuses. Open:
        // the binders the elaborator makes (`$1`) are printed as they are, and the reader has
        // never read them as names (item ZIR-text-binders); such a graph is counted.
        let printed = text::print(&g);
        match text::parse(&printed) {
            Ok(h) => assert_eq!(h, g, "{printed}"),
            Err(e) => {
                assert!(e.contains("expected a name, found `$"), "{e}\n{printed}");
                unread.set(unread.get() + 1);
            }
        }
        // The binary form reads every lowered graph back, and its canonical form, whose binders
        // are levels (`\0` and a number): it reads the binders the compiler makes.
        assert_eq!(
            binary::decode(&binary::encode(&g)).as_ref(),
            Ok(&g),
            "{printed}"
        );
        let c = canonicalize(&g);
        assert_eq!(binary::decode(&binary::encode(&c)), Ok(c), "{printed}");
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
    // The seven units of L1 hold 41 checks, which evaluate 58 closed terms; the 11 waves
    // among them lower to port regions. L25.8's unit adds 7 checks and 7 closed terms, and
    // no wave; L1.40d's unit adds 19 checks and 19 closed terms, and no wave; L1.26's readings
    // unit 18 checks and 18 closed terms, and no wave; and L1.26a's unit 7 checks and 7 closed
    // terms, and no wave. The three rejection units add 6 marked lines, which run nothing. A
    // runner that skipped the map would pass the comparison above.
    assert_eq!(rows, 98);
    assert_eq!((lowered.get(), ported.get()), (109, 11));
    // The 11 port graphs bind a wave's values with the elaborator's `$` names.
    assert_eq!(unread.get(), 11);
}

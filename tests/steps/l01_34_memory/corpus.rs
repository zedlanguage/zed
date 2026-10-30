//! Every table row of every corpus unit, waves included, run by the counting machine: each
//! closed term the runner evaluates is lowered, planned and run with its counts checked after
//! every node, and the row still passes.

use std::cell::Cell;
use std::path::PathBuf;

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
fn every_row_passes_through_the_machine() {
    for fuse in [true, false] {
        let (runs, cells, writes) = (Cell::new(0), Cell::new(0), Cell::new(0));
        let through = |t: &zed_kernel::Term, ev: &mut zed_kernel::Evaluator| {
            let g = lower(t)?;
            let (v, s) = run(&g, &plan(&g, fuse), ev)?;
            runs.set(runs.get() + 1);
            cells.set(cells.get() + s.allocations);
            writes.set(writes.get() + s.writes());
            Ok(v)
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
        // The seven corpus units evaluate 58 closed terms, which allocate 125 cells; fusion
        // saves 10 count writes.
        let want = if fuse { 129 } else { 139 };
        assert_eq!((runs.get(), cells.get(), writes.get()), (58, 125, want));
    }
}

/// A function that pushes and is called twice runs as one closure whose calls thread the
/// state: the machine's counts check, and the value and the pushes are the kernel's.
#[test]
fn a_function_that_pushes_and_is_called_twice_passes_through_the_machine() {
    use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
    use zed_kernel::{Evaluator, Prim, Term, World};
    let say = lam(
        &["m"],
        let_(
            "_",
            Term::Push("stdout".into(), var("m").into()),
            prim(Prim::Concat, vec![var("m"), lit("!")]),
        ),
    );
    let t = let_(
        "say",
        say,
        prim(
            Prim::Tuple,
            vec![
                app(var("say"), vec![lit("a")]),
                app(var("say"), vec![lit("b")]),
            ],
        ),
    );
    let g = lower(&t).unwrap();
    for fuse in [true, false] {
        let world = || World::new().output("stdout");
        let mut ev = Evaluator::new(world());
        let (v, _) = run(&g, &plan(&g, fuse), &mut ev).unwrap();
        let mut kev = Evaluator::new(world());
        assert_eq!(v, kev.run(&t).unwrap());
        assert_eq!(ev.world.log("stdout"), kev.world.log("stdout"));
        assert_eq!(ev.world.log("stdout").len(), 2);
    }
}

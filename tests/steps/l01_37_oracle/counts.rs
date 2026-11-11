//! The counts of a test build of the runtime (OSP-diag): each cell records the node that
//! allocated it, and the cells left live are listed by type and by that node. The oracle's
//! native runs each end with none (`oracle.rs`).

use zed_kernel::Value;
use zed_rt::{Heap, Obj, Survivor, Word};
use zed_tests::scaling;

#[test]
fn live_cells_are_listed_by_type_and_allocating_node() {
    let mut h = Heap::new();
    let outside = h.alloc(Obj::Str("a".into()));
    h.allocating(Some(3));
    let pair = h
        .fresh(&Value::tuple(vec![Value::str("b"), Value::str("c")]))
        .unwrap();
    let gone = h.alloc(Obj::Str("d".into()));
    h.allocating(Some(1));
    let clo = h.alloc(Obj::Clo {
        lambda: 0,
        caps: vec![Word::int(1)].into(),
    });
    h.dec(gone).unwrap();
    let survivor = |kind, node, cells| Survivor { kind, node, cells };
    assert_eq!(
        h.survivors(),
        [
            survivor("String", None, 1),
            survivor("String", Some(3), 2),
            survivor("closure", Some(1), 1),
            survivor("tuple", Some(3), 1),
        ]
    );
    // A freed cell taken again by another node is listed under that node.
    for w in [outside, pair, clo] {
        h.dec(w).unwrap();
    }
    assert_eq!(h.survivors(), []);
    h.allocating(Some(7));
    h.alloc(Obj::Str("e".into()));
    assert_eq!(h.survivors(), [survivor("String", Some(7), 1)]);
}

#[test]
fn reading_the_runs_counted_starts_the_count_again() {
    zed_native::counted();
    let run = zed_native::through(true);
    let mut ev = zed_kernel::Evaluator::new(zed_kernel::World::new());
    let term = zed_kernel::Term::Lit(Value::tuple(vec![Value::str("a"), Value::Int(1)]));
    assert_eq!(run(&term, &mut ev).unwrap().to_string(), "(\"a\", 1)");
    let c = zed_native::counted();
    assert_eq!((c.runs, c.left), (1, Vec::<String>::new()));
    assert_eq!(zed_native::counted().runs, 0);
}

/// A heap with `n` live cells, allocated by `n / 8 + 1` nodes in turn, built once.
fn heap(n: usize) -> Heap {
    let mut h = Heap::new();
    for i in 0..n {
        h.allocating(Some(i % (n / 8 + 1)));
        h.alloc(Obj::Str("x".into()));
    }
    h
}

#[test]
fn listing_the_live_cells_scales() {
    let n = 20_000;
    let heaps = [(n, heap(n)), (8 * n, heap(8 * n))];
    scaling::check("listing n live cells by type and node", n, |size| {
        let h = &heaps
            .iter()
            .find(|(m, _)| *m == size)
            .expect("a built size")
            .1;
        let total: u64 = h.survivors().iter().map(|s| s.cells).sum();
        assert_eq!(total, size as u64);
    });
}

//! A `match` with a binder at every level of a deep pattern (HEAP-binder-memory): the machine
//! finds each binder's cell and releases the scrutinee in time linear in the depth of the
//! pattern, where a copy of the path above each binder made `d²/2` part indices
//! (COMPLEXITY.md HEAP-binder-memory).

use zed_kernel::Shared;

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::{Evaluator, Pattern, Prim, Term, Value, World};

use super::{planned, run};

/// An invoice of `depth` lines, `((0), ((1), … (total)))`, built by the program (part 0 of a
/// constant pair), so that each line and each spine pair is a cell of the machine.
fn invoice(depth: usize) -> Term {
    let v = (0..depth)
        .rev()
        .fold(Value::tuple(vec![Value::str("total")]), |rest, k| {
            Value::tuple(vec![Value::tuple(vec![Value::from(k as i64)]), rest])
        });
    prim(
        Prim::TupleGet,
        vec![lit(Value::tuple(vec![v, Value::from(0i64)])), lit(0i64)],
    )
}

/// `match invoice { (l0, (l1, … total)) => (the binders in `used`) }`: a binder at each level,
/// the arm keeping those it uses. With `shared`, the invoice is also held by a pair, so the
/// scrutinee's cells are shared and the arm's entry gives each kept line a reference.
pub(super) fn read_lines(depth: usize, used: &[usize], shared: bool) -> Term {
    let name = |k: usize| {
        if k == depth {
            "total".to_string()
        } else {
            format!("l{k}")
        }
    };
    let p = (0..depth)
        .rev()
        .fold(Pattern::Bind("total".into()), |p, k| {
            Pattern::Tuple(vec![Pattern::Bind(name(k).into()), p])
        });
    let body = prim(Prim::Tuple, used.iter().map(|&k| var(&name(k))).collect());
    if !shared {
        return Term::Match(Shared::new(invoice(depth)), vec![(p, body)]);
    }
    let get = prim(Prim::TupleGet, vec![var("t"), lit(0)]);
    let_(
        "i",
        invoice(depth),
        let_(
            "t",
            prim(Prim::Tuple, vec![var("i"), var("i")]),
            prim(
                Prim::Tuple,
                vec![Term::Match(Shared::new(get), vec![(p, body)]), var("t")],
            ),
        ),
    )
}

/// Every set of binders used, of an invoice 4 deep, held once or shared: the machine checks
/// each cell's count after every node, and fused and unfused runs agree on the value, the cells
/// allocated and freed, and, for a shared invoice, the count writes (nothing is freed early).
#[test]
fn every_set_of_kept_lines_of_a_deep_match_is_released_exactly() {
    const DEPTH: usize = 4;
    for shared in [false, true] {
        for set in 0..1u32 << (DEPTH + 1) {
            let used: Vec<usize> = (0..=DEPTH).filter(|b| set >> b & 1 == 1).collect();
            let t = read_lines(DEPTH, &used, shared);
            let what = format!("used {used:?}, shared {shared}");
            let (g, p) = planned(&t, true);
            let (v, fused) = run(&g, &p).unwrap_or_else(|e| panic!("{what}: {e}"));
            let (g, p) = planned(&t, false);
            let (w, unfused) = run(&g, &p).unwrap_or_else(|e| panic!("{what}: {e}"));
            assert_eq!(v, w, "{what}");
            assert_eq!(
                (fused.allocations, fused.frees),
                (unfused.allocations, unfused.frees),
                "{what}"
            );
            assert_eq!(fused.allocations, fused.frees, "{what}");
            if shared {
                assert_eq!(fused.writes(), unfused.writes(), "{what}");
            } else {
                assert!(fused.writes() <= unfused.writes(), "{what}");
            }
            let want = Evaluator::new(World::new()).run(&t).unwrap();
            assert_eq!(v, want.to_string(), "{what}");
        }
    }
}

#[test]
fn a_held_once_invoice_moves_its_kept_lines_out_with_no_count_write() {
    // Each of the 3 spine pairs and the unused line 1 are freed at the arm's entry; lines 0
    // and 2 and the total move out of their freed cells. The only writes are the frees of what
    // the arm does not keep and the drop of the result after the run.
    let t = read_lines(3, &[0, 2, 3], false);
    let (g, p) = planned(&t, true);
    let (v, s) = run(&g, &p).unwrap();
    assert_eq!(v, r#"((0,), (2,), ("total",))"#);
    assert_eq!(s.increments, 0, "{s:?}");
}

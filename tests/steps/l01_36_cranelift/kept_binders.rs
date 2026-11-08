//! A fused release that keeps binders of a shared scrutinee gives each kept binder a
//! reference by walking the tree of nodes on the way to it (`zed_kernel::paths::Kept`, which
//! the counting machine of step L1.34 and the runtime's heap share since HEAP-paths-shared).
//! Two cases the walk must get right: a named field, whose part is its place among the atom's
//! sorted field names and not its place in the pattern; and a part with no cell partway down,
//! a constant, below which nothing is counted, so the walk stops there. For every set of kept
//! binders, the kernel, the machine and native code give one value, the machine and native
//! code make the same allocations and count writes, fused and not, and every cell is freed.

use zed_kernel::Shared;

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::{Evaluator, Pattern, Prim, Term, Value, World};
use zedc::zir::lower::lower;
use zedc::zir::memory;

use super::kernel;

fn bind(x: &str) -> Pattern {
    Pattern::Bind(x.into())
}

/// `v` made by the program (part 0 of a constant pair), so that each tuple and atom in it is
/// a cell of the machine and of the heap.
fn made(v: Value) -> Term {
    prim(
        Prim::TupleGet,
        vec![lit(Value::tuple(vec![v, Value::from(0i64)])), lit(0)],
    )
}

/// `s = scrutinee; t = (s, s); (match t.0 { p -> (the binders used) }, t)`: the scrutinee is
/// shared, so the arm's entry gives each kept binder a reference.
fn shared_match(scrutinee: Term, p: Pattern, used: &[&str]) -> Term {
    let body = prim(Prim::Tuple, used.iter().map(|&x| var(x)).collect());
    let get = prim(Prim::TupleGet, vec![var("t"), lit(0)]);
    let_(
        "s",
        scrutinee,
        let_(
            "t",
            prim(Prim::Tuple, vec![var("s"), var("s")]),
            prim(
                Prim::Tuple,
                vec![Term::Match(Shared::new(get), vec![(p, body)]), var("t")],
            ),
        ),
    )
}

/// Asserts, for every subset of `names` kept by the arm, that the kernel, the counting
/// machine and native code agree on the value of `case(subset)`, fused and not; that native
/// code allocates, increments and decrements as the machine does; that each frees every cell;
/// and that fused and unfused runs make the same writes, since a shared scrutinee frees
/// nothing at the arm's entry.
fn every_kept_set(names: &[&str], case: impl Fn(&[&str]) -> Term) {
    for set in 0..1u32 << names.len() {
        let used: Vec<&str> = (0..names.len())
            .filter(|b| set >> b & 1 == 1)
            .map(|b| names[b])
            .collect();
        let t = case(&used);
        let want = kernel(&t).unwrap_or_else(|e| panic!("used {used:?}: {e}"));
        let g = zed_native::legalize(lower(&t).unwrap_or_else(|e| panic!("{e}")));
        let mut writes = Vec::new();
        for fuse in [true, false] {
            let what = format!("used {used:?}, fuse {fuse}");
            let p = memory::plan(g.graph(), fuse);
            let (m, s) = memory::run(g.graph(), &p, &mut Evaluator::new(World::new()))
                .unwrap_or_else(|e| panic!("machine, {what}: {e}"));
            let o = zed_native::run(&g, &p, &mut Evaluator::new(World::new()))
                .unwrap_or_else(|e| panic!("native, {what}: {e}"));
            assert_eq!((&m, &o.value), (&want, &want), "{what}");
            assert_eq!(
                (o.stats.allocations, o.stats.increments, o.stats.decrements),
                (s.allocations, s.increments, s.decrements),
                "{what}"
            );
            assert_eq!(s.frees, s.allocations, "machine, {what}");
            assert_eq!(o.stats.frees, o.stats.allocations, "native, {what}");
            writes.push(s.writes());
        }
        assert_eq!(writes[0], writes[1], "used {used:?}");
    }
}

/// `#line(qty: (2,), price: ((5,), "eur"))` matched by `#line(qty: q, price: (amount,
/// currency))`: the pattern names `qty` first, but the payload is sorted by field name, so
/// `price` is part 0 and `qty` part 1, and a kept `q` is part 1 of the atom.
#[test]
fn kept_binders_of_a_shared_atom_are_found_by_field_name() {
    let line = Value::atom_named(
        "line",
        vec![
            ("qty".into(), Value::tuple(vec![Value::from(2i64)])),
            (
                "price".into(),
                Value::tuple(vec![
                    Value::tuple(vec![Value::from(5i64)]),
                    Value::str("eur"),
                ]),
            ),
        ],
    )
    .expect("distinct field names");
    let p = Pattern::Fields(
        "line".into(),
        vec![
            ("qty".into(), bind("q")),
            (
                "price".into(),
                Pattern::Tuple(vec![bind("amount"), bind("currency")]),
            ),
        ],
    );
    every_kept_set(&["q", "amount", "currency"], |used| {
        shared_match(made(line.clone()), p.clone(), used)
    });
}

/// `(((7,), "fixed"), ((9,),))`, whose part 0 is a constant written in the program: no cell
/// on either path, so the walk to `a` and `b` stops there and gives neither a reference, while
/// `c`, below the cell of part 1, gets one.
#[test]
fn kept_binders_below_a_part_with_no_cell_get_no_reference() {
    let fixed = Value::tuple(vec![
        Value::tuple(vec![Value::from(7i64)]),
        Value::str("fixed"),
    ]);
    let scrutinee = prim(
        Prim::Tuple,
        vec![
            lit(fixed),
            made(Value::tuple(vec![Value::tuple(vec![Value::from(9i64)])])),
        ],
    );
    let p = Pattern::Tuple(vec![
        Pattern::Tuple(vec![bind("a"), bind("b")]),
        Pattern::Tuple(vec![bind("c")]),
    ]);
    every_kept_set(&["a", "b", "c"], |used| {
        shared_match(scrutinee.clone(), p.clone(), used)
    });
}

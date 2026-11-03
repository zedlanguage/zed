//! A value the native runtime hands to the kernel is made from its cells once: each tuple, atom
//! or string cell keeps the kernel value read from it until the cell is freed, so an order
//! record checked against many rules is read once, not once per rule (COMPLEXITY.md R1).

use std::cell::RefCell;

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, Value};
use zed_rt::{Heap, Obj, Rope, Word};
use zed_tests::scaling;

use super::planned;
use super::scaling::{counted_in, strings};

/// `x = read x; (x == 0, x == 1, …, x == n-1)`: the record `x` handed to the kernel `n` times.
fn compared(n: usize) -> Term {
    compared_as(n, var("x"))
}

/// `x = read x; y = record; (y == 0, y == 1, …, y == n-1)`.
fn compared_as(n: usize, record: Term) -> Term {
    let checks = (0..n)
        .map(|i| prim(Prim::Eq, vec![var("y"), lit(i as i64)]))
        .collect();
    let body = let_("y", record, prim(Prim::Tuple, checks));
    let_("x", Term::Read("x".into()), body)
}

/// An order record: a customer, its lines, and a note.
fn order(note: &str) -> Value {
    let line = |item: &str, qty| Value::tuple(vec![Value::str(item), Value::Int(qty)]);
    Value::tuple(vec![
        Value::str("acme"),
        Value::tuple(vec![line("bolt", 40), line("nut", 40)]),
        Value::str(note),
    ])
}

/// The words read to make kernel values when `t` runs natively in `w`, after checking it runs
/// as the counting machine runs it and calls the kernel once per comparison.
fn converted(t: &Term, w: zed_kernel::World, n: usize) -> u64 {
    let want = format!("({})", vec!["false"; n].join(", "));
    assert_eq!(counted_in(t, w.clone()), want);
    let (g, p) = planned(t);
    let o = zed_native::run(&g, &p, &mut Evaluator::new(w)).unwrap();
    assert_eq!(o.kernel_calls, n as u64);
    o.stats.converted
}

#[test]
fn a_record_read_from_a_port_and_compared_many_times_is_not_read_again() {
    let n = 20;
    // The read of the port makes the record's 65 cells from its value, which they keep: each
    // call reads the top cell and the integer, and the result is its `n + 1` words.
    assert_eq!(converted(&compared(n), strings(64), n), 3 * n as u64 + 1);
}

#[test]
fn a_record_built_natively_and_compared_many_times_is_read_from_its_cells_once() {
    let n = 20;
    // `y = (x, "a" ++ "b")`: the first call reads `y`, `x`, whose value the port's read made,
    // and the string; each later call reads `y` only. Each call reads its integer too.
    let record = prim(
        Prim::Tuple,
        vec![var("x"), prim(Prim::Concat, vec![lit("a"), lit("b")])],
    );
    let t = compared_as(n, record);
    assert_eq!(converted(&t, strings(64), n), 3 * n as u64 + 3);
}

#[test]
fn a_cell_read_again_gives_the_same_value_without_reading_its_parts() {
    let mut h = Heap::new();
    let w = h.fresh(&order("rush"));
    assert_eq!(h.value(w).unwrap(), order("rush"));
    let first = h.stats.converted;
    assert_eq!(h.value(w).unwrap(), order("rush"));
    assert_eq!(h.stats.converted, first + 1);
}

#[test]
fn a_cell_freed_and_taken_again_gives_its_new_value() {
    let mut h = Heap::new();
    let old = h.fresh(&order("rush"));
    assert_eq!(h.value(old).unwrap(), order("rush"));
    h.dec(old).unwrap();
    // The program builds a new record, whose cells take freed ones that kept values.
    let customer = h.alloc(Obj::Str(Rope::leaf("acme".into())));
    let note = h.alloc(Obj::Str(Rope::leaf("hold".into())));
    let new = h.alloc(Obj::Tuple(vec![customer, note]));
    assert_eq!(h.cell_slots(), 8);
    assert!(
        h.value(old).is_err(),
        "a word of the freed record is caught"
    );
    let want = Value::tuple(vec![Value::str("acme"), Value::str("hold")]);
    assert_eq!(h.value(new).unwrap(), want);
    // The same through `fresh`, which keeps the value it is given.
    h.dec(new).unwrap();
    let again = h.fresh(&order("hold"));
    assert_eq!(h.cell_slots(), 8);
    assert_eq!(h.value(again).unwrap(), order("hold"));
}

#[test]
fn a_record_built_again_from_new_parts_between_two_runs_of_the_kernel_gives_the_new_value() {
    // `x = read x; y = (x, 1); a = y == (…, 1); z = (x, 2); (a, z == (…, 2))`: `y` is freed
    // after its comparison, and `z` may take its cell.
    let w = strings(3);
    let x = w.inputs["x"].clone();
    let pair = |k: i64| prim(Prim::Tuple, vec![var("x"), lit(k)]);
    let same = |t: Term, k: i64| {
        let v = Value::tuple(vec![x.clone(), Value::Int(k)]);
        prim(Prim::Eq, vec![t, lit(v)])
    };
    let t = let_(
        "x",
        Term::Read("x".into()),
        let_(
            "a",
            same(pair(1), 1),
            prim(Prim::Tuple, vec![var("a"), same(pair(2), 2)]),
        ),
    );
    assert_eq!(counted_in(&t, w.clone()), "(true, true)");
    let k = Evaluator::new(w).run(&t).unwrap();
    assert_eq!(k.to_string(), "(true, true)");
}

#[test]
fn a_cell_shared_by_two_tuples_is_read_once() {
    let mut h = Heap::new();
    let lines = h.fresh(&order("rush"));
    h.inc(lines);
    let a = h.alloc(Obj::Tuple(vec![lines, Word::int(1)]));
    let b = h.alloc(Obj::Tuple(vec![lines, Word::int(2)]));
    let va = h.value(a).unwrap();
    let before = h.stats.converted;
    let vb = h.value(b).unwrap();
    // `b`, `lines` (kept from the first read) and the integer.
    assert_eq!(h.stats.converted, before + 3);
    assert_eq!(va, Value::tuple(vec![order("rush"), Value::Int(1)]));
    assert_eq!(vb, Value::tuple(vec![order("rush"), Value::Int(2)]));
    h.dec(a).unwrap();
    assert_eq!(
        h.value(b).unwrap(),
        vb,
        "the shared record outlives one tuple"
    );
    h.dec(b).unwrap();
    assert_eq!(h.live(), 0);
}

#[test]
fn an_empty_tuple_and_an_empty_string_read_the_same_each_time() {
    let mut h = Heap::new();
    let v = Value::tuple(vec![
        Value::tuple(Vec::new()),
        Value::str(""),
        Value::str(""),
    ]);
    let w = h.fresh(&v);
    for _ in 0..3 {
        assert_eq!(h.value(w).unwrap(), v);
    }
    let empty = h.fresh(&Value::str(""));
    assert_eq!(h.value(empty).unwrap(), Value::str(""));
    assert_eq!(h.value(empty).unwrap(), Value::str(""));
    let none = h.fresh(&Value::tuple(Vec::new()));
    assert_eq!(h.value(none).unwrap(), Value::tuple(Vec::new()));
}

/// The record holds `64n` strings and is handed to the kernel `n` times: read whole each time,
/// the work would grow 64 times at `8n`.
#[test]
fn a_record_handed_to_the_kernel_many_times_scales() {
    let n = 50;
    let at = |m: usize| (planned(&compared(m)), strings(64 * m));
    let (small, large) = (at(n), at(scaling::FACTOR * n));
    scaling::check(
        "a tuple of 64n strings handed to the kernel n times",
        n,
        |m| {
            let ((g, p), w) = if m == n { &small } else { &large };
            let o = zed_native::run(g, p, &mut Evaluator::new(w.clone())).unwrap();
            std::hint::black_box(o);
        },
    );
}

/// A heap holding a shipping manifest the program built, `64n` lines in their own cells, and
/// its word.
fn manifest(n: usize) -> RefCell<(Heap, Word)> {
    let mut h = Heap::new();
    let lines = (0..64 * n)
        .map(|i| h.alloc(Obj::Str(Rope::leaf(format!("crate {i}").into()))))
        .collect();
    let w = h.alloc(Obj::Tuple(lines));
    RefCell::new((h, w))
}

/// A record whose cells the program built, not the kernel, keeps its value from its first read:
/// read whole each time, the `n` reads of `64n` cells would grow 64 times at `8n`.
#[test]
fn a_record_the_program_built_read_many_times_scales() {
    let n = 50;
    let (small, large) = (manifest(n), manifest(scaling::FACTOR * n));
    scaling::check(
        "the value of a tuple of 64n strings, read n times",
        n,
        |m| {
            let mut at = if m == n { &small } else { &large }.borrow_mut();
            let (h, w) = &mut *at;
            for _ in 0..m {
                std::hint::black_box(h.value(*w).unwrap());
            }
        },
    );
}

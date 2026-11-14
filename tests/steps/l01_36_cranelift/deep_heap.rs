//! Values and patterns as deep as a program builds them, in the runtime's heap: a list read from
//! a port, matched down to its last element and released (COMPLEXITY.md R9). The tests here run
//! each check at a few small depths on the test's own stack; the same checks 10,000 deep, on the
//! default stack of a test thread, and the wide function on a 64 KiB stack are benchmarks, in
//! `deep_heap_bench.rs` (author P178: a test that needs an unusual size is a benchmark). No
//! depth is refused.

use std::sync::Arc;

use zed_kernel::term::build::{app, lam, lit, prim, var};
use zed_kernel::{Evaluator, Lookup, Pattern, Prim, Term, Text, Value, World};
use zed_rt::{Heap, Obj, Paths, Word};
use zed_tests::deep::{SHAPES, in_atom, in_named_atom, in_tuple, nested};
use zedc::zir::lower::lower;
use zedc::zir::memory::plan;

#[path = "deep_heap_bench.rs"]
mod bench;

/// The depths of the tests here: a bare value, one level, and a few levels more. The same
/// checks 10,000 deep, past the depths at which the recursive runtime overflowed a 2 MiB stack,
/// are benchmarks, in `deep_heap_bench.rs`.
const DEPTHS: [usize; 4] = [0, 1, 2, 8];

/// `#order(customer: name, lines: (first, rest), total: "…")`, as a program's record holds it.
fn order() -> Value {
    Value::atom_named(
        "order",
        vec![
            ("customer".into(), Value::str("Ada")),
            (
                "lines".into(),
                Value::tuple(vec![Value::str("pen"), Value::str("ink")]),
            ),
            ("total".into(), Value::Int(12)),
        ],
    )
    .unwrap()
}

/// `bottom` inside `depth` patterns of `(_, p)`.
fn in_tuples(depth: usize, bottom: Pattern) -> Pattern {
    (0..depth).fold(bottom, |p, _| Pattern::Tuple(vec![Pattern::Wild, p]))
}

/// `bottom` inside `depth` patterns of `#cons(_, p)`.
fn in_atoms(depth: usize, bottom: Pattern) -> Pattern {
    (0..depth).fold(bottom, |p, _| {
        Pattern::Atom("cons".into(), vec![Pattern::Wild, p])
    })
}

/// `bottom` inside `depth` patterns of `#node(next: p)`.
fn in_fields(depth: usize, bottom: Pattern) -> Pattern {
    (0..depth).fold(bottom, |p, _| {
        Pattern::Fields("node".into(), vec![("next".into(), p)])
    })
}

fn bind(x: &str) -> Pattern {
    Pattern::Bind(x.into())
}

/// The nodes of the path `p` alone, and the node at its end.
fn one_path(p: &[usize]) -> (Paths, usize) {
    let mut paths = Paths::default();
    let end = p.iter().fold(Paths::ROOT, |at, &i| paths.push(at, i));
    (paths, end)
}

/// A port that gives the same value for every key.
#[derive(Debug)]
struct Same(Value);

impl Lookup for Same {
    fn get(&self, _: &Value) -> Result<Value, String> {
        Ok(self.0.clone())
    }
}

/// A list `depth` deep read from a port and run natively: the value read, a cell a level.
fn list_read_from_a_port_runs_natively(depth: usize) {
    let list = nested(in_tuple, depth, Value::Int(0));
    let mut w = World::new();
    let port: Arc<dyn Lookup> = Arc::new(Same(list.clone()));
    w.sources.insert("db".into(), port);
    let t = app(Term::Read("db".into()), vec![lit(0i64)]);
    let g = zed_native::legalize(lower(&t).unwrap());
    let o = zed_native::run(&g, &plan(g.graph(), true), &mut Evaluator::new(w)).unwrap();
    assert_eq!(o.value, list);
    assert_eq!(o.stats.allocations, depth as u64, "depth {depth}");
}

/// Each shape of value `depth` deep made in the heap, read back and freed.
fn each_shape_enters_and_leaves_the_heap(depth: usize) {
    for (what, wrap) in SHAPES {
        let v = nested(wrap, depth, Value::str("end"));
        let mut h = Heap::new();
        let w = h.fresh(&v).unwrap();
        assert_eq!(h.value(w).unwrap(), v, "{what}");
        h.dec(w).unwrap();
        assert_eq!(h.live(), 0, "{what}");
    }
}

/// A pattern `depth` deep, on a list, a nest of atoms and a nest of records, binds the last
/// element at a path of `depth` parts.
fn a_pattern_binds_the_last_element(depth: usize) {
    type Case = (fn(usize, Value) -> Value, fn(usize, Pattern) -> Pattern);
    let list: fn(usize, Value) -> Value = |d, b| nested(in_tuple, d, b);
    let atoms: fn(usize, Value) -> Value = |d, b| nested(in_atom, d, b);
    let records: fn(usize, Value) -> Value = |d, b| nested(in_named_atom, d, b);
    let cases: [Case; 3] = [(list, in_tuples), (atoms, in_atoms), (records, in_fields)];
    for (value, pattern) in cases {
        let mut h = Heap::new();
        let w = h.fresh(&value(depth, Value::str("last"))).unwrap();
        let p = pattern(depth, bind("x"));
        let (mut paths, mut out) = (Paths::default(), Vec::new());
        assert!(h.matches(&p, w, &mut paths, &mut out).unwrap());
        let [(x, node)] = &out[..] else {
            panic!("{} binders", out.len())
        };
        assert_eq!(paths.path(*node).len(), depth, "one part per level entered");
        assert_eq!(h.value(*x).unwrap(), Value::str("last"));
    }
}

/// A list `depth` deep against a pattern that differs from it at the bottom: no match, no
/// binder.
fn a_difference_at_the_bottom_fails(depth: usize) {
    let mut h = Heap::new();
    let w = h.fresh(&nested(in_tuple, depth, Value::Int(1))).unwrap();
    let p = in_tuples(depth, Pattern::Lit(Value::Int(2)));
    let mut out = Vec::new();
    assert!(!h.matches(&p, w, &mut Paths::default(), &mut out).unwrap());
    assert!(out.is_empty());
}

/// A list `depth` deep matched and released keeping its last element: each level freed.
fn release_keeps_only_the_last_element(depth: usize) {
    let mut h = Heap::new();
    let w = h
        .fresh(&nested(in_tuple, depth, Value::str("last")))
        .unwrap();
    let p = in_tuples(depth, bind("x"));
    let (mut paths, mut out) = (Paths::default(), Vec::new());
    assert!(h.matches(&p, w, &mut paths, &mut out).unwrap());
    let (x, node) = out.pop().unwrap();
    h.release(w, &paths, &[node]).unwrap();
    assert_eq!(h.live(), 1);
    assert_eq!(h.stats.frees, depth as u64);
    assert_eq!(h.value(x).unwrap(), Value::str("last"));
}

#[test]
fn a_list_read_from_a_port_runs_natively() {
    for depth in DEPTHS {
        list_read_from_a_port_runs_natively(depth);
    }
}

#[test]
fn each_shape_of_value_enters_and_leaves_the_heap() {
    for depth in DEPTHS {
        each_shape_enters_and_leaves_the_heap(depth);
    }
}

#[test]
fn a_nested_pattern_binds_the_last_element() {
    for depth in DEPTHS {
        a_pattern_binds_the_last_element(depth);
    }
}

#[test]
fn a_difference_at_the_bottom_fails_with_no_binder() {
    for depth in DEPTHS {
        a_difference_at_the_bottom_fails(depth);
    }
}

#[test]
fn releasing_a_list_keeps_only_the_last_element() {
    for depth in DEPTHS {
        release_keeps_only_the_last_element(depth);
    }
}

#[test]
fn a_shared_tail_stays_for_its_other_owner() {
    // `tail` is held by the list and by the caller; the head is released keeping `name`.
    let mut h = Heap::new();
    let name = h.fresh(&Value::str("Ada")).unwrap();
    let tail = h.alloc(Obj::Tuple(vec![name, Word::int(1)].into()));
    h.inc(tail).unwrap();
    let head = h.alloc(Obj::Tuple(vec![Word::int(0), tail].into()));
    let (paths, end) = one_path(&[1, 0]);
    h.release(head, &paths, &[end]).unwrap();
    assert_eq!(h.live(), 2, "the head goes; the tail and the name stay");
    // The tail is still held, and the name now has a reference for the binder as well.
    h.dec(tail).unwrap();
    assert_eq!(h.live(), 1);
    assert_eq!(h.value(name).unwrap(), Value::str("Ada"));
}

#[test]
fn a_record_binds_in_the_order_of_its_pattern() {
    let mut h = Heap::new();
    let w = h.fresh(&order()).unwrap();
    let lines = Pattern::Tuple(vec![bind("first"), bind("second")]);
    let p = Pattern::Fields(
        "order".into(),
        vec![
            ("total".into(), bind("total")),
            ("customer".into(), Pattern::Lit(Value::str("Ada"))),
            ("lines".into(), lines),
        ],
    );
    let (mut paths, mut out) = (Paths::default(), Vec::new());
    assert!(h.matches(&p, w, &mut paths, &mut out).unwrap());
    let got: Vec<_> = out
        .iter()
        .map(|(x, node)| (h.value(*x).unwrap(), paths.path(*node)))
        .collect();
    // The fields of a value are in name order: customer, lines, total.
    assert_eq!(
        got,
        [
            (Value::Int(12), vec![2]),
            (Value::str("pen"), vec![1, 0]),
            (Value::str("ink"), vec![1, 1]),
        ]
    );
}

#[test]
fn a_missing_field_fails_after_the_fields_before_it() {
    let mut h = Heap::new();
    let w = h.fresh(&order()).unwrap();
    let p = Pattern::Fields(
        "order".into(),
        vec![
            ("total".into(), bind("total")),
            ("discount".into(), bind("discount")),
        ],
    );
    let (mut paths, mut out) = (Paths::default(), Vec::new());
    assert!(!h.matches(&p, w, &mut paths, &mut out).unwrap());
    assert_eq!(
        out.len(),
        1,
        "the binder before the missing field was reached"
    );
    assert_eq!(paths.path(out[0].1), [2]);
}

#[test]
fn a_wrong_length_or_name_does_not_match() {
    let mut h = Heap::new();
    let w = h
        .fresh(&Value::tuple(vec![Value::Int(1), Value::Int(2)]))
        .unwrap();
    let (mut paths, mut out) = (Paths::default(), Vec::new());
    for p in [
        Pattern::Tuple(vec![Pattern::Wild]),
        Pattern::Atom("pair".into(), vec![Pattern::Wild, Pattern::Wild]),
        Pattern::AnyAtom,
    ] {
        assert!(!h.matches(&p, w, &mut paths, &mut out).unwrap());
    }
    assert!(paths.is_empty() && out.is_empty());
}

#[test]
fn a_function_matches_a_binder_and_no_shape() {
    let mut h = Heap::new();
    let f = h.alloc(Obj::Clo {
        lambda: 0,
        caps: Box::new([]),
    });
    let w = h.alloc(Obj::Tuple(vec![f, Word::int(1)].into()));
    let (mut paths, mut out) = (Paths::default(), Vec::new());
    let p = Pattern::Tuple(vec![bind("f"), Pattern::Wild]);
    assert!(h.matches(&p, w, &mut paths, &mut out).unwrap());
    let [(x, node)] = out[..] else {
        panic!("{} binders", out.len())
    };
    assert_eq!((x, paths.path(node)), (f, vec![0]));
    let shape = Pattern::Tuple(vec![Pattern::Tuple(Vec::new()), Pattern::Wild]);
    assert!(!h.matches(&shape, w, &mut paths, &mut out).unwrap());
}

#[test]
fn a_part_is_made_before_the_cell_that_holds_it() {
    let mut h = Heap::new();
    let parts = vec![Value::str("a"), Value::tuple(vec![Value::str("b")])];
    let w = h.fresh(&Value::tuple(parts)).unwrap();
    assert_eq!(
        w.bits, 3,
        "the string, the inner string, its tuple, then this"
    );
    assert_eq!(h.stats.allocations, 4);
}

#[test]
fn an_empty_tuple_and_a_bare_atom_are_uncounted_at_any_depth() {
    let mut h = Heap::new();
    let v = Value::tuple(vec![Value::tuple(Vec::new()), Value::atom("none")]);
    let w = h.fresh(&v).unwrap();
    assert_eq!(h.live(), 1, "only the outer tuple is a cell");
    assert_eq!(h.value(w).unwrap(), v);
}

#[test]
fn a_rope_inside_a_tuple_is_shared_not_copied_when_read() {
    // A block longer than the text's leaves, doubled 50 times: about 145 PB in 51 nodes, which
    // no copy would finish writing.
    let mut r = Text::from("x".repeat(129).as_str());
    for _ in 0..50 {
        r = Text::join(&r, &r).unwrap();
    }
    let mut h = Heap::new();
    let s = h.alloc(Obj::Str(r.clone()));
    let w = h.alloc(Obj::Tuple(vec![Word::int(1), s].into()));
    for _ in 0..2 {
        let Value::Tuple(parts) = h.value(w).unwrap() else {
            panic!("not a tuple")
        };
        assert_eq!(parts[0], Value::Int(1));
        let Value::Str(t) = &parts[1] else {
            panic!("{}", parts[1])
        };
        assert_eq!(t.len(), r.len());
    }
    // A join of two pieces too long to merge reads as its parts.
    let (a, b) = ("a".repeat(200), "b".repeat(200));
    let r = Text::join(&a.as_str().into(), &b.as_str().into()).unwrap();
    assert!(!r.is_flat());
    let s = h.alloc(Obj::Str(r));
    let w = h.alloc(Obj::Tuple(vec![Word::int(1), s].into()));
    let want = Value::tuple(vec![Value::Int(1), Value::str(&format!("{a}{b}"))]);
    assert_eq!(h.value(w).unwrap(), want);
}

#[test]
fn a_closure_below_a_value_is_not_data() {
    let mut h = Heap::new();
    let f = h.alloc(Obj::Clo {
        lambda: 0,
        caps: Box::new([]),
    });
    let w = h.alloc(Obj::Tuple(vec![Word::int(1), f].into()));
    let e = h.value(w).unwrap_err();
    assert_eq!(
        e,
        zed_rt::bug(
            "treated a function as a data value such as a number, a string, a tuple or a family",
            "a closure cell was read as data"
        )
    );
}

#[test]
fn a_freed_cell_below_a_value_is_reported() {
    let mut h = Heap::new();
    let s = h.fresh(&Value::str("gone")).unwrap();
    let w = h.alloc(Obj::Tuple(vec![s].into()));
    h.dec(s).unwrap();
    let e = h.value(w).unwrap_err();
    assert_eq!(
        e,
        zed_rt::bug(
            "read a value after it had released the value's memory",
            "the heap's cell 0 was read after it was freed"
        )
    );
}

#[test]
fn a_state_word_is_not_data() {
    let mut h = Heap::new();
    let w = h.alloc(Obj::Tuple(vec![Word::state()].into()));
    let e = h.value(w).unwrap_err();
    assert_eq!(
        e,
        zed_rt::bug(
            "treated something that is not a value as a data value",
            &format!("a word tagged {} was read as data", Word::STATE)
        )
    );
}

/// `(x -> (x ++ "0", x ++ "1", …))("a")` with `k` concatenations, whose results are all live
/// until the tuple is built, as a generated report's lines are. Each result has a slot of 16
/// bytes in the frame, so the frame grows with `k`.
fn wide(k: usize) -> Term {
    let lines = (0..k).map(|i| prim(Prim::Concat, vec![var("x"), lit(i.to_string().as_str())]));
    app(
        lam(&["x"], prim(Prim::Tuple, lines.collect())),
        vec![lit("a")],
    )
}

/// `wide(k)` run natively gives the kernel's value.
fn a_wide_function_runs_as_the_kernel_does(k: usize) {
    let t = wide(k);
    let want = Evaluator::new(World::new()).run(&t).unwrap();
    let g = zed_native::legalize(lower(&t).unwrap());
    let p = plan(g.graph(), true);
    let got = zed_native::run(&g, &p, &mut Evaluator::new(World::new())).unwrap();
    assert!(
        got.value == want,
        "{k} concatenations: the native value differs from the kernel's"
    );
}

/// A function of no, one and a few concatenations, run on the test's own stack. The function of
/// 5,000 concatenations whose frame is larger than a thread stack of 64 KiB is a benchmark, in
/// `deep_heap_bench.rs`.
#[test]
fn a_function_of_concatenations_runs_as_the_kernel_does() {
    for k in [0, 1, 8] {
        a_wide_function_runs_as_the_kernel_does(k);
    }
}

/// The bytes the heap holds for each level of a list of pairs, measured on 2026-11-11 in this
/// build (feature `counts`): one cell of 96 bytes, the two parts in it (COMPLEXITY.md R16).
/// Before, a level held a cell of 144 bytes and a block of 32 for its parts.
const BYTES_PER_LEVEL: f64 = 96.0;

/// The heap of a list of pairs `(k, rest)` `n` levels deep holds at most 1.25 times
/// [`BYTES_PER_LEVEL`] a level, counted exactly on this thread, the kernel value it was made from
/// living outside the count. A block of its own for a pair's parts (32 bytes) or a kernel value
/// in each cell (56) is past the bound. `n` is a power of two, so the table of cells has no
/// growth slack at the end and the bytes are the cells' own.
fn a_level_of_a_list_of_pairs_is_one_small_cell_at(n: usize) {
    assert!(n.is_power_of_two(), "{n}");
    let v = nested(in_tuple, n, Value::Int(0));
    let (h, live) = zed_alloc_count::live(|| {
        let mut h = Heap::new();
        h.fresh(&v).unwrap();
        h
    });
    assert_eq!(h.cell_slots(), n);
    let per_level = live.net as f64 / n as f64;
    assert!(
        per_level <= 1.25 * BYTES_PER_LEVEL,
        "{per_level} bytes a level, measured {BYTES_PER_LEVEL}"
    );
}

/// A list of 1,024 levels: the heap's fixed tables only add to the bytes a level, so a level
/// past the bound fails here as it does on a long list. The list of 2^17 levels is a
/// benchmark, in `deep_heap_bench.rs`.
#[test]
fn a_level_of_a_list_of_pairs_is_one_small_cell() {
    a_level_of_a_list_of_pairs_is_one_small_cell_at(1 << 10);
}

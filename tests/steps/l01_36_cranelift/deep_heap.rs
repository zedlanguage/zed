//! Values and patterns as deep as a program builds them, in the runtime's heap: a long list read
//! from a port, matched down to its last element and released, on the default stack of a test
//! thread (COMPLEXITY.md R9). No test here sets a stack size, and no depth is refused.

use std::sync::Arc;
use std::sync::Mutex;

use zed_kernel::term::build::{app, lam, lit, prim, var};
use zed_kernel::{Evaluator, Lookup, Pattern, Prim, Term, Text, Value, World};
use zed_rt::{Heap, Obj, Word};
use zed_tests::deep::{SHAPES, in_atom, in_named_atom, in_tuple, nested};
use zed_tests::scaling;
use zedc::zir::lower::lower;
use zedc::zir::memory::plan;

/// How deep the values go; the recursive runtime overflowed its stack far above this.
const DEPTH: usize = 1_000_000;

/// The depth of the scaling tests, and 8 times it; below about 160,000 cells the run is still
/// in the fast caches (COMPLEXITY.md K22).
const N: usize = 100_000;

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

/// A port that gives the same value for every key.
#[derive(Debug)]
struct Same(Value);

impl Lookup for Same {
    fn get(&self, _: &Value) -> Result<Value, String> {
        Ok(self.0.clone())
    }
}

#[test]
fn a_deep_list_read_from_a_port_runs_natively() {
    let list = nested(in_tuple, DEPTH, Value::Int(0));
    let mut w = World::new();
    let port: Arc<dyn Lookup> = Arc::new(Same(list.clone()));
    w.sources.insert("db".into(), port);
    let t = app(Term::Read("db".into()), vec![lit(0i64)]);
    let g = zed_native::legalize(lower(&t).unwrap());
    let o = zed_native::run(&g, &plan(g.graph(), true), &mut Evaluator::new(w)).unwrap();
    assert_eq!(o.value, list);
    assert_eq!(o.stats.allocations, DEPTH as u64);
}

#[test]
fn each_shape_of_deep_value_enters_and_leaves_the_heap() {
    for (what, wrap) in SHAPES {
        let v = nested(wrap, DEPTH, Value::str("end"));
        let mut h = Heap::new();
        let w = h.fresh(&v).unwrap();
        assert_eq!(h.value(w).unwrap(), v, "{what}");
        h.dec(w).unwrap();
        assert_eq!(h.live(), 0, "{what}");
    }
}

#[test]
fn a_deep_pattern_binds_the_last_element() {
    type Case = (fn(usize, Value) -> Value, fn(usize, Pattern) -> Pattern);
    let list: fn(usize, Value) -> Value = |d, b| nested(in_tuple, d, b);
    let atoms: fn(usize, Value) -> Value = |d, b| nested(in_atom, d, b);
    let records: fn(usize, Value) -> Value = |d, b| nested(in_named_atom, d, b);
    let cases: [Case; 3] = [(list, in_tuples), (atoms, in_atoms), (records, in_fields)];
    for (value, pattern) in cases {
        let mut h = Heap::new();
        let w = h.fresh(&value(DEPTH, Value::str("last"))).unwrap();
        let p = pattern(DEPTH, bind("x"));
        let (mut at, mut out) = (vec![9], Vec::new());
        assert!(h.matches(&p, w, &mut at, &mut out).unwrap());
        assert_eq!(at, [9], "the path comes back as it went in");
        let [(x, path)] = &out[..] else {
            panic!("{} binders", out.len())
        };
        assert_eq!(path.len(), DEPTH + 1);
        assert_eq!(h.value(*x).unwrap(), Value::str("last"));
    }
}

#[test]
fn a_difference_at_the_bottom_fails_and_restores_the_path() {
    let mut h = Heap::new();
    let w = h.fresh(&nested(in_tuple, DEPTH, Value::Int(1))).unwrap();
    let p = in_tuples(DEPTH, Pattern::Lit(Value::Int(2)));
    let (mut at, mut out) = (vec![3, 4], Vec::new());
    assert!(!h.matches(&p, w, &mut at, &mut out).unwrap());
    assert_eq!(at, [3, 4]);
    assert!(out.is_empty());
}

#[test]
fn releasing_a_deep_list_keeps_only_the_last_element() {
    let mut h = Heap::new();
    let w = h
        .fresh(&nested(in_tuple, DEPTH, Value::str("last")))
        .unwrap();
    let p = in_tuples(DEPTH, bind("x"));
    let (mut at, mut out) = (Vec::new(), Vec::new());
    assert!(h.matches(&p, w, &mut at, &mut out).unwrap());
    let (x, path) = out.pop().unwrap();
    h.release(w, &[&path]).unwrap();
    assert_eq!(h.live(), 1);
    assert_eq!(h.stats.frees, DEPTH as u64);
    assert_eq!(h.value(x).unwrap(), Value::str("last"));
}

#[test]
fn a_shared_tail_stays_for_its_other_owner() {
    // `tail` is held by the list and by the caller; the head is released keeping `name`.
    let mut h = Heap::new();
    let name = h.fresh(&Value::str("Ada")).unwrap();
    let tail = h.alloc(Obj::Tuple(vec![name, Word::int(1)]));
    h.inc(tail).unwrap();
    let head = h.alloc(Obj::Tuple(vec![Word::int(0), tail]));
    h.release(head, &[&[1, 0]]).unwrap();
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
    let (mut at, mut out) = (Vec::new(), Vec::new());
    assert!(h.matches(&p, w, &mut at, &mut out).unwrap());
    let got: Vec<_> = out
        .iter()
        .map(|(x, path)| (h.value(*x).unwrap(), path.clone()))
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
    let (mut at, mut out) = (vec![5], Vec::new());
    assert!(!h.matches(&p, w, &mut at, &mut out).unwrap());
    assert_eq!(at, [5]);
    assert_eq!(
        out.len(),
        1,
        "the binder before the missing field was reached"
    );
}

#[test]
fn a_wrong_length_or_name_does_not_match() {
    let mut h = Heap::new();
    let w = h
        .fresh(&Value::tuple(vec![Value::Int(1), Value::Int(2)]))
        .unwrap();
    let (mut at, mut out) = (Vec::new(), Vec::new());
    for p in [
        Pattern::Tuple(vec![Pattern::Wild]),
        Pattern::Atom("pair".into(), vec![Pattern::Wild, Pattern::Wild]),
        Pattern::AnyAtom,
    ] {
        assert!(!h.matches(&p, w, &mut at, &mut out).unwrap());
    }
    assert!(at.is_empty() && out.is_empty());
}

#[test]
fn a_function_matches_a_binder_and_no_shape() {
    let mut h = Heap::new();
    let f = h.alloc(Obj::Clo {
        lambda: 0,
        caps: Vec::new(),
    });
    let w = h.alloc(Obj::Tuple(vec![f, Word::int(1)]));
    let (mut at, mut out) = (Vec::new(), Vec::new());
    let p = Pattern::Tuple(vec![bind("f"), Pattern::Wild]);
    assert!(h.matches(&p, w, &mut at, &mut out).unwrap());
    assert_eq!(out, [(f, vec![0])]);
    let shape = Pattern::Tuple(vec![Pattern::Tuple(Vec::new()), Pattern::Wild]);
    assert!(!h.matches(&shape, w, &mut at, &mut out).unwrap());
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
    let w = h.alloc(Obj::Tuple(vec![Word::int(1), s]));
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
    let w = h.alloc(Obj::Tuple(vec![Word::int(1), s]));
    let want = Value::tuple(vec![Value::Int(1), Value::str(&format!("{a}{b}"))]);
    assert_eq!(h.value(w).unwrap(), want);
}

#[test]
fn a_closure_below_a_value_is_not_data() {
    let mut h = Heap::new();
    let f = h.alloc(Obj::Clo {
        lambda: 0,
        caps: Vec::new(),
    });
    let w = h.alloc(Obj::Tuple(vec![Word::int(1), f]));
    let e = h.value(w).unwrap_err();
    assert_eq!(e, "runtime: a closure is not data");
}

#[test]
fn a_freed_cell_below_a_value_is_reported() {
    let mut h = Heap::new();
    let s = h.fresh(&Value::str("gone")).unwrap();
    let w = h.alloc(Obj::Tuple(vec![s]));
    h.dec(s).unwrap();
    let e = h.value(w).unwrap_err();
    assert_eq!(e, "runtime: cell 0 is used after it was freed");
}

#[test]
fn a_state_word_is_not_data() {
    let mut h = Heap::new();
    let w = h.alloc(Obj::Tuple(vec![Word::state()]));
    let e = h.value(w).unwrap_err();
    assert_eq!(
        e,
        format!("runtime: a word tagged {} is not data", Word::STATE)
    );
}

/// The runs of one measured size: a warming run and five for each measurement.
const RUNS: usize = 1 + 5 * scaling::TRIES;

/// A heap holding the list of `n` cells.
fn list_heap(n: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let w = h.fresh(&nested(in_tuple, n, Value::Int(0))).unwrap();
    (h, w)
}

#[test]
fn making_a_deep_value_scales() {
    let lists = [N, scaling::FACTOR * N].map(|n| (n, nested(in_tuple, n, Value::Int(0))));
    let used = Mutex::new(Vec::new());
    scaling::check("Heap::fresh on a list", N, |n| {
        let v = &lists.iter().find(|(m, _)| *m == n).unwrap().1;
        let mut h = Heap::new();
        h.fresh(v).unwrap();
        used.lock().unwrap().push(h);
    });
}

#[test]
fn reading_a_deep_value_scales() {
    let heaps = Mutex::new([N, scaling::FACTOR * N].map(|n| (n, list_heap(n))));
    let used = Mutex::new(Vec::new());
    scaling::check("Heap::value on a list", N, |n| {
        let mut heaps = heaps.lock().unwrap();
        let (_, (h, w)) = heaps.iter_mut().find(|(m, _)| *m == n).unwrap();
        used.lock().unwrap().push(h.value(*w).unwrap());
    });
}

#[test]
fn matching_a_deep_pattern_scales() {
    let heaps = Mutex::new([N, scaling::FACTOR * N].map(|n| (n, list_heap(n))));
    let patterns = [N, scaling::FACTOR * N].map(|n| (n, in_tuples(n, Pattern::Wild)));
    scaling::check("Heap::matches on a list", N, |n| {
        let mut heaps = heaps.lock().unwrap();
        let (_, (h, w)) = heaps.iter_mut().find(|(m, _)| *m == n).unwrap();
        let p = &patterns.iter().find(|(m, _)| *m == n).unwrap().1;
        assert!(h.matches(p, *w, &mut Vec::new(), &mut Vec::new()).unwrap());
    });
}

#[test]
fn releasing_a_deep_value_scales() {
    let paths = [N, scaling::FACTOR * N].map(|n| (n, vec![1; n]));
    let heaps = Mutex::new(
        [N, scaling::FACTOR * N].map(|n| (n, (0..RUNS).map(|_| list_heap(n)).collect::<Vec<_>>())),
    );
    let used = Mutex::new(Vec::new());
    scaling::check("Heap::release on a list", N, |n| {
        let path = &paths.iter().find(|(m, _)| *m == n).unwrap().1;
        let (mut h, w) = {
            let mut heaps = heaps.lock().unwrap();
            heaps
                .iter_mut()
                .find(|(m, _)| *m == n)
                .unwrap()
                .1
                .pop()
                .unwrap()
        };
        h.release(w, &[path]).unwrap();
        used.lock().unwrap().push(h);
    });
}

/// The width of the wide function of the scaling test; the test also runs 8 times as wide.
const WIDE: usize = 2_500;

/// A stack of 256 KiB for a test thread, smaller than the frame of `wide(FACTOR * WIDE)`.
const SMALL_STACK: usize = 256 << 10;

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

/// A function of 20,000 concatenations has a frame of more than 312 KiB, larger than the stack
/// of 256 KiB its thread runs on: before generated code had a stack of its own (COMPLEXITY.md
/// R10), the run stopped at that stack's guard page. A thread of 2 MiB would need about 150,000
/// concatenations, which compile in about 20 s alone and over 120 s at a load of 180.
#[test]
fn a_function_of_20000_concatenations_runs_on_a_smaller_thread_stack() {
    let t = wide(scaling::FACTOR * WIDE);
    let want = Evaluator::new(World::new()).run(&t).unwrap();
    let g = zed_native::legalize(lower(&t).unwrap());
    let p = plan(g.graph(), true);
    let got = scaling::on_a_thread(SMALL_STACK, || {
        zed_native::run(&g, &p, &mut Evaluator::new(World::new())).unwrap()
    });
    assert!(
        got.value == want,
        "the native value differs from the kernel's"
    );
}

/// Compiling and running the wide function natively, at 2,500 and 20,000 concatenations, on a
/// thread of 256 KiB: the frame of the larger is larger than that thread's stack. The work is
/// linear in the width: the code generator's passes, Cranelift's at `OptLevel::None`
/// (COMPLEXITY.md Z15), and the stack probes, which touch each page of the frame once.
#[test]
fn a_wide_function_runs_in_time_linear_in_its_width() {
    let programs = [WIDE, scaling::FACTOR * WIDE].map(|k| {
        let g = zed_native::legalize(lower(&wide(k)).unwrap());
        let p = plan(g.graph(), true);
        (k, g, p)
    });
    scaling::on_a_thread(SMALL_STACK, || {
        scaling::check(
            "native compile and run of a function of n concatenations",
            WIDE,
            |k| {
                let (_, g, p) = programs.iter().find(|(m, _, _)| *m == k).unwrap();
                drop(zed_native::run(g, p, &mut Evaluator::new(World::new())).unwrap());
            },
        )
    });
}

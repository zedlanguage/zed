//! Values and patterns as deep as a program builds them, in the runtime's heap: a long list read
//! from a port, matched down to its last element and released, on the default stack of a test
//! thread (COMPLEXITY.md R9). No test here sets a stack size, and no depth is refused.

use std::cell::RefCell;
use std::mem::ManuallyDrop;
use std::sync::Arc;

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

/// `bottom` inside `depth` patterns of `(_, p)`. A pattern drops by recursion in the kernel, so
/// it is never dropped here.
fn in_tuples(depth: usize, bottom: Pattern) -> ManuallyDrop<Pattern> {
    ManuallyDrop::new((0..depth).fold(bottom, |p, _| Pattern::Tuple(vec![Pattern::Wild, p])))
}

/// `bottom` inside `depth` patterns of `#cons(_, p)`.
fn in_atoms(depth: usize, bottom: Pattern) -> ManuallyDrop<Pattern> {
    ManuallyDrop::new((0..depth).fold(bottom, |p, _| {
        Pattern::Atom("cons".into(), vec![Pattern::Wild, p])
    }))
}

/// `bottom` inside `depth` patterns of `#node(next: p)`.
fn in_fields(depth: usize, bottom: Pattern) -> ManuallyDrop<Pattern> {
    ManuallyDrop::new((0..depth).fold(bottom, |p, _| {
        Pattern::Fields("node".into(), vec![("next".into(), p)])
    }))
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
    let g = Arc::new(lower(&t).unwrap());
    let o = zed_native::run(&g, &plan(&g, true), &mut Evaluator::new(w)).unwrap();
    assert_eq!(o.value, list);
    assert_eq!(o.stats.allocations, DEPTH as u64);
}

#[test]
fn each_shape_of_deep_value_enters_and_leaves_the_heap() {
    for (what, wrap) in SHAPES {
        let v = nested(wrap, DEPTH, Value::str("end"));
        let mut h = Heap::new();
        let w = h.fresh(&v);
        assert_eq!(h.value(w).unwrap(), v, "{what}");
        h.dec(w).unwrap();
        assert_eq!(h.live(), 0, "{what}");
    }
}

#[test]
fn a_deep_pattern_binds_the_last_element() {
    type Case = (
        fn(usize, Value) -> Value,
        fn(usize, Pattern) -> ManuallyDrop<Pattern>,
    );
    let list: fn(usize, Value) -> Value = |d, b| nested(in_tuple, d, b);
    let atoms: fn(usize, Value) -> Value = |d, b| nested(in_atom, d, b);
    let records: fn(usize, Value) -> Value = |d, b| nested(in_named_atom, d, b);
    let cases: [Case; 3] = [(list, in_tuples), (atoms, in_atoms), (records, in_fields)];
    for (value, pattern) in cases {
        let mut h = Heap::new();
        let w = h.fresh(&value(DEPTH, Value::str("last")));
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
    let w = h.fresh(&nested(in_tuple, DEPTH, Value::Int(1)));
    let p = in_tuples(DEPTH, Pattern::Lit(Value::Int(2)));
    let (mut at, mut out) = (vec![3, 4], Vec::new());
    assert!(!h.matches(&p, w, &mut at, &mut out).unwrap());
    assert_eq!(at, [3, 4]);
    assert!(out.is_empty());
}

#[test]
fn releasing_a_deep_list_keeps_only_the_last_element() {
    let mut h = Heap::new();
    let w = h.fresh(&nested(in_tuple, DEPTH, Value::str("last")));
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
    let name = h.fresh(&Value::str("Ada"));
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
    let w = h.fresh(&order());
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
    let w = h.fresh(&order());
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
    let w = h.fresh(&Value::tuple(vec![Value::Int(1), Value::Int(2)]));
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
    let w = h.fresh(&Value::tuple(parts));
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
    let w = h.fresh(&v);
    assert_eq!(h.live(), 1, "only the outer tuple is a cell");
    assert_eq!(h.value(w).unwrap(), v);
}

#[test]
fn a_rope_inside_a_tuple_is_shared_not_copied_when_read() {
    let mut h = Heap::new();
    let r = Text::join(&"ab".into(), &"cd".into()).unwrap();
    let s = h.alloc(Obj::Str(r.clone()));
    let w = h.alloc(Obj::Tuple(vec![Word::int(1), s]));
    let want = Value::tuple(vec![Value::Int(1), Value::str("abcd")]);
    let v = h.value(w).unwrap();
    assert!(!r.is_written_out(), "the value holds the join itself");
    assert_eq!(v, want);
    assert!(
        r.is_written_out(),
        "comparing it wrote it out, once, for both"
    );
    assert_eq!(h.value(w).unwrap(), want);
    assert_eq!(h.stats.copied, 0);
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
    let s = h.fresh(&Value::str("gone"));
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
    let w = h.fresh(&nested(in_tuple, n, Value::Int(0)));
    (h, w)
}

#[test]
fn making_a_deep_value_scales() {
    let lists = [N, scaling::FACTOR * N].map(|n| (n, nested(in_tuple, n, Value::Int(0))));
    let used = RefCell::new(Vec::new());
    scaling::check("Heap::fresh on a list", N, |n| {
        let v = &lists.iter().find(|(m, _)| *m == n).unwrap().1;
        let mut h = Heap::new();
        h.fresh(v);
        used.borrow_mut().push(h);
    });
}

#[test]
fn reading_a_deep_value_scales() {
    let heaps = RefCell::new([N, scaling::FACTOR * N].map(|n| (n, list_heap(n))));
    let used = RefCell::new(Vec::new());
    scaling::check("Heap::value on a list", N, |n| {
        let mut heaps = heaps.borrow_mut();
        let (_, (h, w)) = heaps.iter_mut().find(|(m, _)| *m == n).unwrap();
        used.borrow_mut().push(h.value(*w).unwrap());
    });
}

#[test]
fn matching_a_deep_pattern_scales() {
    let heaps = RefCell::new([N, scaling::FACTOR * N].map(|n| (n, list_heap(n))));
    let patterns = [N, scaling::FACTOR * N].map(|n| (n, in_tuples(n, Pattern::Wild)));
    scaling::check("Heap::matches on a list", N, |n| {
        let mut heaps = heaps.borrow_mut();
        let (_, (h, w)) = heaps.iter_mut().find(|(m, _)| *m == n).unwrap();
        let p = &patterns.iter().find(|(m, _)| *m == n).unwrap().1;
        assert!(h.matches(p, *w, &mut Vec::new(), &mut Vec::new()).unwrap());
    });
}

#[test]
fn releasing_a_deep_value_scales() {
    let paths = [N, scaling::FACTOR * N].map(|n| (n, vec![1; n]));
    let heaps = RefCell::new(
        [N, scaling::FACTOR * N].map(|n| (n, (0..RUNS).map(|_| list_heap(n)).collect::<Vec<_>>())),
    );
    let used = RefCell::new(Vec::new());
    scaling::check("Heap::release on a list", N, |n| {
        let path = &paths.iter().find(|(m, _)| *m == n).unwrap().1;
        let (mut h, w) = {
            let mut heaps = heaps.borrow_mut();
            heaps
                .iter_mut()
                .find(|(m, _)| *m == n)
                .unwrap()
                .1
                .pop()
                .unwrap()
        };
        h.release(w, &[path]).unwrap();
        used.borrow_mut().push(h);
    });
}

/// A function of 150,000 concatenations, `(x -> (x ++ "0", x ++ "1", …))("a")`, whose results are
/// all live until the tuple is built, as a generated report's lines are. Each result has a slot of
/// 16 bytes in the frame, so the frame is larger than the 2 MiB stack of a test thread: before
/// generated code had a stack of its own (COMPLEXITY.md R10), the run stopped at that stack's
/// guard page. 100,000 concatenations make a frame close to 2 MiB, which overflowed the stack of
/// a test thread but fitted that of a fresh thread, so the test takes half as many again.
#[test]
fn a_function_of_150000_concatenations_runs_on_the_stack_of_a_test_thread() {
    let lines =
        (0..150_000).map(|i| prim(Prim::Concat, vec![var("x"), lit(i.to_string().as_str())]));
    let t = app(
        lam(&["x"], prim(Prim::Tuple, lines.collect())),
        vec![lit("a")],
    );
    let want = Evaluator::new(World::new()).run(&t).unwrap();
    let g = Arc::new(lower(&t).unwrap());
    let got = zed_native::run(&g, &plan(&g, true), &mut Evaluator::new(World::new())).unwrap();
    assert!(
        got.value == want,
        "the native value differs from the kernel's"
    );
}

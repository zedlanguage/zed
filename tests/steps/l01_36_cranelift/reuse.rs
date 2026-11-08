//! The runtime's heap reuses what it has: a freed cell is taken by the next allocation, and the
//! parts of a constant are entered in the table of uncounted values once, the first time a match
//! reads them, so a program that matches a rate table on every request runs in memory that does
//! not grow with the requests (COMPLEXITY.md R3, R6). A word kept past the free of its cell is
//! still reported when the cell has been taken again, by the generation the word carries.

use std::mem::ManuallyDrop;
use zed_kernel::Shared;

use zed_kernel::types::Type;
use zed_kernel::{Pattern, Term, Text, Value};
use zed_rt::{Heap, Obj, Paths, Word};
use zed_tests::deep::{in_tuple, nested};

use super::{kernel, native};

fn bind(x: &str) -> Pattern {
    Pattern::Bind(x.into())
}

/// `bottom` inside `depth` patterns of `(_, p)`, never dropped: a pattern drops by recursion.
fn in_tuples(depth: usize, bottom: Pattern) -> ManuallyDrop<Pattern> {
    ManuallyDrop::new((0..depth).fold(bottom, |p, _| Pattern::Tuple(vec![Pattern::Wild, p])))
}

/// A shipping rate table as a constant: `(zone, rest)` pairs, `depth` deep, ending at 0.
fn rate_table(depth: usize) -> Value {
    nested(in_tuple, depth, Value::Int(0))
}

/// Matches `p` against `w`, which must match; the binders' words.
fn bound(h: &mut Heap, p: &Pattern, w: Word) -> Vec<Word> {
    let mut out = Vec::new();
    assert!(h.matches(p, w, &mut Paths::default(), &mut out).unwrap());
    out.into_iter().map(|(w, _)| w).collect()
}

#[test]
fn matching_a_rate_table_again_adds_no_entries() {
    let mut h = Heap::new();
    let table = h.uncounted(rate_table(100));
    let p = in_tuples(100, bind("last"));
    assert_eq!(bound(&mut h, &p, table), [Word::int(0)]);
    let once = h.table_len();
    assert!(once <= 1 + 2 * 100, "each level's two parts once: {once}");
    for _ in 1..10 {
        bound(&mut h, &p, table);
    }
    assert_eq!(h.table_len(), once, "after 10 matches");
    for _ in 10..100 {
        bound(&mut h, &p, table);
    }
    assert_eq!(h.table_len(), once, "after 100 matches");
    assert_eq!(
        h.stats.allocations, 0,
        "a constant is matched without cells"
    );
}

#[test]
fn a_part_of_a_constant_bound_once_reads_the_same_after_more_matches() {
    let mut h = Heap::new();
    let north = Value::tuple(vec![Value::str("north"), Value::Int(12)]);
    let rates = Value::atom_named(
        "rates",
        vec![
            ("table".into(), north.clone()),
            ("fallback".into(), Value::str("south")),
        ],
    )
    .unwrap();
    let w = h.uncounted(rates);
    let p = Pattern::Fields("rates".into(), vec![("table".into(), bind("t"))]);
    let first = bound(&mut h, &p, w)[0];
    for _ in 0..50 {
        assert_eq!(bound(&mut h, &p, w), [first], "the same entry each time");
    }
    assert_eq!(h.value(first).unwrap(), north);
    let missing = Pattern::Fields("rates".into(), vec![("express".into(), bind("e"))]);
    assert!(
        !h.matches(&missing, w, &mut Paths::default(), &mut Vec::new())
            .unwrap()
    );
}

#[test]
fn a_constant_matches_as_the_kernel_matches_it() {
    let mut h = Heap::new();
    let order = Value::atom_with("order", vec![Value::str("Ada"), Value::Int(3)]);
    let path = Value::path(vec![Value::Int(1), Value::Int(2)]);
    let (o, k) = (h.uncounted(order), h.uncounted(path));
    let yes =
        |h: &mut Heap, p: &Pattern, w| h.matches(p, w, &mut Paths::default(), &mut Vec::new());
    let named = Pattern::Atom("order".into(), vec![bind("who"), Pattern::Wild]);
    assert!(yes(&mut h, &named, o).unwrap());
    assert!(yes(&mut h, &Pattern::AnyAtom, o).unwrap());
    let short = Pattern::Atom("order".into(), vec![bind("who")]);
    assert!(
        !yes(&mut h, &short, o).unwrap(),
        "a payload of another length"
    );
    let other = Pattern::Atom("refund".into(), vec![bind("who"), Pattern::Wild]);
    assert!(!yes(&mut h, &other, o).unwrap(), "an atom of another name");
    let pair = Pattern::Tuple(vec![Pattern::Wild, Pattern::Wild]);
    assert!(!yes(&mut h, &pair, k).unwrap(), "a keypath is not a tuple");
    assert!(!yes(&mut h, &Pattern::AnyAtom, k).unwrap());
    let lit = Pattern::Atom(
        "order".into(),
        vec![Pattern::Lit(Value::str("Ada")), bind("n")],
    );
    let (mut paths, mut out) = (Paths::default(), Vec::new());
    assert!(h.matches(&lit, o, &mut paths, &mut out).unwrap());
    let [(x, node)] = out[..] else {
        panic!("{} binders", out.len())
    };
    assert_eq!((x, paths.path(node)), (Word::int(3), vec![1]));
}

#[test]
fn a_bare_atom_or_an_empty_tuple_made_again_adds_no_entry() {
    let mut h = Heap::new();
    let none = h.fresh(&Value::atom("none")).unwrap();
    let unit = h.fresh(&Value::tuple(Vec::new())).unwrap();
    let len = h.table_len();
    for _ in 0..100 {
        assert_eq!(h.fresh(&Value::atom("none")).unwrap(), none);
        assert_eq!(h.fresh(&Value::tuple(Vec::new())).unwrap(), unit);
    }
    let pair = h
        .fresh(&Value::tuple(vec![
            Value::atom("none"),
            Value::tuple(Vec::new()),
        ]))
        .unwrap();
    assert_eq!(h.table_len(), len);
    assert_ne!(h.fresh(&Value::atom("some")).unwrap(), none);
    assert_eq!(
        h.value(pair).unwrap(),
        Value::tuple(vec![Value::atom("none"), Value::tuple(Vec::new())])
    );
}

#[test]
fn a_string_made_and_freed_again_and_again_takes_one_cell() {
    let mut h = Heap::new();
    for i in 0..1000 {
        let w = h.fresh(&Value::str(&format!("request {i}"))).unwrap();
        h.dec(w).unwrap();
    }
    assert_eq!(
        (h.cell_slots(), h.live(), h.stats.allocations),
        (1, 0, 1000)
    );
    // A pair of strings is three cells, taken again each time.
    for _ in 0..1000 {
        let w = h
            .fresh(&Value::tuple(vec![Value::str("a"), Value::str("b")]))
            .unwrap();
        h.dec(w).unwrap();
    }
    assert_eq!((h.cell_slots(), h.live()), (3, 0));
    assert_eq!(h.stats.peak, 3);
}

#[test]
fn a_word_kept_past_the_free_of_its_cell_is_reported_after_the_cell_is_taken_again() {
    let mut h = Heap::new();
    let old = h.fresh(&Value::str("old")).unwrap();
    h.dec(old).unwrap();
    let new = h.fresh(&Value::str("new")).unwrap();
    assert_eq!(h.cell_slots(), 1, "the new string takes the freed cell");
    assert_ne!(old, new, "with another generation");
    assert_eq!(
        h.value(old).unwrap_err(),
        "runtime: cell 0 is used after it was freed"
    );
    assert_eq!(
        h.dec(old).unwrap_err(),
        "runtime: cell 0 is dropped after it was freed"
    );
    assert_eq!(
        h.inc(old).unwrap_err(),
        "runtime: cell 0 is shared after it was freed"
    );
    assert_eq!(h.value(new).unwrap(), Value::str("new"));
    assert_eq!(h.live(), 1);
    h.dec(new).unwrap();
    assert_eq!(h.live(), 0);
}

/// A block longer than the text's leaves, doubled 50 times: about 145 PB held in 51 nodes.
/// Reading it would not finish, so a test that finishes on it read none of it.
fn vast() -> Text {
    let mut s = Text::from("x".repeat(129).as_str());
    for _ in 0..50 {
        s = Text::join(&s, &s).unwrap();
    }
    s
}

#[test]
fn a_literal_pattern_reads_a_string_only_when_the_lengths_agree() {
    let mut h = Heap::new();
    let is = |h: &mut Heap, s: Word, l: Value| {
        h.matches(&Pattern::Lit(l), s, &mut Paths::default(), &mut Vec::new())
            .unwrap()
    };
    // Lengths that differ: answered from the kept length, none of the text read.
    let s = h.alloc(Obj::Str(vast()));
    assert!(!is(&mut h, s, Value::str("abc")));
    assert!(!is(&mut h, s, Value::Int(4)));
    // Lengths that agree: a join of two pieces too long to merge is read in its parts.
    let (a, b) = ("a".repeat(200), "b".repeat(200));
    let r = Text::join(&a.as_str().into(), &b.as_str().into()).unwrap();
    assert!(!r.is_flat());
    let s = h.alloc(Obj::Str(r));
    assert!(is(&mut h, s, Value::str(&format!("{a}{b}"))));
    assert!(!is(&mut h, s, Value::str(&format!("{a}{}c", &b[1..]))));
}

#[test]
fn a_literal_pattern_compares_a_tuple_part_by_part() {
    let mut h = Heap::new();
    let x = h.fresh(&Value::str("x")).unwrap();
    let t = h.alloc(Obj::Tuple(vec![Word::int(1), x]));
    let k = h.uncounted(Value::tuple(vec![Value::Int(1), Value::str("x")]));
    let lit = |l: Value| Pattern::Lit(l);
    let one_x = Value::tuple(vec![Value::Int(1), Value::str("x")]);
    let one_y = Value::tuple(vec![Value::Int(1), Value::str("y")]);
    for w in [t, k] {
        let mut is = |l| h.matches(&lit(l), w, &mut Paths::default(), &mut Vec::new());
        assert!(is(one_x.clone()).unwrap());
        assert!(!is(one_y.clone()).unwrap());
        assert!(!is(Value::tuple(vec![Value::Int(1)])).unwrap());
        assert!(!is(Value::Int(1)).unwrap());
        assert!(!is(Value::atom_with("t", vec![Value::Int(1), Value::str("x")])).unwrap());
    }
    // A float literal compares bitwise, as the kernel does.
    let f = Word::scalar(&Value::float(-0.0)).unwrap();
    let zero = |h: &mut Heap, l: f64| {
        h.matches(
            &lit(Value::float(l)),
            f,
            &mut Paths::default(),
            &mut Vec::new(),
        )
        .unwrap()
    };
    assert_eq!(
        (zero(&mut h, -0.0), zero(&mut h, 0.0)),
        (
            Value::float(-0.0) == Value::float(-0.0),
            Value::float(-0.0) == Value::float(0.0)
        )
    );
}

#[test]
fn a_literal_pattern_on_a_state_word_is_an_error() {
    let mut h = Heap::new();
    let e = h
        .matches(
            &Pattern::Lit(Value::Int(1)),
            Word::state(),
            &mut Paths::default(),
            &mut Vec::new(),
        )
        .unwrap_err();
    assert_eq!(
        e,
        format!("runtime: a word tagged {} is not data", Word::STATE)
    );
}

#[test]
fn an_is_pattern_reads_a_constant_and_a_kernel_value_in_place() {
    let mut h = Heap::new();
    let name = h.uncounted(Value::str("Ada"));
    let big = h
        .fresh(
            &Value::int_text("1180591620717411303424", 10)
                .unwrap()
                .unwrap(),
        )
        .unwrap();
    let pair = h
        .fresh(&Value::tuple(vec![Value::Int(1), Value::str("x")]))
        .unwrap();
    let is = |h: &mut Heap, t: Type, w| {
        h.matches(&Pattern::Is(t), w, &mut Paths::default(), &mut Vec::new())
            .unwrap()
    };
    assert!(is(&mut h, Type::string(), name));
    assert!(!is(&mut h, Type::int(), name));
    assert!(is(&mut h, Type::int(), big));
    assert!(!is(&mut h, Type::string(), big));
    assert!(is(&mut h, Type::int(), Word::int(7)));
    assert!(!is(&mut h, Type::int(), pair));
    assert!(is(&mut h, Type::top(), pair));
}

#[test]
fn a_value_whose_parts_share_one_cell_is_read_once_per_cell() {
    // A report that pairs a summary with itself, 64 levels deep: 2^64 paths, 65 cells.
    let mut h = Heap::new();
    let mut w = h.fresh(&Value::str("total 12")).unwrap();
    let mut want = Value::str("total 12");
    for _ in 0..64 {
        h.inc(w).unwrap();
        w = h.alloc(Obj::Tuple(vec![w, w]));
        want = Value::tuple(vec![want.clone(), want]);
    }
    assert_eq!(h.value(w).unwrap(), want);
    h.dec(w).unwrap();
    assert_eq!(h.live(), 0);
}

#[test]
fn a_nested_constant_matched_natively_agrees_with_the_kernel() {
    let p = in_tuples(30, bind("last"));
    let t = Term::Match(
        Shared::new(Term::Lit(rate_table(30))),
        vec![((*p).clone(), Term::Var("last".into()))],
    );
    let want = kernel(&t).unwrap();
    assert_eq!(want, Value::Int(0));
    assert_eq!(native(&t).unwrap().value, want);
}

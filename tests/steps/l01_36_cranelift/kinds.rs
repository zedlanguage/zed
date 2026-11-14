//! `is T` on a string, tuple or atom in cells: when `T` holds every value of the cell's kind
//! or none of them, the runtime heap answers from the kind, without reading the text or the
//! parts, so the cost of the test does not grow with the value (COMPLEXITY.md R13).

use zed_kernel::types::{Type, Universe};
use zed_kernel::{Pattern, Text, Value};
use zed_rt::{Heap, Obj, Paths, Word};

/// Whether `w` matches `is t`.
pub(crate) fn is(h: &mut Heap, w: Word, t: &Type) -> bool {
    let p = Pattern::Is(t.clone());
    h.matches(&p, w, &mut Paths::default(), &mut Vec::new())
        .unwrap()
}

/// A heap holding the tuple `("s0", "s1", …)` of `n` strings in `n + 1` cells, and its word.
pub(crate) fn tuple_of_strings(n: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let xs = (0..n).map(|i| Value::str(&format!("s{i}"))).collect();
    let w = h.fresh(&Value::tuple(xs)).unwrap();
    (h, w)
}

#[test]
fn a_tuple_in_cells_is_tested_by_its_kind() {
    let (mut h, w) = tuple_of_strings(2);
    assert!(is(&mut h, w, &Type::universe(Universe::Tuple)));
    assert!(is(&mut h, w, &Type::top()));
    assert!(!is(&mut h, w, &Type::int()));
    assert!(!is(&mut h, w, &Type::string()));
    // A type holding some tuples and not others reads the parts.
    assert!(is(
        &mut h,
        w,
        &Type::tuple(vec![Type::string(), Type::string()])
    ));
    assert!(!is(
        &mut h,
        w,
        &Type::tuple(vec![Type::int(), Type::string()])
    ));
    assert!(!is(&mut h, w, &Type::tuple(vec![Type::string()])));
}

#[test]
fn a_string_in_cells_is_tested_without_flattening_it() {
    // A block longer than the text's leaves, doubled 50 times: about 145 PB in 51 nodes. A
    // test that read it would not finish.
    let mut vast = Text::from("x".repeat(129).as_str());
    for _ in 0..50 {
        vast = Text::join(&vast, &vast).unwrap();
    }
    let mut h = Heap::new();
    let w = h.alloc(Obj::Str(vast));
    assert!(is(&mut h, w, &Type::string()));
    assert!(is(&mut h, w, &Type::top()));
    assert!(!is(&mut h, w, &Type::int()));
    assert!(!is(&mut h, w, &Type::universe(Universe::Tuple)));
    // A type holding some strings and not others reads the text, here a join of two pieces
    // too long to merge.
    let (a, b) = ("a".repeat(200), "b".repeat(200));
    let ab = Text::join(&a.as_str().into(), &b.as_str().into()).unwrap();
    assert!(!ab.is_flat());
    let w = h.alloc(Obj::Str(ab));
    let lit = |s: String| Type::lit(&Value::str(&s)).unwrap();
    assert!(is(&mut h, w, &lit(format!("{a}{b}"))));
    assert!(!is(&mut h, w, &lit(format!("{b}{a}"))));
}

#[test]
fn an_atom_in_cells_is_tested_by_its_name() {
    let mut h = Heap::new();
    let w = h
        .fresh(&Value::atom_with("some", vec![Value::str("x")]))
        .unwrap();
    assert!(matches!(h.obj(w), Ok(Some(Obj::Atom { .. }))));
    let some = Type::atom_with("some", &Type::top());
    assert!(is(&mut h, w, &some));
    assert!(!is(&mut h, w, &Type::atom("some")));
    assert!(!is(&mut h, w, &Type::atom_with("none", &Type::top())));
    assert!(!is(&mut h, w, &Type::string()));
    // A payload type holding some payloads and not others reads the parts.
    let of = |t: Type| Type::atom_with("some", &Type::tuple(vec![t]));
    assert!(is(&mut h, w, &of(Type::string())));
    assert!(!is(&mut h, w, &of(Type::int())));
}

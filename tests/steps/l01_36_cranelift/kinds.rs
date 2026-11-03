//! `is T` on a string, tuple or atom in cells: when `T` holds every value of the cell's kind
//! or none of them, the runtime heap answers from the kind, without reading the text or the
//! parts, so the cost of the test does not grow with the value (COMPLEXITY.md R13).

use std::cell::RefCell;

use zed_kernel::types::{Type, Universe};
use zed_kernel::{Pattern, Text, Value};
use zed_rt::{Heap, Obj, Word};
use zed_tests::scaling;

/// Whether `w` matches `is t`.
fn is(h: &mut Heap, w: Word, t: &Type) -> bool {
    let p = Pattern::Is(t.clone());
    h.matches(&p, w, &mut Vec::new(), &mut Vec::new()).unwrap()
}

/// A heap holding the tuple `("s0", "s1", …)` of `n` strings in `n + 1` cells, and its word.
fn tuple_of_strings(n: usize) -> (Heap, Word) {
    let mut h = Heap::new();
    let xs = (0..n).map(|i| Value::str(&format!("s{i}"))).collect();
    let w = h.fresh(&Value::tuple(xs));
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
    let mut h = Heap::new();
    let ab = Text::join(&"a".into(), &"b".into());
    let w = h.alloc(Obj::Str(ab.clone()));
    assert!(is(&mut h, w, &Type::string()));
    assert!(is(&mut h, w, &Type::top()));
    assert!(!is(&mut h, w, &Type::int()));
    assert!(!is(&mut h, w, &Type::universe(Universe::Tuple)));
    assert_eq!(h.stats.copied, 0, "no test above reads the text");
    // A type holding some strings and not others reads the text.
    assert!(is(&mut h, w, &Type::lit(&Value::str("ab")).unwrap()));
    assert!(!is(&mut h, w, &Type::lit(&Value::str("ba")).unwrap()));
    assert!(ab.is_written_out());
    assert_eq!(
        h.stats.copied, 0,
        "the kernel reads the cell's own text, not a copy"
    );
}

#[test]
fn an_atom_in_cells_is_tested_by_its_name() {
    let mut h = Heap::new();
    let w = h.fresh(&Value::atom_with("some", vec![Value::str("x")]));
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

/// `TESTS` tests of a tuple of `n` strings, which the kind decides, at `n` and `8n`: the work
/// is the same at both sizes. Each would read all `n` parts if the tuple were made a value.
#[test]
fn testing_the_kind_of_a_large_tuple_scales() {
    const TESTS: usize = 64;
    let n = 2000;
    let small = RefCell::new(tuple_of_strings(n));
    let large = RefCell::new(tuple_of_strings(scaling::FACTOR * n));
    let types = [Type::universe(Universe::Tuple), Type::int(), Type::string()];
    let run = |hw: &RefCell<(Heap, Word)>| {
        let (h, w) = &mut *hw.borrow_mut();
        for i in 0..TESTS {
            let t = &types[i % types.len()];
            std::hint::black_box(is(h, *w, t));
        }
    };
    scaling::compare(
        &format!(
            "{TESTS} tests by kind of a tuple of {n} and {} strings",
            scaling::FACTOR * n
        ),
        "the tests do not read the parts, so the work should not grow with the tuple; 3 allows \
         for the noise of processor time where instructions are not counted",
        3.0,
        || run(&small),
        || run(&large),
    );
}

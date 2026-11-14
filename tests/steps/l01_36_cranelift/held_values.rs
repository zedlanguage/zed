//! A tuple or an atom that holds a function (DESIGN.md step L1.17): the counting machine of
//! step L1.34 and native code keep it as a held value, a cell whose parts are counted as a data
//! tuple's are, and give what the kernel gives, value or error, with native code counting as
//! the machine does, the release fused and not. Each test runs `calls(3, m)`: `f = (y) -> y`,
//! and `m` run at `z` = 0, 1 and 2.

use zed_kernel::Shared;
use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{KernelError, Pattern, Prim, Term, Value};

use super::function_binders::{agree, bind, calls, ints, match1};

/// `(f, z)`.
fn pair() -> Term {
    prim(Prim::Tuple, vec![var("f"), var("z")])
}

/// `#box(f)`.
fn boxed() -> Term {
    prim(
        Prim::Atom,
        vec![
            lit(Value::str("box")),
            lit(Value::tuple(Vec::new())),
            var("f"),
        ],
    )
}

/// `#box(h) -> h(z)`.
fn unbox(s: Term) -> Term {
    match1(
        s,
        Pattern::Atom("box".into(), vec![bind("h")]),
        app(var("h"), vec![var("z")]),
    )
}

/// The kernel's type error `m`.
fn type_err(m: &str) -> Result<Value, String> {
    Err(KernelError::Type(m.into()).to_string())
}

/// `t = (f, z); t[0](t[1])`, through the tuple read and through `at`.
#[test]
fn a_held_tuple_is_read_at_its_keys() {
    for p in [Prim::TupleGet, Prim::At] {
        let m = let_(
            "t",
            pair(),
            app(
                prim(p, vec![var("t"), lit(0)]),
                vec![prim(p, vec![var("t"), lit(1)])],
            ),
        );
        assert_eq!(agree(&calls(3, m)), Ok(ints(3)), "{p:?}");
    }
}

/// A key outside a held tuple is `#outOfBounds`, and a data atom key is given back, as for
/// data: the kernel makes both, from the held tuple's term.
#[test]
fn a_held_tuple_read_outside_it_is_the_kernels_value() {
    for (k, want) in [
        (lit(5), Value::atom("outOfBounds")),
        (lit(-1), Value::atom("outOfBounds")),
        (lit(Value::atom("k")), Value::atom("k")),
    ] {
        let m = prim(Prim::TupleGet, vec![pair(), k]);
        assert_eq!(agree(&calls(3, m)), Ok(Value::tuple(vec![want; 3])));
    }
}

/// `t(0)(t(1))`: a held tuple called at a key is read there.
#[test]
fn a_held_tuple_called_at_a_key_is_read() {
    let m = let_(
        "t",
        pair(),
        app(
            app(var("t"), vec![lit(0)]),
            vec![app(var("t"), vec![lit(1)])],
        ),
    );
    assert_eq!(agree(&calls(3, m)), Ok(ints(3)));
}

/// `match ((f, z), 1) { ((h, n), _) -> h(n) }`: a held tuple inside a held tuple.
#[test]
fn a_nested_held_tuple_binds_its_parts() {
    let s = prim(Prim::Tuple, vec![pair(), lit(1)]);
    let p = Pattern::Tuple(vec![
        Pattern::Tuple(vec![bind("h"), bind("n")]),
        Pattern::Wild,
    ]);
    let m = match1(s, p, app(var("h"), vec![var("n")]));
    assert_eq!(agree(&calls(3, m)), Ok(ints(3)));
}

/// A literal in a pattern is data: it never matches the function, and it matches a data part
/// of a held tuple by its value.
#[test]
fn a_literal_pattern_reads_a_held_tuples_data_part() {
    let arms = vec![
        (
            Pattern::Tuple(vec![Pattern::Lit(Value::Int(0)), Pattern::Wild]),
            lit(7),
        ),
        (
            Pattern::Tuple(vec![Pattern::Wild, Pattern::Lit(Value::Int(1))]),
            lit(9),
        ),
        (
            Pattern::Tuple(vec![bind("h"), bind("n")]),
            app(var("h"), vec![var("n")]),
        ),
    ];
    let m = Term::Match(Shared::new(pair()), arms);
    let want = Value::tuple(vec![Value::Int(0), Value::Int(9), Value::Int(2)]);
    assert_eq!(agree(&calls(3, m)), Ok(want));
}

/// `is T` on a held value: the function is in a type exactly when the type holds every
/// function, so `is String` misses and `is _` matches.
#[test]
fn a_type_test_on_a_held_tuple() {
    let arms = vec![
        (Pattern::Is(Type::string()), lit(7)),
        (Pattern::AnyAtom, lit(8)),
        (Pattern::Is(Type::top()), var("z")),
    ];
    let m = Term::Match(Shared::new(pair()), arms);
    assert_eq!(agree(&calls(3, m)), Ok(ints(3)));
}

/// A held value that no arm matches is the kernel's error.
#[test]
fn a_held_tuple_no_arm_matches_is_the_kernels_error() {
    let p = Pattern::Tuple(vec![bind("a"), bind("b"), bind("c")]);
    let m = match1(pair(), p, var("z"));
    assert_eq!(
        agree(&calls(3, m)),
        type_err("no arm matches the value that holds a function")
    );
}

/// `match #box(f) { #box(h) -> h(z) }`.
#[test]
fn a_held_atom_binds_its_payload() {
    assert_eq!(agree(&calls(3, unbox(boxed()))), Ok(ints(3)));
}

/// `#s(b: f, a: z)`, its fields sorted `a`, `b`, read by name.
#[test]
fn a_held_struct_atom_binds_its_fields_by_name() {
    let names = Value::tuple(vec![Value::str("b"), Value::str("a")]);
    let s = prim(
        Prim::Atom,
        vec![lit(Value::str("s")), lit(names), var("f"), var("z")],
    );
    let p = Pattern::Fields(
        "s".into(),
        vec![("b".into(), bind("h")), ("a".into(), bind("n"))],
    );
    let m = match1(s, p, app(var("h"), vec![var("n")]));
    assert_eq!(agree(&calls(3, m)), Ok(ints(3)));
}

/// An atom that holds a function passes through a primitive, an `if` and a call as any
/// failure does.
#[test]
fn a_held_atom_passes_through_as_a_failure() {
    for s in [
        prim(Prim::Add, vec![boxed(), lit(1)]),
        prim(Prim::Add, vec![lit(1), boxed()]),
        if_(boxed(), lit(1), lit(2)),
        app(boxed(), vec![var("z")]),
    ] {
        assert_eq!(agree(&calls(3, unbox(s))), Ok(ints(3)));
    }
}

/// An atom that holds a function and another failure: `#errs`, a family, holds data only.
#[test]
fn a_held_atom_and_another_failure_is_the_kernels_error() {
    let m = prim(Prim::Add, vec![boxed(), lit(Value::atom("x"))]);
    assert_eq!(
        agree(&calls(3, m)),
        type_err(
            "`+` given several failures, one of which holds a function, which `#errs` cannot hold"
        )
    );
}

/// `==` on a held value compares functions: the kernel's error.
#[test]
fn equality_on_a_held_value_is_the_kernels_error() {
    let m = prim(Prim::Eq, vec![pair(), pair()]);
    let got = agree(&calls(3, m));
    assert!(
        got.as_ref()
            .is_err_and(|e| e.contains("compares that function")),
        "{got:?}"
    );
}

/// A program whose result holds a function stops with the kernel's error.
#[test]
fn a_result_that_holds_a_function_is_the_kernels_error() {
    assert_eq!(
        agree(&calls(3, pair())),
        type_err("the program's result holds a function")
    );
}

/// A held tuple used twice, and one built and never read: its cell is shared, then freed, with
/// its closure, as the machine counts.
#[test]
fn a_held_tuple_shared_and_one_dropped_are_freed() {
    let m = let_(
        "t",
        pair(),
        let_(
            "u",
            pair(),
            prim(
                Prim::Add,
                vec![
                    app(prim(Prim::TupleGet, vec![var("t"), lit(0)]), vec![var("z")]),
                    prim(Prim::TupleGet, vec![var("t"), lit(1)]),
                ],
            ),
        ),
    );
    let want = Value::tuple(vec![Value::Int(0), Value::Int(2), Value::Int(4)]);
    assert_eq!(agree(&calls(3, m)), Ok(want));
}

/// A closure that captures a held tuple, inside a held tuple read outside it: the kernel gets
/// the whole term, closures and held values nested, and gives `#outOfBounds`.
#[test]
fn a_held_tuple_holding_a_closure_that_captures_one_becomes_a_term() {
    let m = let_(
        "u",
        pair(),
        let_(
            "c",
            lam(&["y"], prim(Prim::TupleGet, vec![var("u"), var("y")])),
            prim(
                Prim::TupleGet,
                vec![prim(Prim::Tuple, vec![var("c"), var("z")]), lit(5)],
            ),
        ),
    );
    let want = Value::tuple(vec![Value::atom("outOfBounds"); 3]);
    assert_eq!(agree(&calls(3, m)), Ok(want));
}

/// `match (f, (z, 1)) { (h, (a, b)) -> h(a) + b }`: a sub-pattern other than a name on a data
/// part of a held tuple binds inside that part.
#[test]
fn a_data_sub_pattern_binds_inside_a_held_tuple() {
    let s = prim(
        Prim::Tuple,
        vec![var("f"), prim(Prim::Tuple, vec![var("z"), lit(1)])],
    );
    let p = Pattern::Tuple(vec![bind("h"), Pattern::Tuple(vec![bind("a"), bind("b")])]);
    let body = prim(Prim::Add, vec![app(var("h"), vec![var("a")]), var("b")]);
    let want = Value::tuple((1..4).map(Value::Int).collect());
    assert_eq!(agree(&calls(3, match1(s, p, body))), Ok(want));
}

/// An atom that would hold a function and that the kernel refuses, a field name given twice or
/// a function as its name, is the kernel's error in all three.
#[test]
fn a_held_atom_the_kernel_refuses_is_its_error() {
    let twice = Value::tuple(vec![Value::str("a"), Value::str("a")]);
    for (name, fields) in [
        (lit(Value::str("s")), lit(twice)),
        (var("f"), lit(Value::tuple(Vec::new()))),
    ] {
        let m = prim(Prim::Atom, vec![name, fields, var("f"), var("z")]);
        let got = agree(&calls(3, m));
        assert!(got.is_err(), "{got:?}");
    }
}

/// Keys of a held tuple other than an int: an atom that holds a function is given back, as any
/// failure key is, data other than an int or an atom misses, and a function is the kernel's
/// error.
#[test]
fn a_held_tuple_read_at_a_key_that_is_no_int() {
    let m = unbox(prim(Prim::TupleGet, vec![pair(), boxed()]));
    assert_eq!(agree(&calls(3, m)), Ok(ints(3)));
    let m = prim(Prim::TupleGet, vec![pair(), lit(Value::str("k"))]);
    assert_eq!(
        agree(&calls(3, m)),
        Ok(Value::tuple(vec![Value::atom("outOfBounds"); 3]))
    );
    let m = prim(Prim::TupleGet, vec![pair(), var("f")]);
    let got = agree(&calls(3, m));
    assert!(got.is_err(), "{got:?}");
}

/// A held value called through a primitive bound to a name, so the call is not lowered to the
/// primitive: `+` passes a held atom through and `.` reads a held tuple; a key outside it
/// misses, and two keys are the kernel's error.
#[test]
fn a_held_value_called_through_a_primitive_value() {
    let through =
        |p: Prim, args: Vec<Term>| match1(Term::PrimFn(p), bind("p"), app(var("p"), args));
    let m = unbox(through(Prim::Add, vec![boxed(), lit(1)]));
    assert_eq!(agree(&calls(3, m)), Ok(ints(3)));
    let m = through(Prim::TupleGet, vec![pair(), lit(1)]);
    assert_eq!(agree(&calls(3, m)), Ok(ints(3)));
    let m = app(pair(), vec![lit(5)]);
    assert_eq!(
        agree(&calls(3, m)),
        Ok(Value::tuple(vec![Value::atom("outOfBounds"); 3]))
    );
    let got = agree(&calls(3, app(pair(), vec![lit(0), lit(1)])));
    assert!(got.is_err(), "{got:?}");
}

/// A held atom beside data: a tuple is no failure, so the atom passes through alone; a data
/// atom made at run time is a second failure, and `#errs` holds data only.
#[test]
fn a_held_atom_beside_a_data_tuple_and_a_data_atom() {
    let m = unbox(prim(
        Prim::Add,
        vec![boxed(), prim(Prim::Tuple, vec![var("z"), lit(1)])],
    ));
    assert_eq!(agree(&calls(3, m)), Ok(ints(3)));
    let e = prim(
        Prim::Atom,
        vec![
            lit(Value::str("e")),
            lit(Value::tuple(Vec::new())),
            var("z"),
        ],
    );
    let m = prim(Prim::Add, vec![boxed(), e]);
    assert_eq!(
        agree(&calls(3, m)),
        type_err(
            "`+` given several failures, one of which holds a function, which `#errs` cannot hold"
        )
    );
    // `#outOfBounds` made by the kernel, a data cell.
    let miss = prim(Prim::TupleGet, vec![pair(), lit(5)]);
    let m = prim(Prim::Add, vec![boxed(), miss]);
    assert_eq!(
        agree(&calls(3, m)),
        type_err(
            "`+` given several failures, one of which holds a function, which `#errs` cannot hold"
        )
    );
    // A held tuple is no failure: `+` on it is the kernel's error.
    let got = agree(&calls(3, prim(Prim::Add, vec![pair(), lit(1)])));
    assert!(got.is_err(), "{got:?}");
}

/// Patterns that miss a held value: a literal against a held part, fields of another atom, a
/// field the atom does not have; the arm that fits is taken.
#[test]
fn patterns_that_miss_a_held_value_pass_to_the_next_arm() {
    let s = prim(Prim::Tuple, vec![pair(), lit(1)]);
    let arms = vec![
        (
            Pattern::Tuple(vec![Pattern::Lit(Value::Int(0)), Pattern::Wild]),
            lit(7),
        ),
        (
            Pattern::Tuple(vec![
                Pattern::Tuple(vec![bind("h"), bind("n")]),
                Pattern::Wild,
            ]),
            app(var("h"), vec![var("n")]),
        ),
    ];
    assert_eq!(
        agree(&calls(3, Term::Match(Shared::new(s), arms))),
        Ok(ints(3))
    );
    let names = Value::tuple(vec![Value::str("a"), Value::str("b")]);
    let st = prim(
        Prim::Atom,
        vec![lit(Value::str("s")), lit(names), var("f"), var("z")],
    );
    for (s, miss) in [
        (
            boxed(),
            Pattern::Fields("s".into(), vec![("a".into(), bind("h"))]),
        ),
        (
            st.clone(),
            Pattern::Fields("s".into(), vec![("c".into(), bind("h"))]),
        ),
    ] {
        let arms = vec![(miss, lit(7)), (Pattern::Wild, var("z"))];
        assert_eq!(
            agree(&calls(3, Term::Match(Shared::new(s), arms))),
            Ok(ints(3))
        );
    }
}

/// `is` on a held atom, on a held tuple inside a held tuple, and on a tuple that holds a
/// primitive: each stand-in is built as the kernel builds it, so `is String` misses and `is _`
/// matches.
#[test]
fn a_type_test_on_held_atoms_nested_held_tuples_and_primitives() {
    for s in [
        boxed(),
        prim(Prim::Tuple, vec![pair(), lit(1)]),
        prim(Prim::Tuple, vec![Term::PrimFn(Prim::Sub), var("z")]),
    ] {
        let arms = vec![
            (Pattern::Is(Type::string()), lit(7)),
            (Pattern::Is(Type::top()), var("z")),
        ];
        assert_eq!(
            agree(&calls(3, Term::Match(Shared::new(s), arms))),
            Ok(ints(3))
        );
    }
}

//! A tuple or an atom that holds a function (DESIGN.md step L1.17): the counting machine of
//! step L1.34 and native code keep it as a held value, a cell whose parts are counted as a data
//! tuple's are, and give what the kernel gives, value or error, with native code counting as
//! the machine does, the release fused and not. Each test runs `calls(3, m)`: `f = (y) -> y`,
//! and `m` run at `z` = 0, 1 and 2.

use zed_kernel::Shared;
use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{Family, KernelError, Pattern, Prim, Term, Value};

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

/// `t = { "a" -> f, "b" -> z }; t["a"](t["b"])`: a family that holds a function is a held
/// value in the counting machine too (row FAIL-machine-held-family), read at its keys, with
/// native code's counts equal to the machine's.
#[test]
fn a_held_family_is_read_at_its_keys_and_applied() {
    let fam = prim(
        Prim::Entries,
        vec![
            lit(Value::str("a")),
            var("f"),
            lit(Value::str("b")),
            var("z"),
        ],
    );
    let m = let_(
        "t",
        fam,
        app(
            app(var("t"), vec![lit(Value::str("a"))]),
            vec![app(var("t"), vec![lit(Value::str("b"))])],
        ),
    );
    assert_eq!(agree(&calls(3, m)), Ok(ints(3)));
}

/// `t = (f, z); u = (k in {0, 1, 2, 3}) -> t; u[3][0](u[0][1]) + count(u)`: the family the
/// kernel makes holds one held tuple at each key, one cell with a reference per key, in the
/// machine as in native code, which bind each held value once outside the node's term (row
/// PROOF-native-held-early-build).
#[test]
fn a_held_tuple_at_each_key_of_a_family_is_one_cell() {
    let keys = Family::set((0..4).map(Value::Int));
    let fam = Term::Fam {
        domain: Shared::new(lit(Value::Family(keys))),
        var: "k".into(),
        body: Shared::new(var("t")),
    };
    let at = |k: i64, i: i64| prim(Prim::TupleGet, vec![app(var("u"), vec![lit(k)]), lit(i)]);
    let m = let_(
        "t",
        pair(),
        let_(
            "u",
            fam,
            prim(
                Prim::Add,
                vec![
                    app(at(3, 0), vec![at(0, 1)]),
                    prim(Prim::Count, vec![var("u")]),
                ],
            ),
        ),
    );
    let want = Value::tuple(vec![Value::Int(4), Value::Int(5), Value::Int(6)]);
    assert_eq!(agree(&calls(3, m)), Ok(want));
}

/// `(k in {0, 1, 2}) -> body`, a family the kernel makes.
fn three(body: Term) -> Term {
    Term::Fam {
        domain: Shared::new(lit(Value::Family(Family::set((0..3).map(Value::Int))))),
        var: "k".into(),
        body: Shared::new(body),
    }
}

/// `(z, z + 1, z + 2)` for each `z` of `calls(3, _)`, plus `c`.
fn plus(c: i64) -> Value {
    Value::tuple((0..3).map(|z| Value::Int(z + c)).collect())
}

/// `t = { "a" -> f, "b" -> z }; u = (k in {0, 1, 2}) -> if k == j { t["b"](t["a"]) } else
/// { k + z }; u[2]`: `t` is read only on the branch the family's entries do not take when `j`
/// is 9, and native code and the machine make it before the kernel runs the family (row
/// PROOF-native-held-early-build). Taken (`j` 2), the branch stops, applying data, in all three;
/// not taken, nothing stops, and the counts agree.
#[test]
fn a_held_value_read_only_on_an_untaken_branch_is_made_without_stopping() {
    let m = |j: i64| {
        let t = prim(
            Prim::Entries,
            vec![
                lit(Value::str("a")),
                var("f"),
                lit(Value::str("b")),
                var("z"),
            ],
        );
        let at = |s: &str| app(var("t"), vec![lit(Value::str(s))]);
        let body = if_(
            prim(Prim::Eq, vec![var("k"), lit(j)]),
            app(at("b"), vec![at("a")]),
            prim(Prim::Add, vec![var("k"), var("z")]),
        );
        let_(
            "t",
            t,
            let_("u", three(body), app(var("u"), vec![lit(2i64)])),
        )
    };
    assert_eq!(agree(&calls(3, m(9))), Ok(plus(2)));
    assert!(agree(&calls(3, m(2))).is_err());
}

/// `g = (y) -> y + z; t = (g, z); u = (k in {0, 1, 2}) -> t[0](k); u[2] + count(u)`: `g`, made
/// in each call, has no holder but `t` once `t` is made, and the family is `t`'s last use, so
/// every part of `t` is owned by `t` alone when native code and the machine make `t` again for
/// the kernel; the frees and the peak agree, fused and not.
#[test]
fn a_held_value_whose_parts_have_no_other_holder_is_made_for_its_last_use() {
    let g = lam(&["y"], prim(Prim::Add, vec![var("y"), var("z")]));
    let body = app(
        prim(Prim::TupleGet, vec![var("t"), lit(0i64)]),
        vec![var("k")],
    );
    let m = let_(
        "g",
        g,
        let_(
            "t",
            prim(Prim::Tuple, vec![var("g"), var("z")]),
            let_(
                "u",
                three(body),
                prim(
                    Prim::Add,
                    vec![
                        app(var("u"), vec![lit(2i64)]),
                        prim(Prim::Count, vec![var("u")]),
                    ],
                ),
            ),
        ),
    );
    assert_eq!(agree(&calls(3, m)), Ok(plus(5)));
}

/// `t = (f, z); u = (k in {0, 1, 2}) -> ((y) -> t[0](y) + k); w = (f, z + 1); v = (k in {0, 1,
/// 2}) -> u[k](w[1]) + t[1]; v[2] + v[0]`: two kernel calls in one run. The closures the first
/// makes capture `t` under the name native code and the machine bound it to in that call, and
/// the second binds `t` and `w` under names of its own; each closure binds its captures inside
/// its lambda, so no name of one call reads a value of the other (`fun_term`).
#[test]
fn closures_a_kernel_call_made_read_their_own_held_values_in_a_later_call() {
    let t0 = prim(Prim::TupleGet, vec![var("t"), lit(0i64)]);
    let inner = lam(
        &["y"],
        prim(Prim::Add, vec![app(t0, vec![var("y")]), var("k")]),
    );
    let w = prim(
        Prim::Tuple,
        vec![var("f"), prim(Prim::Add, vec![var("z"), lit(1i64)])],
    );
    let get = |x: &str, i: i64| prim(Prim::TupleGet, vec![var(x), lit(i)]);
    let v = three(prim(
        Prim::Add,
        vec![
            app(app(var("u"), vec![var("k")]), vec![get("w", 1)]),
            get("t", 1),
        ],
    ));
    let m = let_(
        "t",
        pair(),
        let_(
            "u",
            three(inner),
            let_(
                "w",
                w,
                let_(
                    "v",
                    v,
                    prim(
                        Prim::Add,
                        vec![
                            app(var("v"), vec![lit(2i64)]),
                            app(var("v"), vec![lit(0i64)]),
                        ],
                    ),
                ),
            ),
        ),
    );
    // v[k] = (z + 1) + k + z, so v[2] + v[0] = 4z + 4.
    let want = Value::tuple((0..3).map(|z| Value::Int(4 * z + 4)).collect());
    assert_eq!(agree(&calls(3, m)), Ok(want));
}

//! Recursive definitions: the plan's four (`Tree` and `W` accepted, `Nest` and `T` rejected at
//! the definition), the other ways a definition is rejected, and emptiness and subtyping of
//! recursive types, where the check is coinductive.

use zed_kernel::Value;
use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};

fn def(name: &str, params: &[&str], body: Expr) -> Def {
    Def {
        name: name.into(),
        params: params.iter().map(|p| p.to_string()).collect(),
        body,
    }
}

fn r(i: usize, args: Vec<Expr>) -> Expr {
    Expr::Ref(i, args)
}

fn ty(t: Type) -> Expr {
    Expr::Type(t)
}

fn atom(name: &str, items: Vec<Expr>) -> Expr {
    Expr::Atom(name.into(), items)
}

fn bare(name: &str) -> Expr {
    ty(Type::atom(name))
}

fn or(xs: Vec<Expr>) -> Expr {
    Expr::Union(xs)
}

/// The one type of a group with no parameters.
fn one(defs: Vec<Def>) -> Type {
    Group::new(defs).unwrap().instance(vec![]).remove(0)
}

fn rejected(defs: Vec<Def>) -> String {
    Group::new(defs).unwrap_err().message
}

/// `type Tree(A) = #leaf(A) | #fork(Tree(A), Tree(A))`.
fn tree() -> Group {
    let a = Expr::Param(0);
    let t = || r(0, vec![Expr::Param(0)]);
    Group::new(vec![def(
        "Tree",
        &["A"],
        or(vec![atom("leaf", vec![a]), atom("fork", vec![t(), t()])]),
    )])
    .unwrap()
}

fn leaf(v: Value) -> Value {
    Value::atom_with("leaf", vec![v])
}

fn fork(l: Value, r: Value) -> Value {
    Value::atom_with("fork", vec![l, r])
}

#[test]
fn the_plans_definitions() {
    // `Tree` is guarded by its atoms and passes `A` unchanged.
    let t = tree().instance(vec![Type::int()]).remove(0);
    assert_eq!(t.to_string(), "Tree(int)");
    let v = fork(
        leaf(Value::Int(1)),
        fork(leaf(Value::Int(2)), leaf(Value::Int(3))),
    );
    assert!(t.contains(&v));
    assert!(!t.contains(&fork(leaf(Value::Int(1)), leaf(Value::str("x")))));
    assert!(!t.is_empty());
    // `type W = (W) -> int`: the recursive occurrence is in a guarantee, but the value type
    // is not empty and does not mention `W`.
    let w = || Expr::exact(r(0, vec![]), ty(Type::int()));
    assert!(!one(vec![def("W", &[], w())]).is_empty());
    // `type Nest(A) = #leaf(A) | #node(Nest((A, A)))` changes its parameter.
    let pair = Expr::Tuple(vec![Expr::Param(0), Expr::Param(0)]);
    let nest = def(
        "Nest",
        &["A"],
        or(vec![
            atom("leaf", vec![Expr::Param(0)]),
            atom("node", vec![r(0, vec![pair])]),
        ]),
    );
    assert_eq!(
        rejected(vec![nest]),
        "the type `Nest` is not regular: its recursive occurrence `Nest((A, A))` changes the \
         parameters, so the type has no end of components"
    );
    // `type T = (T) -> (#a & #b)` would be inhabited exactly when it is empty.
    let t = Expr::exact(r(0, vec![]), Expr::And(vec![bare("a"), bare("b")]));
    assert_eq!(
        rejected(vec![def("T", &[], t)]),
        "the type `T` is not monotone in emptiness: a recursive occurrence stands in the \
         guaranteed domain of a morphism type whose value type may be empty or mentions the \
         group"
    );
}

#[test]
fn other_rejections() {
    let n = || r(0, vec![]);
    let msg = |defs| rejected(defs);
    // Not contractive: alone, and through a second definition.
    assert!(msg(vec![def("N", &[], or(vec![n(), ty(Type::int())]))]).contains("not contractive"));
    let mutual = vec![
        def("A", &[], r(1, vec![])),
        def("B", &[], or(vec![r(0, vec![]), ty(Type::int())])),
    ];
    assert!(msg(mutual).contains("`A` is not contractive"));
    // Under a complement, to the right of `\`, and in a guarantee whose value is the group.
    let under_not = atom("a", vec![Expr::Not(Box::new(n()))]);
    assert!(msg(vec![def("N", &[], under_not)]).contains("under a complement"));
    let diff = Expr::Diff(Box::new(ty(Type::int())), Box::new(atom("b", vec![n()])));
    assert!(msg(vec![def("N", &[], diff)]).contains("to the right of `\\`"));
    assert!(msg(vec![def("U", &[], Expr::exact(n(), n()))]).contains("guaranteed domain"));
    // A value type that a parameter can make empty: `type F(A) = (F(A)) -> A`, and one that a
    // larger argument shrinks, `(H(A)) -> (int \ A)`.
    let p = || Expr::Param(0);
    let self_ = || r(0, vec![p()]);
    assert!(msg(vec![def("F", &["A"], Expr::exact(self_(), p()))]).contains("guaranteed"));
    let shrinking = Expr::Diff(Box::new(ty(Type::int())), Box::new(p()));
    assert!(msg(vec![def("H", &["A"], Expr::exact(self_(), shrinking))]).contains("guaranteed"));
    // Parameters that differ across a group.
    let uneven = vec![
        def("A", &["X"], atom("a", vec![r(1, vec![p()])])),
        def("B", &[], atom("b", vec![r(0, vec![])])),
    ];
    assert!(msg(uneven).contains("takes other parameters"));
}

#[test]
fn accepted_neighbors_of_the_rejections() {
    let p = || Expr::Param(0);
    // `(G(A)) -> (A | int)` is never empty, and a guarantee with a nonrecursive value is
    // admitted however deep the occurrence.
    let g = Expr::exact(r(0, vec![p()]), or(vec![p(), ty(Type::int())]));
    assert!(Group::new(vec![def("G", &["A"], g)]).is_ok());
    // A recursive occurrence in a permission only, under no complement.
    let perm = Expr::Morphism(
        Box::new(ty(Type::empty())),
        Box::new(r(0, vec![])),
        Box::new(r(0, vec![])),
    );
    assert!(Group::new(vec![def("P", &[], perm)]).is_ok());
    // One definition naming another bare, the other guarded: the cycle has a constructor.
    let mutual = vec![
        def("A", &[], r(1, vec![])),
        def(
            "B",
            &[],
            or(vec![atom("b", vec![r(0, vec![])]), ty(Type::int())]),
        ),
    ];
    let ab = Group::new(mutual).unwrap().instance(vec![]);
    assert!(ab[0].equiv(&ab[1]));
    assert!(ab[0].contains(&Value::atom_with("b", vec![Value::Int(1)])));
}

#[test]
fn emptiness_is_coinductive() {
    // Values are finite, so a type each of whose values holds a smaller one is empty.
    let e = one(vec![def("E", &[], atom("e", vec![r(0, vec![])]))]);
    assert!(e.is_empty());
    let stream = one(vec![def(
        "S",
        &[],
        Expr::Tuple(vec![ty(Type::int()), r(0, vec![])]),
    )]);
    assert!(stream.is_empty());
    // A tree with no leaf type has no leaf, so no tree.
    assert!(tree().instance(vec![Type::empty()])[0].is_empty());
    assert!(!tree().instance(vec![Type::atom("x")])[0].is_empty());
    // A meet in a component is kept unevaluated while the body is built:
    // `type M = #z | #a(M & (#z | #a(_)))` holds `#a(#z)`, and without `#z` it is empty.
    let shaped = || {
        Expr::And(vec![
            r(0, vec![]),
            or(vec![bare("z"), atom("a", vec![ty(Type::top())])]),
        ])
    };
    let m = one(vec![def(
        "M",
        &[],
        or(vec![bare("z"), atom("a", vec![shaped()])]),
    )]);
    let az = Value::atom_with("a", vec![Value::atom("z")]);
    assert!(m.contains(&az) && !m.is_empty());
    assert!(!m.contains(&Value::atom_with("a", vec![Value::Int(1)])));
    let m0 = one(vec![def("M", &[], atom("a", vec![shaped()]))]);
    assert!(m0.is_empty());
}

/// `type L = #nil | #cons(A, L)` at `a`.
fn list(a: Type) -> Type {
    let body = or(vec![bare("nil"), atom("cons", vec![ty(a), r(0, vec![])])]);
    one(vec![def("L", &[], body)])
}

#[test]
fn recursive_subtyping() {
    let ints = list(Type::int());
    let wider = list(Type::int() | Type::string());
    assert!(ints.subtype(&wider) && !wider.subtype(&ints));
    // Two definitions of one set are one type.
    assert!(ints.equiv(&list(Type::int())));
    // Even and odd lengths together are every list, and neither alone is.
    let even = one(vec![def(
        "Even",
        &[],
        or(vec![
            bare("nil"),
            atom(
                "cons",
                vec![
                    ty(Type::int()),
                    atom("cons", vec![ty(Type::int()), r(0, vec![])]),
                ],
            ),
        ]),
    )]);
    let odd = Type::atom_with("cons", &Type::tuple(vec![Type::int(), even.clone()]));
    assert!((&even | &odd).equiv(&ints));
    assert!(even.subtype(&ints) && !ints.subtype(&even));
    assert!((&even & &odd).is_empty());
    // `W` is one type however it is written; `(W) -> int` is not `(W) -> String`.
    let w = |v: Type| one(vec![def("W", &[], Expr::exact(r(0, vec![]), ty(v)))]);
    assert!(w(Type::int()).equiv(&w(Type::int())));
    assert!(!w(Type::int()).subtype(&w(Type::string())));
    // A tree of a subtype is a subtype of the tree.
    let small = tree()
        .instance(vec![Type::lit(&Value::Int(0)).unwrap()])
        .remove(0);
    let big = tree().instance(vec![Type::int()]).remove(0);
    assert!(small.subtype(&big) && !big.subtype(&small));
}

#[test]
fn a_result_resting_on_a_false_assumption_is_dropped() {
    // Deciding the list assumes it empty, which makes its `#cons` payload empty for a moment;
    // the list then has `#nil`, so that answer must not be kept.
    let l = list(Type::int());
    assert!(!l.is_empty());
    assert!(!Type::tuple(vec![Type::int(), l.clone()]).is_empty());
    assert!(!Type::atom_with("cons", &Type::tuple(vec![Type::int(), l])).is_empty());
}

#[test]
fn recursive_types_are_decidable_unless_they_bound_functions() {
    assert!(tree().instance(vec![Type::int()])[0].decidable());
    let f = Type::exact(Type::int(), Type::int());
    assert!(!tree().instance(vec![f])[0].decidable());
    let w = one(vec![def(
        "W",
        &[],
        Expr::exact(r(0, vec![]), ty(Type::int())),
    )]);
    assert!(!w.decidable());
}

#[test]
fn recursive_definitions_scale() {
    // The check for contractiveness searched from each definition in turn, so a chain of `d`
    // definitions took `O(d²)` steps (ratio 31); one pass of Tarjan's components now finds
    // the cycles. A body nested `d` deep had each part kept unevaluated copied, walked for
    // recursive occurrences and named in full, and an atom's payload was copied to test a
    // value, each once per level: `O(d²)` (ratio 68). The body is now a shared tree whose
    // nodes know whether they mention the group, a part's name is made when it is printed,
    // and a payload is tested in place.
    use zed_tests::scaling;
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            scaling::check("chain of definitions", 100, |d| {
                let defs = (0..d)
                    .map(|i| {
                        let body = if i + 1 < d {
                            or(vec![r(i + 1, vec![]), bare(&format!("a{i}"))])
                        } else {
                            bare("end")
                        };
                        def(&format!("T{i}"), &[], body)
                    })
                    .collect();
                let t = one(defs);
                assert!(t.contains(&Value::atom("end")));
            });
            scaling::check("nested body", 100, |d| {
                let mut body = Expr::Tuple(vec![r(0, vec![]), ty(Type::int())]);
                for _ in 0..d {
                    body = atom("n", vec![body]);
                }
                let t = one(vec![def("T", &[], or(vec![body, bare("z")]))]);
                let mut v = Value::Tuple(vec![Value::atom("z"), Value::Int(1)]);
                for _ in 0..d {
                    v = Value::atom_with("n", vec![v]);
                }
                assert!(t.contains(&v));
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn the_lowest_definition_on_a_cycle_is_named() {
    // `A = B | int` reaches the cycle `B = C | int`, `C = B | #c` but is not on it.
    let (b, c) = (|| r(1, vec![]), || r(2, vec![]));
    let g = Group::new(vec![
        def("A", &[], or(vec![b(), ty(Type::int())])),
        def("B", &[], or(vec![c(), ty(Type::int())])),
        def("C", &[], or(vec![b(), bare("c")])),
    ]);
    let e = g.unwrap_err();
    assert_eq!(e.def, 1, "{}", e.message);
    assert!(
        e.message.contains("`B` is not contractive"),
        "{}",
        e.message
    );
    // Two cycles: `{B, C}` is completed first, and `A`, the lowest, is named.
    let g = Group::new(vec![
        def("A", &[], or(vec![b(), r(0, vec![])])),
        def("B", &[], or(vec![c(), ty(Type::int())])),
        def("C", &[], or(vec![b(), bare("c")])),
    ]);
    assert_eq!(g.unwrap_err().def, 0);
    // A definition naming itself is a cycle of one, and a guarded cycle is none.
    let g = Group::new(vec![
        def("A", &[], atom("a", vec![r(1, vec![])])),
        def("B", &[], or(vec![r(1, vec![]), bare("b")])),
    ]);
    assert_eq!(g.unwrap_err().def, 1);
    assert!(
        Group::new(vec![
            def("A", &[], atom("a", vec![r(1, vec![])])),
            def("B", &[], or(vec![r(0, vec![]), bare("b")])),
        ])
        .is_ok()
    );
}

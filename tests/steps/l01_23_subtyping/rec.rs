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
fn definitions_written_alike_at_equal_arguments_are_one_type() {
    // Two modules each write `type Tree(A) = #leaf(A) | #fork(Tree(A), Tree(A))` and use
    // `Tree(int | String)`, one spelling the argument `String | int`: both name one type.
    let int_or_string = &Type::int() | &Type::string();
    let string_or_int = &Type::string() | &Type::int();
    let a = tree().instance(vec![int_or_string.clone()]).remove(0);
    let b = tree().instance(vec![string_or_int]).remove(0);
    assert!(a == b, "{a} and {b}");
    // Another argument is another type, and the same one asked again is the first.
    let at_int = tree().instance(vec![Type::int()]).remove(0);
    assert!(at_int != a);
    assert!(at_int == tree().instance(vec![Type::int()]).remove(0));
    // A type inside a body counts by its value, not by how it was built.
    let pair = |t: Type| {
        Group::new(vec![def(
            "Pairs",
            &[],
            or(vec![bare("end"), atom("pair", vec![ty(t), r(0, vec![])])]),
        )])
        .unwrap()
        .instance(vec![])
        .remove(0)
    };
    assert!(pair(int_or_string.clone()) == pair(&Type::string() | &Type::int()));
    assert!(pair(int_or_string) != pair(Type::int()));
    // A definition renamed is written otherwise and prints otherwise: another type, with the
    // same values. One with its parameter renamed prints alike, so it is the same type, its
    // canonical form the same (item REC-canon).
    let a_t = |name: &str, param: &str| {
        let t = || r(0, vec![Expr::Param(0)]);
        Group::new(vec![def(
            name,
            &[param],
            or(vec![
                atom("leaf", vec![Expr::Param(0)]),
                atom("fork", vec![t(), t()]),
            ]),
        )])
        .unwrap()
        .instance(vec![Type::int()])
        .remove(0)
    };
    let renamed = a_t("Tree2", "A");
    assert!(renamed != at_int);
    assert!(renamed.subtype(&at_int) && at_int.subtype(&renamed));
    assert!(a_t("Tree", "B") == at_int);
    assert!(a_t("Tree", "A") == at_int);
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
         parameters, so following it reaches a new type at each step and the type has no end of \
         components. To repair it, pass the parameters unchanged at every recursive occurrence, \
         as `Nest(A)`"
    );
    // `type T = (T) -> (#a & #b)` would be inhabited exactly when it is empty.
    let t = Expr::exact(r(0, vec![]), Expr::And(vec![bare("a"), bare("b")]));
    assert_eq!(
        rejected(vec![def("T", &[], t)]),
        "the type `T` is outside the form the checker accepts: a recursive occurrence stands in \
         the guarantee of `(T) -> #a & #b`, whose value type `#a & #b` is empty; the check is \
         sufficient, not necessary, so a type it refuses may still be monotone in emptiness. To repair it, write the type so that no recursive occurrence \
         stands there; one inside a tuple, an atom's payload, a union or a function's value \
         type is always accepted"
    );
}

/// A recursive occurrence in a message is written with the parentheses the grammar needs and
/// no others (DESIGN.md sec:grammar): an argument is a whole type, so a union stands bare in
/// it; a tuple of one component is `(A,)`; a tuple as the key of `->?` is parenthesized, or it
/// would read as two parameters. Each text parses as a type.
#[test]
fn an_irregular_occurrence_is_written_with_only_the_parentheses_it_needs() {
    let a = || Expr::Param(0);
    let pair = || Expr::Tuple(vec![a(), a()]);
    for (arg, shown) in [
        (Expr::Tuple(vec![a()]), "Nest((A,))"),
        (or(vec![a(), bare("x")]), "Nest(A | #x)"),
        (
            Expr::Morphism(Box::new(ty(Type::empty())), Box::new(pair()), Box::new(a())),
            "Nest(((A, A)) ->? A)",
        ),
        (
            Expr::Tuple(vec![Expr::exact(a(), a()), or(vec![a(), bare("x")])]),
            "Nest(((A) -> A, A | #x))",
        ),
    ] {
        let nest = def(
            "Nest",
            &["A"],
            or(vec![
                atom("leaf", vec![a()]),
                atom("node", vec![r(0, vec![arg])]),
            ]),
        );
        let message = rejected(vec![nest]);
        assert!(
            message.contains(&format!("its recursive occurrence `{shown}` changes")),
            "{message}"
        );
        let tokens = zedc::lex::lex_fence(shown).expect("tokens");
        zedc::parse::parse(shown, &tokens, "Type", zedc::parse::TOP)
            .unwrap_or_else(|e| panic!("{shown}: {e:?}"));
    }
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
    assert!(
        msg(vec![def("U", &[], Expr::exact(n(), n()))]).contains("in the guarantee of `(U) -> U`")
    );
    // A value type that a parameter can make empty: `type F(A) = (F(A)) -> A`, and one that a
    // larger argument shrinks, `(H(A)) -> (int \ A)`.
    let p = || Expr::Param(0);
    let self_ = || r(0, vec![p()]);
    assert!(
        msg(vec![def("F", &["A"], Expr::exact(self_(), p()))])
            .contains("`A` is empty when every parameter is `empty`")
    );
    let shrinking = Expr::Diff(Box::new(ty(Type::int())), Box::new(p()));
    assert!(
        msg(vec![def("H", &["A"], Expr::exact(self_(), shrinking))]).contains("so it may be empty")
    );
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

/// Lists of int whose length is a multiple of `p`.
fn multiple(p: usize) -> Type {
    let mut body = r(0, vec![]);
    for _ in 0..p {
        body = atom("cons", vec![ty(Type::int()), body]);
    }
    one(vec![def("M", &[], or(vec![bare("nil"), body]))])
}

/// Lists of int whose `n`-th item from the end is `1`, guessed where it is.
fn nth_from_end(n: usize) -> Type {
    let one_ = Type::lit(&Value::Int(1)).unwrap();
    let mut rest = vec![def("R0", &[], bare("nil"))];
    for k in 1..n {
        rest.push(def(
            &format!("R{k}"),
            &[],
            atom("cons", vec![ty(Type::int()), r(k - 1, vec![])]),
        ));
    }
    rest.push(def(
        "G",
        &[],
        or(vec![
            atom("cons", vec![ty(Type::int()), r(n, vec![])]),
            atom("cons", vec![ty(one_), r(n - 1, vec![])]),
        ]),
    ));
    Group::new(rest).unwrap().instance(vec![]).pop().unwrap()
}

#[test]
fn products_of_recursive_types() {
    // Deciding these meets one type per state of the product of the definitions, or per set
    // of states of a definition whose alternatives overlap: 30 states for 2, 3 and 5, about
    // 1000 types for the third item from the end. Both grow exponentially with the
    // definitions and the item, as emptiness of regular tree types can (DESIGN.md L1.23).
    let six = &(&multiple(2) & &multiple(3)) & &multiple(5);
    assert!(six.subtype(&multiple(30)) && multiple(30).subtype(&six));
    assert!(!(&multiple(2) & &multiple(3)).subtype(&multiple(12)));
    assert!(!multiple(4).subtype(&multiple(6)));
    for n in 1..=3 {
        assert!(nth_from_end(n).subtype(&nth_from_end(n)), "n = {n}");
        if n < 3 {
            assert!(!nth_from_end(n).equiv(&nth_from_end(n + 1)), "n = {n}");
        }
    }
}

/// `Type::contains` keeps each test by the id of the sequence it reads (`Items::id`), which
/// copies of one sequence share and no other sequence has. A tree whose two halves are one
/// shared value at every level has `2^d` paths and `d` sequences: each is tested once, so depth
/// 60 is decided at once. The answers agree with those on copies built apart, whose sequences
/// are all distinct, and do not change when the values are rebuilt elsewhere in memory.
#[test]
fn membership_by_sequence_id_is_deterministic() {
    let t = tree().instance(vec![Type::int()]).remove(0);
    let shared = |d: usize, x: Value| (0..d).fold(x, |v, _| fork(v.clone(), v));
    fn apart(d: usize, x: &Value) -> Value {
        match d {
            0 => x.clone(),
            _ => fork(apart(d - 1, x), apart(d - 1, x)),
        }
    }
    let bad = || leaf(Value::str("x"));
    // One bad leaf at the right end, under a left half that is shared and good.
    let right_bad = |d: usize| (0..d).fold(bad(), |v, i| fork(shared(i, leaf(Value::Int(1))), v));
    for round in 0..3 {
        // Values built in each round sit at new addresses.
        let _spacer: Vec<Value> = (0..round * 7).map(|i| leaf(Value::Int(i as i64))).collect();
        assert!(t.contains(&shared(60, leaf(Value::Int(1)))));
        assert!(!t.contains(&shared(60, bad())));
        assert!(!t.contains(&right_bad(60)));
        for d in [0, 1, 5, 10] {
            for x in [leaf(Value::Int(1)), bad()] {
                assert_eq!(
                    t.contains(&shared(d, x.clone())),
                    t.contains(&apart(d, &x)),
                    "depth {d}"
                );
            }
            assert!(!t.contains(&right_bad(d)), "depth {d}");
        }
    }
    // The same queries in one batch on one thread, and each alone on a fresh thread, whose
    // allocations and kept results start empty, agree.
    let queries = || -> Vec<(Type, Value)> {
        let mut q = Vec::new();
        for d in [0, 3, 8] {
            for x in [leaf(Value::Int(1)), bad()] {
                q.push((t.clone(), shared(d, x.clone())));
                q.push((t.clone(), apart(d, &x)));
            }
            q.push((t.clone(), right_bad(d)));
        }
        q
    };
    let batch: Vec<bool> = queries().iter().map(|(t, v)| t.contains(v)).collect();
    let alone: Vec<bool> = (0..batch.len())
        .map(|i| {
            std::thread::spawn(move || {
                let t = tree().instance(vec![Type::int()]).remove(0);
                let shared = |d: usize, x: Value| (0..d).fold(x, |v, _| fork(v.clone(), v));
                let bad = || leaf(Value::str("x"));
                let right_bad =
                    |d: usize| (0..d).fold(bad(), |v, i| fork(shared(i, leaf(Value::Int(1))), v));
                let (d, k) = ([0, 3, 8][i / 5], i % 5);
                let v = match k {
                    0 => shared(d, leaf(Value::Int(1))),
                    1 => apart(d, &leaf(Value::Int(1))),
                    2 => shared(d, bad()),
                    3 => apart(d, &bad()),
                    _ => right_bad(d),
                };
                t.contains(&v)
            })
            .join()
            .expect("a query thread")
        })
        .collect();
    assert_eq!(batch, alone);
    assert_eq!(batch.iter().filter(|&&b| b).count(), 6);
}

/// One tail read against two types: `[1, 2]` as a `#cons` whose tail is a list of ints or a
/// list of strings. The tail `[2]` is tested against both list types, and a kept test must not
/// give the answer for one to the other: the value is in `P | Q` and in `P \ Q`, and not in
/// `Q \ P`. With the kept tests keyed by the sequence alone, not the type, the tail's answer
/// under the list of ints is read for the list of strings too.
#[test]
fn membership_tells_two_types_of_one_tail_apart() {
    let of = |t: Type| Type::atom_with("cons", &Type::tuple(vec![Type::int(), t]));
    let (p, q) = (of(list(Type::int())), of(list(Type::string())));
    let tail = Value::atom_with("cons", vec![Value::Int(2), Value::atom("nil")]);
    let v = Value::atom_with("cons", vec![Value::Int(1), tail]);
    assert!((&p | &q).contains(&v));
    assert!((&p - &q).contains(&v));
    assert!(!(&q - &p).contains(&v));
    assert!(p.contains(&v) && !q.contains(&v));
}

/// A chain of `d` definitions, `T{i} = T{i+1} | #a{i}`, the last `#end`: each names the next
/// bare, so the group is admitted and its first member holds `#end` and every `#a{i}`.
fn chain(d: usize) -> Vec<Def> {
    (0..d)
        .map(|i| {
            let body = if i + 1 < d {
                or(vec![r(i + 1, vec![]), bare(&format!("a{i}"))])
            } else {
                bare("end")
            };
            def(&format!("T{i}"), &[], body)
        })
        .collect()
}

/// Small instance of `bench::writing_an_irregular_occurrence_scales_with_its_depth`
/// (TEST-bench-move-l0123, author P170; the text at depth 3 was checked only inside the
/// benchmark): an argument nested `d` levels, a function's result, a tuple component and a
/// member of a union in turn, is written with the parentheses each level needs, and the text
/// parses as a type.
#[test]
fn an_irregular_occurrence_nested_in_turn_is_written_with_the_parentheses_it_needs() {
    let a = || Expr::Param(0);
    let arg = |d: usize| {
        (0..d).fold(a(), |x, k| match k % 3 {
            0 => Expr::exact(a(), x),
            1 => Expr::Tuple(vec![x, a()]),
            _ => or(vec![x, bare("x")]),
        })
    };
    for d in 1..=12 {
        let nest = def(
            "Nest",
            &["A"],
            or(vec![
                atom("leaf", vec![a()]),
                atom("node", vec![r(0, vec![arg(d)])]),
            ]),
        );
        let message = rejected(vec![nest]);
        let start = "its recursive occurrence `";
        let at = message
            .find(start)
            .unwrap_or_else(|| panic!("{d}: {message}"))
            + start.len();
        let end = message[at..]
            .find("` changes")
            .unwrap_or_else(|| panic!("{d}: {message}"));
        let shown = &message[at..at + end];
        if d == 3 {
            assert_eq!(shown, "Nest(((A) -> A, A) | #x)");
        }
        let tokens = zedc::lex::lex_fence(shown).expect("tokens");
        zedc::parse::parse(shown, &tokens, "Type", zedc::parse::TOP)
            .unwrap_or_else(|e| panic!("{d}: {shown}: {e:?}"));
    }
}

/// Small instance of `bench::recursive_definitions_scale` (TEST-bench-move-l0123, author P170):
/// a chain of definitions each naming the next bare is admitted and holds the last one's value
/// and each one's own, not the last one's `#a`; a body nested `d` deep holds the value nested as
/// deep and not one level deeper.
#[test]
fn chains_of_definitions_and_nested_bodies_are_admitted_and_hold_their_values() {
    for d in 1..=12 {
        assert!(Group::new(chain(d)).is_ok(), "{d}");
        let t = one(chain(d));
        assert!(t.contains(&Value::atom("end")), "{d}");
        for i in 0..d - 1 {
            assert!(t.contains(&Value::atom(&format!("a{i}"))), "{d}: #a{i}");
        }
        assert!(!t.contains(&Value::atom(&format!("a{}", d - 1))), "{d}");
    }
    for d in 0..=12 {
        let mut body = Expr::Tuple(vec![r(0, vec![]), ty(Type::int())]);
        for _ in 0..d {
            body = atom("n", vec![body]);
        }
        let t = one(vec![def("T", &[], or(vec![body, bare("z")]))]);
        let mut v = Value::tuple(vec![Value::atom("z"), Value::Int(1)]);
        for _ in 0..d {
            v = Value::atom_with("n", vec![v]);
        }
        assert!(t.contains(&v), "{d}");
        assert!(!t.contains(&Value::atom_with("n", vec![v])), "{d}");
    }
}

/// Small instance of `bench::membership_in_two_mutual_definitions_scales`
/// (TEST-bench-move-l0123, author P170; its asserts at length 5 ran only inside the benchmark):
/// in two definitions whose `#cons` alternatives overlap, a list of ints that ends in `#nil` is
/// a member and one that ends in a string is not, at every length; length 0 is `#nil` and the
/// string alone.
#[test]
fn membership_in_two_mutual_definitions() {
    let body = || {
        or(vec![
            bare("nil"),
            atom("cons", vec![ty(Type::int()), r(0, vec![])]),
            atom("cons", vec![ty(Type::int()), r(1, vec![])]),
        ])
    };
    let t = one(vec![def("X", &[], body()), def("Y", &[], body())]);
    let ending = |l: usize, end: Value| {
        (0..l).fold(end, |v, i| {
            Value::atom_with("cons", vec![Value::Int(i as i64), v])
        })
    };
    for l in 0..=12 {
        assert!(t.contains(&ending(l, Value::atom("nil"))), "{l}");
        assert!(!t.contains(&ending(l, Value::str("end"))), "{l}");
    }
}

mod bench;

//! `Nodes::node` refuses a row tail outside the class of the first list it read
//! (TEST-kernel-unreached-paths-4). A file of its own, not a module inside `escape.rs`: it
//! builds the lists with `rec::Group`, and that import written in `escape.rs` would close an
//! import cycle through `escape.rs` and `rec/group.rs` (step S.1f, `s_01f_import_graph`).

use super::*;

/// The list `L = #stop | #link((int, L))`.
fn list(stop: &str, link: &str) -> Type {
    use super::super::super::rec::{Def, Expr, Group};
    let body = Expr::Union(vec![
        Expr::Type(Type::atom(stop)),
        Expr::Atom(
            link.into(),
            vec![Expr::Type(Type::int()), Expr::Ref(0, vec![])],
        ),
    ]);
    (Group::new(vec![Def {
        name: "L".into(),
        params: vec![],
        body,
    }]))
    .expect("a group")
    .instance(vec![])
    .remove(0)
}

/// `#cons((int, l) - (int, m))`, with the payload's rows as `decide` reads them: `(int, l)`
/// taken and `(int, m)` refused.
fn cons_minus(l: &Type, m: &Type) -> Type {
    let pair = |r: &Type| Type::tuple(vec![Type::int(), r.clone()]);
    let t = Type::atom_with("cons", &(&pair(l) - &pair(m)));
    let f = t.p().atoms.names()[&std::sync::Arc::<str>::from("cons")]
        .payload
        .p()
        .tuples
        .lens
        .get(&2)
        .expect("pairs")
        .clone();
    let (taken, refused) = f.forced();
    assert_eq!((taken.len(), refused.len()), (1, 1), "{t:?}");
    t
}

/// A refused tail `M = #nil | #other((int, M))` links by another atom than the taken tail
/// `L = #nil | #cons((int, L))`. `M` is no list of `L`'s class, and its carrier has `L`'s
/// head; read as one, the refused row would cover the taken one and give `Empty`, though
/// `#cons((1, #cons((2, #nil))))` is a value: its tail is in `L` and not in `M`.
///
/// Also the same without a cycle: the taken tail `#cons((int, #nil))` and the refused tail
/// `#other((int, #nil))`, which, read as one link, are one node. Control (kernel14): the arm
/// `l != self.link` falling through makes `decide` answer `Empty` for both, and `is_empty`
/// answer `true` for both, though each holds the value above; the arm is needed.
#[test]
fn a_tail_that_links_by_another_atom_is_outside_the_class() {
    let w = cons_value(&[1, 2]);
    let lists = cons_minus(&list("nil", "cons"), &list("nil", "other"));
    let nil = Type::atom("nil");
    let chains = cons_minus(&step("cons", &nil), &step("other", &nil));
    for t in [lists, chains] {
        assert!(t.contains(&w), "{t:?}");
        assert!(decide(&t).is_none(), "{t:?}");
        assert!(!t.is_empty(), "{t:?}");
    }
}

/// A refused tail `#end` ends at another stop than the taken tail `#nil`. Read as one stop,
/// the refused row would cover the taken one and give `Empty`, though `#cons((1, #nil))` is
/// a value. Also one link deeper: the taken tail `#cons((int, #nil))` and the refused tail
/// `#cons((int, #end))`, which differ only at their ends. Control (kernel14): the arm
/// `Some(_)` at the end falling through makes `decide` answer `Empty` for both; the arm is
/// needed.
#[test]
fn a_tail_that_ends_at_another_stop_is_outside_the_class() {
    let (nil, end) = (Type::atom("nil"), Type::atom("end"));
    let ends = (cons_minus(&nil, &end), cons_value(&[1]));
    let deeper = (
        cons_minus(&step("cons", &nil), &step("cons", &end)),
        cons_value(&[1, 2]),
    );
    for (t, w) in [ends, deeper] {
        assert!(t.contains(&w), "{t:?}");
        assert!(decide(&t).is_none(), "{t:?}");
        assert!(!t.is_empty(), "{t:?}");
    }
}

/// `#link((int, next))`.
fn step(link: &str, next: &Type) -> Type {
    Type::atom_with(link, &Type::tuple(vec![Type::int(), next.clone()]))
}

/// The list value `#cons((n0, #cons((n1, … #nil))))`.
fn cons_value(items: &[i64]) -> crate::value::Value {
    use crate::value::Value;
    (items.iter().rev()).fold(Value::atom("nil"), |rest, &n| {
        Value::atom_with("cons", vec![Value::int(n.into()), rest])
    })
}

/// The type of the integers `ns`.
fn ints(ns: &[i64]) -> Type {
    Type::union_all(
        ns.iter()
            .map(|&n| Type::lit(&crate::value::Value::int(n.into())).expect("an integer literal")),
    )
}

/// The list `#cons((h0, #cons((h1, … #nil))))` of the heads `hs`.
fn chain(hs: &[Type]) -> Type {
    (hs.iter().rev()).fold(Type::atom("nil"), |rest, h| {
        Type::atom_with("cons", &Type::tuple(vec![h.clone(), rest]))
    })
}

/// Item TEST-kernel-unreached-paths-4 (kernel14, the 2-SAT with no model): the lists of three
/// bits less six refused lists, each of which forbids two bits together, written so that the
/// clauses read `x2 = x1`, `x3 = x2` and `x3 != x1`. No two clauses share an atom and the other
/// place (the merge U1 joins nothing) and none has one atom (U2 narrows nothing), so the
/// clauses reach the 2-SAT, which has no model, and `decide` answers `Empty`. Control (kernel14):
/// `return None` in place of the `Empty` at the 2-SAT's failure makes `decide` answer `None`,
/// and the test fails.
#[test]
fn clauses_with_no_model_give_empty() {
    let (b, zero, one) = (|| ints(&[0, 1]), || ints(&[0]), || ints(&[1]));
    let row = |h: [Type; 3]| {
        let [h0, h1, h2] = h;
        Type::tuple(vec![h0, chain(&[h1, h2])])
    };
    let mut payload = row([b(), b(), b()]);
    for r in [
        [one(), zero(), b()],
        [zero(), one(), b()],
        [b(), one(), zero()],
        [b(), zero(), one()],
        [one(), b(), one()],
        [zero(), b(), zero()],
    ] {
        payload = &payload - &row(r);
    }
    let t = Type::atom_with("cons", &payload);
    let f = t.p().atoms.names()[&std::sync::Arc::<str>::from("cons")]
        .payload
        .p()
        .tuples
        .lens
        .get(&2)
        .expect("pairs")
        .clone();
    let (taken, refused) = f.forced();
    assert_eq!((taken.len(), refused.len()), (1, 6), "{t:?}");
    assert!(matches!(decide(&t), Some(ChainPlan::Empty)), "{t:?}");
    assert!(t.is_empty(), "{t:?}");
}

/// Item TEST-kernel-unreached-paths-10 (kernel20, the kill in `read_on`): the lists
/// `[x1, x2, x3, 1]` of integers, less three rows that force `x1 = x2 = x3 = 2` (each refuses
/// `int \ 2` at one place and covers the others, so its clause is one atom), less the row
/// `(2, 2, 2, 3)`. That row's read stops at its third atom (places 1 to 3, each `int \ 2`)
/// with place 4 left, so its clause is cut. The unit narrowing (U2) sets places 1 to 3 to `2`,
/// which empties all three atoms, and `read_on` reads place 4: its set `1` is disjoint from
/// the row's head `3` there, a kill, so the row holds no list of the places and drops out. The
/// type holds `[2, 2, 2, 1]`. Control (kernel20): `false` in place of the kill's `return true`
/// leaves the cut row an empty clause, and `decide` answers `Empty` (a wrong answer: `is_empty`
/// then answers `true` too); the kill is needed.
#[test]
fn a_cut_row_read_on_to_a_kill_drops_out() {
    let int = Type::int;
    let not2 = || &Type::int() - &ints(&[2]);
    let row = |h: [Type; 4]| {
        let [h0, h1, h2, h3] = h;
        Type::tuple(vec![h0, chain(&[h1, h2, h3])])
    };
    let mut payload = row([int(), int(), int(), ints(&[1])]);
    for r in [
        [not2(), int(), int(), ints(&[1])],
        [int(), not2(), int(), ints(&[1])],
        [int(), int(), not2(), ints(&[1])],
        [ints(&[2]), ints(&[2]), ints(&[2]), ints(&[3])],
    ] {
        payload = &payload - &row(r);
    }
    let t = Type::atom_with("cons", &payload);
    let f = t.p().atoms.names()[&std::sync::Arc::<str>::from("cons")]
        .payload
        .p()
        .tuples
        .lens
        .get(&2)
        .expect("pairs")
        .clone();
    let (taken, refused) = f.forced();
    assert_eq!((taken.len(), refused.len()), (1, 4), "{t:?}");
    assert!(t.contains(&cons_value(&[2, 2, 2, 1])), "{t:?}");
    assert!(!matches!(decide(&t), Some(ChainPlan::Empty)), "{t:?}");
    assert!(!t.is_empty(), "{t:?}");
}

/// Item TEST-kernel-unreached-paths-4 (kernel14, the carrier with an empty head): the group
/// `L = #nil | #cons((H, L))`, `H = int & #z(L)` makes a carrier whose head `H` holds no
/// value, though `Type::tuple` keeps it: `H` names the group, so it stays a recursive node,
/// which lists its values only when unfolded (`H = int \ int` would be made plain and empty,
/// and the link would drop out). `#cons((0 | 1, L) - (0 | 1, #nil))` has no value, since `L`
/// holds `#nil` alone. At length 1 the refused row leaves an empty clause, but its tail is not
/// the carrier, so the answer there is not exact; the lengths past 1 are read by extending the
/// positive cells with the carrier's head, which is empty, so there is no longer list and
/// `decide` refuses (the search then answers). Control (kernel14): without the check of an
/// empty carrier head, the empty cell is pushed and `decide` panics picking a value of it
/// (`not empty`); the check is needed.
#[test]
fn a_carrier_with_an_empty_head_gives_no_longer_list() {
    use super::super::super::rec::{Def, Expr, Group};
    let body = Expr::Union(vec![
        Expr::Type(Type::atom("nil")),
        Expr::Atom(
            "cons".into(),
            vec![Expr::Ref(1, vec![]), Expr::Ref(0, vec![])],
        ),
    ]);
    let h = Expr::And(vec![
        Expr::Type(Type::int()),
        Expr::Atom("z".into(), vec![Expr::Ref(0, vec![])]),
    ]);
    let defs = vec![
        Def {
            name: "EmptyHeadL".into(),
            params: vec![],
            body,
        },
        Def {
            name: "EmptyHeadH".into(),
            params: vec![],
            body: h,
        },
    ];
    let l = Group::new(defs)
        .expect("a group")
        .instance(vec![])
        .remove(0);
    let b = ints(&[0, 1]);
    let pair = |r: &Type| Type::tuple(vec![b.clone(), r.clone()]);
    let t = Type::atom_with("cons", &(&pair(&l) - &pair(&Type::atom("nil"))));
    assert!(decide(&t).is_none(), "{t:?}");
    assert!(t.is_empty(), "{t:?}");
}

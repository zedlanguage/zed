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
#[test]
fn a_tail_that_links_by_another_atom_is_outside_the_class() {
    let t = cons_minus(&list("nil", "cons"), &list("nil", "other"));
    assert!(decide(&t).is_none());
    assert!(!t.is_empty());
}

/// A refused tail `#end` ends at another stop than the taken tail `#nil`. Read as one stop,
/// the refused row would cover the taken one and give `Empty`, though `#cons((1, #nil))` is
/// a value.
#[test]
fn a_tail_that_ends_at_another_stop_is_outside_the_class() {
    let t = cons_minus(&Type::atom("nil"), &Type::atom("end"));
    assert!(decide(&t).is_none());
    assert!(!t.is_empty());
}

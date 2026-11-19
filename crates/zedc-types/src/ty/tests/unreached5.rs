//! Tests of paths of `ty.rs` that the local suite did not reach (row
//! TEST-types-unreached-paths-5; the cases are listed in `crates/zedc-types/COMPLETENESS.md`).
//! Each gives an input that takes the path and the answer DESIGN.md or the function's own
//! contract gives for it.

use super::*;

fn int() -> Ty {
    Ty::carrier(Carrier::Int)
}

fn string() -> Ty {
    Ty::carrier(Carrier::Str)
}

/// `#name(items)`.
fn atom(name: &str, items: Vec<Ty>) -> Ty {
    Ty::atom_of(name, items, BTreeMap::new())
}

/// A tuple less the unknown is empty: the unknown holds every value ([`Ty::sub`]), so the
/// tuple's part near it, which is the unknown too, holds the tuple ([`Comparing::near_form`]).
#[test]
fn a_tuple_less_the_unknown_is_empty() {
    let t = Ty::tuple(vec![int(), int()]);
    let d = t.diff(&Ty::dynamic());
    assert!(d.is_empty(), "{d:?}");
}

/// A payload of one item is in no payload of two items: `#a(int) <: #a(T, int)` is false,
/// whatever `T` is bound to. The variable keeps the kernel from deciding it, so the shapes are
/// compared one by one ([`Comparing::payloads_in`]), and no shape of `#a(T, int)` has one item.
#[test]
fn a_payload_of_one_item_is_in_no_payload_of_two() {
    let t = atom("a", vec![int()]);
    let u = atom("a", vec![Ty::var("T".into()), int()]);
    assert!(!t.sub(&u, &mut Binds::new()));
}

/// Whether `a` and `b` hold the same values.
fn same(a: &Ty, b: &Ty) -> bool {
    a.subtype(b) && b.subtype(a)
}

/// The atoms `#a` with a payload of none of the shapes: a list of payload shapes that is empty,
/// which a rebuild keeps where it was empty already (`rebuild_ty`).
fn no_shape_of_a() -> Ty {
    let mut t = Ty::set(KType::atom_with("a", &KType::top()));
    t.payloads.insert("a".into(), Some(vec![]));
    t
}

/// The atoms `#a` with a payload of no shape hold no value, so they are within `#a(int)`, as
/// decided by the rests of their shapes ([`Comparing::payloads_by_rest`]) and, beside a
/// variable, shape by shape ([`Comparing::payloads_in`]): a list of no shapes leaves nothing to
/// hold.
#[test]
fn atoms_with_a_payload_of_no_shape_are_within_any_payload() {
    let t = no_shape_of_a();
    assert!(!t.contains(&Value::atom("a")));
    assert!(t.subtype(&atom("a", vec![int()])));
    let u = atom("a", vec![Ty::var("T".into()), int()]);
    let mut b = Binds::new();
    assert!(t.sub(&u, &mut b));
}

/// A tuple less a type that holds it only through its kind-wide part and a tuple with no
/// exact kernel type: `(int | String, int)` less every tuple but `(String, int)` and
/// `(int, int | #b(x: int))`. The tuple of `u` near the row has no exact kernel type (a
/// payload with fields), so the row is not cut by it, and the rest is the row less `u`'s
/// kernel type: `(String, int)` ([`Comparing::diff`]).
#[test]
fn a_tuple_less_a_kind_wide_part_keeps_the_rest_outside_the_kernel_type() {
    let t = Ty::tuple(vec![int().union(&string()), int()]);
    let field = BTreeMap::from([(Arc::from("x"), int())]);
    let mut u = Ty::tuple(vec![int(), int().union(&Ty::atom_of("b", vec![], field))]);
    u.set = &wide() - &KType::tuple(vec![KType::string(), KType::int()]);
    let d = t.diff(&u);
    let want = Ty::tuple(vec![string(), int()]);
    assert!(same(&d, &want), "{d}");
}

/// The same payload shape at two depths, `X | (X, 1)` for `X = #a(f1 | f2)`, is read once at
/// the spot of every depth ([`met_at`]): its functions, all of one domain, fit those of `Y |
/// (Y, 1)`, `Y = #a(g1 | g2)`, each `fi` within `gi`. Its four pairs of functions are no more
/// than the four functions; read twice on each side, the pairs would count sixteen against
/// eight functions, and the comparison would be refused ([`star_pairs`]).
#[test]
fn a_payload_shape_at_two_depths_is_read_once() {
    let f = |p: Ty, r: Ty| Ty::func(Arc::new(one_of(p, r)));
    let bool_ = Ty::carrier(Carrier::Bool);
    let one = Ty::lit(&Value::Int(1));
    let both = |a: Ty, b: Ty| {
        let x = atom("a", vec![a.union(&b)]);
        x.union(&Ty::tuple(vec![x.clone(), one.clone()]))
    };
    let t = both(f(int(), int()), f(int(), string()));
    let other = both(
        f(int(), int().union(&bool_)),
        f(int(), string().union(&bool_)),
    );
    assert!(t.subtype(&other), "{}", t.refused(&other));
}

/// A check whose other side holds a variable or the unknown is not decided by the forms of the
/// two sides ([`Forms::tie`]), so nothing in it is refused: `(#a(int), 1) <: _` holds, and
/// `(#a(int), 1) <: String | T` fails, decided.
#[test]
fn a_check_against_a_variable_or_the_unknown_is_not_tied() {
    let t = Ty::tuple(vec![atom("a", vec![int()]), Ty::lit(&Value::Int(1))]);
    assert!(t.subtype(&Ty::dynamic()));
    assert_eq!(t.refused(&Ty::dynamic()), "");
    let u = string().union(&Ty::var("T".into()));
    assert!(!t.subtype(&u));
    assert_eq!(t.refused(&u), "");
}

/// A refused check of the sets, beside a variable, names the recursive type it reads: `(Ints,
/// Ints) | T` within the pairs whose second list has an even or an odd length, which only the
/// two together hold, so the kernel refuses. The variable leaves `self` with no exact kernel
/// type, so the site is found in the sets ([`Ty::refused_in_group`]).
#[test]
fn a_refused_check_beside_a_variable_names_its_recursive_type() {
    use zed_kernel::types::rec::{Def, Expr, Group};
    KType::forget_emptiness();
    let def = |name: &str, body: Expr| Def {
        name: name.into(),
        params: vec![],
        body,
    };
    let nil = || Expr::Type(KType::atom("nil"));
    let cons = |next: usize| {
        Expr::Atom(
            "cons".into(),
            vec![Expr::Type(KType::int()), Expr::Ref(next, vec![])],
        )
    };
    let ints = Group::new(vec![def("Ints", Expr::Union(vec![nil(), cons(0)]))])
        .unwrap()
        .instance(vec![])
        .remove(0);
    let parity = Group::new(vec![
        def("Even", Expr::Union(vec![nil(), cons(1)])),
        def("Odd", cons(0)),
    ])
    .unwrap()
    .instance(vec![]);
    let pair = |a: &KType, b: &KType| KType::tuple(vec![a.clone(), b.clone()]);
    let a = Ty::set(pair(&ints, &ints)).union(&Ty::var("T".into()));
    let b = Ty::set(&pair(&ints, &parity[0]) | &pair(&ints, &parity[1]));
    assert!(a.exact_kernel().is_none());
    assert!(!a.subtype(&b));
    let why = a.refused(&b);
    assert!(
        why.contains("the check reads the recursive type `Ints`, defined by:"),
        "{why}"
    );
}

/// The meet of a type that holds the atoms `#a` with a payload not known and `#a(int)` is
/// `#a(int)`: the payloads of the side that lists them ([`Ty::meet_rest`]).
#[test]
fn the_meet_with_a_payload_not_known_takes_the_listed_payloads() {
    let a_any = Ty::set(KType::atom_with("a", &KType::top())).union(&atom("a", vec![int()]));
    assert_eq!(a_any.payloads.get("a"), Some(&None));
    let m = a_any.meet(&atom("a", vec![int()]));
    assert!(same(&m, &atom("a", vec![int()])), "{m}");
    assert!(!atom("a", vec![string()]).subtype(&m));
    // With no side listing them, the payloads stay not known.
    let m = a_any.meet(&Ty::set(KType::atom_with("a", &KType::top())));
    assert!(atom("a", vec![string()]).subtype(&m), "{m}");
}

/// A row, a payload shape and a family each met twice in a walk of the functions a type
/// holds are entered once, so each function is given once ([`Ty::each_held_fn`]).
#[test]
fn a_node_met_twice_in_the_walk_of_held_functions_is_entered_once() {
    let f = Arc::new(one_of(int(), int()));
    let one = Ty::lit(&Value::Int(1));
    let mut family = one_of(int(), int());
    family.arrows = vec![Arrow::exact(
        vec![Ty::set(KType::atom("k"))],
        Ty::func(f.clone()),
    )];
    family.data = true;
    let family = Ty::func(Arc::new(family));
    for x in [
        Ty::tuple(vec![Ty::func(f.clone()), one.clone()]),
        atom("a", vec![Ty::func(f.clone())]),
        family,
    ] {
        let t = Ty::tuple(vec![x.clone(), x]);
        let mut met = 0;
        t.each_held_fn(|s| {
            assert!(Arc::ptr_eq(s, &f));
            met += 1;
        });
        assert_eq!(met, 1, "{t}");
    }
}

/// A family value is in a type with a family of data and in no other: the empty family is in
/// `#k ->? int` and not in `int` or `int -> int` ([`Ty::contains`]).
#[test]
fn a_family_value_is_in_a_type_with_a_family() {
    let mut family = one_of(Ty::set(KType::atom("k")), int());
    family.data = true;
    let v = Value::Family(zed_kernel::Family::new());
    assert!(Ty::func(Arc::new(family)).contains(&v));
    assert!(!int().contains(&v));
    assert!(!Ty::func(Arc::new(one_of(int(), int()))).contains(&v));
}

/// One tuple read for 30 values in one check, `((x0,), …, (x29,))` within 30 copies of `((0,)
/// | … | (63,))`, is scanned for the first and filed once scanning costs more
/// ([`Pairs::tried`]); the filed tuples give the scan's answer.
#[test]
fn a_tuple_read_for_many_values_is_filed() {
    let lits = (0..64).map(|i| Ty::tuple(vec![Ty::lit(&Value::Int(i))]));
    let t = lits.fold(Ty::empty(), |a, b| a.union(&b));
    let wide = Ty::tuple(vec![Ty::tuple(vec![t]); 30]);
    let value = |last: i64| {
        let mut items: Vec<Value> = (0..29)
            .map(|i| Value::tuple(vec![Value::tuple(vec![Value::Int(i)])]))
            .collect();
        items.push(Value::tuple(vec![Value::tuple(vec![Value::Int(last)])]));
        Value::tuple(items)
    };
    assert!(wide.contains(&value(29)));
    assert!(!wide.contains(&value(99)));
}

/// `a` and `b` printed in one message, its definitions written: as each prints alone.
fn in_one_message(a: &Ty, b: &Ty) -> String {
    let _on = defs::collect();
    let mut text = format!("{a} and {b}");
    defs::finish(&mut text);
    text
}

/// A row and a function that one print of a message placed in its table, met below a part
/// in a later print of the same message, are written by the reference kept, not entered again
/// ([`Shared::of`]); a function of several arrows so written as a member of a union opens the
/// bounds clause its union closes ([`write_text`]). The message reads as the two types printed
/// alone.
#[test]
fn a_part_placed_by_an_earlier_print_of_a_message_is_written_by_its_reference() {
    let lit = |i: i64| Ty::lit(&Value::Int(i));
    let f = Ty::func(Arc::new(one_of(int(), int())));
    let r = Ty::tuple(vec![f.clone(), string()]);
    let pair = |x: &Ty, i: i64, j: i64| {
        Ty::tuple(vec![
            Ty::tuple(vec![x.clone(), r.clone(), lit(i)]),
            Ty::tuple(vec![x.clone(), r.clone(), lit(j)]),
        ])
    };
    let (a, b) = (pair(&f, 1, 2), pair(&f, 3, 4));
    let inner = "(int -> int, (int -> int, String),";
    assert_eq!(
        in_one_message(&a, &b),
        format!("({inner} 1), {inner} 2)) and ({inner} 3), {inner} 4))")
    );
    assert_eq!(in_one_message(&a, &b), format!("{a} and {b}"));
    let mut two = one_of(int(), int());
    two.arrows.push(Arrow::exact(vec![string()], string()));
    let g = Ty::func(Arc::new(two)).union(&string());
    let c = Ty::tuple(vec![
        Ty::tuple(vec![g.clone(), lit(1)]),
        Ty::tuple(vec![g.clone(), lit(2)]),
    ]);
    let d = Ty::tuple(vec![Ty::tuple(vec![g.clone(), lit(3)]), g.clone()]);
    let g = "String | (int -> int) & (String -> String)";
    assert_eq!(
        in_one_message(&c, &d),
        format!("(({g}, 1), ({g}, 2)) and (({g}, 3), {g})")
    );
}

/// `_` held 2^`depth` times, through rows (`(X, X)`) or payload shapes (`#b(X, X)`) each
/// holding the one below twice: `depth` nodes.
fn doubled(depth: usize, shapes: bool) -> Ty {
    (0..depth).fold(Ty::dynamic(), |x, _| match shapes {
        false => Ty::tuple(vec![x.clone(), x]),
        true => atom("b", vec![x.clone(), x]),
    })
}

/// The meet of two functions whose parameter types hold one row or payload shape in many
/// places reads each once ([`Domains::no_fn_type`], [`Domains::plain`]): read in each place,
/// a key holding `_` 2^48 times through 48 nodes would not be read in any time. The answers
/// are those of the meet of functions (DESIGN.md sec:type_language): no function takes
/// exactly the keys `K` and exactly `bool` (`Never`), and a function of `K ->? int` and `K
/// ->? K` gives no value at any key (`K ->? Never`).
#[test]
fn a_node_met_twice_in_the_domain_of_a_meet_is_read_once() {
    let x = || SParam {
        name: "x".into(),
        positional: true,
        default: None,
        range: None,
    };
    for shapes in [false, true] {
        let key = doubled(48, shapes);
        let f = |s: Sig| Ty::func(Arc::new(s));
        let m = f(one_of(key.clone(), int())).meet(&f(one_of(Ty::carrier(Carrier::Bool), int())));
        assert!(m.is_empty(), "{m}");
        let partial = |v: Ty| f(Sig::one_partial(vec![x()], vec![key.clone()], v));
        let m = partial(int()).meet(&partial(key.clone()));
        assert!(same(&m, &partial(Ty::empty())), "{m}");
    }
}

/// The digest of the names a call may write in a type tells a payload not known, which may
/// hold any field names, from a list of no payload shapes, which holds none
/// ([`NameDigests::ty`]).
#[test]
fn the_names_digest_tells_a_payload_not_known_from_no_payload() {
    let mut any = Ty::set(KType::atom_with("a", &KType::top()));
    any.payloads.insert("a".into(), None);
    let none = no_shape_of_a();
    let (x, y) = (
        NameDigests::default().ty(&any),
        NameDigests::default().ty(&none),
    );
    assert_ne!(x, y);
    assert_eq!(x, NameDigests::default().ty(&any.clone()));
}

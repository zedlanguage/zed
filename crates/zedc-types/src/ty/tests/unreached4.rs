//! Tests of paths of `ty.rs` that the local suite did not reach (row
//! TEST-types-unreached-paths-4; the cases are listed in `crates/zedc-types/COMPLETENESS.md`).
//! Each gives an input that takes the path and the answer DESIGN.md or the function's own
//! contract gives for it.

use super::*;

/// The function `int -> r`, as a type.
fn int_to(r: Ty) -> Ty {
    Ty::func(Arc::new(one_of(Ty::carrier(Carrier::Int), r)))
}

/// Functions nested `int -> int -> … -> r` 20,000 deep that differ only in the innermost
/// result are unequal, and equal where it is the same. A signature is compared field by field
/// with no digest of the whole first ([`Same::sig`]), so the comparison goes down to the
/// bottom, past the stack it may take, and the pair that differs is one pushed on the list
/// and read by [`Same::rest`]. Rows, by contrast, are first compared by digest, which covers
/// every field `==` compares, so tuples nested as deep with the same difference are found
/// unequal at the top, and below rows a pair put off differs only where two 64-bit digests
/// collide.
#[test]
fn deep_functions_that_differ_only_in_the_innermost_result_are_unequal() {
    let n = 20_000;
    let (int, bool) = (Ty::carrier(Carrier::Int), Ty::carrier(Carrier::Bool));
    let deep = |bottom: Ty| (0..n).fold(bottom, |t, _| int_to(t));
    let (a, b, c) = (deep(int.clone()), deep(bool), deep(int));
    assert!(a != b);
    assert!(b != a);
    assert!(a == c);
    let sig = |t: &Ty| Sig::clone(t.fns.only().unwrap());
    assert!(sig(&a) != sig(&b));
    assert!(sig(&a) == sig(&c));
}

/// A width too wide for a machine int ([`Width`]) hashes as nothing, so two equal wide widths,
/// built apart, hash alike and are one key of a set; a wide width and a machine one are two.
#[test]
fn equal_wide_widths_hash_alike() {
    use std::collections::HashSet;
    let wide = || {
        Width(
            Value::int_text("100000000000000000000000", 10)
                .unwrap()
                .unwrap(),
        )
    };
    assert!(matches!(wide().0, Value::Big(_)));
    let h = |w: &Width| {
        use std::hash::BuildHasher;
        std::hash::BuildHasherDefault::<std::collections::hash_map::DefaultHasher>::default()
            .hash_one(w)
    };
    assert_eq!(h(&wide()), h(&wide()));
    let set: HashSet<Width> = [wide(), wide()].into_iter().collect();
    assert_eq!(set.len(), 1);
    let set: HashSet<Width> = [wide(), Width(Value::Int(64))].into_iter().collect();
    assert_eq!(set.len(), 2);
}

/// [`errs_members`] gives the keys of an `#errs` only where each payload is a family [`errs_of`]
/// builds, `E ->? E`: one arrow of one parameter, the family alone in the one item, no field.
/// Any other payload, which a program cannot write for `#errs` but a type may still hold, gives
/// `None`: what it holds is not known.
#[test]
fn errs_members_reads_only_the_family_errs_of_builds() {
    let ab = Ty::set(KType::atom("a")).union(&Ty::set(KType::atom("b")));
    let built = errs_of(ab.clone());
    assert_eq!(errs_members(&built), Some(ab.clone()));
    // The payload of `built` with its one item changed by `item`, and fields `fields`.
    let with = |item: &dyn Fn(&Ty) -> Ty, fields: BTreeMap<Arc<str>, Ty>| {
        let mut t = built.clone();
        let shapes = t.payloads.get_mut("errs").unwrap().as_mut().unwrap();
        let s = &shapes[0];
        shapes[0] = Shape::new(vec![item(&s.items[0])], fields);
        t
    };
    let sig_of = |f: &Ty| Sig::clone(f.fns.only().unwrap());
    // Two arrows.
    let two_arrows = with(
        &|f| {
            let mut s = sig_of(f);
            s.arrows.push(s.arrows[0].clone());
            Ty::func(Arc::new(s))
        },
        BTreeMap::new(),
    );
    // One arrow of two parameters.
    let two_params = with(
        &|f| {
            let mut s = sig_of(f);
            let p = s.arrows[0].params[0].clone();
            s.arrows[0].params.push(p);
            s.params.push(s.params[0].clone());
            Ty::func(Arc::new(s))
        },
        BTreeMap::new(),
    );
    // A field beside the item.
    let field = with(&|f| f.clone(), [("k".into(), ab.clone())].into());
    // The family beside an int in the item.
    let beside = with(&|f| f.union(&Ty::carrier(Carrier::Int)), BTreeMap::new());
    // A function, not a family.
    let not_data = with(
        &|f| {
            let mut s = sig_of(f);
            s.data = false;
            Ty::func(Arc::new(s))
        },
        BTreeMap::new(),
    );
    for (t, what) in [
        (two_arrows, "two arrows"),
        (two_params, "two parameters"),
        (field, "a field"),
        (beside, "an int beside the family"),
        (not_data, "a function"),
    ] {
        assert_eq!(errs_members(&t), None, "{what}: {t}");
    }
    // Control: the same edits that leave the payload as built keep its keys.
    assert_eq!(
        errs_members(&with(&|f| f.clone(), BTreeMap::new())),
        Some(ab)
    );
}

/// [`Binds::remove`] gives what the variable was bound to and drops it from the digest and
/// from the index of the variables, whether or not the index was made; a variable not bound
/// gives `None` and changes nothing.
#[test]
fn removing_a_binding_drops_it_from_the_digest_and_the_index() {
    let (int, bool) = (Ty::carrier(Carrier::Int), Ty::carrier(Carrier::Bool));
    let only_b = || {
        let mut b = Binds::new();
        b.insert("B".into(), bool.clone());
        b
    };
    for made in [false, true] {
        let mut b = only_b();
        b.insert("A".into(), int.clone());
        if made {
            b.index();
        }
        assert_eq!(b.remove("A"), Some(int.clone()), "index made: {made}");
        assert_eq!(b.remove("C"), None, "index made: {made}");
        let want = only_b();
        assert!(b == want, "index made: {made}");
        assert_eq!(b.digest, want.digest, "index made: {made}");
        let (got, fresh) = (b.index(), BindKeys::of(&want.map));
        assert_eq!(got.names, fresh.names, "index made: {made}");
        assert_eq!(got.classes, fresh.classes, "index made: {made}");
        assert_eq!(got.ks, fresh.ks, "index made: {made}");
    }
}

/// [`Cx::unread`] puts back a function read as a variable with each variable of its reading
/// replaced: one read as its mask ([`Read::Mask`]) by the carriers of the mask, one read as a
/// type already bound ([`Read::Bound`]) by that type, so a message prints the function as the
/// comparison holds it.
#[test]
fn a_function_put_back_for_a_message_reads_its_masks_and_bound_variables() {
    let v = |x: &str| Ty::var(x.into());
    let (int, bool) = (Ty::carrier(Carrier::Int), Ty::carrier(Carrier::Bool));
    let m = Carrier::Int.bit() | Carrier::F64.bit();
    let s = Arc::new(one_of(v("U"), v("V")));
    let mut env = Env::new();
    env.insert("U".into(), Read::Mask(m));
    env.insert("V".into(), Read::Bound(bool.clone()));
    let mut cx = Cx::default();
    cx.fns.insert("F".into(), (s, env));
    let got = cx
        .unread(&Ty::tuple(vec![v("F"), int.clone()]))
        .into_owned();
    let f = Ty::func(Arc::new(one_of(Ty::of_mask(m), bool)));
    assert_eq!(got, Ty::tuple(vec![f, int]));
    // A union parameter is parenthesized, `(#x | #y) -> value` (DESIGN.md sec:values_morphisms).
    assert_eq!(got.to_string(), "((int | f64) -> bool, int)");
}

/// [`member`] on a lone rigid variable: of one carrier, held by class by the shapes of that
/// carrier and by value by none (a variable of one carrier is no one value); of no carrier,
/// holding no value, held anywhere; two of the same carrier as one, and of two carriers by
/// none.
#[test]
fn a_rigid_variable_is_a_member_where_its_one_carrier_is_filed() {
    // The `member` of `ty`, not the test helper of that name.
    use super::super::member;
    let v = |x: &str| Ty::var(x.into());
    let rigid: BTreeMap<Arc<str>, u8> = [
        ("I".into(), Carrier::Int.bit()),
        ("J".into(), Carrier::Int.bit()),
        ("B".into(), Carrier::Bool.bit()),
        ("N".into(), 0),
    ]
    .into();
    let at_int = |m: Member| matches!(m, Member::At(ShapeKey::Carrier(Carrier::Int)));
    assert!(at_int(member(&v("I"), false, &rigid)));
    assert!(matches!(member(&v("I"), true, &rigid), Member::Nowhere));
    assert!(matches!(member(&v("N"), false, &rigid), Member::Anywhere));
    assert!(matches!(member(&v("N"), true, &rigid), Member::Anywhere));
    assert!(at_int(member(&v("I").union(&v("J")), false, &rigid)));
    assert!(at_int(member(&v("I").union(&v("N")), false, &rigid)));
    let int_or_bool = v("I").union(&v("B"));
    assert!(matches!(
        member(&int_or_bool, false, &rigid),
        Member::Nowhere
    ));
}

/// [`some_value`] takes the zero of a rigid variable's first carrier, `""` for `str` and `0`
/// for `f32`; gives no value for the unknown; and builds a row shared at two places once,
/// the same value at both.
#[test]
fn some_value_of_rigid_strings_and_f32_shared_rows_and_the_unknown() {
    let mut cx = Cx::default();
    cx.rigid.insert("S".into(), Carrier::Str.bit());
    cx.rigid.insert("F".into(), Carrier::F32.bit());
    let of = |t: &Ty| some_value(t, &cx, None);
    assert_eq!(of(&Ty::var("S".into())), Ok(Value::str("")));
    assert_eq!(of(&Ty::var("F".into())), Ok(Value::float32(0.0)));
    assert_eq!(of(&Ty::dynamic()), Err(None));
    let x = Ty::tuple(vec![Ty::var("S".into()), Ty::carrier(Carrier::Int)]);
    let one = Value::tuple(vec![Value::str(""), Value::Int(0)]);
    assert_eq!(
        of(&Ty::tuple(vec![x.clone(), x])),
        Ok(Value::tuple(vec![one.clone(), one]))
    );
}

/// [`value_class`] of an `f32` is the `f32` carrier, the class of a component of `f32` values.
#[test]
fn the_class_of_an_f32_value_is_its_carrier() {
    assert!(value_class(&Value::float32(0.5)) == Some(ShapeKey::Carrier(Carrier::F32)));
    assert!(value_class(&Value::float(0.5)) == Some(ShapeKey::Carrier(Carrier::F64)));
}

/// A part of a shape's rest whose item lists no value ([`Rest::push`]) is kept as a part, not
/// as a shape, and its verdict is empty, so a rest of such parts is held ([`Rest::held`]); a
/// part with a value is a shape and is not held.
#[test]
fn a_rest_of_parts_that_list_no_value_is_held() {
    let mut rest = Rest::default();
    rest.push(vec![(Ty::empty(), KType::empty())]);
    rest.push(vec![
        (Ty::empty(), KType::empty()),
        (Ty::carrier(Carrier::Int), KType::int()),
    ]);
    assert!(rest.shapes.is_empty());
    assert_eq!(rest.parts.len(), 2);
    assert!(matches!(rest.held(), Held::Yes));
    rest.push(vec![(Ty::carrier(Carrier::Int), KType::int())]);
    assert_eq!(rest.shapes.len(), 1);
    assert!(matches!(rest.held(), Held::No));
}

/// [`Choices::apart`], the reason a message gives for shapes of one bucket that the search
/// could not tell apart, names a place past the items as the field there, and says, for the
/// bucket of a member held anywhere (`None`), that each of the two has a component any of
/// them may hold there, and, for a bucket of one key, that they agree with both.
#[test]
fn the_reason_shapes_are_not_told_apart_names_fields_and_the_bucket_held_anywhere() {
    let int = Some((ShapeKey::Carrier(Carrier::Int), None));
    let bool = Some((ShapeKey::Carrier(Carrier::Bool), None));
    let shapes = [
        vec![int.clone(), bool.clone()],
        vec![int.clone(), bool.clone()],
    ];
    let choices = Choices::new(shapes.iter().enumerate().map(|(i, k)| (i, &k[..])));
    let k: Arc<str> = "k".into();
    assert_eq!(
        choices.apart(0, &None, 1, &[&k]),
        "are told apart only at component 1, field k, where each of the two has a component \
         that any of them may hold"
    );
    let key = Some(vec![
        ShapeKey::Carrier(Carrier::Int),
        ShapeKey::Carrier(Carrier::Bool),
    ]);
    assert_eq!(
        choices.apart(0, &key, 2, &[]),
        "are told apart only at component 1, component 2, where they agree with both"
    );
}

/// The shapes of a bucket in the order [`Shapes`] gives them.
fn listed(lists: &[Shapes]) -> Vec<Vec<usize>> {
    let each = |l: &Shapes| {
        let mut out = Vec::new();
        let mut at = l.after(None);
        while let Some((r, n)) = at {
            out.push(r);
            at = l.next(r, n);
        }
        out
    };
    lists.iter().map(each).collect()
}

/// The lists [`Bound::lists`] gives a member, for a bucket of the shapes 0 and 1 where shape
/// 0's first component is the variable `v`, pinned under `w` ([`Bound::pin`]): the shapes
/// pinned nowhere, `[1]`, then those of each node whose path the member allows. A component
/// with no variable keyed (here none at all) allows the node under any variable
/// ([`Allow::Any`]), as one whose first keyed variable is `w` allows it ([`Allow::One`]); one
/// holding an `int`, or another variable, allows none. With nothing pinned, every shape is
/// free.
#[test]
fn a_member_with_no_keyed_variable_reads_the_shapes_pinned_under_any_variable() {
    let bucket = [0, 1];
    let mut exact = ExactVars::new();
    exact.insert("v".into(), vec![(0, 0)]);
    let (binds, cx) = (Binds::new(), Cx::default());
    let free = Bound::default();
    assert_eq!(
        listed(&free.lists(&bucket, &[&Ty::empty()], &binds, &cx)),
        [vec![0, 1]]
    );
    let mut pins = Bound::default();
    pins.pin(&bucket, &exact, &[("v".into(), "w".into())]);
    let of = |x: Ty| listed(&pins.lists(&bucket, &[&x], &binds, &cx));
    assert_eq!(of(Ty::empty()), [vec![1], vec![0]]);
    assert_eq!(of(Ty::var("w".into())), [vec![1], vec![0]]);
    assert_eq!(of(Ty::var("z".into())), [vec![1]]);
    assert_eq!(of(Ty::carrier(Carrier::Int)), [vec![1]]);
    // Shape 0 holding `v` at component 0 and `u` at component 1, pinned under `w` and `x`:
    // the edge to its node is labeled with the second step, which a member allows if its
    // component 1 has no keyed variable, or `x` first, and not if it holds an `int`.
    exact.insert("u".into(), vec![(0, 1)]);
    let mut two = Bound::default();
    two.pin(
        &bucket,
        &exact,
        &[("v".into(), "w".into()), ("u".into(), "x".into())],
    );
    let of2 = |x: Ty, y: Ty| listed(&two.lists(&bucket, &[&x, &y], &binds, &cx));
    assert_eq!(of2(Ty::empty(), Ty::empty()), [vec![1], vec![0]]);
    assert_eq!(
        of2(Ty::var("w".into()), Ty::var("x".into())),
        [vec![1], vec![0]]
    );
    assert_eq!(of2(Ty::empty(), Ty::carrier(Carrier::Int)), [vec![1]]);
}

/// The pair of signatures of `a_signature_the_pins_do_not_separate_is_still_refused`, which
/// the comparison refuses.
fn refused_pair() -> (Arc<Sig>, Arc<Sig>) {
    let v = |x: &str| Ty::var(x.into());
    let (int, bool) = (Ty::carrier(Carrier::Int), Ty::carrier(Carrier::Bool));
    let make = |t: &str, u: &str, w: &str, order: [usize; 5]| {
        let shapes = [
            vec![bool.clone(), v(t)],
            vec![v(t).union(&int)],
            vec![v(t).union(&int), v(t)],
            vec![v(u)],
            vec![v(w)],
        ];
        let members: Vec<Vec<Ty>> = order.iter().map(|&i| shapes[i].clone()).collect();
        Arc::new(random_shapes_sig(
            &[t, u, w],
            &members,
            &[vec![v(t)], vec![v(t), v(t)]],
        ))
    };
    (
        make("T", "U", "V", [0, 1, 2, 3, 4]),
        make("X", "W", "Y", [1, 2, 3, 0, 4]),
    )
}

/// A verdict kept with its refusal is given again with that refusal: by
/// [`Comparing::fits_written`] and [`Comparing::fits_alone`], each asked twice of a pair the
/// comparison refuses. Each answer is no, refused, for the same reason; with the refusal
/// dropped the second time, the kept no would read as a proof that the function does not fit.
#[test]
fn a_kept_verdict_on_functions_is_given_again_with_its_refusal() {
    let (s, q) = refused_pair();
    let mut cx = Cx::default();
    let got = comparing!(&mut cx, |c| async {
        let mut out = Vec::new();
        for _ in 0..2 {
            let ok = c.fits_written(&s, &q).await;
            out.push((ok, c.cx.borrow_mut().unchosen.take()));
        }
        for _ in 0..2 {
            let ok = c.fits_alone(&s, q.clone()).await;
            out.push((ok, c.cx.borrow_mut().unchosen.take()));
        }
        out
    });
    let why = got[0].1.clone();
    assert!(why.is_some(), "not refused: {got:?}");
    for (i, g) in got.iter().enumerate() {
        assert_eq!(g, &(false, why.clone()), "answer {i}");
    }
}

/// [`Comparing::kept_rows_in`] on rows read as kept ([`Cx::kept_read`]): a no that was
/// refused is kept with its refusal and given again with it; and where the components give
/// no and a component of `t` is empty though it lists a value ([`Ty::is_empty`]), it gives
/// nothing and keeps nothing, so the comparison goes on as before.
#[test]
fn a_kept_verdict_on_rows_is_given_again_with_its_refusal() {
    let (s, q) = refused_pair();
    let t = Ty::tuple(vec![Ty::func(q)]);
    let other = Ty::tuple(vec![Ty::func(s)]);
    // `type E = (E,)`, which holds no value, as the kernel's search proves, and lists one.
    use zed_kernel::types::rec::{Def, Expr, Group};
    let def = Def {
        name: "E".into(),
        params: vec![],
        body: Expr::Tuple(vec![Expr::Ref(0, vec![])]),
    };
    let rec = Group::new(vec![def]).unwrap().instance(vec![]).remove(0);
    let empty = Ty::set(rec);
    assert!(empty.is_empty() && !empty.lists_nothing());
    let e = Ty::tuple(vec![empty, Ty::carrier(Carrier::Int)]);
    let bools = Ty::tuple(vec![Ty::carrier(Carrier::Bool); 2]);
    let mut cx = Cx::default();
    for r in [&t, &other, &e, &bools] {
        cx.kept_read.insert(r.tuples[0].node());
    }
    let (got, gone) = comparing!(&mut cx, |c| async {
        let mut out = Vec::new();
        for _ in 0..2 {
            let ok = c.kept_rows_in(&t, &other, &Binds::new()).await;
            out.push((ok, c.cx.borrow_mut().unchosen.take()));
        }
        let gone = c.kept_rows_in(&e, &bools, &Binds::new()).await;
        (out, gone)
    });
    let why = got[0].1.clone();
    assert!(why.is_some(), "not refused: {got:?}");
    assert_eq!(got, [(Some(false), why.clone()), (Some(false), why)]);
    assert_eq!(gone, None);
    let key = (e.tuples[0].node(), bools.tuples[0].node());
    assert!(!cx.kept_compared.contains_key(&key));
}

/// [`FoldForm::fold_name`] names each fold as it is written, `.sum` included, which the
/// full suite's coverage did not reach.
#[test]
fn each_fold_is_named_as_it_is_written() {
    let names = [
        FoldForm::Infix,
        FoldForm::Reduce,
        FoldForm::Sum,
        FoldForm::Scan,
    ]
    .map(FoldForm::fold_name);
    assert_eq!(
        names,
        [
            "a fold `><`",
            "a fold `.reduce`",
            "a fold `.sum`",
            "a scan `.scan`"
        ]
    );
}

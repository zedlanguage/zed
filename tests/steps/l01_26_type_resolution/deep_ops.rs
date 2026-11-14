//! The operations on a type nested as deep as the program keep their own stack (T2-ty). The
//! tests here run each on types a few levels deep, on the default stack, and check what it
//! gives; the benchmarks in `bench::deep_ops` run the same checks on a type
//! `bench::deep_ops::DEEP` levels deep on a stack as small a level as 2 MiB at 100,000 levels,
//! and measure that each costs time linear in the depth (author P178: a test that needs an
//! unusual depth or stack is a benchmark).
//!
//! `Debug` of a type or signature, [`Ty::meet`], [`Ty::meets`] and [`Ty::contains`] recursed
//! once a level and overflowed that stack; the others passed before and are kept so that none
//! comes back. A meet, a `meets` and a `contains` walk a pair of nodes shared at many places
//! once, so a tuple with `2^n` paths through `n` nodes costs `O(n)`.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::Value;
use zed_kernel::types::Type;
use zedc::check::ty::{self, Binds, SParam, Shape, Sig, Ty, Vars};

pub(super) fn z() -> Ty {
    Ty::set(Type::atom("z"))
}

pub(super) fn y() -> Ty {
    Ty::set(Type::atom("y"))
}

/// The atom `#a` with a payload of `items` and the field `f`.
fn atom(items: Vec<Ty>, f: Ty) -> Ty {
    let mut t = Ty::set(Type::atom_with("a", &Type::top()));
    let shape = Shape::new(items, [("f".into(), f)].into());
    t.payloads.insert("a".into(), Some(vec![shape]));
    t
}

/// The signature `(x: param) -> result`.
pub(super) fn sig(param: Ty, result: Ty) -> Sig {
    let x = SParam {
        name: "x".into(),
        positional: true,
        default: None,
    };
    let own: BTreeSet<Arc<str>> = param.vars.clone();
    let mut s = Sig::one(vec![x], vec![param], result);
    s.own = own;
    s
}

fn func(param: Ty, result: Ty) -> Ty {
    Ty::func(Arc::new(sig(param, result)))
}

/// A type `n` levels deep with `bottom` at the bottom, a tuple, an atom's payload and a
/// function's result in turn, each level built anew.
pub(super) fn levels(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, k| match k % 3 {
        0 => Ty::tuple(vec![t, z()]),
        1 => atom(vec![z(), t], z()),
        _ => func(z(), t),
    })
}

/// [`levels`] with no function: a tuple and an atom's payload in turn.
fn data(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, k| match k % 2 {
        0 => Ty::tuple(vec![t, z()]),
        _ => atom(vec![z(), t], z()),
    })
}

/// `((… (bottom, #z) …, #z), #z)`, `n` tuples deep, each built anew.
pub(super) fn tuples(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, _| Ty::tuple(vec![t, z()]))
}

/// A tuple `n` levels deep holding a variable at each level, in a tuple and a payload in turn.
fn open(n: usize) -> Ty {
    (0..n).fold(Ty::var("T".into()), |t, k| match k % 2 {
        0 => Ty::tuple(vec![t, Ty::var(format!("V{k}").into())]),
        _ => atom(vec![t], Ty::var("T".into())),
    })
}

/// The value `((… (#bottom, #z) …, #z), #z)`, `n` tuples deep.
pub(super) fn value(n: usize, bottom: &str) -> Value {
    (0..n).fold(Value::atom(bottom), |v, _| {
        Value::tuple(vec![v, Value::atom("z")])
    })
}

/// `(t, t)` for `t` the same `n - 1` deep, `bottom` at the bottom: `2^n` paths through `n`
/// tuples.
pub(super) fn shared(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, _| Ty::tuple(vec![t.clone(), t]))
}

/// `#a(t, t)` (field `f` the atom `#z`) for `t` the same `n - 1` deep, the variable `v` at
/// the bottom: `2^n` paths through `n` payloads, each shared by both places that hold it.
pub(super) fn shared_payloads(n: usize, v: &str) -> Ty {
    (0..n).fold(Ty::var(v.into()), |t, _| atom(vec![t.clone(), t], z()))
}

/// The value of [`shared`] with `#z` at the bottom, its tuples shared too.
pub(super) fn shared_value(n: usize) -> Value {
    (0..n).fold(Value::atom("z"), |v, _| Value::tuple(vec![v.clone(), v]))
}

/// Depths of a few levels that leave the same remainder by 6 as `bench::deep_ops::DEEP`, so the
/// outermost level of [`levels`] and the parity of the depth are those of the benchmarks.
const SMALL: [usize; 3] = [4, 10, 16];

/// Clones, hashes and drops [`levels`] `n` deep.
pub(super) fn clone_hash_and_drop(n: usize) {
    let t = levels(n, z());
    let u = t.clone();
    use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
    let h = BuildHasherDefault::<DefaultHasher>::default();
    assert_eq!(h.hash_one(&t), h.hash_one(&u), "{n} deep");
    drop(t);
    drop(u);
}

/// Writes types and a signature `n` deep with `Display` and `Debug`: the derived `Debug` of a
/// type and a signature recursed once a level.
pub(super) fn display_and_debug(n: usize) {
    let t = levels(n, z());
    assert!(t.to_string().len() > n, "{n} deep");
    assert!(format!("{t:?}").len() > n, "{n} deep");
    assert!(format!("{t:#?}").len() > n, "{n} deep");
    let s = sig(levels(n, z()), data(n, z()));
    assert!(format!("{s:?}").len() > n, "{n} deep");
    assert!(
        format!("{:?}", tuples(n, z()).tuples[0]).len() > n,
        "{n} deep"
    );
}

/// The union of equal and of different [`levels`] `n` deep, `n` at least 1 and leaving 4 by 6,
/// so the outermost level is a tuple.
pub(super) fn union(n: usize) {
    let (a, b, c) = (levels(n, z()), levels(n, z()), levels(n, y()));
    assert_eq!(
        a.union(&b).fns.len() + a.union(&b).tuples.len(),
        1,
        "{n} deep"
    );
    assert_eq!(
        a.union(&c).fns.len() + a.union(&c).tuples.len(),
        2,
        "{n} deep"
    );
    assert_eq!(Ty::union_all([&a, &b, &c]).tuples.len(), 2, "{n} deep");
}

/// Meet, `meets` and `contains` of tuples `n` deep, `n` at least 1.
pub(super) fn meet_meets_and_contains(n: usize) {
    let (a, b, c) = (tuples(n, z()), tuples(n, z()), tuples(n, y()));
    assert_eq!(a.meet(&b), a, "{n} deep");
    assert!(a.meet(&c).is_empty(), "{n} deep");
    assert!(a.meets(&b), "{n} deep");
    assert!(!a.meets(&c), "{n} deep");
    let v = value(n, "z");
    assert!(a.contains(&v), "{n} deep");
    assert!(!c.contains(&v), "{n} deep");
}

/// A subtype verdict between equal [`levels`] `n` deep.
pub(super) fn subtype_of_types(n: usize) {
    let (a, b) = (levels(n, z()), levels(n, z()));
    assert!(a.subtype(&b), "{n} deep");
}

/// Subtype verdicts and the refusal between [`data`] and tuples `n` deep.
pub(super) fn subtype_of_data(n: usize) {
    let (a, c) = (data(n, z()), data(n, y()));
    assert!(!a.subtype(&c), "{n} deep");
    assert!(!a.refused(&c).contains("undecided"), "{n} deep");
    let (a, b, c) = (tuples(n, z()), tuples(n, z()), tuples(n, y()));
    assert!(a.subtype(&b), "{n} deep");
    assert!(!a.subtype(&c), "{n} deep");
    let _ = a.verdict(&c);
}

/// The difference of tuples and of [`levels`] `n` deep, `n` at least 1.
pub(super) fn diff(n: usize) {
    let (a, b, c) = (tuples(n, z()), tuples(n, z()), tuples(n, y()));
    assert!(a.diff(&b).is_empty(), "{n} deep");
    assert_eq!(a.diff(&c), a, "{n} deep");
    let (a, b) = (levels(n, z()), levels(n, z()));
    let _ = a.diff(&b);
}

/// The kernel and the other views of tuples `n` deep.
pub(super) fn kernel(n: usize) {
    let a = tuples(n, z());
    assert!(a.kernel().is_some(), "{n} deep");
    assert!(a.exact_kernel().is_some(), "{n} deep");
    assert!(a.exact_data().is_some(), "{n} deep");
    assert!(a.held_wide().is_none(), "{n} deep");
    let _ = a.pieces();
    let _ = a.without_loose();
    let _ = a.without(&Type::atom("z"));
}

/// The variables of [`open`] `n` deep, gathered and bound.
pub(super) fn variables(n: usize) {
    let t = open(n);
    let mut out = Vars::default();
    t.vars_in(&mut out);
    assert_eq!(out.order.len(), n.div_ceil(2) + 1, "{n} deep");
    let mut out = Vars::default();
    t.vars_outside(&mut out);
    assert_eq!(out.order.len(), n.div_ceil(2) + 1, "{n} deep");
    let _ = t.var_facts();
    let mut b = Binds::new();
    assert!(t.sub(&open(n), &mut b), "{n} deep");
}

/// The operations on signatures of [`levels`] `n` deep.
pub(super) fn signatures(n: usize) {
    let s = sig(levels(n, z()), levels(n, z()));
    let q = sig(levels(n, z()), levels(n, z()));
    assert!(ty::fits_sig(&s, &q), "{n} deep");
    let _ = s.expand();
    let _ = s.int_params();
    assert!(s.same_kinds(&q), "{n} deep");
    let _ = s.digest();
    let _ = s.facts();
    let _ = s.unheld();
    let mut t = s.clone();
    t.note_held();
}

/// A signature taking [`shared_payloads`] `n` deep with the variable `v` at the bottom,
/// returning `v`, its own variable, bounded to `bound`.
pub(super) fn shared_payload_sig(n: usize, v: &str, bound: &str) -> Sig {
    let text = format!("(x: T) -> T for T in {bound}");
    let read = zedc::check::read::parse_type(&text).unwrap_or_else(|e| panic!("{e}"));
    let mut s = sig(shared_payloads(n, v), Ty::var(v.into()));
    s.own = [Arc::from(v)].into();
    s.bounds = [(Arc::from(v), read.fns[0].bounds["T"])].into();
    s.note_held();
    s
}

/// `fits_sig` and `why_unfit` of signatures of tuples `n` deep that differ at the bottom, `n`
/// at least 1.
pub(super) fn signatures_that_differ(n: usize) {
    let s = sig(tuples(n, z()), tuples(n, z()));
    let r = sig(tuples(n, y()), tuples(n, z()));
    assert!(!ty::fits_sig(&s, &r), "{n} deep");
    let _ = ty::why_unfit(&s, &r);
}

#[test]
fn the_operations_on_a_type_a_few_levels_deep_are_as_built() {
    // Small instances of the benchmarks in `bench::deep_ops` that run each operation on a type
    // `bench::deep_ops::DEEP` levels deep on a shallow stack.
    for n in SMALL {
        clone_hash_and_drop(n);
        display_and_debug(n);
        union(n);
        meet_meets_and_contains(n);
        subtype_of_types(n);
        subtype_of_data(n);
        diff(n);
        kernel(n);
        variables(n);
        signatures(n);
        signatures_that_differ(n);
    }
}

#[test]
fn debug_writes_what_a_derived_debug_writes() {
    // The parts are in the order and form of the derived `Debug` it replaced: the text of
    // 33 types and signatures, with needs of every kind, was compared with the derived text
    // and was the same (T2-ty).
    let t = atom(vec![tuples(1, z())], open(1));
    let text = format!("{t:?}");
    assert!(text.starts_with("Ty { set: "), "{text}");
    for part in [
        ", tuples: [], fns: [], vars: {}, dynamic: false, family: ",
        ", payloads: {\"a\": Some([Shape { items: [Ty { set: ",
        ", tuples: [[Ty { set: ",
        "payloads: {} }], fields: {\"f\": Ty { set: ",
        "vars: {\"V0\"}",
    ] {
        assert!(text.contains(part), "{part} in {text}");
    }
    assert!(text.ends_with("payloads: {} }} }])} }"), "{text}");
    assert_eq!(format!("{t:#?}"), text, "one line for {{:#?}} too");
    let s = format!("{:?}", sig(z(), z()));
    assert!(s.starts_with("Sig { params: [SParam { name: \"x\""), "{s}");
    assert!(s.contains("arrows: [Arrow { params: [Ty { set: "), "{s}");
    assert!(
        s.ends_with(", needs: [], own: {}, held: {}, named: 0, facts: _ }"),
        "{s}"
    );
}

#[test]
fn a_bounded_variable_in_shared_payloads_is_read_as_elsewhere() {
    // Each side's variable is read under a new name in every payload that holds it
    // (FAIL-types-payload-vars-unread), each shared payload once.
    for n in 1..6 {
        let s = shared_payload_sig(n, "B", "int | f64");
        for (bound, fits) in [("int | f64", true), ("int", true), ("int | String", false)] {
            let q = shared_payload_sig(n, "C", bound);
            assert_eq!(ty::fits_sig(&s, &q), fits, "{n} deep, C in {bound}");
        }
        let same = shared_payload_sig(n, "B", "int");
        assert!(ty::fits_sig(&s, &same), "{n} deep, the same name");
    }
}

#[test]
fn meet_meets_and_contains_of_shallow_tuples_are_as_built() {
    for n in 0..7 {
        let (a, c) = (tuples(n, z()), tuples(n, y()));
        let both = a.union(&c);
        assert_eq!(a.meet(&tuples(n, z())), a, "{n} deep");
        assert_eq!(both.meet(&a), a, "{n} deep");
        assert_eq!(a.meet(&both), a, "{n} deep");
        assert!(a.meets(&both) && both.meets(&c), "{n} deep");
        assert!(both.contains(&value(n, "y")), "{n} deep");
        assert!(!a.contains(&value(n, "x")), "{n} deep");
        if n > 0 {
            assert!(a.meet(&c).is_empty(), "{n} deep");
            assert!(!a.meets(&c) && !c.meets(&a), "{n} deep");
            assert!(!a.contains(&value(n, "y")), "{n} deep");
            assert!(!a.contains(&value(n - 1, "z")), "{n} deep");
        }
        // Small instances of the benchmarks `bench::deep_ops::meet_of_shared_tuples_…`,
        // `meets_of_shared_tuples_…` and `contains_of_a_shared_value_…`, each in its order.
        let (s, t) = (shared(n, z()), shared(n, Ty::union(&z(), &y())));
        assert_eq!(t.meet(&s), s, "{n} deep");
        assert_eq!(s.meet(&t), s, "{n} deep");
        assert!(t.meets(&s) && t.contains(&shared_value(n)), "{n} deep");
        assert!(s.contains(&shared_value(n)), "{n} deep");
        assert!(!s.meets(&shared(n, y())), "{n} deep");
    }
    // A variable meets every value and holds every value.
    let v = tuples(3, Ty::var("T".into()));
    assert!(v.meets(&tuples(3, y())));
    assert!(v.contains(&value(3, "q")));
    assert!(!v.contains(&value(2, "q")));
}

/// A type `n` levels deep in which the level below stands, in turn, as a function's parameter,
/// in a union in a function's result, as a tuple component and as a member of a union: the
/// places where a function type needs or does not need parentheses (PRINT-fn-parens).
pub(super) fn functions(n: usize) -> Ty {
    (0..n).fold(z(), |t, k| match k % 4 {
        0 => func(t, z()),
        1 => func(z(), t.union(&y())),
        2 => Ty::tuple(vec![t, z()]),
        _ => t.union(&y()),
    })
}

#[test]
fn a_type_with_a_function_at_every_place_prints_and_reads_back() {
    // A small instance of the benchmark
    // `bench::deep_ops::printing_a_type_with_a_function_at_every_place_takes_linear_time_in_the_depth`:
    // the printer decides each part's parentheses from where it stands, and what it writes
    // reads back as the type it printed.
    let printed = functions(5).to_string();
    assert_eq!(printed, "(#z -> (#z -> #z) | #y, #z) | #y -> #z");
    let again = zedc::check::read::parse_type(&printed).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(again.to_string(), printed);
    assert!(again.subtype(&functions(5)) && functions(5).subtype(&again));
}

/// `#a(t, t)` (field `f` the atom `#z`) for `t` the same `n - 1` deep, `bottom` at the bottom.
fn shared_payloads_of(n: usize, bottom: Ty) -> Ty {
    (0..n).fold(bottom, |t, _| atom(vec![t.clone(), t], z()))
}

#[test]
fn shared_payloads_with_a_variable_are_compared_once_a_level() {
    // Small instances of `bench::deep_ops::sub_of_shared_payloads_takes_linear_time`: each
    // pair of shared rows or payloads met again under the same bindings is not compared again
    // (FAIL-types-sub-shared-payloads), and the verdict and bindings are those of a comparison
    // of every path.
    let var = |v: &str| Ty::var(v.into());
    for n in 1..7 {
        for (what, a, b, bottom) in [
            (
                "payloads",
                shared_payloads(n, "B"),
                shared_payloads(n, "C"),
                var("B"),
            ),
            ("tuples", shared(n, var("B")), shared(n, var("C")), var("B")),
            (
                "payloads",
                shared_payloads_of(n, z()),
                shared_payloads(n, "C"),
                z(),
            ),
            ("tuples", shared(n, z()), shared(n, var("C")), z()),
        ] {
            let mut binds = Binds::new();
            assert!(a.sub(&b, &mut binds), "{what} {n} deep, {bottom}");
            assert_eq!(
                binds,
                [("C".into(), bottom.clone())].into(),
                "{what} {n} deep"
            );
        }
        let on_y = shared_payloads_of(n, y());
        assert!(
            !shared_payloads(n, "B").sub(&on_y, &mut Binds::new()),
            "{n} deep"
        );
        assert!(
            !shared(n, var("B")).sub(&shared(n, y()), &mut Binds::new()),
            "{n} deep"
        );
        // Two shared payloads, one on `#z` and one on `#y`, within the same on `C` twice: `C`
        // is bound to both. Within the one on `C` and the one on `#z`, the second fails.
        let one = Ty::tuple(vec![shared_payloads_of(n, z()), shared_payloads_of(n, y())]);
        let both = Ty::tuple(vec![shared_payloads(n, "C"), shared_payloads(n, "C")]);
        let mut binds = Binds::new();
        assert!(one.sub(&both, &mut binds), "{n} deep");
        assert_eq!(binds, [("C".into(), z().union(&y()))].into(), "{n} deep");
        let on_z = Ty::tuple(vec![shared_payloads(n, "C"), shared_payloads_of(n, z())]);
        assert!(!one.sub(&on_z, &mut Binds::new()), "{n} deep");
    }
}

#[test]
fn a_shared_pair_met_again_under_other_bindings_keeps_them() {
    // The shared pair `(#z,)` in `(E,)` is met first with `C` bound and then with `C` and `D`
    // bound. Its answer kept by the pair alone, and not by the bindings in force too, would
    // give the second time the bindings of the first, with `D` dropped.
    let x = Ty::set(Type::atom("x"));
    let var = |v: &str| Ty::var(v.into());
    let (r, q) = (Ty::tuple(vec![z()]), Ty::tuple(vec![var("E")]));
    let pair = |a: Ty, b: Ty| Ty::tuple(vec![a, b]);
    let left = pair(pair(x.clone(), r.clone()), pair(y(), r.clone()));
    let right = pair(pair(var("C"), q.clone()), pair(var("D"), q.clone()));
    let mut binds = Binds::new();
    assert!(left.sub(&right, &mut binds));
    let all: Binds = [
        ("C".into(), x.clone()),
        ("D".into(), y()),
        ("E".into(), z()),
    ]
    .into();
    assert_eq!(binds, all);
    // The same in payloads.
    let (r, q) = (atom(vec![z()], z()), atom(vec![var("E")], z()));
    let left = atom(
        vec![
            atom(vec![x.clone(), r.clone()], z()),
            atom(vec![y(), r], z()),
        ],
        z(),
    );
    let right = atom(
        vec![
            atom(vec![var("C"), q.clone()], z()),
            atom(vec![var("D"), q], z()),
        ],
        z(),
    );
    let mut binds = Binds::new();
    assert!(left.sub(&right, &mut binds));
    assert_eq!(binds, all);
}

/// A comparison of rows made after the comparison is refused is neither read from nor kept in
/// the memo of rows (`Cx::compared`): `search` then answers false at once, so that answer is the
/// refusal's and not the rows'. Here the first shape of `g`'s parameter, `(B, bool)`, is
/// refused, as `B`'s bucket cannot choose between `(int, int)` and `(int, int, int)`, and the
/// second, `(A, bool)`, is then tried with the refusal in force; the verdict is the refusal.
#[test]
fn rows_compared_after_a_refusal_give_the_refusal() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    let a = "((int, int),) | ((int, int, int),)";
    let b = "((int, bool) | (int, bool, bool),) | ((int, U) | (int, U, U),)";
    let program = |g: &str| {
        format!(
            "p(f: (x: ({a}, bool)) -> int) = 0;\nq(g: (x: {g}) -> int for U in int) = p(f: g);\n"
        )
    };
    let refusal = "the tuples ((int, int),) and ((int, int, int),) may each be held by one of the \
                   shapes";
    for g in [format!("({b}, bool)"), format!("({b}, bool) | ({a}, bool)")] {
        let errs = type_errors(&program(&g));
        assert_eq!(errs.len(), 1, "{g}: {errs:?}");
        assert!(errs[0].contains(refusal), "{g}: {errs:?}");
    }
    // The control: with no shape refused, the parameter fits (`(U, int)`, which holds no
    // value of `p`'s parameter, gives the bound its variable).
    assert_eq!(
        type_errors(&program(&format!("({a}, bool) | (U, int)"))),
        Vec::<String>::new()
    );
}

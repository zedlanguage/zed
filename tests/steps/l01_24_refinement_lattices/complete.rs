//! Completeness cases for the lattices of step L1.24 with the widenings and narrowings of
//! step M0.5 (DESIGN.md, the paragraphs of both steps and sec:domains, literal domains): each
//! operation of each lattice on the bottom, the top and the elements between, the premise sets
//! of a cell, the cell of each kind of literal, and the printed forms. COMPLETENESS.md lists
//! each case with the test that covers it.

use std::collections::BTreeSet;

use num_bigint::BigInt;
use zed_kernel::Value;
use zed_kernel::provenance::{FactAddress, NodeAddress, Position, Vector};
use zed_kernel::types::{Type, Universe};
use zedc::store::affine::{Affine, Bounds};
use zedc::store::cell::{Cell, Premise, Premises};
use zedc::store::float::{FloatClass, Kind, Width};
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::landmarks::Landmarks;
use zedc::store::lattice::{Card, Congruence, FiniteSet, Lattice};

fn addr(n: u32) -> FactAddress {
    FactAddress {
        node: NodeAddress(Vector::from(vec![
            Position::root(),
            Position::root().child(n),
        ])),
        keypath: Vector::new(),
    }
}

fn constraint(n: u32) -> Premise {
    Premise::Constraint(addr(n))
}

fn set(ns: &[u32]) -> BTreeSet<Premise> {
    ns.iter().map(|&n| constraint(n)).collect()
}

fn class(m: i64, r: i64) -> Congruence {
    Congruence::new(m, r)
}

#[test]
fn a_congruence_prints_each_of_its_forms() {
    for (c, want) in [
        (Congruence::Bottom, "{}"),
        (Congruence::single(5), "5"),
        (Congruence::single(-5), "-5"),
        (Congruence::top(), "any"),
        (class(3, 1), "1 mod 3"),
        // The modulus is taken by its magnitude and the residue kept in `0..modulus`.
        (class(-3, -2), "1 mod 3"),
        (class(4, 9), "1 mod 4"),
        (class(1, 7), "any"),
    ] {
        assert_eq!(c.to_string(), want, "{c:?}");
    }
}

#[test]
fn a_congruence_holds_the_members_of_its_class() {
    let cases: [(Congruence, i64, bool); 9] = [
        (Congruence::Bottom, 0, false),
        (Congruence::single(4), 4, true),
        (Congruence::single(4), 5, false),
        (Congruence::top(), -17, true),
        (class(3, 1), 7, true),
        (class(3, 1), -2, true),
        (class(3, 1), -1, false),
        (class(3, 1), 0, false),
        (class(2, 0), 0, true),
    ];
    for (c, v, want) in cases {
        assert_eq!(c.contains(&Num::from(v)), want, "{v} in {c}");
    }
}

#[test]
fn congruence_join_and_meet_on_every_kind_of_operand() {
    let top = Congruence::top();
    let bot = Congruence::Bottom;
    // Join: the bottom is the unit, the top absorbs, two values give the class of their
    // difference, and two classes the gcd of the moduli and the difference.
    for (a, b, want) in [
        (bot.clone(), class(3, 1), class(3, 1)),
        (class(3, 1), bot.clone(), class(3, 1)),
        (bot.clone(), bot.clone(), bot.clone()),
        (top.clone(), class(3, 1), top.clone()),
        (Congruence::single(1), Congruence::single(4), class(3, 1)),
        (
            Congruence::single(4),
            Congruence::single(4),
            Congruence::single(4),
        ),
        (class(4, 1), class(6, 3), class(2, 1)),
        (class(4, 0), class(4, 2), class(2, 0)),
        (class(2, 0), class(2, 1), top.clone()),
    ] {
        assert_eq!(a.join(&b), want, "{a} join {b}");
        assert_eq!(a.widen(&b, &Landmarks::none()), want, "{a} widen {b}");
    }
    // Meet: the bottom absorbs, the top is the unit, a value meets a class it is or is not in,
    // and two classes meet by the Chinese remainder theorem or not at all.
    for (a, b, want) in [
        (bot.clone(), class(3, 1), bot.clone()),
        (class(3, 1), bot.clone(), bot.clone()),
        (top.clone(), class(3, 1), class(3, 1)),
        (Congruence::single(5), class(2, 1), Congruence::single(5)),
        (class(2, 1), Congruence::single(5), Congruence::single(5)),
        (Congruence::single(4), class(2, 1), bot.clone()),
        (Congruence::single(4), Congruence::single(5), bot.clone()),
        (class(2, 1), class(3, 2), class(6, 5)),
        (class(4, 1), class(6, 3), class(12, 9)),
        (class(2, 0), class(4, 1), bot.clone()),
        (class(4, 1), class(4, 1), class(4, 1)),
    ] {
        assert_eq!(a.meet(&b), want, "{a} meet {b}");
    }
    // The order read off the meet.
    assert!(class(4, 0).leq(&class(2, 0)));
    assert!(!class(2, 0).leq(&class(4, 0)));
    assert!(bot.leq(&Congruence::single(3)) && Congruence::single(3).leq(&top));
}

/// DESIGN.md step M0.5: the congruence narrowing takes `b` only from the top, or when `b` is
/// one value or none.
#[test]
fn a_congruence_narrowing_takes_next_only_from_the_top_or_for_one_value_or_none() {
    let none = Landmarks::none();
    let top = Congruence::top();
    for (a, b, want) in [
        (top.clone(), class(4, 0), class(4, 0)),
        (top.clone(), Congruence::Bottom, Congruence::Bottom),
        (top.clone(), Congruence::single(8), Congruence::single(8)),
        (class(2, 0), class(4, 0), class(2, 0)),
        (class(2, 0), Congruence::single(8), Congruence::single(8)),
        (class(2, 0), Congruence::Bottom, Congruence::Bottom),
        (
            Congruence::single(8),
            Congruence::Bottom,
            Congruence::Bottom,
        ),
        (Congruence::Bottom, Congruence::Bottom, Congruence::Bottom),
    ] {
        assert_eq!(a.narrow(&b, &none), want, "{a} narrow {b}");
    }
}

#[test]
fn finite_set_join_and_meet_with_the_top_on_either_side() {
    let a = FiniteSet::of([1i64, 2]);
    let top = FiniteSet::<i64>::top();
    assert_eq!(a.join(&top), top);
    assert_eq!(top.join(&a), top);
    assert_eq!(top.join(&top), top);
    assert_eq!(a.meet(&top), a);
    assert_eq!(top.meet(&a), a);
    assert_eq!(top.meet(&top), top);
    assert_eq!(a.join(&FiniteSet::of([3])), FiniteSet::of([1, 2, 3]));
    assert_eq!(a.meet(&FiniteSet::of([2, 3])), FiniteSet::of([2]));
    assert_eq!(a.meet(&FiniteSet::of([3])), FiniteSet::bottom());
    assert!(a.leq(&top) && FiniteSet::bottom().leq(&a) && !top.leq(&a));
}

/// DESIGN.md step M0.5: the finite-set widening is the join when every member it adds is a
/// landmark, and the top otherwise; its narrowing is `b`. The landmarks are the program's
/// integer literals `k` as `k - 1`, `k` and `k + 1`, and its other literal values.
#[test]
fn a_finite_set_widening_keeps_landmark_members_and_otherwise_goes_to_the_top() {
    let none = Landmarks::none();
    let top = FiniteSet::<Value>::top();
    let ints = |vs: &[i64]| FiniteSet::of(vs.iter().map(|&v| Value::Int(v)));
    // From the bottom: `next`, whatever it holds.
    assert_eq!(FiniteSet::bottom().widen(&ints(&[7]), &none), ints(&[7]));
    assert_eq!(FiniteSet::<Value>::bottom().widen(&top, &none), top);
    // Nothing added: unchanged, with or without landmarks.
    assert_eq!(ints(&[0]).widen(&ints(&[0]), &none), ints(&[0]));
    // Growing to the top.
    assert_eq!(ints(&[0]).widen(&top, &none), top);
    assert_eq!(top.widen(&top, &none), top);
    // The literal 3 makes 2, 3 and 4 landmarks, and no other integer.
    let three = Landmarks::of([3], []);
    for (v, kept) in [(1, false), (2, true), (3, true), (4, true), (5, false)] {
        let want = if kept { ints(&[0, v]) } else { top.clone() };
        assert_eq!(ints(&[0]).widen(&ints(&[0, v]), &three), want, "add {v}");
    }
    // A member added with a landmark and one without: the top.
    assert_eq!(ints(&[0]).widen(&ints(&[0, 3, 9]), &three), top);
    // An integer past the 64-bit range is a landmark by its value.
    let big = Value::int(BigInt::from(2).pow(70));
    let big_marks = Landmarks::of([Num::from(BigInt::from(2).pow(70))], []);
    let with_big = FiniteSet::of([Value::Int(0), big.clone()]);
    assert_eq!(ints(&[0]).widen(&with_big, &big_marks), with_big);
    assert_eq!(ints(&[0]).widen(&with_big, &none), top);
    // Strings, atoms and booleans are landmarks as written values.
    let words = Landmarks::of(
        std::iter::empty::<i64>(),
        [Value::str("b"), Value::atom("on")],
    );
    let a = FiniteSet::of([Value::str("a")]);
    for v in [Value::str("b"), Value::atom("on")] {
        let grown = a.join(&FiniteSet::of([v.clone()]));
        assert_eq!(a.widen(&grown, &words), grown, "{v:?}");
    }
    for v in [Value::str("c"), Value::atom("off"), Value::Bool(true)] {
        let grown = a.join(&FiniteSet::of([v.clone()]));
        assert_eq!(a.widen(&grown, &words), top, "{v:?}");
    }
    // The narrowing is `next`, from the top or from a set.
    assert_eq!(top.narrow(&ints(&[1, 2]), &none), ints(&[1, 2]));
    assert_eq!(ints(&[1, 2]).narrow(&ints(&[2]), &none), ints(&[2]));
    assert_eq!(
        ints(&[1, 2]).narrow(&FiniteSet::bottom(), &none),
        FiniteSet::bottom()
    );
}

fn card(lo: i64, hi: Option<i64>) -> Card {
    Card::range(End::of(lo), hi.map_or(End::PosInf, End::of))
}

/// DESIGN.md sec:domains (`card` and `len`) and step M0.5: a size is one interval of the
/// nonnegative integers; the cardinality widening and narrowing are the interval ones met
/// with `int[0..]`.
#[test]
fn a_cardinality_is_one_interval_of_the_nonnegative_integers() {
    let none = Landmarks::none();
    // The range is met with `[0..]`.
    assert_eq!(card(-3, Some(5)).interval(), &IntervalSet::of(0, 5));
    assert_eq!(card(-5, Some(-1)), Card::bottom());
    assert_eq!(
        Card::range(End::NegInf, End::PosInf).interval(),
        &IntervalSet::range(End::of(0), End::PosInf)
    );
    assert_eq!(Card::range(End::NegInf, End::PosInf), Card::top());
    assert!(Card::bottom().interval().is_empty());
    // The join is the hull: no pieces.
    assert_eq!(card(0, Some(1)).join(&card(5, Some(6))), card(0, Some(6)));
    assert_eq!(Card::bottom().join(&card(2, Some(3))), card(2, Some(3)));
    assert_eq!(card(0, Some(1)).join(&Card::top()), Card::top());
    // The meet.
    assert_eq!(card(0, Some(5)).meet(&card(3, Some(9))), card(3, Some(5)));
    assert_eq!(card(0, Some(1)).meet(&card(3, Some(9))), Card::bottom());
    assert_eq!(card(2, Some(4)).meet(&Card::top()), card(2, Some(4)));
    assert!(card(2, Some(4)).leq(&card(0, None)) && !card(0, None).leq(&card(2, Some(4))));
    // A lower end that moves down with no landmark goes to minus infinity, then to 0.
    assert_eq!(
        card(2, Some(3)).widen(&card(1, Some(3)), &none),
        card(0, Some(3))
    );
    // An upper end that moves up with no landmark goes to infinity.
    assert_eq!(
        card(2, Some(3)).widen(&card(2, Some(7)), &none),
        card(2, None)
    );
    // With the literal 9 written, 8, 9 and 10 are landmarks: the upper end stops at 8.
    let nine = Landmarks::of([9], []);
    assert_eq!(
        card(2, Some(3)).widen(&card(2, Some(7)), &nine),
        card(2, Some(8))
    );
    // From the bottom, or with nothing new: `next`.
    assert_eq!(
        Card::bottom().widen(&card(4, Some(5)), &none),
        card(4, Some(5))
    );
    assert_eq!(
        card(4, Some(5)).widen(&card(4, Some(5)), &none),
        card(4, Some(5))
    );
    // The narrowing: an infinite end takes the finite bound once, and a finite end of `next`
    // moves out to an old end or a landmark.
    assert_eq!(
        card(0, None).narrow(&card(0, Some(5)), &none),
        card(0, Some(5))
    );
    assert_eq!(
        card(0, None).narrow(&card(0, Some(5)), &nine),
        card(0, Some(8))
    );
    assert_eq!(
        card(0, Some(9)).narrow(&card(2, Some(5)), &none),
        card(0, Some(9))
    );
    assert_eq!(
        card(0, Some(9)).narrow(&Card::bottom(), &none),
        Card::bottom()
    );
}

fn lit(v: Value) -> Type {
    Type::lit(&v).expect("a literal type")
}

/// The type lattice of the cell (DESIGN.md sec:type_resolution rule 5 and step L1.39): join
/// and meet are union and intersection, the order is subtyping, a widening takes whole each
/// base type, and the rest of each universe, in which `next` gained a value, and a narrowing
/// takes `next` only in a part `self` holds whole.
#[test]
fn the_type_lattice_widens_and_narrows_by_whole_parts() {
    let none = Landmarks::none();
    let one = lit(Value::Int(1));
    let a = lit(Value::str("a"));
    let t2 = Type::tuple(vec![Type::int(), Type::int()]);
    assert_eq!(Type::bottom(), Type::empty());
    assert_eq!(<Type as Lattice>::top(), Type::top());
    assert_eq!(one.join(&a), &one | &a);
    assert_eq!((&one | &a).meet(&Type::int()), one);
    assert!(one.leq(&Type::int()) && !Type::int().leq(&one));
    assert!(Type::bottom().leq(&Type::bottom()) && Type::top().leq(&Type::top()));
    // A string gained: the whole string type, and the int part kept as it was.
    let w = one.widen(&(&one | &a), &none);
    assert_eq!(w, &one | &Type::string());
    // From the bottom every part `next` touches is taken whole.
    assert_eq!(
        Type::bottom().widen(&(&one | &a), &none),
        &Type::int() | &Type::string()
    );
    // A tuple gained: every tuple, and no scalar beyond the old ones.
    let w = one.widen(&(&one | &t2), &none);
    assert!(Type::tuple(vec![Type::bool()]).leq(&w));
    assert!(Type::tuple(vec![Type::string(), Type::f64()]).leq(&w));
    assert!(t2.leq(&w) && one.leq(&w));
    assert!(!Type::int().leq(&w) && !Type::bool().leq(&w));
    // An atom gained: the rest of the scalar universe, which holds every atom and no base.
    let on = Type::atom("on");
    let w = on.widen(&(&on | &Type::atom("off")), &none);
    assert!(Type::atom("other").leq(&w));
    assert!(!Type::int().leq(&w) && !Type::string().leq(&w) && !Type::bool().leq(&w));
    // Each of the other bases.
    for (base, v) in [
        (Type::bool(), Value::Bool(true)),
        (Type::f64(), Value::float(0.5)),
        (Type::f32(), Value::float32(0.5)),
    ] {
        let grown = &one | &lit(v.clone());
        assert_eq!(one.widen(&grown, &none), &one | &base, "{v:?}");
    }
    // A widening is above the join, the same when nothing is gained, and a second one on the
    // same gain changes nothing more.
    let w = one.widen(&(&one | &a), &none);
    assert_eq!(w.widen(&(&w | &lit(Value::str("b"))), &none), w);
    assert_eq!(Type::top().widen(&Type::top(), &none), Type::top());
    // The narrowing: from the top every part is whole, so it is `next`.
    assert_eq!(Type::top().narrow(&one, &none), one);
    assert_eq!(Type::top().narrow(&Type::bottom(), &none), Type::bottom());
    // `int | "a"`: the int part is whole and takes `1`, the string part is not and stays.
    assert_eq!((&Type::int() | &a).narrow(&one, &none), &one | &a);
    // A part `self` lacks stays empty.
    assert_eq!(Type::int().narrow(&Type::int(), &none), Type::int());
    assert_eq!(
        Type::bottom().narrow(&Type::bottom(), &none),
        Type::bottom()
    );
    // Universe parts: every tuple narrowed to the pairs of ints.
    let tuples = Type::universe(Universe::Tuple);
    assert_eq!(tuples.narrow(&t2, &none), t2);
}

#[test]
fn removing_premises_rebuilds_only_the_unions_that_held_them() {
    let a = Premises::one(constraint(1));
    let b = Premises::one(constraint(2));
    let c = Premises::one(constraint(3));
    let d = Premises::one(constraint(4));
    let mut ab = a.clone();
    ab.extend(&b);
    let mut cd = c.clone();
    cd.extend(&d);
    let mut all = ab.clone();
    all.extend(&cd);
    // Nothing to drop: the same set, shared.
    assert!(all.without(&[]).same(&all));
    // The empty set stays empty.
    assert!(Premises::new().without(std::slice::from_ref(&a)).is_empty());
    // A set of one premise without itself is empty, without another unchanged.
    assert!(a.without(std::slice::from_ref(&a)).is_empty());
    assert!(a.without(std::slice::from_ref(&b)).same(&a));
    // One from each side, both from one side, one from one side.
    assert_eq!(all.without(&[b.clone(), d.clone()]), set(&[1, 3]));
    assert_eq!(all.without(&[a.clone(), b.clone()]), set(&[3, 4]));
    assert_eq!(all.without(std::slice::from_ref(&c)), set(&[1, 2, 4]));
    // The side that holds none of them is kept shared.
    let kept = all.without(std::slice::from_ref(&d));
    assert_eq!(kept, set(&[1, 2, 3]));
    // All of them.
    assert!(
        all.without(&[a.clone(), b.clone(), c.clone(), d.clone()])
            .is_empty()
    );
    // A premise made later and not in the set: unchanged and shared.
    let e = Premises::one(constraint(5));
    assert!(all.without(std::slice::from_ref(&e)).same(&all));
    // An equal premise made apart is a different part and stays.
    let a2 = Premises::one(constraint(1));
    assert_eq!(all.without(std::slice::from_ref(&a2)), set(&[1, 2, 3, 4]));
    // A part shared twice is entered once and dropped on both paths.
    let mut twice = ab.clone();
    twice.extend(&c);
    twice.extend(&ab);
    assert_eq!(twice, set(&[1, 2, 3]));
    assert_eq!(twice.without(std::slice::from_ref(&a)), set(&[2, 3]));
    // Dropping the one widening leaves a set that rests on none.
    let w = Premises::one(Premise::Widened(addr(9)));
    let mut cw = c.clone();
    cw.extend(&w);
    assert!(cw.widened());
    let dropped = cw.without(std::slice::from_ref(&w));
    assert!(!dropped.widened());
    assert_eq!(dropped, set(&[3]));
}

#[test]
fn premise_sets_compare_by_their_premises() {
    let a = Premises::one(constraint(1));
    let a2 = Premises::one(constraint(1));
    let b = Premises::one(constraint(2));
    assert_eq!(Premises::new(), Premises::new());
    assert_ne!(Premises::new(), a);
    assert_ne!(a, Premises::new());
    assert_eq!(a, a.clone());
    assert!(a.same(&a.clone()) && !a.same(&a2) && Premises::new().same(&Premises::new()));
    assert!(!a.same(&Premises::new()) && !Premises::new().same(&a));
    // Made apart, the same premise: equal, though not the same part.
    assert_eq!(a, a2);
    assert_ne!(a, b);
    // The same premises reached by different unions.
    let (mut ab, mut ba) = (a.clone(), b.clone());
    ab.extend(&b);
    ba.extend(&a);
    assert_eq!(ab, ba);
    // Against a plain set, and back from one.
    assert_eq!(ab, set(&[1, 2]));
    assert!(Premises::new() == BTreeSet::new());
    assert_eq!(Premises::from(set(&[1, 2])), ab);
    assert!(Premises::from(BTreeSet::new()).is_empty());
    assert_eq!(format!("{ab:?}"), format!("{:?}", set(&[1, 2])));
    // Inserting a premise already held changes the set's premises in nothing.
    let mut c = ab.clone();
    c.insert(constraint(1));
    assert_eq!(c, ab);
    c.insert(constraint(3));
    assert_eq!(c, set(&[1, 2, 3]));
    assert!(c.contains(&constraint(3)) && !c.contains(&constraint(4)));
}

/// DESIGN.md sec:domains, literal domains: a literal's domain is the singleton containing it,
/// in each domain that reads its kind, and a literal rests on nothing.
#[test]
fn the_cell_of_each_kind_of_literal() {
    let top = Cell::top();
    // An integer past the 64-bit range: its point and its one-value class.
    let n: BigInt = BigInt::from(2).pow(70) + 1;
    let big = Value::int(n.clone());
    assert!(matches!(big, Value::Big(_)));
    let c = Cell::literal(&big);
    let num = Num::from(n);
    assert_eq!(
        c.ints.element,
        Bounds::ints(IntervalSet::point(num.clone()))
    );
    assert_eq!(c.congruence.element, Congruence::single(num));
    assert_eq!(c.finite.element, FiniteSet::of([big.clone()]));
    assert_eq!((&c.float, &c.length), (&top.float, &top.length));
    assert!(c.premises().is_empty());
    // `true` and an atom: the finite set alone.
    for v in [Value::Bool(true), Value::Bool(false), Value::atom("on")] {
        let c = Cell::literal(&v);
        assert_eq!(c.finite.element, FiniteSet::of([v.clone()]), "{v:?}");
        assert_eq!(
            (&c.ints, &c.congruence, &c.float, &c.length),
            (&top.ints, &top.congruence, &top.float, &top.length),
            "{v:?}"
        );
    }
    // The ends of the 64-bit range.
    for v in [i64::MIN, -1, 0, i64::MAX] {
        let c = Cell::literal(&Value::Int(v));
        assert_eq!(c.ints.element, Bounds::ints(IntervalSet::single(v)));
        assert_eq!(c.congruence.element, Congruence::single(v));
    }
    // The empty string has length 0.
    let c = Cell::literal(&Value::str(""));
    assert_eq!(c.length.element, Bounds::ints(IntervalSet::single(0)));
    // Each float kind of an f64 literal.
    for (x, kinds, width) in [
        (f64::INFINITY, Kind::PosInf, Width::F16),
        (f64::NEG_INFINITY, Kind::NegInf, Width::F16),
        (1e300, Kind::Finite, Width::F64),
    ] {
        let c = Cell::literal(&Value::float(x));
        assert_eq!(c.float.element, FloatClass::new(&[kinds], width), "{x}");
    }
}

#[test]
fn float_widths_and_printed_classes() {
    // The narrowest format holding a finite value exactly, at each format's largest value
    // and past it.
    for (x, want) in [
        (0.0, Width::F16),
        (65504.0, Width::F16),
        (65505.0, Width::F32),
        (131072.0, Width::F32),
        (1e10, Width::F32),
        (f64::from(f32::MAX), Width::F32),
        (f64::from(f32::MAX) * 2.0, Width::F64),
        (1e300, Width::F64),
        (-1e300, Width::F64),
        (f64::NAN, Width::F16),
        // The least subnormal of each format, and half of it.
        (2f64.powi(-24), Width::F16),
        (2f64.powi(-25), Width::F32),
        (2f64.powi(-149), Width::F32),
        (2f64.powi(-150), Width::F64),
        (f64::from_bits(1), Width::F64),
        (-f64::from_bits(3), Width::F64),
    ] {
        assert_eq!(Width::of(x), want, "{x:e}");
    }
    for (c, want) in [
        (FloatClass::new(&[Kind::NegInf], Width::F32), "f32{-inf}"),
        (
            FloatClass::new(
                &[Kind::NegInf, Kind::Finite, Kind::PosInf, Kind::NaN],
                Width::F64,
            ),
            "f64{-inf, finite, inf, nan}",
        ),
        (FloatClass::new(&[Kind::NaN], Width::F16), "f16{nan}"),
        (FloatClass::bottom(), "{}"),
    ] {
        assert_eq!(c.to_string(), want);
    }
}

#[test]
fn affine_bounds_print_each_sign_of_their_constant() {
    let n = Affine::sym("n");
    for (a, want) in [
        (n.clone(), "n"),
        (n.plus(-1), "n - 1"),
        (n.plus(2), "n + 2"),
        (n.times(-1), "-n"),
        (n.times(3).plus(-4), "3 * n - 4"),
        (Affine::constant(0), "0"),
        (Affine::constant(-3), "-3"),
        (n.plus(5).plus(-5), "n"),
    ] {
        assert_eq!(a.to_string(), want);
    }
}

//! Questions over shared conjunctions, decided from the answers of the conjunction each extends
//! (`presburger::extend`, LOAD-chain-share): each answer is the one `decide` gives the whole,
//! and a chain of n extensions is decided in time of its links.

use zedc::store::presburger::extend::{Answers, Extending};
use zedc::store::presburger::{Atom, Con, Formula, Lin, decide};

pub(super) fn sym(name: &str) -> Lin {
    Lin::atom(Atom::Sym(name.into()))
}

/// `a >= b`.
pub(super) fn ge(a: Lin, b: Lin) -> Formula {
    Formula::Con(Con::ge(&a, &b))
}

/// `part && rest`, with `part` kept whole, as the translator joins a call's relation.
pub(super) fn extend(part: &Formula, rest: Vec<Formula>) -> Formula {
    let mut fs = vec![part.clone()];
    fs.extend(rest);
    Formula::and_keeping(fs, |i| i == 0)
}

/// The answers `decide` gives `f` and its negation.
pub(super) fn decided(f: &Formula) -> Answers {
    Answers {
        holds: decide(f),
        fails: decide(&Formula::negate(f.clone())),
    }
}

/// `x + k * y <= c`.
pub(super) fn sum(k: i64, c: i64) -> Formula {
    ge(Lin::constant(c), sym("x").plus(&sym("y").times(k)))
}

#[test]
fn each_answer_is_the_one_the_whole_has() {
    let (x, y) = (sym("x"), sym("y"));
    // A conjunction of two, so that it is kept whole and not one constraint.
    let base = Formula::and(vec![
        ge(x.clone(), y.clone()),
        ge(y.clone(), Lin::constant(0)),
    ]);
    // Holding everywhere: x >= 0 or x <= -1 with y in either of two halves, not seen as `true`
    // when it is built.
    let halves = |v: &Lin| {
        Formula::or(vec![
            ge(v.clone(), Lin::constant(0)),
            ge(Lin::constant(-1), v.clone()),
        ])
    };
    let everywhere = Formula::and(vec![halves(&x), halves(&y)]);
    let empty = Formula::and(vec![
        ge(x.clone(), Lin::constant(5)),
        ge(Lin::constant(4), x.clone()),
    ]);
    let cases = [
        // The point of the part serves.
        extend(&base, vec![ge(Lin::constant(100), x.clone())]),
        // The point of the part does not serve: decided whole.
        extend(
            &base,
            vec![
                ge(x.clone(), Lin::constant(50)),
                ge(y.clone(), Lin::constant(7)),
            ],
        ),
        // Nowhere, by the new parts alone.
        extend(&base, vec![ge(Lin::constant(-1), y.clone())]),
        // Nowhere, since the part holds nowhere.
        extend(&empty, vec![ge(x.clone(), Lin::constant(0))]),
        // The part holds everywhere: the negation is that of the new parts.
        extend(&everywhere, vec![ge(x.clone(), Lin::constant(3))]),
        extend(&everywhere, vec![]),
        // A part of a part.
        extend(&extend(&base, vec![sum(2, 40)]), vec![sum(3, 60)]),
        // No kept part, and not a conjunction.
        Formula::and(vec![ge(x.clone(), y.clone()), ge(y.clone(), x.clone())]),
        ge(x.clone(), Lin::constant(1)),
        Formula::or(vec![base.clone(), empty.clone()]),
    ];
    let mut e = Extending::new();
    for f in &cases {
        assert_eq!(e.answers(f), decided(f), "{f}");
        // Asked again, from what is remembered.
        assert_eq!(e.answers(f), decided(f), "{f} again");
    }
    // Each in a new memory, so that no answer depends on what was asked before.
    for f in &cases {
        assert_eq!(Extending::new().answers(f), decided(f), "{f} alone");
    }
}

#[test]
fn a_chain_whose_points_move_is_decided_whole() {
    // f{i} = f{i-1} && x + i * y >= 1000 i: the point found for f{i-1} is below the new
    // constraint, so each f{i} is decided whole, and each answer is still the one the whole has
    // (the Complexity tradeoff at `Extending::defined`).
    let mut f = Formula::and(vec![
        ge(sym("x"), sym("y").plus(&Lin::constant(1))),
        ge(sym("y"), Lin::constant(0)),
    ]);
    let mut e = Extending::new();
    for i in 1..=40i64 {
        f = extend(
            &f,
            vec![ge(
                sym("x").plus(&sym("y").times(i)),
                Lin::constant(1000 * i),
            )],
        );
        assert_eq!(e.answers(&f), decided(&f), "{f}");
    }
}

/// A chain of `n` calls as the scope reads it (LOAD-extend-refuses): `x{i} == x{i+1} + k`, the
/// argument of call i bound to its callee's atom, written from the last link back so that the
/// bindings resolve through long paths; `b{i} == i`, a binding's own variable; and at each link
/// the callee's `x{i} mod 3`, a division over the callee's atom, with a disjunction over its
/// remainder. With `k` 0 every division divides the same term.
pub(super) fn bound_chain(n: usize, k: i64) -> Formula {
    let x = |i: usize| sym(&format!("x{i}"));
    let eq = |a: Lin, b: Lin| Formula::Con(Con::eq(&a, &b));
    let mut fs = Vec::new();
    for i in (0..n).rev() {
        fs.push(eq(x(i), x(i + 1).plus(&Lin::constant(k))));
        fs.push(eq(sym(&format!("b{i}")), Lin::constant(i as i64)));
    }
    for i in 0..=n {
        let (q, r) = (sym(&format!("q{i}")), sym(&format!("r{i}")));
        fs.push(eq(x(i), q.times(3).plus(&r)));
        fs.push(ge(r.clone(), Lin::constant(0)));
        fs.push(ge(Lin::constant(2), r.clone()));
        fs.push(Formula::or(vec![
            eq(r.clone(), Lin::constant(1)),
            ge(x(i), Lin::constant(10 * i as i64)),
        ]));
    }
    Formula::and(fs)
}

#[test]
fn bindings_put_in_place_leave_one_atom_and_one_division() {
    // LOAD-extend-refuses: a whole question the solver refuses is asked again with its
    // bindings in place. Over a chain they leave one of the x atoms and no binding variable,
    // the divisions of one term merge into one, and the formula with them in place has the
    // answer of the formula.
    use zedc::store::presburger::extend::with_bindings_in_place;
    for k in [0, 2] {
        let f = bound_chain(6, k);
        let g = with_bindings_in_place(&f).expect("bindings");
        let atoms = g.atoms();
        let xs = atoms
            .iter()
            .filter(|a| format!("{a:?}").contains("\"x"))
            .count();
        let bs = atoms
            .iter()
            .filter(|a| format!("{a:?}").contains("\"b"))
            .count();
        let rs = atoms
            .iter()
            .filter(|a| format!("{a:?}").contains("\"r"))
            .count();
        assert_eq!((xs, bs), (1, 0), "{g}");
        // With k 0 each x is the same term, so the seven divisions are one; with k 2 the terms
        // differ by 2, so none merge.
        assert_eq!(rs, if k == 0 { 1 } else { 7 }, "{g}");
        assert_eq!(decide(&g), decide(&f), "{f}");
    }
}

/// A kept part whose face holds a clause over a quotient that clause alone reads, and a
/// constraint beside the part over that quotient (SOUND-extend-face-local-atoms). The part is
/// `q(x) = (x mod 2 != 1 || x mod 4 == 1) && x >= 2 && x <= 9` over the pairs `x == 2 * q0 +
/// q1` and `x == 4 * q2 + q3`, whose face keeps the clause `x == 4 * q2 + 1 || x == 2 * q0`;
/// the whole is `q && x >= 9 && q0 <= 2`, which holds nowhere: `x` is 9 and `9 div 2` is 4.
/// The face's `q0` is bound inside its clause (the clause holds by its first disjunct at
/// `x = 9`, whatever `q0` is), so it is not read beside the face, and the answer is the one
/// the whole has with its definitions. Before the fix the face counted `q0` as one of its
/// atoms, and the point `x = 9, q0 = 0` of the faces answered `true`.
#[test]
fn an_atom_a_face_clause_alone_reads_is_not_read_beside_it() {
    let x = sym("x");
    let q = |n: u32| Lin::atom(Atom::Aux(n));
    let k = Lin::constant;
    let eq = |a: Lin, b: Lin| Formula::Con(Con::eq(&a, &b));
    let pair = |m: i64, n: u32| {
        Formula::and(vec![
            eq(x.clone(), q(n).times(m).plus(&q(n + 1))),
            ge(q(n + 1), k(0)),
            ge(k(m - 1), q(n + 1)),
        ])
    };
    let defs = [pair(2, 0), pair(4, 2)];
    let def = |n: u32| defs[n as usize / 2].clone();
    let part = Formula::and(vec![
        Formula::or(vec![Formula::negate(eq(q(1), k(1))), eq(q(3), k(1))]),
        ge(x.clone(), k(2)),
        ge(k(9), x.clone()),
    ]);
    let whole = extend(&part, vec![ge(x.clone(), k(9)), ge(k(2), q(0))]);
    // Only the part is a call, and its caller reads `x`.
    let iface = |g: &Formula| matches!(g, Formula::And(_)).then(|| vec![Atom::Sym("x".into())]);
    let with_defs = |f: Formula| Formula::and(vec![defs[0].clone(), defs[1].clone(), f]);
    let want = Answers {
        holds: decide(&with_defs(whole.clone())),
        fails: decide(&with_defs(Formula::negate(whole.clone()))),
    };
    assert_eq!(
        (want.holds.clone(), want.fails.clone()),
        (Ok(false), Ok(true))
    );
    let mut e = Extending::new();
    // The part asked first, as a unit asks its callee before its caller, and the whole after.
    e.defined_with(&part, &def, &iface);
    assert_eq!(e.defined_with(&whole, &def, &iface), want, "{whole}");
    // The control: `x div 4 <= 2` beside the part, which holds at `x = 9`, so the fix does not
    // turn a true answer false.
    let control = extend(&part, vec![ge(x.clone(), k(9)), ge(k(2), q(2))]);
    let want = Answers {
        holds: decide(&with_defs(control.clone())),
        fails: decide(&with_defs(Formula::negate(control.clone()))),
    };
    assert_eq!(want.holds, Ok(true));
    assert_eq!(e.defined_with(&control, &def, &iface), want, "{control}");
}

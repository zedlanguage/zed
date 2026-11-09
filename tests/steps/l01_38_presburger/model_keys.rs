//! The point `satisfiable` gives is a point of the formula as `Formula::holds` reads it, each
//! atom the point leaves out read as zero (PRES-model-keys). The solver leaves atoms out in three
//! places, all of which read an atom left out as zero: `repair` gives an atom of a disjunction
//! that `absorb` removed no value where zero already lies between its bounds; the other disjuncts
//! of such a disjunction are not read at all; and the search takes a disjunct whose rows hold at
//! the point with its atoms left out read as zero (`Con::holds`). Its callers read each atom left
//! out as zero, which is this convention. The formulas here are random, with base rows,
//! disjunctions whose disjuncts bound atoms that no other part reads, negations, equalities and
//! auxiliary variables, so that all three are met often; products are left out, since the solver
//! reads a product as an atom of its own and `holds` as the product of its factors.

use std::sync::Arc;

use zed_tests::instances::Rng;
use zedc::store::int::Int;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, satisfiable};

/// A row `Σ c·a + k >= 0`, or `== 0` when `eq`.
fn row(terms: &[(Atom, i64)], k: i64, eq: bool) -> Formula {
    let mut lin = Lin::constant(k);
    for (a, c) in terms {
        lin = lin.plus(&Lin::atom(a.clone()).times(*c));
    }
    let zero = Lin::constant(0);
    Formula::Con(if eq {
        Con::eq(&lin, &zero)
    } else {
        Con::ge(&lin, &zero)
    })
}

/// The `i`-th shared atom: a symbol, or an auxiliary variable.
fn shared(i: usize) -> Atom {
    if i.is_multiple_of(2) {
        Atom::Sym(Arc::from(format!("s{i}")))
    } else {
        Atom::Aux(i as u32)
    }
}

/// The `i`-th atom of disjunction `j` that no other part reads.
fn private(j: usize, i: usize) -> Atom {
    if i.is_multiple_of(2) {
        Atom::Sym(Arc::from(format!("p{j}_{i}")))
    } else {
        Atom::Aux(100 + 10 * j as u32 + i as u32)
    }
}

/// A coefficient: 1 or -1 mostly, sometimes 2 or -2.
fn coef(rng: &mut Rng) -> i64 {
    let c = if rng.below(5) == 0 { 2 } else { 1 };
    if rng.below(2) == 0 { c } else { -c }
}

/// A random row over the atoms `atoms`, of one or two terms.
fn any_row(rng: &mut Rng, atoms: &[Atom]) -> Formula {
    let a = rng.pick(atoms);
    let mut terms = vec![(a.clone(), coef(rng))];
    let b = rng.pick(atoms);
    if b != a && rng.below(2) == 0 {
        terms.push((b, coef(rng)));
    }
    row(&terms, rng.int(-4, 4), rng.below(6) == 0)
}

/// A disjunct of disjunction `j`: rows bounding one or two of its own atoms, each `x - s + k`
/// or `s - x + k` over a shared atom `s` or none, so that the bounds of a disjunct and of the
/// base often cancel and the disjunction is removed; sometimes any row, a negation or a
/// disjunction of its own.
fn disjunct(rng: &mut Rng, j: usize, ss: &[Atom]) -> Formula {
    let mut parts = Vec::new();
    for _ in 0..1 + rng.below(3) {
        let x = private(j, rng.below(2));
        let side = if rng.below(2) == 0 { 1 } else { -1 };
        let mut terms = vec![(x.clone(), side)];
        if rng.below(2) == 0 {
            terms.push((rng.pick(ss), -side));
        }
        let mut atoms = ss.to_vec();
        atoms.push(x);
        parts.push(match rng.below(8) {
            0 => any_row(rng, &atoms),
            1 => Formula::negate(any_row(rng, &atoms)),
            2 => Formula::or(vec![any_row(rng, &atoms), any_row(rng, &atoms)]),
            _ => row(&terms, rng.int(-3, 3), false),
        });
    }
    Formula::and(parts)
}

/// A random formula: base rows over the shared atoms and the disjunctions' own atoms, and
/// disjunctions of [`disjunct`]s, sometimes under a negation.
fn formula(rng: &mut Rng) -> Formula {
    let ss: Vec<Atom> = (0..1 + rng.below(3)).map(shared).collect();
    let ors = 1 + rng.below(4);
    let mut parts = Vec::new();
    for _ in 0..rng.below(5) {
        let mut atoms = ss.clone();
        if rng.below(2) == 0 {
            atoms.push(private(rng.below(ors), rng.below(2)));
        }
        parts.push(any_row(rng, &atoms));
    }
    for j in 0..ors {
        let ds = (0..2 + rng.below(2))
            .map(|_| disjunct(rng, j, &ss))
            .collect();
        parts.push(Formula::or(ds));
    }
    let f = Formula::and(parts);
    if rng.below(8) == 0 {
        Formula::negate(Formula::negate(f))
    } else {
        f
    }
}

/// The atoms of `f` that `m` leaves out.
fn left_out(f: &Formula, m: &Model) -> usize {
    f.atoms().iter().filter(|a| !m.contains_key(*a)).count()
}

#[test]
fn every_point_satisfiable_gives_holds_with_the_atoms_it_leaves_out_read_as_zero() {
    let mut rng = Rng::new(0x5eed_4b3f);
    let (mut points, mut short, mut refused) = (0, 0, 0);
    for case in 0..4000 {
        let f = formula(&mut rng);
        match satisfiable(&f) {
            Ok(Some(m)) => {
                assert!(f.holds(&m), "case {case}: {m:?} fails {f}");
                points += 1;
                if left_out(&f, &m) > 0 {
                    short += 1;
                }
            }
            Ok(None) => {}
            Err(_) => refused += 1,
        }
    }
    // The case the test is for is met: points that leave atoms out.
    assert!(points > 1000, "{points} points");
    assert!(short > 100, "{short} of {points} points leave an atom out");
    assert!(refused < 40, "{refused} refused");
}

/// The disjunction `x - s >= 0 || s - x >= 0` changes no answer once `x`, read by nothing else,
/// is projected away, so the solver removes it and gives `x` a value only where zero misses the
/// bounds of the disjunct it reads: the point has `s = 3`, and holds with `x` at its value or,
/// left out, at zero.
#[test]
fn a_removed_disjunction_holds_at_the_point_with_its_own_atom_read_as_zero_when_left_out() {
    let s = Atom::Sym(Arc::from("s"));
    let x = Atom::Sym(Arc::from("x"));
    let f = Formula::and(vec![
        row(&[(s.clone(), 1)], -3, true),
        Formula::or(vec![
            row(&[(x.clone(), 1), (s.clone(), -1)], 0, false),
            row(&[(s.clone(), 1), (x.clone(), -1)], 0, false),
        ]),
    ]);
    let m = satisfiable(&f).expect("answered").expect("a point");
    assert_eq!(m.get(&s), Some(&Int::from(3)));
    assert!(f.holds(&m), "{m:?} fails {f}");
}

/// Where zero does not lie between the bounds of the removed disjunct, `repair` gives its own
/// atom the nearer bound: either disjunct, `5 <= x <= 7` or `-12 <= x <= -9`, with `x` read by
/// nothing else, removes the disjunction, and `x` gets a value within it (5 or -9).
#[test]
fn a_removed_disjunction_gives_its_own_atom_a_value_where_zero_misses_it() {
    let x = Atom::Sym(Arc::from("x"));
    let y = Atom::Sym(Arc::from("y"));
    let f = Formula::and(vec![
        row(&[(y.clone(), 1)], -2, true),
        Formula::or(vec![
            Formula::and(vec![
                row(&[(x.clone(), 1)], -5, false),
                row(&[(x.clone(), -1)], 7, false),
            ]),
            Formula::and(vec![
                row(&[(x.clone(), -1)], -9, false),
                row(&[(x.clone(), 1)], 12, false),
            ]),
        ]),
    ]);
    let m = satisfiable(&f).expect("answered").expect("a point");
    assert!(f.holds(&m), "{m:?} fails {f}");
    let v = m.get(&x).expect("x has a value");
    assert!(
        (Int::from(5)..=Int::from(7)).contains(v) || (Int::from(-12)..=Int::from(-9)).contains(v),
        "{m:?}"
    );
}

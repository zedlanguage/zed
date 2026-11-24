//! [`two_var_domains`] on formulas that reduce to two atoms by unit equalities (COMPLEXITY.md
//! row XR-l139-neon-r4): its answers on chains of equalities given in either order, and, in
//! [`bench`], its work as the number of equalities grows.

use super::*;

mod bench;

fn xa(i: usize) -> Atom {
    Atom::Sym(format!("x{i:06}").into())
}

fn x(i: usize) -> Lin {
    Lin::atom(xa(i))
}

/// `x_i == x_{i+1} + 1` for `i < e`, then `0 <= x_e <= 100`, with the equalities in reverse
/// order when `reverse`. The projection of `x_0` is `e..=e + 100`.
fn chain(e: usize, reverse: bool) -> Formula {
    let mut eqs: Vec<Formula> = (0..e)
        .map(|i| {
            let row = x(i).minus(&x(i + 1)).minus(&Lin::constant(1));
            Formula::Con(Con::eq(&row, &Lin::default()))
        })
        .collect();
    if reverse {
        eqs.reverse();
    }
    eqs.push(Formula::Con(Con::ge(&x(e), &Lin::default())));
    eqs.push(Formula::Con(Con::ge(
        &Lin::constant(100).minus(&x(e)),
        &Lin::default(),
    )));
    Formula::and(eqs)
}

/// The answer [`chain`] must get: `e..=e + 100`.
fn expected(e: usize) -> IntervalSet {
    IntervalSet::range(End::of(e as i64), End::of(e as i64 + 100))
}

#[test]
fn chains_of_unit_equalities_project_exactly_in_either_order() {
    for e in [1, 2, 5, 40] {
        for reverse in [false, true] {
            let f = chain(e, reverse);
            let (each, _) = two_var_domains(&f, &[xa(0)]).expect("two_var_domains answers");
            assert_eq!(each.len(), 1);
            assert_eq!(
                each[0].as_ref().expect("a domain"),
                &expected(e),
                "e = {e}, reverse = {reverse}"
            );
        }
    }
}

/// A chain whose last value is fixed by an equality of one atom, `2·x_e == 6`, and one with
/// no integer value, `2·x_e == 7`: the single-atom branch gives `x_e` its value or the empty
/// set.
#[test]
fn single_atom_equalities_fix_a_value_or_empty_the_domain() {
    for (k, answer) in [(6, Some(3 + 5)), (7, None)] {
        let mut parts: Vec<Formula> = (0..5)
            .map(|i| {
                let row = x(i).minus(&x(i + 1)).minus(&Lin::constant(1));
                Formula::Con(Con::eq(&row, &Lin::default()))
            })
            .collect();
        let two = x(5).plus(&x(5));
        parts.push(Formula::Con(Con::eq(&two, &Lin::constant(k))));
        parts.push(Formula::Con(Con::ge(&x(5), &Lin::default())));
        let (each, _) =
            two_var_domains(&Formula::and(parts), &[xa(0)]).expect("two_var_domains answers");
        let got = each[0].as_ref().expect("a domain");
        match answer {
            Some(v) => assert_eq!(got, &IntervalSet::single(v)),
            None => assert_eq!(got, &IntervalSet::empty()),
        }
    }
}

fn con_eq(l: Lin, r: Lin) -> Formula {
    Formula::Con(Con::eq(&l, &r))
}

fn con_ge(l: Lin, r: Lin) -> Formula {
    Formula::Con(Con::ge(&l, &r))
}

/// The domains of `syms` in `f`, each one answered.
fn domains(f: &Formula, syms: &[Atom]) -> Vec<IntervalSet> {
    let (each, _) = two_var_domains(f, syms).expect("two_var_domains answers");
    each.into_iter().map(|d| d.expect("a domain")).collect()
}

/// Every symbol of [`chain`] asked at once (row PERF-twovar-elim-per-arm: each read off one
/// elimination as `x_e + (e - i)`): `x_i` takes `e - i..=e - i + 100`, in either order.
#[test]
fn every_symbol_of_a_chain_projects_exactly_in_either_order() {
    for e in [1, 2, 5, 40] {
        for reverse in [false, true] {
            let syms: Vec<Atom> = (0..=e).map(xa).collect();
            let got = domains(&chain(e, reverse), &syms);
            for (i, d) in got.iter().enumerate() {
                let lo = (e - i) as i64;
                assert_eq!(
                    d,
                    &IntervalSet::of(lo, lo + 100),
                    "e {e} reverse {reverse} x{i}"
                );
            }
        }
    }
}

/// `x_i + x_{i+1} == 0` for `i < 4`, `0 <= x_4 <= 100`: each `x_i` is `±x_4`, read with the
/// sign (the negated form): `0..=100` at even distance from `x_4`, `-100..=0` at odd.
#[test]
fn negated_forms_project_with_their_sign() {
    let mut parts: Vec<Formula> = (0..4)
        .map(|i| con_eq(x(i).plus(&x(i + 1)), Lin::default()))
        .collect();
    parts.push(con_ge(x(4), Lin::default()));
    parts.push(con_ge(Lin::constant(100), x(4)));
    let syms: Vec<Atom> = (0..=4).map(xa).collect();
    let got = domains(&Formula::and(parts), &syms);
    for (i, d) in got.iter().enumerate() {
        let want = if (4 - i) % 2 == 0 {
            IntervalSet::of(0, 100)
        } else {
            IntervalSet::of(-100, 0)
        };
        assert_eq!(d, &want, "x{i}");
    }
}

/// `x0 == y + z` with `0 <= y <= 2`, `0 <= z <= 3`: the form of `x0` reads two atoms, so it
/// is not read off the elimination but projected by the old one with `x0` kept (`0..=5`);
/// `y` and `z`, left in the rows, are read off it.
#[test]
fn a_form_of_two_atoms_falls_back_to_the_symbol_kept() {
    let (y, z) = (xa(1), xa(2));
    let parts = vec![
        con_eq(x(0), x(1).plus(&x(2))),
        con_ge(x(1), Lin::default()),
        con_ge(Lin::constant(2), x(1)),
        con_ge(x(2), Lin::default()),
        con_ge(Lin::constant(3), x(2)),
    ];
    let got = domains(&Formula::and(parts), &[xa(0), y, z]);
    assert_eq!(
        got,
        vec![
            IntervalSet::of(0, 5),
            IntervalSet::of(0, 2),
            IntervalSet::of(0, 3)
        ]
    );
}

/// A constant form, `2·x0 == 14`, beside `x1 >= 0` and an atom `w` free but for `x2 == w`:
/// `x0` is `{7}`, `x1` is `0..`, and `x2` and `w` take every integer. With `x1 >= 5` and
/// `x1 <= 4` the rows have no point and every domain is empty, the constant one too.
#[test]
fn constant_and_free_forms_follow_the_rows_point() {
    let w = Atom::Sym("w".into());
    let syms = [xa(0), xa(1), xa(2), w.clone()];
    let base = |extra: Vec<Formula>| {
        let mut parts = vec![
            con_eq(x(0).times(2), Lin::constant(14)),
            con_eq(x(2), Lin::atom(w.clone())),
            con_ge(x(1), Lin::default()),
        ];
        parts.extend(extra);
        Formula::and(parts)
    };
    let top = IntervalSet::top();
    let got = domains(&base(Vec::new()), &syms);
    let from = IntervalSet::range(End::of(0), End::PosInf);
    assert_eq!(got, vec![IntervalSet::single(7), from, top.clone(), top]);
    let none = base(vec![
        con_ge(x(1), Lin::constant(5)),
        con_ge(Lin::constant(4), x(1)),
    ]);
    let got = domains(&none, &syms);
    assert!(got.iter().all(IntervalSet::is_empty), "{got:?}");
}

/// Forms read in each arm and joined: `x0 == x1 + 1`, `0 <= x1 <= 100`, and `x1 <= 10` or
/// `x1 >= 50`: `x0` takes `1..=11` and `51..=101`.
#[test]
fn forms_are_read_in_each_arm_and_joined() {
    let parts = vec![
        con_eq(x(0), x(1).plus(&Lin::constant(1))),
        con_ge(x(1), Lin::default()),
        con_ge(Lin::constant(100), x(1)),
        Formula::or(vec![
            con_ge(Lin::constant(10), x(1)),
            con_ge(x(1), Lin::constant(50)),
        ]),
    ];
    let got = domains(&Formula::and(parts), &[xa(0), xa(1)]);
    let two = |a, b, c, d| IntervalSet::of(a, b).join(&IntervalSet::of(c, d));
    assert_eq!(got, vec![two(1, 11, 51, 101), two(0, 10, 50, 100)]);
}

/// Whether `|c| <= (k+1)^((k+1)/2) · H^(k+1)`, the bound of the claim in the comment above
/// `two_var_domains`, tested squared so no root is taken: `c² <= (k+1)^(k+1) · H^(2(k+1))`.
fn within_size_bound(c: &Int, k: u32, h: &Int) -> bool {
    let mut bound = Int::from(1);
    for _ in 0..=k {
        bound = &(&bound * &Int::from(i64::from(k) + 1)) * &(h * h);
    }
    c * c <= bound
}

/// The constants read off the pivots reach the size the comment above `two_var_domains`
/// bounds: `x_i == H·x_{i+1} + H` for `i < 6` and `x_6 == H`, `H = 2^40`, so the form of
/// `x_0` is the constant `c = H + H² + … + H^7`, over 240 bits (past `i128`), found by seven
/// eliminations. `x_0` gets `{c}`; `c` is within the bound for `k = 7` and at least `H^7`, so
/// within a factor `8^4 · H` of it. Negative control: `c · H²` is past the bound, so the test
/// of the bound can fail.
#[test]
fn back_substituted_constants_reach_the_size_bound() {
    let h = Int::from(1_i64 << 40);
    let n = 6;
    let mut parts: Vec<Formula> = (0..n)
        .map(|i| {
            con_eq(
                x(i),
                x(i + 1).times(h.clone()).plus(&Lin::constant(h.clone())),
            )
        })
        .collect();
    parts.push(con_eq(x(n), Lin::constant(h.clone())));
    parts.push(con_ge(x(n), Lin::default()));
    let mut c = h.clone();
    let mut power = h.clone();
    for _ in 0..n {
        c = &(&c * &h) + &h;
        power = &power * &h;
    }
    let got = domains(&Formula::and(parts), &[xa(0)]);
    assert_eq!(got, vec![IntervalSet::point(Num::from(&c))]);
    let k = n as u32 + 1;
    assert!(within_size_bound(&c, k, &h));
    assert!(c >= power, "c reaches H^{k}");
    assert!(!within_size_bound(&(&c * &(&h * &h)), k, &h));
}

/// Negative control: `x0 == 2·y`, `0 <= y <= 3`. The form of `x0` has coefficient 2, so it is
/// not read as a moved copy of `y` (which would give `0..=6`, wrong: `x0` is even); the old
/// elimination with `x0` kept meets a holed strip and `two_var_domains` answers nothing, as
/// before.
#[test]
fn a_form_with_a_coefficient_of_two_is_not_read() {
    let parts = vec![
        con_eq(x(0), x(1).times(2)),
        con_ge(x(1), Lin::default()),
        con_ge(Lin::constant(3), x(1)),
    ];
    let f = Formula::and(parts);
    assert!(two_var_domains(&f, &[xa(0)]).is_none());
    assert!(two_var_domains(&f, &[xa(0), xa(1)]).is_none());
}

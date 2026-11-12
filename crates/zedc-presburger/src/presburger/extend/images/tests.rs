//! Tests of the scalar images. They are in their own file, not inline in
//! images.rs, since they call `decide_defined` and `Summaries` from
//! extend.rs: inline they would make an import cycle (step S.1f).

use std::collections::{BTreeMap, BTreeSet};

use super::super::super::formula::{Factor, Shared};
use super::super::{Summaries, decide_defined};
use super::*;

#[test]
fn descriptors_agree_with_explicit_residue_images() {
    let mut checked = 0;
    let mut wrong_all = 0;
    for m in 1i64..=41 {
        let modulus = Arc::new(Int::from(m));
        let mut skipping: BTreeSet<i64> = (0..m).collect();
        let mut doubling = skipping.clone();
        let mut exponent = 0;
        for k in 0..=2 * m {
            let skip = Image::Skipping(Arc::clone(&modulus), Int::from(k));
            let power = Image::Power(exponent);
            for c in -2 * m..=2 * m {
                let r = c.rem_euclid(m);
                assert_eq!(
                    skip.contains(&Int::from(c)),
                    skipping.contains(&r),
                    "skip M={m}, k={k}, c={c}"
                );
                assert_eq!(
                    power.contains(&Int::from(c)),
                    doubling.contains(&r),
                    "double M={m}, k={k}, c={c}"
                );
                wrong_all +=
                    usize::from(!skipping.contains(&r)) + usize::from(!doubling.contains(&r));
                checked += 2;
            }
            skipping = skipping
                .into_iter()
                .map(|r| (r + if r == 0 { 1 } else { 2 }) % m)
                .collect();
            doubling = doubling.into_iter().map(|r| 2 * r % m).collect();
            let z = m.trailing_zeros() as usize;
            if exponent < z {
                exponent += 1;
            }
        }
    }
    assert!(wrong_all > 0);
    eprintln!("scalar descriptor checks={checked}, false all-integers control={wrong_all}");
}

fn chain(m: i64, count: usize, skip: bool) -> (Vec<Formula>, Vec<Atom>) {
    let mut defs = Vec::new();
    let mut outputs = Vec::new();
    let mut input = Lin::atom(Atom::Sym("x".into()));
    for _ in 0..count {
        let n = defs.len() as u32;
        let q = Lin::atom(Atom::Aux(n));
        let r = Lin::atom(Atom::Aux(n + 1));
        let pair = Formula::And(Shared::new(vec![
            Formula::Con(Con::eq(&input, &q.times(m).plus(&r))),
            Formula::Con(Con::ge(&r, &Lin::constant(0))),
            Formula::Con(Con::ge(&Lin::constant(m - 1), &r)),
        ]));
        defs.push(pair.clone());
        defs.push(pair);
        let output = Atom::Aux(n + 2);
        let out = Lin::atom(output.clone());
        let f = if skip {
            let guard = Formula::Con(Con::eq(&r, &Lin::constant(0)));
            Formula::Or(Shared::new(vec![
                Formula::and(vec![
                    guard.clone(),
                    Formula::Con(Con::eq(&out, &input.plus(&Lin::constant(1)))),
                ]),
                Formula::and(vec![
                    Formula::negate(guard),
                    Formula::Con(Con::eq(&out, &input.plus(&Lin::constant(2)))),
                ]),
            ]))
        } else {
            Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                &out,
                &input.plus(&r),
            ))]))
        };
        defs.push(f);
        outputs.push(output);
        input = out;
    }
    (defs, outputs)
}

#[test]
fn images_are_scalar_only_and_do_not_forget_correlations() {
    for skip in [false, true] {
        for m in [2, 7, 8, 1000, 1_000_000_007] {
            let (defs, outputs) = chain(m, 7, skip);
            let def = |n: u32| defs[n as usize].clone();
            let mut images = ScalarImages::default();
            for (i, a) in outputs.iter().enumerate() {
                for c in -17i64..=17 {
                    let q = Formula::Con(Con::eq(&Lin::atom(a.clone()), &Lin::constant(c)));
                    let mut predecessors = BTreeSet::from([c]);
                    for _ in 0..=i {
                        let mut next = BTreeSet::new();
                        for y in predecessors {
                            if skip {
                                if (y - 1).rem_euclid(m) == 0 {
                                    next.insert(y - 1);
                                }
                                if (y - 2).rem_euclid(m) != 0 {
                                    next.insert(y - 2);
                                }
                            } else {
                                let top = y.div_euclid(m);
                                for q in [top - 1, top] {
                                    let twice_r = y - m * q;
                                    if twice_r >= 0 && twice_r <= 2 * (m - 1) && twice_r % 2 == 0 {
                                        next.insert(m * q + twice_r / 2);
                                    }
                                }
                            }
                        }
                        predecessors = next;
                    }
                    let expected = !predecessors.is_empty();
                    assert_eq!(
                        images.answer(&q, &def),
                        Some(expected),
                        "M={m}, k={}, skip={skip}, c={c}",
                        i + 1
                    );
                    let joint = Formula::and(vec![
                        q,
                        Formula::Con(Con::eq(
                            &Lin::atom(Atom::Sym("x".into())),
                            &Lin::constant(0),
                        )),
                    ]);
                    assert_eq!(images.answer(&joint, &def), None);
                }
            }
        }
    }
    // The guard D|M is necessary: the image of 2Z under h+h mod 3 is not a lattice.
    let r = Atom::Aux(1);
    let h = Atom::Aux(0);
    let mut images = ScalarImages::default();
    images.by.insert(
        h.clone(),
        Fact {
            image: Some(Image::Power(1)),
            division: None,
        },
    );
    images.by.insert(
        r.clone(),
        Fact {
            image: None,
            division: Some((false, Lin::atom(h.clone()), Arc::new(Int::from(3)))),
        },
    );
    assert!(
        images
            .linear(&Lin::atom(h).plus(&Lin::atom(r)), &|_| Formula::bottom())
            .is_none()
    );
}

#[test]
fn partial_and_product_definitions_do_not_get_scalar_images() {
    let x = Lin::atom(Atom::Sym("x".into()));
    let v = Atom::Aux(0);
    let partial = Formula::And(Shared::new(vec![
        Formula::Con(Con::eq(&Lin::atom(v), &x)),
        Formula::Con(Con::ge(&x, &Lin::constant(0))),
    ]));
    let question = Formula::Con(Con::eq(&Lin::atom(Atom::Aux(0)), &Lin::constant(9)));
    assert_eq!(
        ScalarImages::default().answer(&question, &|_| partial.clone()),
        None
    );
    let (defs, _) = chain(7, 1, true);
    let def = |n: u32| defs[n as usize].clone();
    assert!(
        ScalarImages::default()
            .answer(
                &Formula::Con(Con::eq(&Lin::atom(Atom::Aux(2)), &Lin::constant(1))),
                &def
            )
            .is_some()
    );
    let product = Lin::atom(Atom::Product(
        Factor::Sym("x".into()),
        Factor::Sym("y".into()),
    ));
    let f = Formula::And(Shared::new(vec![Formula::Con(Con::eq(
        &Lin::atom(Atom::Aux(0)),
        &product,
    ))]));
    assert_eq!(
        ScalarImages::default().answer(&question, &|_| f.clone()),
        None
    );
}

#[test]
fn orbit_questions_keep_the_original_input_residue() {
    let mut checked = 0;
    for m in [7i64, 1000, 1_000_000_007] {
        for skip in [false, true] {
            let (defs, outputs) = chain(m, 640, skip);
            let def = |n: u32| defs[n as usize].clone();
            let mut images = ScalarImages::default();
            let mut values = BTreeMap::from([(0i64, 0i64), (3, 3), (m - 1, m - 1)]);
            for output in outputs {
                for (&r, y) in &mut values {
                    *y = if skip {
                        *y + if y.rem_euclid(m) == 0 { 1 } else { 2 }
                    } else {
                        *y + y.rem_euclid(m)
                    };
                    // Keep the independently evaluated orbit modulo M, avoiding
                    // overflow in this native test as well as in the certificate.
                    *y = y.rem_euclid(m);
                    for c in [0i64, 9] {
                        let q = Formula::and(vec![
                            Formula::Con(Con::eq(&Lin::atom(output.clone()), &Lin::constant(c))),
                            Formula::Con(Con::eq(&Lin::atom(Atom::Aux(1)), &Lin::constant(r))),
                        ]);
                        assert_eq!(
                            images.answer(&q, &def),
                            Some(*y == c.rem_euclid(m)),
                            "M={m}, skip={skip}, r={r}, c={c}"
                        );
                        assert_eq!(images.answer(&Formula::negate(q), &def), Some(true));
                        checked += 2;
                    }
                }
            }
        }
    }
    eprintln!("exact joint orbit checks={checked}");
}
#[test]
fn monotone_clamp_images_match_independent_inverse_cuts() {
    let mut checked = 0;
    for a in [1i128, 2, 5, 7] {
        for b in [3i128, 7, 11] {
            if a == b {
                continue;
            }
            for offset in [-9i128, 0, 4] {
                for k in 1..=8 {
                    let basis = ClampBasis {
                        axis: Atom::Sym("x".into()),
                        a: Int::from(a),
                        b: Int::from(b),
                        constant: Int::from(offset),
                    };
                    let value = |x: i128| {
                        let bound = x.div_euclid(a) + x.div_euclid(b) + offset;
                        let mut h = x;
                        for _ in 0..k {
                            h = h.div_euclid(2).max(bound);
                        }
                        h
                    };
                    let cut = |c: i128| {
                        let mut lo = -1i128;
                        let mut hi = 1i128;
                        while value(lo) >= c {
                            lo *= 2;
                        }
                        while value(hi) < c {
                            hi *= 2;
                        }
                        while hi - lo > 1 {
                            let mid = (hi + lo).div_euclid(2);
                            if value(mid) >= c {
                                hi = mid;
                            } else {
                                lo = mid;
                            }
                        }
                        hi
                    };
                    for c in -30i128..=30 {
                        assert_eq!(
                            basis.contains(&Int::from(c), k),
                            cut(c) < cut(c + 1),
                            "a={a} b={b} C={offset} k={k} c={c}"
                        );
                        checked += 1;
                    }
                }
            }
        }
    }
    eprintln!("two-quotient monotone-clamp image comparisons={checked}");
}

#[test]
fn a_changed_modulus_requires_the_divisibility_guard() {
    let (mut defs, outputs) = chain(2, 1, false);
    let input = Lin::atom(outputs[0].clone());
    let n = defs.len() as u32;
    let q = Lin::atom(Atom::Aux(n));
    let r = Lin::atom(Atom::Aux(n + 1));
    let pair = Formula::And(Shared::new(vec![
        Formula::Con(Con::eq(&input, &q.times(3).plus(&r))),
        Formula::Con(Con::ge(&r, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(2), &r)),
    ]));
    defs.push(pair.clone());
    defs.push(pair);
    let output = Atom::Aux(n + 2);
    defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
        &Lin::atom(output.clone()),
        &input.plus(&r),
    ))])));
    let def = |n: u32| defs[n as usize].clone();
    let mut images = ScalarImages::default();
    for c in -12i64..=12 {
        let query = Formula::Con(Con::eq(&Lin::atom(output.clone()), &Lin::constant(c)));
        assert_eq!(images.answer(&query, &def), None);
        assert_eq!(
            decide_defined(&mut Summaries::default(), query, &def),
            Ok([0, 4, 5].contains(&c.rem_euclid(6)))
        );
    }
}
#[test]
fn orbit_questions_keep_previous_and_future_residues_and_the_earlier_image() {
    let mut checked = 0;
    for m in [7i64, 1000, 1_000_000_007] {
        for skip in [false, true] {
            let (defs, outputs) = chain(m, 16, skip);
            let def = |n: u32| defs[n as usize].clone();
            let mut images = ScalarImages::default();
            let step = |h: i64| {
                if skip {
                    h + if h.rem_euclid(m) == 0 { 1 } else { 2 }
                } else {
                    h + h.rem_euclid(m)
                }
            };
            for k in [0usize, 3, 7, 14] {
                for c in [-1i64, 0, 2, 5, 6, 9] {
                    let mut pre = BTreeSet::from([c]);
                    for _ in 0..=k {
                        let mut next = BTreeSet::new();
                        for y in pre {
                            if skip {
                                if (y - 1).rem_euclid(m) == 0 {
                                    next.insert(y - 1);
                                }
                                if (y - 2).rem_euclid(m) != 0 {
                                    next.insert(y - 2);
                                }
                            } else {
                                let q = y.div_euclid(m);
                                for quotient in [q - 1, q] {
                                    let twice = y - m * quotient;
                                    if twice >= 0 && twice <= 2 * (m - 1) && twice % 2 == 0 {
                                        next.insert(m * quotient + twice / 2);
                                    }
                                }
                            }
                        }
                        pre = next;
                    }
                    for j in [0usize, 2, 7, 14] {
                        for r in [0i64, 3, m - 1] {
                            let expected = pre.iter().any(|x| {
                                let mut h = *x;
                                for _ in 0..=j {
                                    h = step(h);
                                }
                                h.rem_euclid(m) == r
                            });
                            let remainder = Atom::Aux((3 * (j + 1) + 1) as u32);
                            let query = Formula::and(vec![
                                Formula::Con(Con::eq(
                                    &Lin::atom(outputs[k].clone()),
                                    &Lin::constant(c),
                                )),
                                Formula::Con(Con::eq(&Lin::atom(remainder), &Lin::constant(r))),
                            ]);
                            assert_eq!(
                                images.answer(&query, &def),
                                Some(expected),
                                "m={m} skip={skip} k={k} j={j} c={c} r={r}"
                            );
                            checked += 1;
                        }
                    }
                }
            }
        }
    }
    for skip in [false, true] {
        let (defs, outputs) = chain(1000, 640, skip);
        let def = |n: u32| defs[n as usize].clone();
        let (c, r) = if skip { (1, 0) } else { (6, 3) };
        let query = Formula::and(vec![
            Formula::Con(Con::eq(&Lin::atom(outputs[639].clone()), &Lin::constant(c))),
            Formula::Con(Con::eq(
                &Lin::atom(Atom::Aux(3 * 639 + 1)),
                &Lin::constant(r),
            )),
        ]);
        assert_eq!(ScalarImages::default().answer(&query, &def), Some(false));
    }
    eprintln!("relative-period/earlier-image checks={checked}, plus two depth-640 exclusions");
}
#[test]
fn scalar_images_keep_moduli_beyond_signed_i128_and_saturate_the_exponent() {
    let boundary = &Int::from(i128::MAX) + &Int::ONE;
    let mut checked = 0;
    for odd in [false, true] {
        let modulus = if odd {
            &boundary + &Int::ONE
        } else {
            boundary.clone()
        };
        let mut defs = Vec::new();
        let mut outputs = Vec::new();
        let mut input = Lin::atom(Atom::Sym("x".into()));
        for _ in 0..130 {
            let n = defs.len() as u32;
            let q = Lin::atom(Atom::Aux(n));
            let r = Lin::atom(Atom::Aux(n + 1));
            let pair = Formula::And(Shared::new(vec![
                Formula::Con(Con::eq(&input, &q.times(modulus.clone()).plus(&r))),
                Formula::Con(Con::ge(&r, &Lin::constant(0))),
                Formula::Con(Con::ge(&Lin::constant(&modulus - &Int::ONE), &r)),
            ]));
            defs.push(pair.clone());
            defs.push(pair);
            let output = Atom::Aux(n + 2);
            defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                &Lin::atom(output.clone()),
                &input.plus(&r),
            ))])));
            input = Lin::atom(output.clone());
            outputs.push(output);
        }
        let def = |n: u32| defs[n as usize].clone();
        let mut images = ScalarImages::default();
        let mut divisor = Int::ONE;
        for (k, a) in outputs.iter().enumerate() {
            if k < 127 {
                divisor = &divisor * &Int::from(2);
            }
            for c in [
                Int::ZERO,
                boundary.clone(),
                -&boundary,
                &boundary + &Int::ONE,
                -&(&boundary + &Int::ONE),
                &boundary + &Int::from(256),
            ] {
                let query = Formula::Con(Con::eq(&Lin::atom(a.clone()), &Lin::constant(c.clone())));
                assert_eq!(
                    images.answer(&query, &def),
                    Some(odd || c.mod_floor(&divisor).is_zero()),
                    "odd={odd} k={k} c={c}"
                );
                checked += 1;
            }
        }
    }
    eprintln!("beyond-i128 scalar image checks={checked}, moduli 2^127 and 2^127+1, depth 130");
}

#[test]
fn prefix_record_certificates_have_concrete_witnesses_for_signed_remainders() {
    fn pair(defs: &mut Vec<Formula>, arg: &Lin, m: i64) -> (Lin, Lin) {
        let n = defs.len() as u32;
        let q = Lin::atom(Atom::Aux(n));
        let r = Lin::atom(Atom::Aux(n + 1));
        let f = Formula::And(Shared::new(vec![
            Formula::Con(Con::eq(arg, &q.times(m).plus(&r))),
            Formula::Con(Con::ge(&r, &Lin::constant(0))),
            Formula::Con(Con::ge(&Lin::constant(m - 1), &r)),
        ]));
        defs.extend([f.clone(), f]);
        (q, r)
    }
    let mut checked = 0;
    for (m, d, w, c) in [
        (5i64, 7i64, 1i64, -9i64),
        (7, 7, -3, 4),
        (3, 11, 4, -2),
        (1, 1, 9, 0),
        (2, 3, -1, 0),
    ] {
        let mut defs = Vec::new();
        let x = Lin::atom(Atom::Sym("x".into()));
        let (_, r) = pair(&mut defs, &x, m);
        let (q, _) = pair(&mut defs, &x, d);
        let b = r.times(w).plus(&q).plus(&Lin::constant(c));
        let mut previous = x.clone();
        let mut outputs = Vec::new();
        for _ in 0..6 {
            let (half, _) = pair(&mut defs, &previous, 2);
            let out = Atom::Aux(defs.len() as u32);
            let guard = Formula::Con(Con::ge(&half, &b));
            let f = Formula::Or(Shared::new(vec![
                Formula::and(vec![
                    guard.clone(),
                    Formula::Con(Con::eq(&Lin::atom(out.clone()), &half)),
                ]),
                Formula::and(vec![
                    Formula::negate(guard),
                    Formula::Con(Con::eq(&Lin::atom(out.clone()), &b)),
                ]),
            ]));
            defs.push(f);
            previous = Lin::atom(out.clone());
            outputs.push(out);
        }
        let def = |n: u32| defs[n as usize].clone();
        let mut images = ScalarImages::default();
        let radius = d * (64 * (8 + c.abs() + 3) + w.abs() * (m - 1) + 3);
        let mut witnesses: Vec<BTreeSet<i64>> = vec![BTreeSet::new(); 6];
        for x in -radius..=radius {
            let bound = w * x.rem_euclid(m) + x.div_euclid(d) + c;
            let mut h = x;
            for ws in &mut witnesses {
                h = h.div_euclid(2).max(bound);
                if (-8..=8).contains(&h) {
                    ws.insert(h);
                }
            }
        }
        for (k, out) in outputs.into_iter().enumerate() {
            for target in -8..=8 {
                assert!(
                    witnesses[k].contains(&target),
                    "m={m},d={d},w={w},c={c},k={k},target={target}"
                );
                let query = Formula::Con(Con::eq(&Lin::atom(out.clone()), &Lin::constant(target)));
                assert_eq!(images.answer(&query, &def), Some(true));
                checked += 1;
            }
        }
    }
    eprintln!(
        "prefix-record concrete witness checks={checked}, five signed/modulus configurations, depth 6"
    );
}

#[test]
fn a_condition_cannot_combine_independent_scalar_images_into_a_joint_image() {
    let x = Lin::atom(Atom::Sym("x".into()));
    let out = Lin::atom(Atom::Aux(0));
    let guard = Formula::Con(Con::ge(&x, &Lin::constant(0)));
    let f = Formula::Or(Shared::new(vec![
        Formula::and(vec![
            guard.clone(),
            Formula::Con(Con::eq(&out, &x.plus(&Lin::constant(100)))),
        ]),
        Formula::and(vec![
            Formula::negate(guard),
            Formula::Con(Con::eq(&out, &x)),
        ]),
    ]));
    let def = |_| f.clone();
    let mut images = ScalarImages::default();
    for c in [9i64, -1, 100] {
        let query = Formula::Con(Con::eq(&out, &Lin::constant(c)));
        let scalar = images.answer(&query, &def);
        if let Some(answer) = scalar {
            assert_eq!(
                answer,
                !(0..100).contains(&c),
                "an accepted certificate must be exact"
            );
        }
        assert_eq!(scalar, None);
        assert_eq!(
            decide_defined(&mut Summaries::default(), query, &def),
            Ok(!(0..100).contains(&c))
        );
    }
}

/// One step of a residue-map chain: guards (s, p, w, c) tried in order, then the default
/// (p, w, c); a branch's value is p h + w (h mod m) + c.
#[derive(Clone)]
struct MapStep {
    guards: Vec<(i64, i64, i64, i64)>,
    default: (i64, i64, i64),
}

impl MapStep {
    fn value(&self, h: i64, m: i64) -> i64 {
        let r = h.rem_euclid(m);
        let (p, w, c) = self
            .guards
            .iter()
            .find(|g| g.0 == r)
            .map_or(self.default, |&(_, p, w, c)| (p, w, c));
        p * h + w * r + c
    }

    /// Pushes the definitions of this step on `input` and gives its output: the remainder
    /// pair, then one choice for each guard from the innermost out, as the front end writes
    /// a nested if.
    fn push(&self, defs: &mut Vec<Formula>, input: &Lin, m: i64) -> Atom {
        let n = defs.len() as u32;
        let q = Lin::atom(Atom::Aux(n));
        let r = Lin::atom(Atom::Aux(n + 1));
        let pair = Formula::And(Shared::new(vec![
            Formula::Con(Con::eq(input, &q.times(m).plus(&r))),
            Formula::Con(Con::ge(&r, &Lin::constant(0))),
            Formula::Con(Con::ge(&Lin::constant(m - 1), &r)),
        ]));
        defs.push(pair.clone());
        defs.push(pair);
        let arm = |p: i64, w: i64, c: i64| input.times(p).plus(&r.times(w)).plus(&Lin::constant(c));
        let (p, w, c) = self.default;
        let mut value = arm(p, w, c);
        if self.guards.is_empty() {
            let out = Atom::Aux(defs.len() as u32);
            defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                &Lin::atom(out.clone()),
                &value,
            ))])));
            return out;
        }
        let mut out = None;
        for &(s, p, w, c) in self.guards.iter().rev() {
            let o = Atom::Aux(defs.len() as u32);
            let ol = Lin::atom(o.clone());
            let guard = Formula::Con(Con::eq(&r, &Lin::constant(s)));
            defs.push(Formula::Or(Shared::new(vec![
                Formula::and(vec![
                    guard.clone(),
                    Formula::Con(Con::eq(&ol, &arm(p, w, c))),
                ]),
                Formula::and(vec![
                    Formula::negate(guard),
                    Formula::Con(Con::eq(&ol, &value)),
                ]),
            ])));
            value = ol;
            out = Some(o);
        }
        out.unwrap()
    }
}

/// The definitions and outputs of a chain of steps from x.
fn map_chain(steps: &[MapStep], m: i64) -> (Vec<Formula>, Vec<Atom>) {
    let mut defs = Vec::new();
    let mut outputs = Vec::new();
    let mut input = Lin::atom(Atom::Sym("x".into()));
    for step in steps {
        let out = step.push(&mut defs, &input, m);
        input = Lin::atom(out.clone());
        outputs.push(out);
    }
    (defs, outputs)
}

#[test]
fn residue_map_images_agree_with_the_values_of_a_window_of_inputs() {
    // I49: chains of nested choices on h mod m with branch values +-h + w (h mod m) + c.
    // Each answer the scalar images give equals the one read from the values of every input
    // in a window wide enough that no input outside it reaches the questions asked; where
    // no step is the skipping step, every question is answered, whether or not the default
    // multipliers p + w are units mod m.
    let mut rng = 0x5eed_u64;
    let mut next = |lo: i64, hi: i64| {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        lo + (rng % (hi - lo + 1) as u64) as i64
    };
    let (mut answered, mut required, mut found, mut trials) = (0, 0, 0, 0);
    for _ in 0..1500 {
        let m = next(1, 36);
        let mut steps = Vec::new();
        for _ in 0..next(1, 6) {
            let branch = |next: &mut dyn FnMut(i64, i64) -> i64| {
                (
                    if next(0, 1) == 0 { 1 } else { -1 },
                    next(-3, 3),
                    next(-2 * m, 2 * m),
                )
            };
            let guards = (0..next(0, 3))
                .map(|_| {
                    let (p, w, c) = branch(&mut next);
                    (next(-1, m), p, w, c)
                })
                .collect();
            steps.push(MapStep {
                guards,
                default: branch(&mut next),
            });
        }
        let (defs, outputs) = map_chain(&steps, m);
        let def = |n: u32| defs[n as usize].clone();
        let mut images = ScalarImages::default();
        // Each step moves a value by at most 5 m + 2 m from +-h.
        let reach = 7 * m * steps.len() as i64;
        let window = 3 * m + reach + 1;
        let mut values: Vec<i64> = (-window..=window).collect();
        let mut covered = true;
        for (i, (step, out)) in steps.iter().zip(&outputs).enumerate() {
            values = values.iter().map(|&h| step.value(h, m)).collect();
            let skipping = step.guards.first().is_some_and(|g| *g == (0, 1, 0, 1))
                && step.default == (1, 0, 2);
            covered &= !skipping;
            let seen: BTreeSet<i64> = values.iter().copied().collect();
            for c in -3 * m..=3 * m {
                let q = Formula::Con(Con::eq(&Lin::atom(out.clone()), &Lin::constant(c)));
                let got = images.answer(&q, &def);
                let expected = seen.contains(&c);
                trials += 1;
                found += usize::from(expected);
                if let Some(got) = got {
                    answered += 1;
                    assert_eq!(got, expected, "m={m} step {i} c={c}");
                } else {
                    assert!(!covered, "m={m} step {i} c={c} unanswered");
                }
                required += usize::from(covered);
            }
        }
    }
    assert!(found > 0 && found < trials);
    assert!(required > trials / 3, "{required} of {trials}");
    eprintln!(
        "residue map answers={answered} required={required} trials={trials} in image={found}"
    );
}

#[test]
fn residue_map_images_with_mixed_multipliers_agree_with_the_image_of_every_residue() {
    // LOAD-max-div-unsolved: chains h + w (h mod m) + c at moduli with two to four primes,
    // whose default multipliers 1 + w are units, divisible by some primes of m, or by others
    // at later steps, with exceptions placed half the time at a residue of the current image.
    // Since every step commutes with h + m, the image is that of Z_m under the residue map,
    // computed here residue by residue; every question must be answered, and equal it.
    let mut rng = 0x10ad_u64;
    let mut next = |lo: i64, hi: i64| {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        lo + (rng % (hi - lo + 1) as u64) as i64
    };
    let multipliers = [1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15];
    for chain in 0..48 {
        let m = [360, 1008, 5400, 7056][chain % 4];
        let mut image: Vec<i64> = (0..m).collect();
        let mut steps = Vec::new();
        let mut images = Vec::new();
        for _ in 0..24 {
            let u = multipliers[next(0, multipliers.len() as i64 - 1) as usize];
            let guards = (0..next(0, 2))
                .map(|_| {
                    let s = if next(0, 1) == 0 {
                        image[next(0, image.len() as i64 - 1) as usize]
                    } else {
                        next(0, m - 1)
                    };
                    (s, 1, next(-3, 3), next(-2 * m, 2 * m))
                })
                .collect();
            let step = MapStep {
                guards,
                default: (1, u - 1, next(-2 * m, 2 * m)),
            };
            let set: BTreeSet<i64> = image
                .iter()
                .map(|&r| step.value(r, m).rem_euclid(m))
                .collect();
            image = set.iter().copied().collect();
            images.push(set);
            steps.push(step);
        }
        let (defs, outputs) = map_chain(&steps, m);
        let def = |n: u32| defs[n as usize].clone();
        let mut answers = ScalarImages::default();
        for (i, (set, out)) in images.iter().zip(&outputs).enumerate() {
            let members: Vec<i64> = set.iter().copied().collect();
            for k in 0..40 {
                let c = if k % 2 == 0 {
                    members[next(0, members.len() as i64 - 1) as usize] + m * next(-2, 2)
                } else {
                    next(-2 * m, 2 * m)
                };
                let q = Formula::Con(Con::eq(&Lin::atom(out.clone()), &Lin::constant(c)));
                let got = answers.answer(&q, &def);
                let expected = set.contains(&c.rem_euclid(m));
                assert_eq!(got, Some(expected), "chain {chain} m={m} step {i} c={c}");
            }
        }
    }
}

#[test]
fn residue_map_images_at_a_large_modulus_agree_with_a_backward_search() {
    // I49 at m = 10^9 + 7: the image of k steps, from all integers, holds y iff some residue
    // reaches y in k steps backward; a backward step from y keeps u^-1 (y - c) unless it is
    // an exception and every exception s with value y. Searched over a few hundred residues.
    let m = 1_000_000_007i64;
    let steps = [
        MapStep {
            guards: vec![(0, 1, 0, 1), (3, 1, 0, 2)],
            default: (1, 0, 3),
        },
        MapStep {
            guards: vec![(2, 1, 0, 5)],
            default: (1, 2, 1),
        },
        MapStep {
            guards: vec![(5, -1, 0, 4), (6, 1, 1, 0)],
            default: (1, 0, 3),
        },
    ];
    let k = 90;
    let chain: Vec<MapStep> = (0..k).map(|i| steps[i % steps.len()].clone()).collect();
    let (defs, outputs) = map_chain(&chain, m);
    let def = |n: u32| defs[n as usize].clone();
    let mut images = ScalarImages::default();
    let modulus = Int::from(m);
    let back = |step: &MapStep, y: i64| -> Vec<i64> {
        let (p, w, c) = step.default;
        let (inv, _) = congruence(&Int::from(p + w), &Int::ONE, &modulus).unwrap();
        let r = (&inv * &Int::from(y - c))
            .mod_floor(&modulus)
            .to_i128()
            .unwrap() as i64;
        let mut out: Vec<i64> = step
            .guards
            .iter()
            .filter(|g| g.0 >= 0 && g.0 < m && step.value(g.0, m).rem_euclid(m) == y)
            .map(|g| g.0)
            .collect();
        if !step.guards.iter().any(|g| g.0 == r) {
            out.push(r);
        }
        out
    };
    let mut missing = 0;
    for (i, out) in outputs.iter().enumerate() {
        for y in (0..40).chain((m - 40)..m).chain([m / 2]) {
            let mut level = vec![y];
            for step in chain[..=i].iter().rev() {
                let mut prev: Vec<i64> = level.iter().flat_map(|&v| back(step, v)).collect();
                prev.sort();
                prev.dedup();
                level = prev;
            }
            let expected = !level.is_empty();
            missing += usize::from(!expected);
            for c in [y, y - m, y + 3 * m] {
                let q = Formula::Con(Con::eq(&Lin::atom(out.clone()), &Lin::constant(c)));
                assert_eq!(images.answer(&q, &def), Some(expected), "step {i} y={y}");
            }
        }
    }
    assert!(missing > 0);
}

/// A step of shifts: guards `h mod m op s` nested to any depth, leaves h + c. The ops are
/// <, <=, >, >=, ==, != by 0 to 5.
#[derive(Clone)]
enum ShiftStep {
    Leaf(i64),
    If(u8, i64, Box<ShiftStep>, Box<ShiftStep>),
}

impl ShiftStep {
    fn random(next: &mut dyn FnMut(i64, i64) -> i64, m: i64, depth: u32) -> ShiftStep {
        if depth == 0 || next(0, 2) == 0 {
            return ShiftStep::Leaf(next(-2 * m, 2 * m));
        }
        ShiftStep::If(
            next(0, 5) as u8,
            next(-1, m),
            Box::new(Self::random(next, m, depth - 1)),
            Box::new(Self::random(next, m, depth - 1)),
        )
    }

    fn residue(&self, r: i64, m: i64) -> i64 {
        match self {
            ShiftStep::Leaf(c) => (r + c).rem_euclid(m),
            ShiftStep::If(op, s, yes, no) => {
                let holds = [r < *s, r <= *s, r > *s, r >= *s, r == *s, r != *s][*op as usize];
                if holds { yes } else { no }.residue(r, m)
            }
        }
    }

    /// Pushes the definitions of this step's choices below the remainder pair, as the front
    /// end writes a nested if: one definition for each if, its branches read as values.
    fn value(&self, defs: &mut Vec<Formula>, h: &Lin, r: &Lin) -> Lin {
        match self {
            ShiftStep::Leaf(c) => h.plus(&Lin::constant(*c)),
            ShiftStep::If(op, s, yes, no) => {
                let (yes, no) = (yes.value(defs, h, r), no.value(defs, h, r));
                let s = Lin::constant(*s);
                let one = Lin::constant(1);
                let guard = match op {
                    0 => Formula::Con(Con::ge(&s.minus(&one), r)),
                    1 => Formula::Con(Con::ge(&s, r)),
                    2 => Formula::Con(Con::ge(r, &s.plus(&one))),
                    3 => Formula::Con(Con::ge(r, &s)),
                    4 => Formula::Con(Con::eq(r, &s)),
                    _ => Formula::negate(Formula::Con(Con::eq(r, &s))),
                };
                let out = Lin::atom(Atom::Aux(defs.len() as u32));
                defs.push(Formula::Or(Shared::new(vec![
                    Formula::and(vec![guard.clone(), Formula::Con(Con::eq(&out, &yes))]),
                    Formula::and(vec![
                        Formula::negate(guard),
                        Formula::Con(Con::eq(&out, &no)),
                    ]),
                ])));
                out
            }
        }
    }
}

/// The definitions and outputs of a chain of shift steps from x; a step that is a lone leaf
/// is given the guard `h mod m == -1`, which never holds.
fn shift_chain(steps: &[ShiftStep], m: i64) -> (Vec<Formula>, Vec<Atom>) {
    let mut defs = Vec::new();
    let mut outputs = Vec::new();
    let mut input = Lin::atom(Atom::Sym("x".into()));
    for step in steps {
        let n = defs.len() as u32;
        let q = Lin::atom(Atom::Aux(n));
        let r = Lin::atom(Atom::Aux(n + 1));
        let pair = Formula::And(Shared::new(vec![
            Formula::Con(Con::eq(&input, &q.times(m).plus(&r))),
            Formula::Con(Con::ge(&r, &Lin::constant(0))),
            Formula::Con(Con::ge(&Lin::constant(m - 1), &r)),
        ]));
        defs.push(pair.clone());
        defs.push(pair);
        let step = match step {
            ShiftStep::Leaf(c) => ShiftStep::If(
                4,
                -1,
                Box::new(ShiftStep::Leaf(*c)),
                Box::new(ShiftStep::Leaf(*c)),
            ),
            s => s.clone(),
        };
        let value = step.value(&mut defs, &input, &r);
        let out = lone_atom(&value).unwrap().clone();
        input = value;
        outputs.push(out);
    }
    (defs, outputs)
}

#[test]
fn shift_chain_images_agree_with_the_image_of_every_residue() {
    // LOAD-max-div-unsolved: chains of nested guards on h mod m with every branch h + c, a
    // pattern of one to four steps repeated, broken now and then by another step, so that
    // repeated steps, whose tree nodes share relative ends, meet steps that differ. Each step
    // commutes with h + m, so the image is that of Z_m, computed residue by residue; every
    // question must be answered, and equal it.
    let mut rng = 0x5_1f7_u64;
    let mut next = |lo: i64, hi: i64| {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        lo + (rng % (hi - lo + 1) as u64) as i64
    };
    let (mut inside, mut asked) = (0, 0);
    for chain in 0..400 {
        let m = next(1, 40);
        let depth = [1, 2, 3][chain % 3];
        let pattern: Vec<ShiftStep> = (0..next(1, 4))
            .map(|_| ShiftStep::random(&mut next, m, depth))
            .collect();
        let steps: Vec<ShiftStep> = (0..48)
            .map(|i| {
                if next(0, 15) == 0 {
                    ShiftStep::random(&mut next, m, depth)
                } else {
                    pattern[i % pattern.len()].clone()
                }
            })
            .collect();
        let (defs, outputs) = shift_chain(&steps, m);
        let def = |n: u32| defs[n as usize].clone();
        let mut images = ScalarImages::default();
        let mut image: BTreeSet<i64> = (0..m).collect();
        let order: Vec<usize> = if chain % 2 == 0 {
            (0..steps.len()).collect()
        } else {
            (0..steps.len()).rev().collect()
        };
        let mut sets = Vec::new();
        for step in &steps {
            image = image.iter().map(|&r| step.residue(r, m)).collect();
            sets.push(image.clone());
        }
        for i in order {
            for c in -m..2 * m {
                let q = Formula::Con(Con::eq(&Lin::atom(outputs[i].clone()), &Lin::constant(c)));
                let expected = sets[i].contains(&c.rem_euclid(m));
                assert_eq!(
                    images.answer(&q, &def),
                    Some(expected),
                    "chain {chain} m={m} step {i} c={c}"
                );
                inside += usize::from(expected);
                asked += 1;
            }
        }
    }
    assert!(inside > 0 && inside < asked);
}

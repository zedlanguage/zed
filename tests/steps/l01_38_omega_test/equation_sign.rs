//! Equations whose sign only the names could choose, as `a - b == 0` (item
//! PRES-solve-equation-sign): `decide` and `satisfiable` give one answer whichever side of such
//! an equation is written first, whether it is written as one equation or as the two rows
//! `t >= 0` and `-t >= 0`, under every naming of the variables and every order of the parts.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_tests::instances::Rng;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Refusal, decide, satisfiable};

/// `Σ c[i]·x[i] + k`, over the variables by place.
#[derive(Clone, Debug)]
pub(super) struct Sum {
    c: Vec<i64>,
    k: i64,
}

impl Sum {
    fn negated(&self) -> Sum {
        Sum {
            c: self.c.iter().map(|c| -c).collect(),
            k: -self.k,
        }
    }

    fn at(&self, p: &[i64]) -> i64 {
        self.k + self.c.iter().zip(p).map(|(c, x)| c * x).sum::<i64>()
    }
}

/// A part of a system: `t >= 0`, an equation `t == 0` whose terms are those of `-t` (so only
/// the names could choose its sign), or a disjunction of conjunctions of rows `t >= 0`.
#[derive(Clone, Debug)]
pub(super) enum Part {
    Ge(Sum),
    Eq(Sum),
    Or(Vec<Vec<Sum>>),
}

/// How an equation `t == 0` is written: as `t == 0`, as `-t == 0`, or as the two rows
/// `t >= 0` and `-t >= 0` with one or the other first.
#[derive(Clone, Copy, Debug)]
pub(super) enum Writing {
    Plus,
    Minus,
    PlusFirst,
    MinusFirst,
}

const WRITINGS: [Writing; 4] = [
    Writing::Plus,
    Writing::Minus,
    Writing::PlusFirst,
    Writing::MinusFirst,
];

/// A system over `n` variables in the box `[-half, half]^n`.
#[derive(Clone, Debug)]
pub(super) struct System {
    n: usize,
    half: i64,
    parts: Vec<Part>,
}

impl System {
    /// Whether the system holds at some point of its box.
    fn holds_somewhere(&self) -> bool {
        let side = (2 * self.half + 1) as usize;
        let mut p = vec![0i64; self.n];
        (0..side.pow(self.n as u32)).any(|mut code| {
            for x in &mut p {
                *x = (code % side) as i64 - self.half;
                code /= side;
            }
            self.parts.iter().all(|part| match part {
                Part::Ge(t) => t.at(&p) >= 0,
                Part::Eq(t) => t.at(&p) == 0,
                Part::Or(ds) => ds.iter().any(|d| d.iter().all(|t| t.at(&p) >= 0)),
            })
        })
    }

    /// The equations of the system.
    fn equations(&self) -> usize {
        self.parts
            .iter()
            .filter(|p| matches!(p, Part::Eq(_)))
            .count()
    }

    /// The system as a formula: variable `i` named `names[i]`, the parts and then the box in
    /// `order`, the `e`-th equation written as `writing[e]`.
    fn formula(&self, names: &[Arc<str>], order: &[usize], writing: &[Writing]) -> Formula {
        let lin = |t: &Sum| {
            (t.c.iter().enumerate()).fold(Lin::constant(t.k), |l, (i, c)| {
                l.plus(&Lin::atom(Atom::Sym(names[i].clone())).times(*c))
            })
        };
        let zero = Lin::constant(0);
        let ge = |t: &Sum| Formula::Con(Con::ge(&lin(t), &zero));
        let mut eqs = 0;
        let mut written: Vec<Vec<Formula>> = Vec::new();
        for part in &self.parts {
            written.push(match part {
                Part::Ge(t) => vec![ge(t)],
                Part::Eq(t) => {
                    let w = writing[eqs];
                    eqs += 1;
                    match w {
                        Writing::Plus => vec![Formula::Con(Con::eq(&lin(t), &zero))],
                        Writing::Minus => vec![Formula::Con(Con::eq(&lin(&t.negated()), &zero))],
                        Writing::PlusFirst => vec![ge(t), ge(&t.negated())],
                        Writing::MinusFirst => vec![ge(&t.negated()), ge(t)],
                    }
                }
                Part::Or(ds) => vec![Formula::or(
                    ds.iter()
                        .map(|d| Formula::and(d.iter().map(ge).collect()))
                        .collect(),
                )],
            });
        }
        for i in 0..self.n {
            let mut c = vec![0; self.n];
            c[i] = 1;
            let low = Sum {
                c: c.clone(),
                k: self.half,
            };
            c[i] = -1;
            let high = Sum { c, k: self.half };
            written.push(vec![ge(&low), ge(&high)]);
        }
        Formula::and(order.iter().flat_map(|&i| written[i].clone()).collect())
    }
}

/// A sum over `n` variables whose terms are those of its negation and whose constant is zero:
/// `x - y`, `x + y - z - w`, `2x - 2y + z - w` or `x - y + z - w` on distinct variables drawn
/// from `rng`.
fn symmetric_sum(rng: &mut Rng, n: usize) -> Sum {
    let mut vars: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        vars.swap(i, rng.below(i + 1));
    }
    let pattern: &[i64] = match rng.below(if n >= 4 { 4 } else { 1 }) {
        0 => &[1, -1],
        1 => &[1, 1, -1, -1],
        2 => &[2, -2, 1, -1],
        _ => &[1, -1, 3, -3],
    };
    let mut c = vec![0; n];
    for (j, &k) in pattern.iter().enumerate() {
        c[vars[j]] = k;
    }
    Sum { c, k: 0 }
}

/// A row over `n` variables with coefficients in `-5..=5` and a constant in `-10..=6`.
fn row(rng: &mut Rng, n: usize) -> Sum {
    Sum {
        c: (0..n).map(|_| rng.int(-5, 5)).collect(),
        k: rng.int(-10, 6),
    }
}

/// A system over four variables in the box `[-2, 2]^4`: one or two equations of
/// [`symmetric_sum`], one to three rows, and, in half the systems, a disjunction of two or
/// three disjuncts of one or two rows each.
pub(super) fn system(rng: &mut Rng) -> System {
    let n = 4;
    let mut parts = Vec::new();
    for _ in 0..1 + rng.below(2) {
        parts.push(Part::Eq(symmetric_sum(rng, n)));
    }
    for _ in 0..2 + rng.below(4) {
        parts.push(Part::Ge(row(rng, n)));
    }
    if rng.below(2) == 0 {
        let ds = (0..2 + rng.below(2))
            .map(|_| (0..1 + rng.below(2)).map(|_| row(rng, n)).collect())
            .collect();
        parts.push(Part::Or(ds));
    }
    System { n, half: 2, parts }
}

/// One layer of the regular family over `n` variables: `n` rows of one pattern of 2 to 4
/// coefficients in `-5..=5` and one constant, the pattern placed so that each variable has each
/// coefficient once, which gives every variable one color.
fn layer(rng: &mut Rng, n: usize) -> Vec<Sum> {
    let width = 2 + rng.below(3);
    let pattern: Vec<i64> = (0..width)
        .map(|_| {
            loop {
                let c = rng.int(-5, 5);
                if c != 0 {
                    break c;
                }
            }
        })
        .collect();
    let k = rng.int(-10, 6);
    (0..n)
        .map(|i| {
            let mut c = vec![0; n];
            for (j, &p) in pattern.iter().enumerate() {
                c[(i + j) % n] = p;
            }
            Sum { c, k }
        })
        .collect()
}

/// A system over four variables in the box `[-h, h]^4`, `h` 1 or 2: one or two equations of
/// [`symmetric_sum`], a layer of the regular family, and one or two disjunctions each of
/// whose disjuncts is a row of a layer.
pub(super) fn layered(rng: &mut Rng) -> System {
    let n = 4;
    let mut parts = Vec::new();
    for _ in 0..1 + rng.below(2) {
        parts.push(Part::Eq(symmetric_sum(rng, n)));
    }
    parts.extend(layer(rng, n).into_iter().map(Part::Ge));
    for _ in 0..1 + rng.below(2) {
        parts.push(Part::Or(
            layer(rng, n).into_iter().map(|r| vec![r]).collect(),
        ));
    }
    System {
        n,
        half: 1 + rng.below(2) as i64,
        parts,
    }
}

/// An answer of `decide` and `satisfiable` with the names it gives left out, since a renaming
/// changes them.
fn answer(f: &Formula) -> String {
    let d = match decide(f) {
        Err(Refusal::Tie(_)) => "Err(Tie)".to_string(),
        Err(Refusal::Unordered(_)) => "Err(Unordered)".to_string(),
        a => format!("{a:?}"),
    };
    let s = match satisfiable(f) {
        Ok(Some(m)) => {
            assert!(f.holds(&m), "the point {m:?} fails {f}");
            "Ok(point)".to_string()
        }
        Ok(None) => "Ok(none)".to_string(),
        Err(Refusal::Tie(_)) => "Err(Tie)".to_string(),
        Err(Refusal::Unordered(_)) => "Err(Unordered)".to_string(),
        Err(r) => format!("Err({r:?})"),
    };
    format!("{d} / {s}")
}

/// Every writing of the equations of `sys`.
fn writings(sys: &System) -> Vec<Vec<Writing>> {
    let mut out = vec![Vec::new()];
    for _ in 0..sys.equations() {
        out = (out.iter())
            .flat_map(|w| {
                WRITINGS.iter().map(move |&x| {
                    let mut w = w.clone();
                    w.push(x);
                    w
                })
            })
            .collect();
    }
    out
}

/// Calls `visit` with every permutation of `0..n` (Heap's algorithm).
fn each_permutation(n: usize, mut visit: impl FnMut(&[usize])) {
    let mut perm: Vec<usize> = (0..n).collect();
    visit(&perm);
    let mut c = vec![0; n];
    let mut i = 1;
    while i < n {
        if c[i] < i {
            perm.swap(if i % 2 == 0 { 0 } else { c[i] }, i);
            visit(&perm);
            c[i] += 1;
            i = 1;
        } else {
            c[i] = 0;
            i += 1;
        }
    }
}

/// The answers of `sys` with every writing of its equations under the naming as written, and
/// under every other naming of its variables (names that sort in every order) with a writing
/// drawn from `rng`, each with its parts in an order drawn from `rng`, with how many gave each.
/// An answer that is not a refusal is checked against the points of the box.
pub(super) fn answers(sys: &System, rng: &mut Rng) -> BTreeMap<String, usize> {
    let truth = sys.holds_somewhere();
    let expected = if truth {
        "Ok(true) / Ok(point)"
    } else {
        "Ok(false) / Ok(none)"
    };
    let parts = sys.parts.len() + sys.n;
    let mut seen = BTreeMap::new();
    let ws = writings(sys);
    let mut ask = |names: &[Arc<str>], w: &[Writing], rng: &mut Rng| {
        let mut order: Vec<usize> = (0..parts).collect();
        for i in (1..parts).rev() {
            order.swap(i, rng.below(i + 1));
        }
        let f = sys.formula(names, &order, w);
        let a = answer(&f);
        assert!(
            a.contains("Err") || a == expected,
            "{f}: {a}, but the box has {}",
            if truth { "a point" } else { "no point" }
        );
        *seen.entry(a).or_insert(0) += 1;
    };
    let plain: Vec<Arc<str>> = (0..sys.n).map(|p| Arc::from(format!("v{p}"))).collect();
    for w in &ws {
        ask(&plain, w, rng);
    }
    each_permutation(sys.n, |perm| {
        let names: Vec<Arc<str>> = perm.iter().map(|p| Arc::from(format!("v{p}"))).collect();
        let w = ws[rng.below(ws.len())].clone();
        ask(&names, &w, rng);
    });
    seen
}

/// The source of system `i` of `seed`: each system is drawn from a source of its own, so that
/// one of them can be asked again without drawing those before it.
fn source(seed: u64, i: usize) -> Rng {
    Rng::new(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ i as u64)
}

/// Of the systems numbered `range` of `make` under `seed`, those whose answer changes with the
/// naming, the writing of their equations or the order of their parts, with the answers and
/// their counts; and how many systems were refused under some writing.
pub(super) fn differing(
    seed: u64,
    range: std::ops::Range<usize>,
    make: impl Fn(&mut Rng) -> System,
) -> (Vec<(usize, BTreeMap<String, usize>)>, usize) {
    let mut differ = Vec::new();
    let mut refused = 0;
    for i in range {
        let mut rng = source(seed, i);
        let sys = make(&mut rng);
        let seen = answers(&sys, &mut rng);
        refused += usize::from(seen.keys().any(|a| a.contains("Err")));
        if seen.len() > 1 {
            differ.push((i, seen));
        }
    }
    (differ, refused)
}

/// Each system of `cases` (a family, a seed and the system's number) gives one answer.
fn one_answer_each(cases: &[(fn(&mut Rng) -> System, u64, usize)]) {
    for &(make, seed, i) in cases {
        let (differ, _) = differing(seed, i..i + 1, make);
        assert_eq!(differ, Vec::new(), "seed {seed}, system {i}");
    }
}

#[test]
fn an_equation_written_as_one_row_or_two_gives_one_answer() {
    // Layered systems that, while such an equation was kept as written
    // (PRES-solve-equation-sign), were answered with it written as `t == 0` and refused as
    // Unordered (the first four) or Tie (the last) with it written as `t >= 0 && -t >= 0`.
    one_answer_each(&[
        (layered, 1, 0),
        (layered, 1, 108),
        (layered, 2, 30),
        (layered, 2, 86),
        (layered, 1, 128),
    ]);
}

/// The first systems of each family give one answer each.
#[test]
fn the_first_systems_of_each_family_give_one_answer() {
    assert_eq!(differing(3, 0..4, layered).0, Vec::new());
    assert_eq!(differing(3, 0..4, system).0, Vec::new());
}

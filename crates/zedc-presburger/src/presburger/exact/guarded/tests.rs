use super::super::super::{SOLVER, Shared};
use super::*;

/// The recursive walk `pins` replaced, kept to show the two give the same pins, refusals
/// and work (FAIL-ids-shared-parts-stack-overflow).
fn pins_recursive(
    f: &Formula,
    neg: bool,
    vals: &HashMap<&Atom, Val>,
    memo: &mut HashMap<(Id, bool), IntervalSet>,
    work: &mut Work,
) -> Result<IntervalSet, Refusal> {
    let key = Id::of(f).map(|k| (k, neg));
    if let Some(k) = &key
        && let Some(set) = memo.get(k)
    {
        return Ok(set.clone());
    }
    let set = match f {
        Formula::Con(c) => {
            work.charge(PIECE)?;
            con_pins(c, neg, vals)
        }
        Formula::Not(g) => pins_recursive(g, !neg, vals, memo, work)?,
        Formula::Holes(_) => pins_recursive(f.opened(), neg, vals, memo, work)?,
        Formula::And(gs) | Formula::Or(gs) => {
            let meet = matches!(f, Formula::And(_)) != neg;
            let mut out = if meet {
                IntervalSet::top()
            } else {
                IntervalSet::empty()
            };
            for g in gs.iter() {
                let x = pins_recursive(g, neg, vals, memo, work)?;
                out = if meet { out.meet(&x) } else { out.join(&x) };
                if meet && out.is_empty() {
                    break;
                }
            }
            out
        }
    };
    if let Some(k) = key {
        memo.insert(k, set.clone());
    }
    Ok(set)
}

fn a(s: &str) -> Atom {
    Atom::Sym(s.into())
}

/// `sum of c * atom + k >= 0` (or `== 0` where `eq`).
fn row(terms: &[(&str, i64)], k: i64, eq: bool) -> Formula {
    let lin = Lin {
        terms: (terms.iter())
            .filter(|(_, c)| *c != 0)
            .map(|(s, c)| (a(s), Int::from(*c)))
            .collect(),
        constant: Int::from(k),
    };
    let zero = Lin::constant(0);
    Formula::Con(if eq {
        Con::eq(&lin, &zero)
    } else {
        Con::ge(&lin, &zero)
    })
}

fn work(limit: u64) -> Work {
    Work {
        used: 0,
        limit,
        solver: SOLVER,
    }
}

/// A chain of 100,000 negations around `x >= 0`, met with `x <= 5`, `x` the pin itself:
/// the pins are 0 to 5. The recursive walk overflowed the 2 MB stack of a test thread on
/// this chain; the walk with its own stack does not.
#[test]
fn pins_of_a_chain_deeper_than_the_call_stack_are_found() {
    let mut f = row(&[("x", 1)], 0, false);
    for _ in 0..100_000 {
        f = Formula::Not(Shared::new(f));
    }
    let f = Formula::And(Shared::new(vec![f, row(&[("x", -1)], 5, false)]));
    let x = a("x");
    let one = Val {
        slope: Int::from(1),
        lo: Some(Int::from(0)),
        hi: Some(Int::from(0)),
    };
    let vals = HashMap::from([(&x, one)]);
    let got = pins(&f, false, &vals, &mut HashMap::new(), &mut work(u64::MAX));
    assert_eq!(got, Ok(IntervalSet::of(0, 5)));
    // Dropping the chain recurses as deep as the chain (`Formula` has no drop of its own),
    // so the test leaks it rather than measure that drop.
    std::mem::forget(f);
}

use crate::seed::Rng;

const NAMES: [&str; 3] = ["x", "y", "z"];

/// A random formula up to `depth` deep over x, y and z, reusing parts in `made` so that
/// some are shared and read through the memo.
fn formula(rng: &mut Rng, depth: u32, made: &mut Vec<Formula>) -> Formula {
    if !made.is_empty() && rng.below(5) == 0 {
        return made[rng.below(made.len())].clone();
    }
    let f = if depth == 0 || rng.below(4) == 0 {
        let terms: Vec<(&str, i64)> = NAMES.iter().map(|n| (*n, rng.int(-2, 2))).collect();
        row(&terms, rng.int(-4, 4), rng.below(4) == 0)
    } else {
        let n = 1 + rng.below(3);
        let parts: Vec<Formula> = (0..n).map(|_| formula(rng, depth - 1, made)).collect();
        match rng.below(5) {
            0 => Formula::Not(Shared::new(parts.into_iter().next().unwrap())),
            1 | 2 => Formula::And(Shared::new(parts)),
            _ => Formula::Or(Shared::new(parts)),
        }
    };
    made.push(f.clone());
    f
}

fn end(rng: &mut Rng) -> Option<Int> {
    (rng.below(5) != 0).then(|| Int::from(rng.int(-3, 3)))
}

/// The walk with its own stack gives the pins, refusal and work of the recursive walk on
/// random formulas up to 8 deep with shared parts, random values and random work limits.
#[test]
fn pins_match_the_recursive_walk_on_random_formulas() {
    let seed = crate::seed::seed("pins_match_the_recursive_walk_on_random_formulas");
    let mut rng = Rng::new(seed);
    let atoms: Vec<Atom> = NAMES.iter().map(|n| a(n)).collect();
    for round in 0..2000 {
        let f = formula(&mut rng, 8, &mut Vec::new());
        let vals: HashMap<&Atom, Val> = (atoms.iter())
            .map(|x| {
                let (p, q) = (end(&mut rng), end(&mut rng));
                let (lo, hi) = match (p, q) {
                    (Some(p), Some(q)) if q < p => (Some(q), Some(p)),
                    pq => pq,
                };
                let slope = Int::from(rng.int(-2, 2));
                (x, Val { slope, lo, hi })
            })
            .collect();
        let neg = rng.below(2) == 0;
        let limit = if rng.below(3) == 0 {
            rng.below_u64(20) * PIECE
        } else {
            u64::MAX
        };
        let (mut w, mut v) = (work(limit), work(limit));
        let new = pins(&f, neg, &vals, &mut HashMap::new(), &mut w);
        let old = pins_recursive(&f, neg, &vals, &mut HashMap::new(), &mut v);
        assert_eq!(new, old, "seed {seed}, round {round}: {f:?}, neg {neg}");
        assert_eq!(w.used, v.used, "seed {seed}, round {round}: work");
    }
}

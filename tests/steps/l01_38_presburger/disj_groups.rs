//! Many disjunctions over one linked group of rows (plan items DISJ-diff-fast and
//! DISJ-incremental): each disjunct is tested against the base projected onto the atoms of
//! the disjuncts near it, so `n` disjunctions cost about `n log n`, not `n` solves of the
//! whole group.

use std::time::Instant;

use zed_tests::scaling;
use zedc::store::presburger::{Atom, Con, Formula, Lin, decide, project_each, satisfiable};

fn x(i: usize) -> Lin {
    Lin::atom(Atom::Sym(format!("x{i:05}").into()))
}

fn y(i: usize) -> Lin {
    Lin::atom(Atom::Sym(format!("y{i:05}").into()))
}

fn ge(l: Lin) -> Formula {
    Formula::Con(Con::ge(&l, &Lin::constant(0)))
}

fn eq(l: Lin) -> Formula {
    Formula::Con(Con::eq(&l, &Lin::constant(0)))
}

/// `x[i + 1] - x[i]`.
fn step(i: usize) -> Lin {
    x(i + 1).minus(&x(i))
}

/// Which disjunct holds at the point the solver finds for the base.
#[derive(Clone, Copy, PartialEq)]
enum Holds {
    First,
    None,
}

/// A chain of difference rows `x[i + 1] - x[i] >= 1` over `n` stages, `0 <= x[0]` and
/// `x[n - 1] <= 4n`, with a disjunction at every fourth stage: `x[i + 1] - x[i] <= 1 ||
/// x[i + 1] - x[i] >= 3` (the first holds at the least point), or `x[i + 1] - x[i] == 2 ||
/// x[i + 1] - x[i] == 3` (neither does).
pub fn difference_chain(n: usize, holds: Holds) -> Formula {
    let mut fs = vec![ge(x(0)), ge(Lin::constant(4 * n as i128).minus(&x(n - 1)))];
    fs.extend((0..n - 1).map(|i| ge(step(i).minus(&Lin::constant(1)))));
    for i in (0..n - 1).step_by(4) {
        let s = step(i);
        fs.push(Formula::or(match holds {
            Holds::First => vec![
                ge(Lin::constant(1).minus(&s)),
                ge(s.minus(&Lin::constant(3))),
            ],
            Holds::None => vec![
                eq(s.minus(&Lin::constant(2))),
                eq(s.minus(&Lin::constant(3))),
            ],
        }));
    }
    Formula::and(fs)
}

/// The rows of three atoms `x[i + 1] - x[i] - y[i] >= 0` with `1 <= y[i] <= 2`, over `n`
/// stages, `0 <= x[0]` and `x[n - 1] <= 8n`, with a disjunction at every fourth stage on
/// `x[i + 1] - x[i] + y[i]`: `<= 2 || >= 5` (the first holds at the least point), or `== 4 ||
/// == 5` (neither does).
pub fn general_chain(n: usize, holds: Holds) -> Formula {
    let mut fs = vec![ge(x(0)), ge(Lin::constant(8 * n as i128).minus(&x(n - 1)))];
    for i in 0..n - 1 {
        fs.push(ge(step(i).minus(&y(i))));
        fs.push(ge(y(i).minus(&Lin::constant(1))));
        fs.push(ge(Lin::constant(2).minus(&y(i))));
    }
    for i in (0..n - 1).step_by(4) {
        let s = step(i).plus(&y(i));
        fs.push(Formula::or(match holds {
            Holds::First => vec![
                ge(Lin::constant(2).minus(&s)),
                ge(s.minus(&Lin::constant(5))),
            ],
            Holds::None => vec![
                eq(s.minus(&Lin::constant(4))),
                eq(s.minus(&Lin::constant(5))),
            ],
        }));
    }
    Formula::and(fs)
}

/// Times of the three cases at doubling sizes on both families, printed; not a test of the
/// suite (run with `--ignored --nocapture`).
#[test]
#[ignore]
fn probe_times() {
    let max: usize = std::env::var("PROBE_MAX")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(256);
    for (name, fam) in [
        ("difference", difference_chain as fn(usize, Holds) -> Formula),
        ("general", general_chain),
    ] {
        let mut n = 32;
        while n <= max {
            let first = fam(n, Holds::First);
            let none = fam(n, Holds::None);
            let mid = [Atom::Sym(format!("x{:05}", n / 2).into())];
            let t = Instant::now();
            let a = project_each(&first, &mid).map(|e| e.0[0].clone());
            let ta = t.elapsed();
            let t = Instant::now();
            let b = decide(&none);
            let tb = t.elapsed();
            let t = Instant::now();
            let c = project_each(&none, &mid).map(|e| e.0[0].clone());
            let tc = t.elapsed();
            let s = satisfiable(&none).map(|m| m.is_some());
            println!(
                "{name} n={n}: project_each first {ta:?} {a:?}; decide none {tb:?} {b:?}; \
                 project_each none {tc:?} {c:?}; satisfiable none {s:?}"
            );
            n *= 2;
        }
    }
    let _ = scaling::FACTOR;
}

#[test]
#[ignore]
fn probe_one() {
    let n: usize = std::env::var("PROBE_N").ok().and_then(|s| s.parse().ok()).unwrap_or(64);
    let general = std::env::var("PROBE_GENERAL").is_ok();
    let case: usize = std::env::var("PROBE_CASE").ok().and_then(|s| s.parse().ok()).unwrap_or(2);
    let fam = if general { general_chain } else { difference_chain };
    let holds = if case == 0 { Holds::First } else { Holds::None };
    let f = fam(n, holds);
    let mid = [Atom::Sym(format!("x{:05}", n / 2).into())];
    let t = Instant::now();
    let r = if case == 1 { format!("{:?}", decide(&f)) } else { format!("{:?}", project_each(&f, &mid).map(|e| e.0)) };
    println!("n={n} case {case}: {:?} {r}", t.elapsed());
}

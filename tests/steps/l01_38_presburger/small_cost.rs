//! The cost of `satisfiable` and `decide` on small formulas (PRES-small-cost, PRES-small-front).

use std::sync::Arc;

use zed_tests::scaling::{self, Meter};
use zedc::store::presburger::{Atom, Con, Formula, Lin, decide, satisfiable};

fn sym(x: &str) -> Lin {
    Lin::atom(Atom::Sym(Arc::from(x)))
}

fn q(i: u32) -> Lin {
    Lin::atom(Atom::Aux(i))
}

fn k(v: i64) -> Lin {
    Lin::constant(v)
}

fn ge(a: &Lin, b: &Lin) -> Formula {
    Formula::Con(Con::ge(a, b))
}

fn eq(a: &Lin, b: &Lin) -> Formula {
    Formula::Con(Con::eq(a, b))
}

/// `if g >= c { v } else { c }` defining `q`: `(g >= c && v == q) || (!(g >= c) && q == c)`.
fn max_def(g: &Lin, c: i64, v: &Lin, q: &Lin) -> Formula {
    Formula::or(vec![
        Formula::and(vec![ge(g, &k(c)), eq(v, q)]),
        Formula::and(vec![Formula::negate(ge(g, &k(c))), eq(q, &k(c))]),
    ])
}

/// How [`defs`] gives its inputs `x` and `y`.
#[derive(Clone, Copy, Debug)]
enum Inputs {
    /// By equations, `x == 6 && y == 4`.
    Fixed,
    /// By two rows each whose bounds meet, `x >= 6 && 6 >= x`.
    Bounded,
    /// By two rows each that leave two values, `x >= 6 && 7 >= x`: not a point, so left to the
    /// solver.
    Ranged,
}

/// `n` definitions, each a `max` of the one before (or of `x`, or of `y`) and a constant,
/// as the preimages of chains of `if` give, with the inputs given as `inputs` says.
fn defs(n: u32, inputs: Inputs) -> Formula {
    let mut fs = Vec::new();
    for i in 0..n {
        let v = match i % 3 {
            0 => sym("x"),
            1 => sym("y"),
            _ => q(i - 1),
        };
        fs.push(max_def(&v, i64::from(i % 5) - 2, &v, &q(i)));
    }
    for (x, v) in [("x", 6), ("y", 4)] {
        match inputs {
            Inputs::Fixed => fs.push(eq(&sym(x), &k(v))),
            Inputs::Bounded | Inputs::Ranged => {
                let top = if let Inputs::Ranged = inputs {
                    v + 1
                } else {
                    v
                };
                fs.push(ge(&sym(x), &k(v)));
                fs.push(ge(&k(top), &sym(x)));
            }
        }
    }
    Formula::and(fs)
}

/// The least instructions of five runs of `run`.
fn least(meter: &mut Meter, run: &dyn Fn()) -> u64 {
    (0..5).map(|_| meter.work(run).units).min().expect("runs")
}

#[test]
#[ignore = "benchmark: prints instructions per call"]
fn bench_small_formulas() {
    let mut meter = Meter::new();
    let one = Formula::and(vec![
        max_def(&sym("x"), 1, &sym("x"), &q(0)),
        eq(&sym("x"), &k(6)),
        eq(&sym("y"), &k(4)),
    ]);
    let three = Formula::and(vec![
        eq(&q(0), &k(1)),
        eq(&sym("x"), &k(6)),
        eq(&sym("y"), &k(4)),
    ]);
    for (what, f) in [("one disjunction", &one), ("three equations", &three)] {
        let s = least(&mut meter, &|| drop(std::hint::black_box(satisfiable(f))));
        let d = least(&mut meter, &|| drop(std::hint::black_box(decide(f))));
        eprintln!("{what}: satisfiable {s}, decide {d}  {f}");
    }
    for inputs in [Inputs::Fixed, Inputs::Bounded, Inputs::Ranged] {
        for n in [1, 2, 4, 7, 8, 16, 32, 64] {
            let f = defs(n, inputs);
            let s = least(&mut meter, &|| drop(std::hint::black_box(satisfiable(&f))));
            let d = least(&mut meter, &|| drop(std::hint::black_box(decide(&f))));
            eprintln!(
                "{inputs:?} n {n}: satisfiable {s} ({}/def), decide {d}; {:?}",
                s / u64::from(n),
                satisfiable(&f).map(|m| m.map(|m| m.len()))
            );
        }
    }
}

#[test]
fn a_chain_of_definitions_at_a_point_costs_its_size() {
    // Each definition is decided by propagation from the one before, O(1) each, whether the
    // inputs are fixed by equations or by two rows whose bounds meet.
    for inputs in [Inputs::Fixed, Inputs::Bounded] {
        let built = scaling::inputs(64, |n| defs(n as u32, inputs));
        for f in built.values() {
            let m = satisfiable(f).expect("answered").expect("a point");
            assert_eq!(m[&Atom::Sym(Arc::from("x"))], 6.into(), "{f}");
        }
        scaling::check_order(
            &format!("a chain of definitions at a point ({inputs:?}), its point found"),
            64,
            1,
            |n| {
                std::hint::black_box(satisfiable(&built[&n]).is_ok());
            },
        );
        scaling::check_order(
            &format!("a chain of definitions at a point ({inputs:?}), decided"),
            64,
            1,
            |n| {
                std::hint::black_box(decide(&built[&n]).is_ok());
            },
        );
    }
}

#[test]
fn a_chain_of_definitions_at_a_point_is_not_settled_by_the_whole_solver() {
    // Inputs bounded by two rows whose bounds meet are read by propagation as if fixed by
    // equations, at about the same cost (within 5% at eight definitions when measured). Inputs
    // left two values each are not a point, and the same chain takes the whole solver, at about
    // 100 times that cost.
    let mut meter = Meter::new();
    let [fixed, bounded, ranged] =
        [Inputs::Fixed, Inputs::Bounded, Inputs::Ranged].map(|i| defs(8, i));
    assert_eq!(
        satisfiable(&fixed).expect("answered"),
        satisfiable(&bounded).expect("answered")
    );
    let [fixed, bounded, ranged] = [&fixed, &bounded, &ranged]
        .map(|f| least(&mut meter, &|| drop(std::hint::black_box(satisfiable(f)))));
    let unit = meter.unit();
    assert!(
        bounded < 2 * fixed && fixed * 8 < ranged,
        "fixed {fixed} {unit}, bounded {bounded} {unit}, ranged {ranged} {unit}"
    );
}

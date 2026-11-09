//! The cost of `satisfiable` and `decide` on small formulas (PRES-small-cost).

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

/// `n` definitions, each a `max` of the one before (or of `x`, or of `y`) and a constant,
/// as the preimages of chains of `if` give, with the inputs fixed by `x == 6 && y == 4`
/// (`fixed`) or bounded to the same values by two rows each.
fn defs(n: u32, fixed: bool) -> Formula {
    let mut fs = Vec::new();
    for i in 0..n {
        let v = match i % 3 {
            0 => sym("x"),
            1 => sym("y"),
            _ => q(i - 1),
        };
        fs.push(max_def(&v, i64::from(i % 5) - 2, &v, &q(i)));
    }
    if fixed {
        fs.push(eq(&sym("x"), &k(6)));
        fs.push(eq(&sym("y"), &k(4)));
    } else {
        for (x, v) in [("x", 6), ("y", 4)] {
            fs.push(ge(&sym(x), &k(v)));
            fs.push(ge(&k(v), &sym(x)));
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
    for fixed in [true, false] {
        for n in [1, 2, 4, 7, 8, 16, 32, 64] {
            let f = defs(n, fixed);
            let s = least(&mut meter, &|| drop(std::hint::black_box(satisfiable(&f))));
            let d = least(&mut meter, &|| drop(std::hint::black_box(decide(&f))));
            eprintln!(
                "fixed {fixed} n {n}: satisfiable {s} ({}/def), decide {d}; {:?}",
                s / u64::from(n),
                satisfiable(&f).map(|m| m.map(|m| m.len()))
            );
        }
    }
}

#[test]
fn a_chain_of_definitions_at_a_point_costs_its_size() {
    // Each definition is decided by propagation from the one before, O(1) each.
    let built = scaling::inputs(64, |n| defs(n as u32, true));
    for f in built.values() {
        let m = satisfiable(f).expect("answered").expect("a point");
        assert_eq!(m[&Atom::Sym(Arc::from("x"))], 6.into(), "{f}");
    }
    scaling::check_order(
        "a chain of definitions at a point, its point found",
        64,
        1,
        |n| {
            std::hint::black_box(satisfiable(&built[&n]).is_ok());
        },
    );
    scaling::check_order("a chain of definitions at a point, decided", 64, 1, |n| {
        std::hint::black_box(decide(&built[&n]).is_ok());
    });
}

#[test]
fn a_chain_of_definitions_at_a_point_is_not_settled_by_the_whole_solver() {
    // The same chain with its inputs bounded by two rows each, which propagation does not read,
    // goes to the whole solver; fixed by equations it is read by propagation alone, at a small
    // part of that cost (about 1/45 at eight definitions when measured).
    let mut meter = Meter::new();
    let (fixed, bounded) = (defs(8, true), defs(8, false));
    assert_eq!(
        satisfiable(&fixed).expect("answered"),
        satisfiable(&bounded).expect("answered")
    );
    let fast = least(&mut meter, &|| {
        drop(std::hint::black_box(satisfiable(&fixed)))
    });
    let slow = least(&mut meter, &|| {
        drop(std::hint::black_box(satisfiable(&bounded)))
    });
    assert!(
        fast * 8 < slow,
        "fixed: {fast} {}, bounded: {slow} {}",
        meter.unit(),
        meter.unit()
    );
}

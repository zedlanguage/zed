//! Helpers of `tests/steps/l01_38_presburger/small_cost.rs` shared with its hand-run benchmark
//! (`benches/src/bin/small_cost.rs`): the chains of `max` definitions, the ladders of bounds, and
//! the least work of five runs.

use std::sync::Arc;

use crate::scaling::Meter;
use zedc::store::presburger::{Atom, Con, Formula, Lin};

/// The symbol `x`.
pub fn sym(x: &str) -> Lin {
    Lin::atom(Atom::Sym(Arc::from(x)))
}

/// The auxiliary variable `i`.
pub fn q(i: u32) -> Lin {
    Lin::atom(Atom::Aux(i))
}

/// The constant `v`.
pub fn k(v: i64) -> Lin {
    Lin::constant(v)
}

/// `a >= b`.
pub fn ge(a: &Lin, b: &Lin) -> Formula {
    Formula::Con(Con::ge(a, b))
}

/// `a == b`.
pub fn eq(a: &Lin, b: &Lin) -> Formula {
    Formula::Con(Con::eq(a, b))
}

/// `if g >= c { v } else { c }` defining `q`: `(g >= c && v == q) || (!(g >= c) && q == c)`.
pub fn max_def(g: &Lin, c: i64, v: &Lin, q: &Lin) -> Formula {
    Formula::or(vec![
        Formula::and(vec![ge(g, &k(c)), eq(v, q)]),
        Formula::and(vec![Formula::negate(ge(g, &k(c))), eq(q, &k(c))]),
    ])
}

/// How [`defs`] gives its inputs `x` and `y`.
#[derive(Clone, Copy, Debug)]
pub enum Inputs {
    /// By equations, `x == 6 && y == 4`.
    Fixed,
    /// By two rows each whose bounds meet, `x >= 6 && 6 >= x`.
    Bounded,
    /// By two rows each that leave two values, `x >= 6 && 7 >= x`: not a point, but the
    /// inputs at their lower bounds, `x == 6 && y == 4`, are one, which propagation from the
    /// bounds shows (PRES-small-point).
    Ranged,
}

/// `n` definitions, each a `max` of the one before (or of `x`, or of `y`) and a constant,
/// as the preimages of chains of `if` give, with the inputs given as `inputs` says.
pub fn defs(n: u32, inputs: Inputs) -> Formula {
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
pub fn least(meter: &mut Meter, run: &dyn Fn()) -> u64 {
    (0..5).map(|_| meter.work(run).units).min().expect("runs")
}

/// A ladder of `n` bounds, `x0 <= 5 && x1 <= x0 + 1 && ... && x(n-1) <= x(n-2) + 1`: no
/// variable but `x0` is bounded until the one before it is set, so the rounds at the bounds
/// set one rung each, `n` rounds of one continued propagation (PRES-small-point).
pub fn ladder(n: u32) -> Formula {
    let x = |i: u32| sym(&format!("x{i}"));
    let mut fs = vec![ge(&k(5), &x(0))];
    for i in 1..n {
        fs.push(ge(&x(i - 1).plus(&k(1)), &x(i)));
    }
    Formula::and(fs)
}

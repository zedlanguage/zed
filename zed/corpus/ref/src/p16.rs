//! 16 game tick: per tick, each player's moves are summed first (the reducer's coalescing), then
//! applied once and clamped to 0..=10. Players start at 5 and are listed in name order; one line
//! per tick 0..=last.

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write;

use num_bigint::BigInt;
use num_traits::Zero;

use crate::zedrt::parse_int;

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let mut moves: BTreeMap<&str, HashMap<BigInt, BigInt>> = BTreeMap::new();
    let mut last = BigInt::from(-1);
    for l in lines {
        let w: Vec<&str> = l.split(' ').collect();
        let &[t, p, dx] = &w[..] else {
            return Err(format!("not \"tick player dx\": {l}"));
        };
        let (t, dx) = (parse_int(t)?, parse_int(dx)?);
        last = last.max(t.clone());
        *moves.entry(p).or_default().entry(t).or_default() += dx;
    }
    let mut pos: Vec<BigInt> = vec![BigInt::from(5); moves.len()];
    let mut t = BigInt::zero();
    while t <= last {
        let mut row = t.to_string();
        for (x, (p, by_tick)) in pos.iter_mut().zip(&moves) {
            if let Some(m) = by_tick.get(&t) {
                *x += m;
            }
            *x = std::mem::take(x).clamp(BigInt::zero(), BigInt::from(10));
            write!(row, " {p}={x}").expect("writing to a String");
        }
        say!(out, "{row}");
        t += 1;
    }
    Ok(())
}

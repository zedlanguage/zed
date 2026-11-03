//! 17 sensor windows. Zed rules used: int() of a non-integer is #invalid, so `else -1` and the
//! where drop the line; the assumed window signature puts a reading in the window starting at
//! t div 10 * 10 (Euclidean div, t >= 0 here), windows in start order, absent when empty; groups
//! in sensor-name order; the output is the batch result, which the streaming plan must equal.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::Signed;

use crate::zedrt::try_parse_int;

fn num(s: &str) -> BigInt {
    try_parse_int(s).unwrap_or(BigInt::from(-1))
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let ten = BigInt::from(10);
    let mut wins: BTreeMap<BigInt, BTreeMap<&str, Vec<BigInt>>> = BTreeMap::new();
    for l in lines {
        let mut w = l.split(' ');
        let t = num(w.next().unwrap_or(""));
        let s = w.next().unwrap_or("");
        let v = num(w.next().unwrap_or(""));
        if !t.is_negative() && !v.is_negative() {
            let start = t.div_floor(&ten) * &ten;
            wins.entry(start).or_default().entry(s).or_default().push(v);
        }
    }
    for (w, groups) in &wins {
        let parts: Vec<String> = groups
            .iter()
            .map(|(s, vs)| {
                let sum: BigInt = vs.iter().sum();
                let max = vs.iter().max().expect("a group has a reading");
                format!("{s} n={} sum={sum} max={max}", vs.len())
            })
            .collect();
        say!(out, "{w}: {}", parts.join("; "));
    }
    Ok(())
}

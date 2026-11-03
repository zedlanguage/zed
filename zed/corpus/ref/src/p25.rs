//! 25 autocorrelation over the valid range i in 0..<n - l, lags 0..=3.

use num_bigint::BigInt;

use crate::zedrt::{at, parse_int};

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let xs = at(lines, 0)?.split(' ').map(parse_int);
    let xs = xs.collect::<Result<Vec<BigInt>, String>>()?;
    for l in 0..4 {
        let sum: BigInt = xs.iter().zip(xs.iter().skip(l)).map(|(a, b)| a * b).sum();
        say!(out, "{l} {sum}");
    }
    Ok(())
}

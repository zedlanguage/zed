//! 22 top-K: score descending, then name ascending (code-point order).

use num_bigint::BigInt;

use crate::zedrt::{at, parse_int};

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let mut es: Vec<(BigInt, &str)> = Vec::with_capacity(lines.len());
    for l in lines {
        let w: Vec<&str> = l.split(' ').collect();
        es.push((parse_int(at(&w, 1)?)?, w[0]));
    }
    es.sort_by(|x, y| y.0.cmp(&x.0).then(x.1.cmp(y.1)));
    for (i, (s, n)) in es.iter().take(3).enumerate() {
        say!(out, "{} {n} {s}", i + 1);
    }
    Ok(())
}

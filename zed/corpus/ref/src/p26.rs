//! 26 heat stencil. Zed rule used: div is Euclidean; the divisor here is 4 (positive), where
//! Euclidean div equals floor division.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::ToPrimitive;

use crate::zedrt::{at, parse_int};

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let steps = parse_int(at(lines, 0)?)?.to_i64().ok_or("too many steps")?;
    let first = at(lines, 1)?.split(' ').map(parse_int);
    let mut row = first.collect::<Result<Vec<BigInt>, String>>()?;
    let n = row.len();
    // The first rows are all that is printed, with the last.
    let mut kept = vec![row.clone()];
    let four = BigInt::from(4);
    for t in 1..=steps {
        let p = &row;
        let cell = |i: usize| {
            if i == 0 || i == n - 1 {
                p[i].clone()
            } else {
                &p[i] + (&p[i - 1] - &p[i] - &p[i] + &p[i + 1]).div_floor(&four)
            }
        };
        row = (0..n).map(cell).collect();
        if t <= 2 {
            kept.push(row.clone());
        }
    }
    for t in [0, 1, 2, steps] {
        let shown = match usize::try_from(t).ok().filter(|&t| t < 3) {
            Some(t) => kept.get(t),
            None => (t == steps && t >= 3).then_some(&row),
        };
        let shown = shown.ok_or_else(|| format!("no step {t}"))?;
        let cells: Vec<String> = shown.iter().map(BigInt::to_string).collect();
        say!(out, "t={t}: {}", cells.join(" "));
    }
    Ok(())
}

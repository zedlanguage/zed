//! 04 running variance. Zed rules used: a float `+` scan entry is the exact prefix sum rounded
//! once (fsum, here kept exact from one line to the next); `/`, `*`, `-` are IEEE binary64;
//! floats print by the shortest round-trip rule (fmt_float); "${x}" is String(x); f64(s) reads
//! the input text.

use crate::zedrt::{ExactSum, fmt_float, parse_float};

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let xs = lines
        .iter()
        .map(|l| parse_float(l))
        .collect::<Result<Vec<f64>, String>>()?;
    let (mut count, mut sum, mut squares) = (
        ExactSum::default(),
        ExactSum::default(),
        ExactSum::default(),
    );
    for &x in &xs {
        count.add(1.0);
        sum.add(x);
        squares.add(x * x);
        let n = count.value()?;
        let s1 = sum.value()?;
        let s2 = squares.value()?;
        let m = s1 / n;
        say!(
            out,
            "{} {} {}",
            fmt_float(x),
            fmt_float(m),
            fmt_float(s2 / n - m * m)
        );
    }
    Ok(())
}

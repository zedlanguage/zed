//! 04 running variance. Zed rules used: a float `+` scan entry is plain IEEE addition on the
//! canonical tree over the values so far (TreeSum, DESIGN sec:reduction items 1 and 2); `/`,
//! `*`, `-` are IEEE binary64; floats print by the shortest round-trip rule (fmt_float); "${x}"
//! is String(x); f64(s) reads the input text.

use crate::zedrt::{TreeSum, fmt_float, parse_float};

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let xs = lines
        .iter()
        .map(|l| parse_float(l))
        .collect::<Result<Vec<f64>, String>>()?;
    let (mut count, mut sum, mut squares) =
        (TreeSum::default(), TreeSum::default(), TreeSum::default());
    for &x in &xs {
        let n = count.add(1.0);
        let s1 = sum.add(x);
        let s2 = squares.add(x * x);
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

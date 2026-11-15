//! 04 running variance. Zed rules used: a float `+` scan entry is plain IEEE addition on the
//! canonical tree over the values so far (TreeSum, DESIGN sec:reduction items 1 and 2); `/`,
//! `*`, `-` are IEEE binary64; floats print by the shortest round-trip rule (fmt_float); "${x}"
//! is String(x); f64(l) reads each line, and a line it does not read is 0.0 by the program's
//! `else 0.0` (try_parse_float).

use crate::zedrt::{TreeSum, fmt_float, try_parse_float};

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let xs: Vec<f64> = lines
        .iter()
        .map(|l| try_parse_float(l).unwrap_or(0.0))
        .collect();
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

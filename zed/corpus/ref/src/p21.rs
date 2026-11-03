//! 21 stats. Zed rules used: f64(s) parses a decimal (#invalid -> 0.0 by the program's else); a
//! float `.sum` is the exact sum rounded once (fsum); `/`, `-`, `*` and `.sqrt` are IEEE; floats
//! print shortest round-trip (fmt_float). Only mean and sd are printed; the second column is not
//! read.

use crate::zedrt::{fmt_float, fsum, try_parse_float};

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let num = |l: &String| try_parse_float(l.split(' ').next().unwrap_or("")).unwrap_or(0.0);
    let xs: Vec<f64> = lines.iter().map(num).collect();
    if xs.is_empty() {
        return Err("float division by zero".into());
    }
    let n = xs.len() as f64;
    let mx = fsum(xs.iter().copied())? / n;
    let sd = (fsum(xs.iter().map(|x| (x - mx) * (x - mx)))? / n).sqrt();
    say!(out, "mean {}", fmt_float(mx));
    say!(out, "sd {}", fmt_float(sd));
    Ok(())
}

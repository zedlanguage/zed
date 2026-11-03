//! 06 matrix multiply. Zed rules used: each product x * y is one IEEE multiplication; the `+`
//! reduction over a float family is the exact sum rounded once (fsum); floats print by
//! fmt_float. Every line, the header "n m p" included, must read as floats; the row ranges are
//! slices: a negative bound counts from the end, and a bound outside the rows is moved to the
//! nearer end.

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};

use crate::zedrt::{at, fmt_float, fsum, parse_float, parse_int};

fn slice<'a, T>(xs: &'a [T], start: &BigInt, stop: &BigInt) -> &'a [T] {
    let len = BigInt::from(xs.len());
    let bound = |i: &BigInt| {
        let j = if i.is_negative() { i + &len } else { i.clone() };
        if j.is_negative() {
            0
        } else {
            j.min(len.clone()).to_usize().expect("at most the length")
        }
    };
    let (a, b) = (bound(start), bound(stop));
    if a < b { &xs[a..b] } else { &[] }
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let row = |l: &String| {
        l.split(' ')
            .map(parse_float)
            .collect::<Result<Vec<f64>, String>>()
    };
    let rows = lines.iter().map(row).collect::<Result<Vec<_>, _>>()?;
    let head = at(lines, 0)?.split(' ').map(parse_int);
    let head = head.collect::<Result<Vec<BigInt>, String>>()?;
    let [n, m, p] = &head[..] else {
        return Err("the header is not n m p".into());
    };
    let a = slice(&rows, &BigInt::from(1), &(1 + n));
    let b = slice(&rows, &(1 + n), &(1 + n + m));
    let count = |x: &BigInt| x.to_usize().unwrap_or(0);
    let (mi, pi) = (count(m), count(p));
    for row in a {
        let mut cells = Vec::new();
        for k in 0..pi {
            let mut products = Vec::new();
            for c in 0..mi {
                products.push(at(row, c)? * at(at(b, c)?, k)?);
            }
            cells.push(fmt_float(fsum(products)?));
        }
        say!(out, "{}", cells.join(" "));
    }
    Ok(())
}

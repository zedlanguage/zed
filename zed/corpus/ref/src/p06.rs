//! 06 matrix multiply. Zed rules used: each product x * y is one IEEE multiplication; the `+`
//! reduction over a float family is plain IEEE addition on the canonical tree (fsum, DESIGN
//! sec:reduction items 1 and 2); floats print by
//! fmt_float. The program's `else` defaults (06-matrix-multiply.zed lines 9-16): a field that
//! `f64` does not read is 0.0 (try_parse_float), a header field that `int` does not read is 0
//! (try_parse_int), a missing header field is 0, and a cell of B past the end of its row is 0.0.
//! The row ranges are slices: a negative bound counts from the end, and a bound outside the rows
//! is moved to the nearer end. A row of A shorter than m, or a B of fewer than m rows, is an
//! index error: the program's `zip` has no `else` there (row FAIL-corpus-06-zip-keys).

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

use crate::zedrt::{at, fmt_float, fsum, try_parse_float, try_parse_int};

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
            .map(|t| try_parse_float(t).unwrap_or(0.0))
            .collect::<Vec<f64>>()
    };
    let rows: Vec<Vec<f64>> = lines.iter().map(row).collect();
    let head: Vec<BigInt> = lines
        .first()
        .map_or("", String::as_str)
        .split(' ')
        .map(|t| try_parse_int(t).unwrap_or_else(BigInt::zero))
        .collect();
    let zero = BigInt::zero();
    let field = |i: usize| head.get(i).unwrap_or(&zero);
    let (n, m, p) = (field(0), field(1), field(2));
    let a = slice(&rows, &BigInt::from(1), &(1 + n));
    let b = slice(&rows, &(1 + n), &(1 + n + m));
    let count = |x: &BigInt| x.to_usize().unwrap_or(0);
    let (mi, pi) = (count(m), count(p));
    for row in a {
        let mut cells = Vec::new();
        for k in 0..pi {
            let mut products = Vec::new();
            for c in 0..mi {
                products.push(at(row, c)? * at(b, c)?.get(k).copied().unwrap_or(0.0));
            }
            cells.push(fmt_float(fsum(products)));
        }
        say!(out, "{}", cells.join(" "));
    }
    Ok(())
}

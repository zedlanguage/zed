//! 06 matrix multiply. Zed rules used: each product x * y is one IEEE multiplication; the `+`
//! reduction over a float family is plain IEEE addition on the canonical tree, and over no
//! value it is -0.0 (fsum, DESIGN sec:reduction items 1 and 2, "Identity as data"); floats
//! print by fmt_float. The program's `else` defaults (06-matrix-multiply.zed lines 12-19): a
//! field that `f64` does not read is 0.0 (try_parse_float), a header field that `int` does not
//! read is 0 (try_parse_int), a missing header field is 0, and a cell of A or of B past the end
//! of its row is 0.0. The row ranges are `.slice(r)` (DESIGN, the bound table): the lines whose
//! rank, from 0, lies in `r`, keeping their keys; a range with no line in it is empty. Entry
//! (i, k) sums over B's lines c in order, A's cell c - 1 - n times B's cell k.

use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

use crate::zedrt::{fmt_float, fsum, try_parse_float, try_parse_int};

/// The ranks of `0..len` in `lo..hi`, as `.slice(lo..<hi)` keeps them.
fn ranks(len: usize, lo: &BigInt, hi: &BigInt) -> std::ops::Range<usize> {
    let clamp = |i: &BigInt| {
        let i = i.clone().clamp(BigInt::zero(), BigInt::from(len));
        i.to_usize().expect("in 0..=len")
    };
    let lo = clamp(lo);
    lo..clamp(hi).max(lo)
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
    let (n, inner, p) = (field(0), field(1), field(2));
    let a = ranks(rows.len(), &BigInt::from(1), &(1 + n));
    let b = ranks(rows.len(), &(1 + n), &(1 + n + inner));
    // B's line c is A's column c - 1 - n, which is at least 0: c >= 1 + n where 1 + n >= 0, and
    // c >= 0 > 1 + n otherwise; a column past usize is past every row. Columns of A from `inner`
    // on are never read, as in the program.
    let column = |c: usize| (BigInt::from(c) - 1u8 - n).to_usize();
    // `row[j] else 0.0`, with `None` for a j past usize.
    let at = |r: &[f64], j: Option<usize>| j.and_then(|j| r.get(j)).copied();
    for i in a {
        let mut cells = Vec::new();
        // `for k in 0..<p`, p a BigInt: the output has a cell per k, so its size bounds the loop.
        let mut k = BigInt::zero();
        while &k < p {
            let terms = b.clone().map(|c| {
                let x = at(&rows[i], column(c)).unwrap_or(0.0);
                x * at(&rows[c], k.to_usize()).unwrap_or(0.0)
            });
            cells.push(fmt_float(fsum(terms)));
            k += 1;
        }
        say!(out, "{}", cells.join(" "));
    }
    Ok(())
}

//! 24 weighted pick: least i with `cumul[i] > q`, by bisect_right on the prefix sums (the program's
//! binary search must agree), or none when q >= total. bisect_right halves the range [lo, hi)
//! while lo < hi, going right when q >= the middle prefix sum, so a negative weight gives a
//! defined answer too.

use num_bigint::BigInt;
use num_traits::Zero;

use crate::zedrt::{at, parse_int};

fn bisect_right(a: &[BigInt], x: &BigInt) -> usize {
    let (mut lo, mut hi) = (0, a.len());
    while lo < hi {
        let mid = (lo + hi) / 2;
        if *x < a[mid] {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    lo
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let mut total = BigInt::zero();
    let mut cumul = Vec::new();
    for x in at(lines, 0)?.split(' ') {
        total += parse_int(x)?;
        cumul.push(total.clone());
    }
    for l in &lines[1..] {
        let q = parse_int(l)?;
        if q >= total {
            say!(out, "{q} none");
        } else {
            say!(out, "{q} {}", bisect_right(&cumul, &q));
        }
    }
    Ok(())
}

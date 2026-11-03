//! 05 maximum prefix sum: max(0, max of prefix sums), the fold with state (sum, best) started
//! at (0, 0), and the total.

use num_bigint::BigInt;
use num_traits::Zero;

use crate::zedrt::parse_int;

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let xs = lines
        .iter()
        .map(|l| parse_int(l))
        .collect::<Result<Vec<BigInt>, String>>()?;
    let mut s = BigInt::zero();
    let mut direct = BigInt::zero();
    for x in &xs {
        s += x;
        if s > direct {
            direct.clone_from(&s);
        }
    }
    let (mut sum, mut best) = (BigInt::zero(), BigInt::zero());
    for x in &xs {
        sum += x;
        if sum > best {
            best.clone_from(&sum);
        }
    }
    say!(out, "{direct} {best} {sum}");
    Ok(())
}

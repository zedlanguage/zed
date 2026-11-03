//! 18 windowed word frequency: window start t div 5 * 5, words case folded, empty pieces (from
//! double spaces) dropped, words in code-point order. A line whose first piece is not an int is
//! skipped; a window exists once it has a word.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_integer::Integer;

use crate::zedrt::{lower, try_parse_int};

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let five = BigInt::from(5);
    let mut wins: BTreeMap<BigInt, BTreeMap<String, usize>> = BTreeMap::new();
    for l in lines {
        let mut w = l.split(' ');
        let Some(t) = w.next().and_then(try_parse_int) else {
            continue;
        };
        for x in w.filter(|x| !x.is_empty()) {
            let window = wins.entry(t.div_floor(&five) * &five).or_default();
            *window.entry(lower(x)).or_default() += 1;
        }
    }
    for (w, c) in &wins {
        let cells: Vec<String> = c.iter().map(|(x, n)| format!("{x}={n}")).collect();
        say!(out, "{w}: {}", cells.join(" "));
    }
    Ok(())
}

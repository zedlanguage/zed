//! 29 late-arrival dedup, under the window rule this corpus assumes: readings are taken in
//! arrival order (the input's line order); the watermark is the largest event time seen so far
//! minus the lateness 5; a reading is dropped (late: #drop) when its window's end, start + 10, is
//! at or below the watermark at its arrival. Kept readings are deduplicated per window and id,
//! first arrival wins (group then first). Windows print in start order, ids in code-point order.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_integer::Integer;

use crate::zedrt::parse_int;

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let (five, ten) = (BigInt::from(5), BigInt::from(10));
    let mut wins: BTreeMap<BigInt, BTreeMap<&str, BigInt>> = BTreeMap::new();
    let mut top: Option<BigInt> = None;
    for l in lines {
        let w: Vec<&str> = l.split(' ').collect();
        let &[i, ts, vs] = &w[..] else {
            return Err(format!("not \"id time value\": {l}"));
        };
        let (t, v) = (parse_int(ts)?, parse_int(vs)?);
        let start = t.div_floor(&ten) * &ten;
        let wm = top.as_ref().map(|top| top - &five);
        top = Some(top.map_or(t.clone(), |top| top.max(t)));
        if wm.is_some_and(|wm| &start + &ten <= wm) {
            continue;
        }
        wins.entry(start).or_default().entry(i).or_insert(v);
    }
    for (w, ids) in &wins {
        let cells: Vec<String> = ids.iter().map(|(i, v)| format!("{i}={v}")).collect();
        say!(out, "{w}: {}", cells.join(" "));
    }
    Ok(())
}

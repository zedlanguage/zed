//! 23 join zoo. Keys in int order; a missing side prints '-'; amounts per id are summed (group
//! then sum). Output order: the four join blocks, then the difference lines, then the
//! range-split check.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;

use crate::zedrt::parse_int;

type Totals = BTreeMap<BigInt, BigInt>;

fn side(d: &Totals, k: &BigInt) -> String {
    d.get(k).map_or("-".into(), BigInt::to_string)
}

fn joined<'a>(xs: impl IntoIterator<Item = &'a BigInt>) -> String {
    let words: Vec<String> = xs.into_iter().map(BigInt::to_string).collect();
    words.join(" ")
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let (mut o, mut p) = (Totals::new(), Totals::new());
    for l in lines {
        let w: Vec<&str> = l.split(' ').collect();
        let &[s, i, n] = &w[..] else {
            return Err(format!("not \"side id amount\": {l}"));
        };
        let (key, amount) = (parse_int(i)?, parse_int(n)?);
        *(if s == "O" { &mut o } else { &mut p })
            .entry(key)
            .or_default() += amount;
    }
    for (k, v) in &o {
        if let Some(q) = p.get(k) {
            say!(out, "inner {k} {v} {q}");
        }
    }
    for (k, v) in &o {
        say!(out, "left {k} {v} {}", side(&p, k));
    }
    for (k, v) in &p {
        say!(out, "right {k} {} {v}", side(&o, k));
    }
    let all: BTreeSet<&BigInt> = o.keys().chain(p.keys()).collect();
    for k in all {
        say!(out, "outer {k} {} {}", side(&o, k), side(&p, k));
    }
    let only_l: BTreeSet<&BigInt> = o.keys().filter(|k| !p.contains_key(*k)).collect();
    let only_r: BTreeSet<&BigInt> = p.keys().filter(|k| !o.contains_key(*k)).collect();
    say!(out, "unpaid {}", joined(only_l.iter().copied()));
    say!(out, "unordered {}", joined(only_r.iter().copied()));
    say!(out, "symdiff {}", joined(only_l.union(&only_r).copied()));
    let ten = BigInt::from(10);
    let low = o.iter().filter(|(k, _)| **k < ten);
    let high = o.iter().filter(|(k, _)| **k >= ten);
    let rejoined: BTreeMap<&BigInt, &BigInt> = low.chain(high).collect();
    let equal = rejoined.len() == o.len() && rejoined.iter().all(|(k, v)| o.get(*k) == Some(*v));
    say!(
        out,
        "rejoined {}",
        if equal { "equal" } else { "different" }
    );
    Ok(())
}

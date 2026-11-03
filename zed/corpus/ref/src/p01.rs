//! 01 word count. Zed rules used: split(" ") keeps empty pieces (removed by the where); group
//! keys are the lower-cased words; a push of a String-keyed map into stdout is in the keys'
//! natural order, code-point order (sec:order).

use std::collections::BTreeMap;

use crate::zedrt::lower;

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    for w in lines
        .iter()
        .flat_map(|l| l.split(' '))
        .filter(|w| !w.is_empty())
    {
        *counts.entry(lower(w)).or_default() += 1;
    }
    for (w, n) in &counts {
        say!(out, "{w} {n}");
    }
    Ok(())
}

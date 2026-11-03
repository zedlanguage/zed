//! 02 histogram. Both columns are computed independently, as the two spellings are; rows for
//! lengths 1..=maxLen, a missing scatter key printing 0. A length counts code points.

use std::collections::HashMap;

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let pieces = lines.iter().flat_map(|l| l.split(' '));
    let mut words: Vec<usize> = pieces
        .filter(|w| !w.is_empty())
        .map(|w| w.chars().count())
        .collect();
    let mut hist_a: HashMap<usize, usize> = HashMap::new();
    for &n in &words {
        *hist_a.entry(n).or_default() += 1;
    }
    words.sort_unstable();
    let mut shorter = 0;
    for n in 1..=words.last().copied().unwrap_or(0) {
        let upto = shorter + words[shorter..].partition_point(|len| *len <= n);
        let hist_b = upto - shorter;
        shorter = upto;
        say!(out, "{n} {} {hist_b}", hist_a.get(&n).unwrap_or(&0));
    }
    Ok(())
}

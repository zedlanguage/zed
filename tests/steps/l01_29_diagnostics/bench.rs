//! Benchmarks of the diagnostics step (DESIGN.md Part G), run by `tools/run_tests.sh --bench` and
//! left out of its default run (TEST-bench-split). Each check they make besides the ratio has a
//! small instance among the correctness tests.

use std::collections::HashSet;

use zed_tests::scaling;

use super::rejected;

/// `n` functions, each ordering a text with a literal of the number the text reads, spelled in
/// hexadecimal, binary, octal or with `_` in turn, the text first in every other one (row
/// REPAIR-text-cast-spelling), and the repair each is offered: the number the text reads, in
/// decimal, in place of the text.
fn texts_beside_their_values(n: usize) -> (String, HashSet<String>) {
    let mut src = String::new();
    let mut repairs = HashSet::with_capacity(n);
    for i in 0..n {
        let v = 1000 + i;
        let lit = match i % 4 {
            0 => format!("0x{v:x}"),
            1 => format!("0b{v:b}"),
            2 => format!("0o{v:o}"),
            _ => format!("{}_{:03}", v / 1000, v % 1000),
        };
        let (expr, repair) = if i % 2 == 0 {
            (format!("\"{v}\" < {lit}"), format!("{v} < {lit}"))
        } else {
            (format!("{lit} >= \"{v}\""), format!("{lit} >= {v}"))
        };
        src += &format!("site{i}() {{ c = {expr}; return c; }}\n");
        repairs.insert(repair);
    }
    (src, repairs)
}

#[test]
fn writing_the_number_a_text_reads_beside_literals_of_its_value_scales() {
    // Each site's repair is the cast's value printed in decimal, O(1) for these short texts, so
    // the work is linear in the n sites. Before the fix the value was written through the
    // program's spellings of literals near the site, a search of O(log s) for s spelled
    // literals, and came out as the other operand's spelling. The check reads each headline once
    // and looks its repair up in the set of expected repairs, O(n) in all.
    let srcs = scaling::inputs(750, texts_beside_their_values);
    scaling::check(
        "n texts ordered with literals of their values in other spellings",
        750,
        |n| {
            let (src, repairs) = &srcs[&n];
            let out = rejected(src);
            let mut offered = 0;
            for line in out.lines() {
                let Some((_, rest)) = line.split_once(" Try `") else {
                    continue;
                };
                let repair = rest.strip_suffix("` instead.").expect("a repair headline");
                assert!(repairs.contains(repair), "{repair}\n{out}");
                offered += 1;
            }
            assert_eq!(offered, n, "{out}");
        },
    );
}

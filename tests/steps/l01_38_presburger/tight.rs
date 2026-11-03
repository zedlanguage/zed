//! The family on which the general simplex is above O(N log N) (COMPLEXITY.md, S18, "Not
//! fixed"), kept so that the hard-algorithm cross-review xt and the later fix measure the same
//! systems. Ignored: at 64 variables it takes about 10 s. Run it with
//! `cargo test -p zed-tests --test steps tight -- --ignored --nocapture`.

use std::time::Instant;

use zed_tests::instances::Rng;
use zedc::store::presburger::{Con, Formula, Lin, decide};

use super::scaling::x;

/// `2n` rows of up to three terms over `n` variables, coefficients in `-5..=5`, each holding at
/// a random point with slack at most 3: no elimination keeps the rows, so the last step is the
/// simplex, and the point is tight on many rows.
fn tight(n: usize, seed: u64) -> Formula {
    let mut g = Rng::new(seed);
    let p: Vec<i64> = (0..n).map(|_| g.int(-50, 50)).collect();
    let mut r = Vec::new();
    for _ in 0..2 * n {
        let mut t: Vec<(usize, i64)> = Vec::new();
        for _ in 0..3 {
            let i = g.below(n);
            if !t.iter().any(|q| q.0 == i) {
                let c = g.int(-5, 5);
                t.push((i, if c == 0 { 1 } else { c }));
            }
        }
        let at: i64 = t.iter().map(|(i, c)| c * p[*i]).sum();
        let l = t.iter().fold(Lin::constant(g.int(0, 3) - at), |l, (i, c)| {
            l.plus(&x(*i).times(*c))
        });
        r.push(Formula::Con(Con::ge(&l, &Lin::constant(0))));
    }
    Formula::and(r)
}

#[test]
#[ignore = "cross-review xt: the general simplex on this family takes about 10 s at 64 variables"]
fn the_tight_three_term_family() {
    for n in [16, 32, 48, 64] {
        let f = tight(n, 0xfeed_beef_1380);
        let t = Instant::now();
        let a = decide(&f);
        eprintln!("{n} variables: {a:?} in {:.3} s", t.elapsed().as_secs_f64());
    }
}

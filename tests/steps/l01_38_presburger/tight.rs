//! The family on which the general simplex was above O(N log N) (COMPLEXITY.md, S18): rows of
//! three terms that no elimination keeps, refused with Growth after one pass over their terms
//! (the box of their bounds and its five points), at n and 8n.

use zed_tests::instances::Rng;
use zedc::store::presburger::{Con, Formula, Lin};

use super::scaling::x;

/// `2n` rows of up to three terms over `n` variables, coefficients in `-5..=5`, each holding at
/// a random point with slack at most 3: no elimination keeps the rows, so the last step is the
/// box of the bounds, and the point is tight on many rows.
pub(super) fn tight(n: usize, seed: u64) -> Formula {
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

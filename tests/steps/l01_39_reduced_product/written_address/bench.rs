//! Benchmarks of `written_address`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn writing_scales_with_the_constraints_and_the_parts() {
    // `2k` constraints that are `k` addresses: the writes cost about `k log k`. The scope and
    // the constraints are built before the timing.
    let base = ints(&["n".into()]);
    let built = scaling::inputs(256, renamed_pairs);
    scaling::check("2k written constraints, k addresses", 256, |k| {
        let mut s = base.clone();
        for c in &built[&k] {
            s.write(c.clone());
        }
        assert_eq!(s.written.len(), k);
    });
    // Two constraints of `d` shared parts each, alike up to their binder name: the key costs
    // `d`, where the printed text has `2^d` names.
    let built = scaling::inputs(16, |d| [doubled("x", d), doubled("y", d)]);
    scaling::check("a written constraint of d shared parts", 16, |d| {
        let mut s = base.clone();
        for c in &built[&d] {
            s.write(c.clone());
        }
        assert_eq!(s.written.len(), 1);
    });
}

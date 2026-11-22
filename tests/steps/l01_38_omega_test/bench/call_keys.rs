//! The preimage of calls whose compound arguments have one linear term but are read in
//! different callers' scopes (BENCH-preimage-call-key-bound-sharing), at `n` and `8n`.

use zedc::store::preimage::{Demand, preimage};

use zed_tests::scaling;
use zed_tests::step_helpers::l01_25_preimage_catalog::{doms, function};

/// `ok(x) = c1(x: x, z: 1) && … && c{k}(x: x, z: k)` with `c{i}(x, z) = z > 0 && g(p: x +
/// 1)`, `g(p) = p != 2 && … && p != k + 1` (not `f{i}`, since `f32` and `f64` name types):
/// each `c{i}` calls `g` with the compound argument `x + 1`, of one linear term, read in
/// `c{i}`'s own scope, which differs from every other caller's by the binding of `z` to `i`,
/// though the binding `x + 1` reads is the same, the input `x`. A call key that held the
/// argument's form and its whole scope (`Tx::bound_term`, b93ded85e) would read `g`'s `k`
/// tests `k` times, `O(k^2)`; read once for all callers, `O(k)`.
fn callers_of_one_callee(k: usize) -> String {
    let tests: Vec<String> = (2..k + 2).map(|j| format!("p != {j}")).collect();
    let mut src = format!("g(p: int) = {};\n", tests.join(" && "));
    for i in 1..=k {
        src += &format!("c{i}(x: int, z: int) = z > 0 && g(p: x + 1);\n");
    }
    let calls: Vec<String> = (1..=k).map(|i| format!("c{i}(x: x, z: {i})")).collect();
    src += &format!("ok(x: int) = {};\n", calls.join(" && "));
    src
}

/// The preimage of `true` under [`callers_of_one_callee`] at `k` callers is the domain less
/// `1 ..= k`, the `x` with `x + 1 = j` for a `j` of `2 ..= k + 1`, exact.
#[test]
fn callers_of_one_callee_by_a_compound_argument_scale() {
    scaling::check_inputs(
        "the preimage of k callers passing x + 1 to one callee of k tests",
        200,
        |k| {
            let (ps, body) = function(&callers_of_one_callee(k));
            let ds = doms(&[(&*ps[0], Some(-1_000_000), Some(1_000_000))]);
            (ps, body, ds)
        },
        |(ps, body, ds)| {
            let p = preimage(body, ds, &Demand::Bool(true));
            let x = &p.domains[&ps[0]];
            assert!(p.exact && x.contains(0) && !x.contains(1), "{p:?}");
        },
    );
}

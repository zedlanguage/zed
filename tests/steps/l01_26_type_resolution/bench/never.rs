use zed_tests::scaling;

use super::super::never::functions_beside_never;
use super::super::scaling::resolved;

/// A call of `n` functions with needs beside `n` arguments of no value and a literal, all
/// binding one variable: the loop over the arguments is O(n), and the needs of each function
/// are checked once after it (`held` in zedc-check walk.rs `Ck::apply_one`), O(1) each, so
/// the call is O(n). Row PROOF-bind-never-open-cases.
#[test]
fn functions_with_needs_beside_never_scale() {
    let units = resolved(400, functions_beside_never);
    scaling::check_order("n functions with needs beside Never", 400, 1, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

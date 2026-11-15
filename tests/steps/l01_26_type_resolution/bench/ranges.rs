use zed_tests::scaling;

use super::super::ranges::ranged_parameters;
use super::super::scaling::resolved;

/// RANGE-L1: `n` ranged parameters are read and resolved, and then checked, each in time
/// linear in `n`: each range is read once into its parameter's cell, and each argument is
/// compared with it once.
#[test]
fn ranged_parameters_read_and_resolve_in_linear_time() {
    let texts = scaling::inputs(200, ranged_parameters);
    scaling::check("reading and resolving n ranged parameters", 200, |n| {
        let (stmts, _) = zed_tests::deep::resolved(&texts[&n]);
        assert_eq!(stmts.len(), 2 + 3 * n);
    });
}

#[test]
fn ranged_parameters_check_in_linear_time() {
    let units = resolved(200, ranged_parameters);
    scaling::check("checking n ranged parameters", 200, |n| {
        assert_eq!(units[&n].check().errors.len(), n);
    });
}

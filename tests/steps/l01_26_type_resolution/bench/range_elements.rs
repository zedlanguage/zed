use zed_tests::scaling;

use super::super::range_elements::range_moduli;

#[test]
fn range_moduli_scale() {
    // Each read of a lambda parameter that takes a written range's entries reads the range's
    // ends once (`Ck::entry_range`, `range_ints`; row RANGE-element-interval), memoized by span.
    let built = scaling::inputs(1000, |m| {
        let stmts = zed_tests::deep::statements(&range_moduli(m));
        let res = zedc::resolve::resolve(&stmts).unwrap();
        (stmts, res)
    });
    scaling::check(
        "n maps over a range from 1 and n over a range from 0, each taking `x mod i`",
        1000,
        |m| {
            let (stmts, res) = &built[&m];
            let info = zedc::check::walk::check(stmts, res);
            assert_eq!(info.errors.len(), m);
        },
    );
}

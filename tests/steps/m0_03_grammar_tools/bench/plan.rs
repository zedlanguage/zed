//! The `plan` tool's check and fix, each linear in the rows of the plan; what each gives is
//! checked at small sizes by `plan::a_chain_passes_and_its_stale_levels_are_fixed_at_small_sizes`.

use zed_tests::scaling::check;

use crate::plan::{chain, checked, fixed, stale_chain};

#[test]
fn plan_scales_with_the_number_of_rows() {
    let n = 500;
    let texts = [chain(n), chain(8 * n)];
    check("plan, by rows", n, |m| {
        let text = &texts[usize::from(m != n)];
        assert_eq!(checked(text), (true, String::new()));
    });
}

#[test]
fn fix_scales_with_the_number_of_rows() {
    // Every level written as 0, so the fix rewrites every row but the first.
    let n = 500;
    let texts = [stale_chain(n), stale_chain(8 * n)];
    let wants = [chain(n), chain(8 * n)];
    check("plan --fix, by rows", n, |m| {
        let k = usize::from(m != n);
        assert_eq!(fixed(&texts[k]), wants[k]);
    });
}

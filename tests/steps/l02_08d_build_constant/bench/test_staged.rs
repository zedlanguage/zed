//! `zedc test` of n functions on a taken branch and n on a dropped one is linear in n: the
//! benchmark of `test_staged.rs`.

use crate::test_staged::{branches, test};

#[test]
fn test_of_n_taken_and_n_dropped_functions_is_linear() {
    let inputs = zed_tests::scaling::inputs(100, branches);
    zed_tests::scaling::check_order(
        "`zedc test` of n functions on a taken branch and n on a dropped one",
        100,
        1,
        |n| {
            let file = inputs[&n].to_str().unwrap();
            let (status, out, _) = test(&[file]);
            assert_eq!(status, 0);
            assert!(out.ends_with(&format!("{n} not run, 0 rejection units\n")));
        },
    );
}

use super::check;

#[test]
fn if_takes_both_branches_and_else_if_nests_on_the_right() {
    check(&[
        (
            "sign(x) = if x < 0 { -1 } else { 1 };",
            "(def sign (x) = (if (< x 0) (block (return (- 1))) (block (return 1))))",
        ),
        (
            "sign(x) = if x < 0 { -1 } else if x == 0 { 0 } else { 1 };",
            "(def sign (x) = (if (< x 0) (block (return (- 1))) \
             (if (== x 0) (block (return 0)) (block (return 1)))))",
        ),
    ]);
}

#[test]
fn every_branch_block_exports() {
    check(&[(
        "f(x) = if x { y = 1; } else { 2 };",
        "error: this block exports nothing, and a block gives a value, so it must export one. \
             End it with an expression, or with `return e;` to give the value `e`.",
    )]);
}

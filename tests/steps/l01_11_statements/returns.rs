//! `return e;` exports a value and `return a, b;` a tuple; a record display is L2 (step L2.1).

use super::check;

#[test]
fn return_forms() {
    check(&[
        (
            "xs -> { return xs.len; }",
            "(fn (xs) (block (return (. xs len))))",
        ),
        (
            "xs -> { lo = xs.min; hi = xs.max; return lo, hi; }",
            "(fn (xs) (block (= (lo) (. xs min)) (= (hi) (. xs max)) (return lo hi)))",
        ),
        ("xs -> { return xs.min, xs.max, }", "syntax"),
        (
            "xs -> { return { lo: xs.min }; }",
            "(fn (xs) (block (return (record (lo: (. xs min))))))",
        ),
        ("xs -> { return; }", "syntax"),
    ]);
}

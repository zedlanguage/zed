//! `zedc run` of a program branching on n options is linear in n: the benchmark of `staged.rs`.

use crate::staged::run_words;

#[test]
fn run_of_n_option_branches_is_linear() {
    let inputs = zed_tests::scaling::inputs(250, run_words);
    zed_tests::scaling::check_order("`zedc run` of n branches on `build.options`", 250, 1, |n| {
        let (mut out, mut err) = (Vec::new(), Vec::new());
        let words = &inputs[&n];
        assert_eq!(
            zedc::run::command(words, &mut "".as_bytes(), &mut out, &mut err),
            0
        );
    });
}

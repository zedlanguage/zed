//! A call of a prelude word with too many arguments at the rule of low complexity. The input is
//! built in `word_args.rs`, whose test checks it at a small size.

use zed_tests::scaling::{check, inputs};

use super::super::word_args::min_of_n_arguments;

#[test]
fn a_call_with_n_arguments_too_many_scales() {
    // The checker counts the arguments once and writes the message from the first two and the
    // call's text, so the work grows with the length of the call. About 11 µs and 15 KB an
    // argument: 1x about 0.23 s, 2.4 GB at 8n.
    let n = 20_000;
    let built = inputs(n, min_of_n_arguments);
    check("a call of `min` with n arguments", n, |n| {
        let e = zedc::run::load(built[&n].as_bytes()).err().unwrap();
        assert!(e.starts_with("1:5: `min` takes 2 arguments"));
    });
}

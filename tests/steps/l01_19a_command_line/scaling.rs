//! A run reads its command line in time linear in the arguments, up to the family's sort: the
//! words are split at `--` and decoded once each, and the family is built once.

use std::ffi::OsString;

use zed_tests::scaling::{self, FACTOR};

use super::{ECHO, program, run_words, zedc};

#[test]
fn a_run_with_many_arguments_scales() {
    let prog = program("scaling", ECHO);
    let n = 2000;
    // The words of both sizes are built before the runs are measured.
    let words = |n: usize| -> Vec<OsString> {
        let mut w = run_words(&prog, &["--"]);
        w.extend((0..n).map(|i| OsString::from(format!("argument {i}"))));
        w
    };
    let (small, large) = (words(n), words(FACTOR * n));
    scaling::check("`zedc run` echoing n command-line arguments", n, |m| {
        let w = if m == n { &small } else { &large };
        let out = zedc(w);
        assert_eq!(out.status, 0);
        assert_eq!(
            out.stdout.len(),
            (0..m).map(|i| format!("argument {i}\n").len()).sum()
        );
    });
}

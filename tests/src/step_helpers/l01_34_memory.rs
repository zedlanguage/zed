//! Memory-plan helpers of step L1.34 (tests/steps/l01_34_memory).

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Prim, Term};

/// A fresh string: the concatenation of `a` and `b`, made when the program runs.
pub fn cat(a: &str, b: &str) -> Term {
    prim(Prim::Concat, vec![lit(a), lit(b)])
}

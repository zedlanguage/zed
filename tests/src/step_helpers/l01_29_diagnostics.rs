//! Helpers of step L1.29 (tests/steps/l01_29_diagnostics and l01_29_repairs_and_printing): the
//! diagnostics of a rejected program and the step texts in them.

use zedc::run::load;

/// The rendered diagnostics of the rejected program `src`.
pub fn rejected(src: &str) -> String {
    match load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e,
    }
}

/// The step texts of the rendered diagnostics `out`, without their places.
pub fn steps(out: &str) -> Vec<&str> {
    out.lines()
        .filter_map(|l| {
            let l = l.trim_start();
            let rest = l.strip_prefix('[')?;
            let (_, rest) = rest.split_once("] ")?;
            Some(rest.trim_start().split_once(": ")?.1)
        })
        .collect()
}

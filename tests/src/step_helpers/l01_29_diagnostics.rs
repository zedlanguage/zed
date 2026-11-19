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

/// `src` as a whole program: a `main` that pushes `""` is added when it declares none, so that
/// `load` checks its functions.
pub fn with_main(src: &str) -> String {
    match src.contains("main(") {
        true => src.to_string(),
        false => format!("{src}main(m: MainArgs) {{\n  m.stdout <- \"\";\n}}\n"),
    }
}

/// [`rejected`] of `src` [`with_main`].
pub fn rejected_with_main(src: &str) -> String {
    rejected(&with_main(src))
}

/// Whether the program `src` [`with_main`] is accepted.
pub fn accepted_with_main(src: &str) -> bool {
    load(with_main(src).as_bytes()).is_ok()
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

//! Step L1.29: diagnostics. A rejection shows its derivation: each type constraint and each
//! step of propagation that led to it, numbered and placed in the source, the declarations
//! and signatures it met, every failing combination of a signature search, and the repairs
//! the checker discharges.

mod derivations;
mod layout;
mod repairs;
mod scaling;
mod variants;

use zedc::run::load;

/// The rendered diagnostics of the rejected program `src`.
fn rejected(src: &str) -> String {
    match load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e,
    }
}

/// The step texts of the rendered diagnostics `out`, without their places.
fn steps(out: &str) -> Vec<&str> {
    out.lines()
        .filter_map(|l| {
            let l = l.trim_start();
            let rest = l.strip_prefix('[')?;
            let (_, rest) = rest.split_once("] ")?;
            Some(rest.trim_start().split_once(": ")?.1)
        })
        .collect()
}

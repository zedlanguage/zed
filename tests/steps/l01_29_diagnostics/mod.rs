//! Step L1.29: diagnostics. A rejection shows its derivation: each type constraint and each
//! step of propagation that led to it, numbered and placed in the source, the declarations
//! and signatures it met, every failing combination of a signature search, and the repairs
//! the checker discharges.

mod above;
mod always_fails;
mod batch;
mod binder_type;
mod body_display;
mod bug;
mod casts;
mod declared;
mod derivations;
mod domain_repairs;
mod emptied;
mod explained;
mod fresh_names;
mod group_site;
mod kernel_names;
mod kinds;
mod layout;
mod literal_steps;
mod markers;
mod menu_order;
mod negative_literals;
mod neglit;
mod offered_repairs;
mod order;
mod overload_cycles;
mod printed;
mod quoted;
mod rare;
mod recursion;
mod refused_warning;
mod rejection_addresses;
mod repairs;
mod scaling;
mod stable;
mod sum_plus;
mod suppress;
mod type_size;
mod tyvars;
mod untracked;
mod variants;
mod widen;
mod widen_test;

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

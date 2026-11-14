//! Step L1.17: the representation of values. Integers are unbounded and rationals exact;
//! every value has a place in one total order, numbers by value across kinds; the language's
//! `==` is IEEE 754 at floats and the bitwise identity of keys elsewhere; an atom carries a
//! payload by position or by name; and `==` on functions waits for the enumerable domain
//! their types give.

mod asks;
mod atoms;
mod bench;
mod edges;
mod equality;
mod fields;
mod in_place;
pub(crate) mod memory_check;
mod numbers;
mod order;
mod powers;
mod products;
mod string_copies;
mod subquadratic;

/// The seed of a random test: the environment variable `var` when it is set, to run a failure
/// again, else a new one from the clock, so each run draws other cases. Printed either way.
fn seed(var: &str) -> u64 {
    let s = std::env::var(var)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| {
            let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH);
            t.expect("a clock after 1970").as_nanos() as u64
        });
    eprintln!("seed {s}; {var}={s} draws the same cases");
    s
}

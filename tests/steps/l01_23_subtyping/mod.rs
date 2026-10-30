//! Step L1.23: semantic subtyping. `a <: b` iff `a & !b` is empty, decided by a memoized
//! coinductive check; recursive definitions are checked for contractivity, regularity and
//! monotonicity in emptiness when they are defined. The check is compared with an exact oracle
//! over random types, and run on the spec's examples and on recursive types. The four
//! definitions the plan names are written here as kernel definition groups: `type`
//! declarations, which elaborate to them, join at L2.

mod cases;
mod oracle;
mod rec;

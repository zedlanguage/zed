//! The benchmarks of l01_29: each checks how a pass grows from n to 8n (`tools/run_tests.sh
//! --bench`). The correctness tests of the same code, at small sizes, are in the file of
//! the same name one level up.

mod casts;
mod domain_repairs;
mod order;
mod power_repairs;
mod printed;
mod refused_in_rejection;
mod refused_warning;
mod rejection_addresses;
mod scaling;
mod stable;
mod suppress;
mod too_large;
mod type_size;
mod widen_test;

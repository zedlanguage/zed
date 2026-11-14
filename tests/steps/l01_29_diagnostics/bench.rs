//! The benchmarks of l01_29: each checks how a pass grows from n to 8n (`tools/run_tests.sh
//! --bench`). The correctness tests of the same code, at small sizes, are in the file of
//! the same name one level up.

mod binder_type;
mod casts;
mod declared;
mod domain_repairs;
mod emptied;
mod fold_machine;
mod fresh_names;
mod group_site;
mod layout;
mod main_limits;
mod negative_literals;
mod neglit;
mod order;
mod overload_cycles;
mod package_recovery;
mod power_repairs;
mod printed;
mod quoted;
mod recursion;
mod refused_in_rejection;
mod refused_warning;
mod rejection_addresses;
mod scaling;
mod stable;
mod sum_plus;
mod suppress;
mod syntax_recovery;
mod text_cast_spelling;
mod too_large;
mod type_size;
mod tyvars;
mod widen;
mod widen_test;

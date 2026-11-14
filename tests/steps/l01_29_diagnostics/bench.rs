//! The benchmarks of l01_29: each checks how a pass grows from n to 8n (`tools/run_tests.sh
//! --bench`). The correctness tests of the same code, at small sizes, are in the file of
//! the same name one level up.

mod binder_type;
mod declared;
mod emptied;
mod fold_machine;
mod fresh_names;
mod group_site;
mod layout;
mod main_limits;
mod negative_literals;
mod neglit;
mod overload_cycles;
mod package_recovery;
mod quoted;
mod recursion;
mod sum_plus;
mod syntax_recovery;
mod text_cast_spelling;
mod tyvars;
mod widen;

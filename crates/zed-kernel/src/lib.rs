//! The Zed kernel: the seven generators of the kernel calculus (`reindex`, `discard`, `fold`,
//! `fix`, `gen`, `port`, `fam`; DESIGN.md sec:kernel) and the ZIR node inventory built on them
//! (sec:ir).
//!
//! Every surface form elaborates to these terms, so this crate is the contract between the
//! front end, which produces kernel terms, and every back end, which consumes them. Step M0.9
//! adds the executable big-step reference evaluator here; the inventory is fixed by M0 and
//! built whole at L1 (steps L1.15 and L1.31), so later layers add no term and no node kind.

pub mod budgets;
pub mod error;
pub mod eval;
pub mod exact;
pub mod family;
pub mod num;
pub mod print;
pub mod provenance;
pub mod term;
pub mod types;
pub mod value;
pub mod words;

pub use error::KernelError;
pub use eval::{Evaluator, Lookup, Schedule, Stack, World, eval, on_stack};
pub use family::{Family, Keypath};
pub use num::Rat;
pub use provenance::{Fact, FactAddress, NodeAddress, Provenance};
pub use term::{Evidence, FixKind, Grade, GuardPos, Pattern, Prim, Term, Witness};
pub use types::Universe;
pub use value::{Atom, F64, Value};

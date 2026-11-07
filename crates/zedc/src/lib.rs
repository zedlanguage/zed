//! The Rust-hosted Zed compiler (DESIGN.md Part G, "Host and bootstrap").
//!
//! It holds the whole pipeline: source loading, the lexer, the parser, elaboration to kernel
//! terms, the checker and its constraint store, the definitional interpreter, ZIR, and native
//! code generation. It is structured from L1 as content-hash-keyed incremental queries
//! (step L1.30). It stays as the bootstrap root after the compiler is rewritten in Zed (row S),
//! and its interpreter stays as the permanent differential oracle (step L1.37).

pub use zedc_base::address;
pub use zedc_base::axioms;
pub use zedc_syntax::ast;
pub mod canon;
pub mod check;
pub use zedc_base::cost;
mod defs;
pub use zedc_resolve::docs;
pub mod elab;
pub use zedc_base::fence;
pub use zedc_syntax::format;
pub mod front;
pub use zedc_base::interp;
pub use zedc_syntax::lex;
pub mod mutate;
pub use zedc_syntax::parse;
pub mod query;
pub use zedc_base::rejection;
pub use zedc_resolve::resolve;
mod rows;
pub mod run;
pub use zedc_base::source;
pub mod stage;
pub mod store;
pub mod suppress;
pub mod testing;
pub mod unit;
pub use zedc_base::work;
pub mod zir;

/// The scaling test of the rule of low complexity, shared with the step tests.
#[cfg(test)]
#[path = "../../../tests/src/scaling.rs"]
#[expect(
    dead_code,
    reason = "zedc's tests build no input before a timed run (`inputs`)"
)]
mod scaling;

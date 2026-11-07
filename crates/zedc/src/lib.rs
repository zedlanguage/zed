//! The Rust-hosted Zed compiler (DESIGN.md Part G, "Host and bootstrap").
//!
//! It holds the whole pipeline: source loading, the lexer, the parser, elaboration to kernel
//! terms, the checker and its constraint store, the definitional interpreter, ZIR, and native
//! code generation. It is structured from L1 as content-hash-keyed incremental queries
//! (step L1.30). It stays as the bootstrap root after the compiler is rewritten in Zed (row S),
//! and its interpreter stays as the permanent differential oracle (step L1.37).

pub use zedc_base::address;
pub use zedc_base::axioms;
pub use zedc_base::cost;
pub use zedc_base::fence;
pub use zedc_check::check;
pub use zedc_elab::elab;
pub use zedc_resolve::docs;
pub use zedc_syntax::ast;
pub use zedc_syntax::format;
pub use zedc_zir::canon;
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
pub use zedc_stage::stage;
pub mod store;
pub mod suppress;
pub mod testing;
pub mod unit;
pub use zedc_base::work;
pub use zedc_zir::zir;

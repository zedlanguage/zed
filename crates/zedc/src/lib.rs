//! The Rust-hosted Zed compiler (DESIGN.md Part G, "Host and bootstrap").
//!
//! It holds the whole pipeline: source loading, the lexer, the parser, elaboration to kernel
//! terms, the checker and its constraint store, the definitional interpreter, ZIR, and native
//! code generation. It is structured from L1 as content-hash-keyed incremental queries
//! (step L1.30). It stays as the bootstrap root after the compiler is rewritten in Zed (row S),
//! and its interpreter stays as the permanent differential oracle (step L1.37).

pub mod address;
pub mod ast;
pub mod axioms;
pub mod canon;
pub mod cost;
pub mod elab;
pub mod fence;
pub mod format;
pub mod interp;
pub mod lex;
pub mod parse;
pub mod resolve;
pub mod run;
pub mod source;
pub mod store;
pub mod testing;

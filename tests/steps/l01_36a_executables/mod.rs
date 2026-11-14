//! Step L1.36a: `zedc build file -o out` links the object file of step L1.36 with the runtime
//! library into an executable, which binds its ports from its own command line as `zedc run`
//! does and exits with the same statuses. Two builds of a program give the same bytes, and the
//! executable's outputs and exit status equal the interpreter's.

#![cfg(target_os = "linux")]

// binary.rs is not a module of this target: crates/zed-native/Cargo.toml builds it as the test
// `build_binary`, since only a test of that package can name the zedc executable.
mod agreement;
mod and_or;
mod atoms;
mod bench;
mod command;
mod minmax;
mod mul_edges;
mod one_engine;
mod runtime;
mod sites;

pub(crate) use zed_tests::step_helpers::l01_36a_executables::{
    Ran, built, dir, executable, interpreter,
};

//! The catalog of routines the Rust calls: see `zed_tools::catalog`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::catalog::run)
}

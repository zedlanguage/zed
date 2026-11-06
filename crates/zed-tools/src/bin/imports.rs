//! The import graph checker: see `zed_tools::imports`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::imports::run)
}

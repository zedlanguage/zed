//! The M0.4 layer checker: see `zed_tools::layer`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::layer::run)
}

//! Brings the grammar and fixtures up to the spec: see `zed_tools::sync`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::sync::run)
}

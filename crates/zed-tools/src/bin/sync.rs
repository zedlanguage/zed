//! Copies the spec's fences and grammar: see `zed_tools::sync`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::sync::run)
}

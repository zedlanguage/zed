//! The step target writer: see `zed_tools::step_targets`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::step_targets::run)
}

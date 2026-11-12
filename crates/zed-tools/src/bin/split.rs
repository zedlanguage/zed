//! The parallel-parse study tool: see `zed_tools::split`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::split::run)
}

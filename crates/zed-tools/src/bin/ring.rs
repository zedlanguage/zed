//! The lowest ring of each file: see `zed_tools::ring`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::ring::run)
}

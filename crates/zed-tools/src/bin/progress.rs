//! Writes the spec's PROGRESS.md: see `zed_tools::progress`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::progress::run)
}

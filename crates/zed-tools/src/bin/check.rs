//! The grammar checker: see `zed_tools::check`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::check::run)
}

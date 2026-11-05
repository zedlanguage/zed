//! The citation checker: see `zed_tools::cite`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::cite::run)
}

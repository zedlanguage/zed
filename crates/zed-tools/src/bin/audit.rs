//! The M0.8 audit: see `zed_tools::audit`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::audit::run)
}

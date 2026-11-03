//! The containment fuzz: see `zed_tools::fuzz`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::fuzz::run)
}

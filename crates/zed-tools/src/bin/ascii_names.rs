//! The check that names in Zed code are printable ASCII: see `zed_tools::ascii_names`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::ascii_names::run)
}

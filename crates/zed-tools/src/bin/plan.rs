//! The plan DAG checker: see `zed_tools::plan`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::plan::run)
}

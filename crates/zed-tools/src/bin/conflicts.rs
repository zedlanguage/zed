//! Prints the file-conflict lists of docs/plan_dag.md: see `zed_tools::conflicts`.

fn main() -> std::process::ExitCode {
    zed_tools::main_of(zed_tools::conflicts::run)
}

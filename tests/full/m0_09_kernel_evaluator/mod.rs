//! Step M0.9: what the evaluator does when memory runs out.

use std::os::unix::process::ExitStatusExt;

use zed_kernel::eval;
use zed_kernel::term::build::{app, lam, lit, var};
use zed_tests::kernel::*;

/// Set in the environment of the child process of the test below.
const OUT_OF_MEMORY_CHILD: &str = "ZED_TEST_OUT_OF_MEMORY_CHILD";

#[test]
fn a_recursion_without_end_reports_the_allocation_that_failed() {
    // `w(w)` with `w = me -> 1 + me(me)` nests until memory runs out, which is the machine's
    // failure (DESIGN.md sec:kernel, clause (i)). The test runs itself under a limit on its
    // address space, which `ulimit` in `sh` sets, since the kernel crate forbids unsafe code.
    if std::env::var_os(OUT_OF_MEMORY_CHILD).is_some() {
        let me = app(var("me"), vec![var("me")]);
        let w = lam(&["me"], add(lit(1), me));
        let out = eval(&app(w.clone(), vec![w]));
        panic!("the run ended: {out:?}");
    }
    let path = module_path!().split_once("::").unwrap().1;
    let name = format!("{path}::a_recursion_without_end_reports_the_allocation_that_failed");
    let out = std::process::Command::new("sh")
        .args([
            "-c",
            r#"ulimit -c 0; ulimit -v 1000000; exec "$0" --exact "$1""#,
        ])
        .arg(std::env::current_exe().unwrap())
        .arg(name)
        .env(OUT_OF_MEMORY_CHILD, "1")
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("memory allocation of"),
        "status {:?}: {stderr}",
        out.status
    );
    assert_eq!(out.status.signal(), Some(6), "{stderr}");
}

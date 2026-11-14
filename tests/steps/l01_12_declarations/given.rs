//! The tree of a function whose test table has a `test with` clause (DESIGN.md sec:testing,
//! step L1.21): the rows the clause gives to, then each port with its value, in the order
//! written: one table of one row gives to row 0, the next, of two rows, to rows 1 and 2. What
//! the clause means is tested with its step, l01_21_test_runner/ports.rs.

use super::check;

#[test]
fn a_test_with_clause_prints_its_rows_and_ports() {
    check(&[(
        "main(m: MainArgs) { m.stdout <- m.args[0] else \"\"; }\n\
         test with main::args = \"a\" { \"\" -> \"a\\n\" }\n\
         test with main::args = \"b\", main::env = n -> #notFound { \"x\" -> \"b\\n\", \"y\" -> \"b\\n\" }",
        "(def main ((m.args: CommandLine)) (-> (m.stdout: Lines)) \
         (block (<- m.stdout (else (index m.args 0) (str)))) \
         (test ((str) (str \"a\\n\")) ((str \"x\") (str \"b\\n\")) ((str \"y\") (str \"b\\n\"))) \
         (with (rows 0 1) (main::args (str \"a\"))) \
         (with (rows 1 3) (main::args (str \"b\")) (main::env (fn (n) #notFound))))",
    )]);
}

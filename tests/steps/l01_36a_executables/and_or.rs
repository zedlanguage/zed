//! `&&`, `||` and `if` with a failing operand, run by `zedc run` and by a built executable
//! (SPEC-and-or-failing-operand). `a && b` is `if a { b } else { false }` and `a || b` is
//! `if a { true } else { b }` (DESIGN.md sec:failure), so a failing left operand fails the term,
//! a failing right one fails it only where the left one is `true` for `&&` and `false` for
//! `||`, and the branch an `if` does not take adds nothing.

use std::ffi::OsString;

use super::{Ran, built, dir, executable, interpreter};

/// Prints, for each numbered term, 1 for `true`, 0 for `false` and 9 for `#divByZero`; the
/// `if` terms print their value. The first argument is `y`, and `t` is `true` where the second
/// is "t", `f` its negation, so no term is decided before the run.
const SRC: &str = "\
main(m: MainArgs) {
  y = int(m.args[0] else \"\") else 1;
  t = (m.args[1] else \"\") == \"t\";
  f = !t;
  x = 5;
  d = (x div y) > 0;
  m.stdout <- \"1 ${(if f && d { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"2 ${(if t && d { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"3 ${(if d && f { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"4 ${(if d && t { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"5 ${(if t || d { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"6 ${(if f || d { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"7 ${(if d || t { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"8 ${(if d || f { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"9 ${(if f && ((x div y) > 0) { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"10 ${(if t || ((x div y) > 0) { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"11 ${(if ((x div y) > 0) && f { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"12 ${(if ((x div y) > 0) || t { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"13 ${(if t { 1 } else { x div y }) else #divByZero -> 9}\" ++ \" \" ++
  \"14 ${(if f { x div y } else { 1 }) else #divByZero -> 9}\" ++ \" \" ++
  \"15 ${(if d { 1 } else { 2 }) else #divByZero -> 9}\" ++ \" \" ++
  \"16 ${if y != 0 && (x div y) > 0 { 1 } else { 0 }}\" ++ \" \" ++
  \"17 ${(if f && ((0 mod y) < -4) { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"18 ${(if ((0 mod y) < -4) && f { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"19 ${(if t && ((0 mod y) < -4) { 1 } else { 0 }) else #divByZero -> 9}\" ++ \" \" ++
  \"20 ${(if f || ((0 mod y) < -4) { 1 } else { 0 }) else #divByZero -> 9}\";
}
";

#[test]
fn a_failing_operand_fails_and_or_only_where_it_is_taken() {
    let d = dir("and_or");
    let (src, exe) = (d.join("and_or.zed"), d.join("and_or"));
    std::fs::write(&src, SRC).unwrap();
    built(&src, &exe);
    for (args, want) in [
        // `y == 0`, so `d` is `#divByZero`; `t` is `true`.
        (
            ["0", "t"],
            "1 0 2 9 3 9 4 9 5 1 6 9 7 9 8 9 9 0 10 1 11 9 12 9 13 1 14 1 15 9 16 0 17 0 18 9 19 9 20 9",
        ),
        // `y == 0`; `t` is `false`.
        (
            ["0", "f"],
            "1 9 2 0 3 9 4 9 5 9 6 1 7 9 8 9 9 9 10 9 11 9 12 9 13 9 14 9 15 9 16 0 17 9 18 9 19 0 20 1",
        ),
        // Control: `y == 1`, nothing fails.
        (
            ["1", "t"],
            "1 0 2 1 3 0 4 1 5 1 6 1 7 1 8 1 9 0 10 1 11 0 12 1 13 1 14 1 15 1 16 1 17 0 18 0 19 0 20 0",
        ),
    ] {
        // `zedc run` and the executable take the program's own arguments after `--`.
        let after: Vec<OsString> = std::iter::once("--".into())
            .chain(args.iter().map(OsString::from))
            .collect();
        let expected = Ran {
            status: 0,
            stdout: format!("{want}\n"),
            stderr: String::new(),
        };
        assert_eq!(
            interpreter(&src, &after, b""),
            expected,
            "zedc run, {args:?}"
        );
        assert_eq!(
            executable(&exe, &after, b""),
            expected,
            "executable, {args:?}"
        );
    }
}

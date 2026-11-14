//! A tuple or an atom that holds a function (DESIGN.md step L1.17, row FIX-functions-in-tuples)
//! built from a command-line argument, so the run builds it, and from constants: the built
//! executable prints what `zedc run` prints, for each argument.

use std::ffi::OsString;

use super::{Ran, built, dir, executable, interpreter};

/// Program `src`, of test `name`, built and run with argument `n` for each `n` of `runs`, by
/// the executable and by `zedc run`: each gives status 0 and the standard output paired with
/// `n`.
fn agree(name: &str, src: &str, runs: &[(&str, &str)]) {
    let d = dir("held_values");
    let (file, exe) = (d.join(format!("{name}.zed")), d.join(name));
    std::fs::write(&file, src).unwrap();
    built(&file, &exe);
    for (n, out) in runs {
        let words: Vec<OsString> = vec!["--".into(), (*n).into()];
        let want = Ran {
            status: 0,
            stdout: format!("{out}\n"),
            stderr: String::new(),
        };
        assert_eq!(executable(&exe, &words, b""), want, "{name} {n}");
        assert_eq!(interpreter(&file, &words, b""), want, "{name} {n}");
    }
}

/// `t = (f, n); t[0](t[1])`.
#[test]
fn a_tuple_that_holds_a_function_built_from_an_argument_is_read() {
    let src = "f(positional v: int) = v + 1;\nmain(m: MainArgs) {\n  n = int(m.args[0] else \
               \"\") else 0;\n  t = (f, n);\n  m.stdout <- \"${t[0](t[1])}\";\n}\n";
    agree("tuple", src, &[("1", "2"), ("5", "6")]);
}

/// An atom whose payload holds a function, built when the argument is over 2, passed over by
/// an `else` that names another atom.
#[test]
fn an_atom_that_holds_a_function_built_from_an_argument_passes_an_else() {
    let src = "f(positional v: int) = v + 1;\ng(positional a) = a;\nmain(m: MainArgs) {\n  n = \
               int(m.args[0] else \"\") else 0;\n  x = if n > 2 { g(#box(f)) } else { #nope };\n  \
               m.stdout <- (x else #nope -> \"no\") else \"box\";\n}\n";
    agree("payload", src, &[("1", "no"), ("5", "box")]);
}

/// A held tuple chosen at run time, inside a held tuple and a held atom, read two deep.
#[test]
fn a_held_tuple_inside_held_values_is_read_two_deep() {
    let src = "f(positional v: int) = v + 1;\nh(positional v: int) = v * 10;\npick(positional n: \
               int) = if n > 2 { (f, n) } else { (h, n) };\nmain(m: MainArgs) {\n  n = \
               int(m.args[0] else \"\") else 0;\n  p = pick(n);\n  q = ((p, 7), #box(p));\n  r = \
               q[0][0];\n  m.stdout <- \"${r[0](r[1])} ${q[0][1]}\";\n}\n";
    agree("nested", src, &[("1", "10 7"), ("4", "5 7")]);
}

/// An atom that holds a function passes through `*`, `+`, `>` and `if` as any failure does.
#[test]
fn an_atom_that_holds_a_function_passes_through_operators() {
    let src = "f(positional v: int) = v + 1;\ng(positional a) = a;\nmain(m: MainArgs) {\n  n = \
               int(m.args[0] else \"\") else 0;\n  x = if n > 2 { g(#box(f)) } else { n };\n  y = \
               x * 2 + 1;\n  z = if y > 3 { 1 } else { 2 };\n  m.stdout <- \"${(y else #nope -> \
               0) else 99} ${(z else #nope -> 0) else 98}\";\n}\n";
    agree("passes", src, &[("1", "3 2"), ("4", "99 98")]);
}

/// A held tuple of constants, which partial evaluation may fold.
#[test]
fn a_constant_tuple_that_holds_a_function_is_read() {
    let src = "f(positional v: int) = v + 1;\nt = (f, 1);\nmain(m: MainArgs) {\n  m.stdout <- \
               \"${t[0](t[1])}\";\n}\n";
    agree("constant", src, &[("0", "2")]);
}

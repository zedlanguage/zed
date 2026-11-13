//! A run-time error prints its site (plan row RT-sites): `zedc run` and the executable `zedc
//! build` makes print the same text, the error placed at the expression that raised it in the
//! layout of a diagnostic. The sites are kept beside the terms and the graph, so the program's
//! content address and its ZIR text are the same however its source is laid out, and lowering
//! with them is linear in the program.

use std::path::PathBuf;

use zed_tests::scaling;
use zedc::zir::lower::{lower, lower_sited};
use zedc::zir::text::print;

use super::{Ran, built, dir, executable, interpreter};

/// The lines that make `d62`, a string of 2^63 bytes, from the program's arguments: `d0` is
/// the two bytes `[]` when there are none, and each next line doubles the one before. Read
/// from the arguments, the strings are not built while the program is compiled.
fn doubled() -> String {
    let mut src = "main(m: MainArgs) {\n    d0 = String(m.args);\n".to_string();
    for k in 1..=62 {
        src += &format!("    d{k} = d{} ++ d{};\n", k - 1, k - 1);
    }
    src
}

/// The program `src` written to a file of test `name`, built, and run with no words and no
/// input by both engines: the executable's run, then `zedc run`'s.
fn both(name: &str, src: &str) -> (PathBuf, Ran, Ran) {
    let d = dir("sites");
    let file = d.join(format!("{name}.zed"));
    std::fs::write(&file, src).unwrap();
    let exe = d.join(name);
    built(&file, &exe);
    let native = executable(&exe, &[], b"");
    let interpreted = interpreter(&file, &[], b"");
    (file, native, interpreted)
}

/// Checks that `src` stops with status 1 under both engines, the executable writing `stderr`
/// (`FILE` standing for the program's path) after `stdout`, and `zedc run` writing the same
/// output and ending its standard error with the same text, after the warnings it prints
/// first.
fn stops(name: &str, src: &str, stdout: &str, stderr: &str) {
    let (file, native, interpreted) = both(name, src);
    let stderr = stderr.replace("FILE", &file.display().to_string());
    assert_eq!(
        native,
        Ran {
            status: 1,
            stdout: stdout.into(),
            stderr: stderr.clone(),
        },
        "{name}, natively"
    );
    assert_eq!(
        (interpreted.status, interpreted.stdout.as_str()),
        (1, stdout),
        "{name}, by zedc run"
    );
    assert!(
        interpreted.stderr.ends_with(&stderr),
        "{name}, by zedc run, ends its standard error otherwise:\n{}",
        interpreted.stderr
    );
}

#[test]
fn a_number_too_large_is_placed_at_its_operation() {
    stops(
        "plus",
        "main(m: MainArgs) {\n    n = 1;\n    m.stdout <- String(2^2^100 + n);\n}\n",
        "",
        "FILE:3:24: `+` must build a number in full, and the system refused the \
         1267650600228229401496703205379 bytes of memory asked for it; the number is exact and \
         has no size limit, but this machine cannot hold its digits.\n  \
         [1] 3:24: the run stopped here\n      \
         3 |     m.stdout <- String(2^2^100 + n);\n        \
           |                        ^^^^^^^^^^^\n",
    );
}

#[test]
fn a_string_too_long_is_placed_at_its_join() {
    // `d63` is the one join of two strings of 2^63 bytes: line 65, after the 63 lines of
    // `doubled` and `main`'s.
    let src = doubled() + "    d63 = d62 ++ d62;\n    m.stdout <- String(len(d63));\n}\n";
    stops(
        "join",
        &src,
        "",
        "FILE:65:11: `++` cannot join a string of 9223372036854775808 bytes to one of \
         9223372036854775808 bytes: the result would be 18446744073709551616 bytes, more than \
         the 18446744073709551615 bytes a string's length can hold; keep the parts apart, as a \
         list of strings written out one at a time, or join fewer of them.\n  \
         [1] 65:11: the run stopped here\n      \
         65 |     d63 = d62 ++ d62;\n         \
            |           ^^^^^^^^^^\n",
    );
}

/// The message of `lower` refused a string of 2^63 bytes, placed at `line`:`col`, `under`
/// marked under the line `code`.
fn lower_refused(line: usize, col: usize, code: &str, under: &str) -> String {
    let pad = " ".repeat(line.to_string().len());
    format!(
        "FILE:{line}:{col}: `lower` must write a string of 9223372036854775808 bytes, and the \
         system refused the memory for it; the string has no size limit, but this machine \
         cannot hold the result.\n  [1] {line}:{col}: the run stopped here\n      \
         {line} | {code}\n      {pad} | {under}\n"
    )
}

#[test]
fn a_prelude_word_is_placed_at_the_call_in_the_program() {
    // `lower` is a word of the prelude, which has no source in the program: its error is
    // placed at the program's call of it.
    let src = doubled() + "    m.stdout <- lower(d62);\n}\n";
    stops(
        "prelude",
        &src,
        "",
        &lower_refused(
            65,
            17,
            "    m.stdout <- lower(d62);",
            "                ^^^^^^^^^^",
        ),
    );
}

#[test]
fn a_function_of_the_program_is_placed_in_its_body() {
    // The same call of `lower`, made in a function the program defines: the error is placed in
    // that function's body, where the call is written, and not at the call of the function.
    let src = "low(s: String) = lower(s);\n".to_string()
        + &doubled()
        + "    m.stdout <- low(s: d62);\n}\n";
    stops(
        "function",
        &src,
        "",
        &lower_refused(
            1,
            18,
            "low(s: String) = lower(s);",
            "                 ^^^^^^^^",
        ),
    );
}

#[test]
fn a_node_two_expressions_share_takes_the_first_site() {
    // `a` and `b` are the same expression of the same values: one node, which both engines
    // place at `a`, the first written, though `b` is read first.
    let src = doubled()
        + "    a = d62 ++ d62;\n    b = d62 ++ d62;\n    m.stdout <- String(len(b) + len(a));\n}\n";
    stops(
        "shared",
        &src,
        "",
        "FILE:65:9: `++` cannot join a string of 9223372036854775808 bytes to one of \
         9223372036854775808 bytes: the result would be 18446744073709551616 bytes, more than \
         the 18446744073709551615 bytes a string's length can hold; keep the parts apart, as a \
         list of strings written out one at a time, or join fewer of them.\n  \
         [1] 65:9: the run stopped here\n      \
         65 |     a = d62 ++ d62;\n         \
            |         ^^^^^^^^^^\n",
    );
}

/// A program whose `main` joins `n` strings in turn, laid out with `pad` before each line.
fn chain(n: usize, pad: &str) -> String {
    let mut src = format!("main(m: MainArgs) {{\n{pad}s0 = String(m.args);\n");
    for k in 1..=n {
        src += &format!("{pad}s{k} = s{} ++ \"x\";\n", k - 1);
    }
    src + &format!("{pad}m.stdout <- s{n};\n}}\n")
}

#[test]
fn the_sites_change_neither_the_address_nor_the_zir_text() {
    // The same program laid out two ways: its nodes have other sites, and its content
    // address and its graph's text are the same, with sites and without.
    let (one, two) = (chain(3, "    "), chain(3, "\n  "));
    let (p, q) = (
        zedc::run::load(one.as_bytes()).unwrap(),
        zedc::run::load(two.as_bytes()).unwrap(),
    );
    assert!(!p.sites().is_empty());
    assert_eq!(p.address().unwrap(), q.address().unwrap());
    let plain = print(&lower(&p.term()).unwrap());
    let (g, sites) = lower_sited(&p.term(), Some(p.sites())).unwrap();
    let (h, other) = lower_sited(&q.term(), Some(q.sites())).unwrap();
    assert_eq!(print(&g), plain);
    assert_eq!(print(&h), plain);
    assert_eq!(sites.len(), other.len());
    assert!(sites.iter().any(Option::is_some));
    assert_ne!(sites, other);
    // Lowered with no sites, a graph has no table.
    assert_eq!(lower_sited(&p.term(), None).unwrap().1, []);
}

#[test]
fn lowering_with_sites_scales() {
    let n = 200;
    let programs = scaling::inputs(n, |m| zedc::run::load(chain(m, "    ").as_bytes()).unwrap());
    let terms = scaling::inputs(n, |m| programs[&m].term());
    scaling::check("lowering n joins with their sites", n, |m| {
        let (g, sites) = lower_sited(&terms[&m], Some(programs[&m].sites())).unwrap();
        assert!(
            sites.len() >= m && sites.len() < 4 * m + 50,
            "{}",
            sites.len()
        );
        drop(g);
    });
}

#[test]
fn loading_with_sites_scales() {
    // Elaboration marks each node with its site once and the table is frozen in one walk.
    let n = 200;
    let sources = scaling::inputs(n, |m| chain(m, "    "));
    scaling::check("loading n joins, with their sites", n, |m| {
        let p = zedc::run::load(sources[&m].as_bytes()).unwrap();
        assert!(p.sites().len() >= m);
    });
}

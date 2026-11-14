//! A run-time error prints its site (plan row RT-sites): `zedc run` and the executable `zedc
//! build` makes print the same text, the error placed at the expression that raised it in the
//! layout of a diagnostic. The sites are kept beside the terms and the graph, so the program's
//! content address and its ZIR text are the same however its source is laid out, and lowering
//! with them is linear in the program.

use std::path::PathBuf;

use zed_tests::kernel::beyond_machine;
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

/// Checks that `src` stops with `status` under both engines (3 for a fault of the run, as
/// running out of memory, 1 for any other stop), the executable writing `stderr` (`FILE`
/// standing for the program's path) after `stdout`, and `zedc run` writing the same output
/// and ending its standard error with the same text, after the warnings it prints first.
fn stops(name: &str, src: &str, status: u8, stdout: &str, stderr: &str) {
    let (file, native, interpreted) = both(name, src);
    let stderr = stderr.replace("FILE", &file.display().to_string());
    assert_eq!(
        native,
        Ran {
            status,
            stdout: stdout.into(),
            stderr: stderr.clone(),
        },
        "{name}, natively"
    );
    assert_eq!(
        (interpreted.status, interpreted.stdout.as_str()),
        (status, stdout),
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
        "main(m: MainArgs) {\n    n = int(m.args[0] else \"\") else 1;\n    m.stdout <- String(2^2^100 + n);\n}\n",
        3,
        "",
        &format!(
            "FILE:3:24: Number too large for memory: `2^2^100 + n` needs a number of about \
             3.8 × 10^29 digits (1.6 × 10^29 bytes){}.\n  \
             [1] 3:24: the run stopped here\n      \
             3 |     m.stdout <- String(2^2^100 + n);\n        \
               |                        ^^^^^^^^^^^\n",
            beyond_machine()
        ),
    );
}

/// The program raising `base` to `k`, `b = 2^64 + 13` or its rational, `k` 2^64 plus the
/// program's first word read as an integer, so 2^64 when there are none. With `k` read from
/// the input the types do not fix the size, so the checker leaves the power to the run; with
/// `k` written as `2^64`, the power is rejected at compile time (CONST-too-large,
/// l01_29_diagnostics::too_large).
fn input_power(base: &str) -> String {
    format!(
        "main(m: MainArgs) {{\n    b = 2^64 + 13;\n    \
         k = 2^64 + (int(m.args[0] else \"\") else 0);\n    \
         m.stdout <- if k >= 0 {{ String({base} ^ k) }} else {{ \"\" }};\n}}\n"
    )
}

/// Item MSG-too-large-plain: `b ^ k` with `b = 2^64 + 13` and `k = 2^64`, a number of
/// `64 · 2^64 + 1` bits or more, is named as the program writes it, with its size in digits
/// and bytes and the machine's memory. Before, the message named only `^` and a raw count of
/// 22 digits of the memory the evaluator asked for, eight times the number's size. The size
/// in bytes is from 65 bits per factor (plan row MSG-too-large-figure).
#[test]
fn a_power_too_large_is_named_as_written_with_its_size() {
    stops(
        "power",
        &input_power("b"),
        3,
        "",
        &format!(
            "FILE:4:36: Number too large for memory: `b ^ k` needs a number of about \
             3.6 × 10^20 digits (130 EiB){}.\n  [1] 4:36: the run stopped here\n      \
             4 |     m.stdout <- if k >= 0 {{ String(b ^ k) }} else {{ \"\" }};\n        \
               |                                    ^^^^^\n",
            beyond_machine()
        ),
    );
}

/// The same power of the rational `rat(b)`: the same size, named as written.
#[test]
fn a_rational_power_too_large_is_named_as_written_with_its_size() {
    stops(
        "rat_power",
        &input_power("rat(b)"),
        3,
        "",
        &format!(
            "FILE:4:36: Number too large for memory: `rat(b) ^ k` needs a number of about \
             3.6 × 10^20 digits (130 EiB){}.\n  [1] 4:36: the run stopped here\n      \
             4 |     m.stdout <- if k >= 0 {{ String(rat(b) ^ k) }} else {{ \"\" }};\n        \
               |                                    ^^^^^^^^^^\n",
            beyond_machine()
        ),
    );
}

/// `2^(2^64) * b` is a value, `b` times a kept power of 2, but its decimal text, about
/// `0.30 · 2^64` digits, is larger than any memory: `String` of it is named as written, with
/// the size of the text.
#[test]
fn a_string_too_large_is_named_as_written_with_its_size() {
    let src = "main(m: MainArgs) {\n    b = 2^64 + 13;\n    m.stdout <- String(2^(2^64) * b);\n}\n";
    stops(
        "huge_string",
        src,
        3,
        "",
        &format!(
            "FILE:3:17: Text too large for memory: `String(2^(2^64) * b)` would write about \
             5.6 × 10^18 digits (4.8 EiB){}.\n  [1] 3:17: the run stopped here\n      \
             3 |     m.stdout <- String(2^(2^64) * b);\n        \
               |                 ^^^^^^^^^^^^^^^^^^^^\n",
            beyond_machine()
        ),
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
        1,
        "",
        "FILE:65:11: String too long: `d62 ++ d62` would join strings of 8.0 EiB and 8.0 EiB, \
         16 EiB in all; a string holds at most 2^64 - 1 bytes. Keep the parts apart, as a list \
         of strings written out one at a time, or join fewer of them.\n  \
         [1] 65:11: the run stopped here\n      \
         65 |     d63 = d62 ++ d62;\n         \
            |           ^^^^^^^^^^\n",
    );
}

/// The message of `lower` refused a string of 2^63 bytes, placed at `line`:`col`, `under`
/// marked under the line `code`, which writes the call as `call`.
fn lower_refused(line: usize, col: usize, call: &str, code: &str, under: &str) -> String {
    let pad = " ".repeat(line.to_string().len());
    format!(
        "FILE:{line}:{col}: String too large for memory: `{call}` would write a string of \
         8.0 EiB{}.\n  [1] {line}:{col}: the run stopped here\n      \
         {line} | {code}\n      {pad} | {under}\n",
        beyond_machine()
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
        3,
        "",
        &lower_refused(
            65,
            17,
            "lower(d62)",
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
        3,
        "",
        &lower_refused(
            1,
            18,
            "lower(s)",
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
        1,
        "",
        "FILE:65:9: String too long: `d62 ++ d62` would join strings of 8.0 EiB and 8.0 EiB, \
         16 EiB in all; a string holds at most 2^64 - 1 bytes. Keep the parts apart, as a list \
         of strings written out one at a time, or join fewer of them.\n  \
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

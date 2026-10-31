//! Staging at the rule of low complexity (DESIGN.md Part G). Deciding the stage of a term
//! read its free names, and `mix` decided it at every node it entered, so a body of `n`
//! nested definitions was read `O(n)` times, each reading through a scope of `O(n)` names.

use zed_tests::scaling;

use super::{out, staged};

/// `main` with `n` local definitions in a chain from a port, each read by the next; `all`
/// writes their sum, so the last term reads every one.
fn chain(n: usize, all: bool) -> String {
    let mut s = String::from("main(stdin: Lines) -> (stdout: Lines) {\n");
    s += "  x0 = int(stdin[1]) else 0;\n";
    for i in 1..=n {
        s += &format!("  x{i} = x{} + {i};\n", i - 1);
    }
    let last = match all {
        true => (0..=n)
            .map(|i| format!("x{i}"))
            .collect::<Vec<_>>()
            .join(" + "),
        false => format!("x{n}"),
    };
    s += &format!("  stdout <- String({last});\n}}\n");
    s
}

/// `f` on a thread whose stack holds the recursion of a body `O(n)` deep.
fn deep(f: impl FnOnce() + Send + 'static) {
    let t = std::thread::Builder::new().stack_size(1 << 29).spawn(f);
    t.unwrap().join().unwrap();
}

#[test]
fn mixing_a_chain_of_local_definitions_scales() {
    deep(|| {
        scaling::check("mixing a chain of n run-stage definitions", 400, |n| {
            let (_, s, report) = staged(&chain(n, false));
            assert!(report.left.is_empty());
            assert_eq!(out(&s, "1\n"), format!("{}\n", 1 + n * (n + 1) / 2));
        })
    });
}

#[test]
fn mixing_a_term_that_reads_every_definition_scales() {
    deep(|| {
        scaling::check(
            "mixing a chain of n definitions all read at the end",
            200,
            |n| {
                let (_, s, _) = staged(&chain(n, true));
                let want: usize = (0..=n).map(|i| 1 + i * (i + 1) / 2).sum();
                assert_eq!(out(&s, "1\n"), format!("{want}\n"));
            },
        )
    });
}

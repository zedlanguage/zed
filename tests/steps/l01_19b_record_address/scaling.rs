//! A program's content address is taken in O(t log t) for a term of size t, the
//! canonicalizer's cost: measured on a chain of n functions, each calling the one before.

use zed_tests::scaling::{self, FACTOR};
use zedc::run::{Program, load};

/// A program of `n` functions, `step{i}(x) = step{i-1}(x: x) + i`, whose `main` calls the last.
fn chain(n: usize) -> Program {
    let mut src = String::from("step0(x: int) = x;\n");
    for i in 1..n {
        src.push_str(&format!("step{i}(x: int) = step{}(x: x) + {i};\n", i - 1));
    }
    src.push_str(&format!(
        "main(stdin: Lines) -> (stdout: Lines) {{\n  stdout <- \"${{step{}(x: 1)}}\";\n}}\n",
        n - 1
    ));
    load(src.as_bytes()).unwrap()
}

#[test]
fn the_address_of_a_program_scales() {
    let n = 100;
    // Both programs are loaded before the runs are measured. The address is taken from the
    // ports and the term, as `Program::address` does, since that caches it after one run.
    let (small, large) = (chain(n), chain(FACTOR * n));
    assert_ne!(small.address(), large.address());
    scaling::check("the content address of a program of n functions", n, |m| {
        let p = if m == n { &small } else { &large };
        std::hint::black_box(p.ports().address(p.term()));
    });
}

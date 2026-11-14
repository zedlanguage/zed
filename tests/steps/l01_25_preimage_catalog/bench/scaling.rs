//! The checks of `scaling.rs` at `n` and `8n`: the transfer, the exact search and the
//! linear-relation translation, each held to the order the rule of low complexity allows.
//! Each term is built before the timing; `scaling.rs` checks the same terms at small sizes
//! against the interpreter.

use std::sync::Arc;
use zed_kernel::Term;
use zed_tests::scaling;
use zedc::store::preimage::{Classes, Demand, Domains, exact_preimage, preimage, relations};

use crate::scaling::*;
use crate::{doms, pre_listed};

#[test]
fn the_transfer_scales() {
    let ds = doms(&[("i", Some(-50), Some(50))]);
    let ds = &ds;
    let run = |what: &str, n: usize, make: fn(usize) -> Term| {
        let terms = scaling::inputs(n, make);
        scaling::check(what, n, |k| {
            preimage(&terms[&k], ds, &Demand::Bool(true));
        });
    };
    run("a chain of `let`s, each name read twice", 6, doubling);
    run("branches nested in guard position", 6, guards);
    run("a conjunction of tests", 8, conjunction);
    run(
        "functions each calling the one before twice, alike",
        6,
        calls_alike,
    );
    run(
        "functions each calling the one before twice, apart",
        6,
        calls_apart,
    );
}

/// Under `@exact` the search visits fewer than twice as many boxes as there are points in
/// the domain, each in time of the size of the term, so its time is of the order of the
/// number of points: `n` for one input in `0..=n`, `n^2` for two; and where the plain
/// preimage is exact on sub-boxes, of the boxes the boundary crosses: `n` for `x * y <= n`.
#[test]
fn the_exact_search_scales_with_the_number_of_points() {
    let run = |what: &str, n: usize, power: u32, make: fn(usize) -> (Term, Domains)| {
        let made = scaling::inputs(n, make);
        scaling::check_order(what, n, power, |k| {
            let (t, ds) = &made[&k];
            exact_preimage(t, ds, &Classes::new(), &Demand::Bool(true));
        });
    };
    run(
        "`x * x mod 10 == 9` over `0..=n` under `@exact`",
        256,
        1,
        squares,
    );
    run(
        "`x * y mod 7 == 3` over `1..=n` squared under `@exact`",
        16,
        2,
        products,
    );
    run(
        "`x * y <= n` over `1..=n` squared under `@exact`",
        64,
        1,
        hyperbola,
    );
}

#[test]
fn the_linear_translation_of_calls_scales() {
    let ds = doms(&[("i", Some(0), Some(50)), ("j", Some(-50), Some(50))]);
    let ds = &ds;
    for d in [0, 1] {
        let terms = scaling::inputs(6, |k| sums(k, d));
        scaling::check("sums of calls, each calling the one before twice", 6, |k| {
            preimage(&terms[&k], ds, &Demand::Bool(true));
        });
    }
}

/// The sizes the rule of low complexity is about: a summary reads each name in `O(log n)`, and
/// its result and context take the space of what its body reads, whatever encloses it. Sizes
/// 6 and 48 did not show a growth of `n^1.8` that sizes 48 and 384 do. They run on a 2 MiB
/// stack, since the transfer keeps its frames on the heap (PRE-stack-explicit); the terms are
/// built before the timing.
fn long(what: &'static str, make: fn(usize) -> Term, ds: fn(usize) -> Domains) {
    long_at(what, 48, make, ds)
}

/// [`long`] at sizes `n` and `8n`.
fn long_at(what: &'static str, n: usize, make: fn(usize) -> Term, ds: fn(usize) -> Domains) {
    let measure = move || {
        let large = n * scaling::FACTOR;
        let (a, b) = ((make(n), ds(n)), (make(large), ds(large)));
        scaling::check(what, n, |k| {
            let (t, d) = if k == n { &a } else { &b };
            preimage(t, d, &Demand::Bool(true));
        });
    };
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn long_calls_apart() {
    long(
        "functions each calling the one before twice, apart",
        calls_apart,
        one,
    );
}

#[test]
fn long_calls_alike() {
    long(
        "functions each calling the one before twice, alike",
        calls_alike,
        one,
    );
}

#[test]
fn long_doubling() {
    long("a chain of `let`s, each name read twice", doubling, one);
}

#[test]
fn long_reading_the_input() {
    long(
        "a chain of `let`s, each reading the input",
        reading_the_input,
        one,
    );
}

#[test]
fn long_tests_of_many_inputs() {
    long(
        "a conjunction of tests of many inputs",
        tests_of_many_inputs,
        many_inputs,
    );
}

#[test]
fn long_squares_of_one_name() {
    long_at(
        "squares of one long name, each read as a power",
        256,
        squares_of_one_name,
        one,
    );
}

#[test]
fn long_shared_arms() {
    long("branches whose arms are one shared term", shared_arms, one);
}

/// [`long_at`] for the relations of the linear-relation domain.
fn long_relations(what: &'static str, n: usize, make: fn(usize) -> Term) {
    let measure = move || {
        let (a, b) = (make(n), make(n * scaling::FACTOR));
        let inputs: [Arc<str>; 1] = ["i".into()];
        scaling::check(what, n, |k| {
            let t = if k == n { &a } else { &b };
            relations(&[t], &inputs, false).expect("in the domain");
        });
    };
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn long_nested_values() {
    let what = "values nested in the arms of `if`s";
    long_relations(what, 256, nested_values);
    long_at(what, 256, nested_values, one);
}

#[test]
fn long_shared_values() {
    long_relations("`if`s whose arms read one shared term", 256, shared_values);
}

#[test]
fn long_shared_chains() {
    long_relations(
        "chains of `&&` and `||` whose `if` arms read one shared chain",
        256,
        shared_chains,
    );
}

#[test]
fn a_chain_of_and_written_as_ifs_is_joined_in_one_pass() {
    // On origin/main 32654e93 this test fails: k = 256 to 2048 took 0.27 to 22.8 G instructions
    // (86 times) and 0.07 to 4.40 GB (60.1 times; limit 24). Read as a chain (`Walk::chain`):
    // 15.6 to 132 M instructions (8.5 times) and 8.0 times the bytes.
    let measure = || {
        let made = scaling::inputs(256, |k| {
            let names: Vec<Arc<str>> = (0..k).map(|j| format!("a{j}").into()).collect();
            (and_ifs(k), names)
        });
        scaling::check("a chain of k `&&` on k names, written as `if`s", 256, |k| {
            let (t, names) = &made[&k];
            relations(&[t], names, false).expect("in the domain");
        });
    };
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn a_chain_of_or_written_as_ifs_is_joined_in_one_pass() {
    // Read as an `if` (b4e083a7, or `Walk::or_if` turned off) this test fails: k = 256 to 2048
    // took 28.8 to 784 M instructions (27.2 times) and 15.6 to 663 MB (42.6 times; limit 24).
    // Read as `g || b`, a chain (`Walk::chain`): 15.8 to 128 M instructions (8.1 times) and
    // 4.8 to 38.1 MB (8.0 times).
    let measure = || {
        let made = scaling::inputs(256, |k| {
            let names: Vec<Arc<str>> = (0..k).map(|j| format!("a{j}").into()).collect();
            (or_ifs(k), names)
        });
        scaling::check("a chain of k `||` on k names, written as `if`s", 256, |k| {
            let (t, names) = &made[&k];
            relations(&[t], names, false).expect("in the domain");
        });
    };
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

/// [`rereads`] with `r` places and `k` limits, each at `n` and `8n` and both at once: the
/// work is of order `r + k` and not `r k`, since a chain whose formula holds where it is
/// reached on the stack it was read at is read once there (COMPLEXITY.md S31b).
#[test]
fn long_chains_read_at_many_places_under_recursion() {
    let n = 64;
    let measure = move || {
        let inputs: [Arc<str>; 1] = ["i".into()];
        let large = n * scaling::FACTOR;
        let cases = [
            (
                "a chain of 64 limits under recursion read at r places",
                (n, 64),
                (large, 64),
            ),
            (
                "a chain of k limits under recursion read at 64 places",
                (64, n),
                (64, large),
            ),
            (
                "a chain of k limits under recursion read at k places",
                (n, n),
                (large, large),
            ),
        ];
        for (what, (r, k), (r8, k8)) in cases {
            let (a, b) = (rereads(r, k), rereads(r8, k8));
            scaling::check(what, n, |s| {
                let t = if s == n { &a } else { &b };
                relations(&[t], &inputs, false).expect("in the domain");
            });
        }
    };
    let thread = std::thread::Builder::new().stack_size(2 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn long_failing_max_some() {
    long(
        "`max`es whose operands fail, a demand holding some of their values",
        failing_max_some,
        one,
    );
}

#[test]
fn long_failing_max_all() {
    long(
        "`max`es whose operands fail, a demand holding all their values",
        failing_max_all,
        one,
    );
}

/// Closing a call that reads no input visits each shared part once for each scope and set of
/// names bound within it, so `d` nested `if`s over one shared arm close in time of `d`; the
/// tree walk took `2^d`.
#[test]
fn long_closing_shared_arms_in_a_called_lambda() {
    long(
        "a call of a lambda of nested `if`s over one shared arm",
        shared_arms_in_a_called_lambda,
        one,
    );
}

/// A name bound to a value is closed as that value, found once, so the chain closes and runs
/// in time of `k`; copying each name's closed term at each read made a term of `2^k` parts,
/// which the evaluator then ran.
#[test]
fn long_closing_a_chain_of_doubled_calls() {
    long(
        "a chain of calls, each reading the name before twice",
        chain_of_doubled_calls,
        one,
    );
}

#[test]
fn long_shared_values_preimage() {
    long_at(
        "the preimage of `if`s whose arms read one shared term",
        256,
        shared_values,
        one,
    );
}

/// Each part of [`shared_arms_under_recursion`] is read once, in the transfer and in the
/// translation, and not once for each path: d = 14 took 21.6 and 82.9 ms, four times d = 12,
/// before parts read below a stop were remembered (ST-formula-k2-rec).
#[test]
fn long_shared_arms_under_recursion() {
    long_at(
        "`if`s under recursion whose arms are one shared term",
        32,
        shared_arms_under_recursion,
        one,
    );
    long_relations(
        "`if`s under recursion whose arms are one shared term",
        32,
        shared_arms_under_recursion,
    );
}

#[test]
fn a_listed_set_is_enumerated_in_time_of_its_length() {
    let inputs = scaling::inputs(16384, listed_multiples_of_3);
    scaling::check("a listed set of `n` members, enumerated", 16384, |n| {
        let (t, ds) = &inputs[&n];
        pre_listed(t, ds, &Demand::Bool(true));
    });
}

#[test]
fn an_exact_search_reads_only_the_inputs_it_touches() {
    for points in [true, false] {
        let made = scaling::inputs(1024, |n| unread_inputs(n, points));
        scaling::check("an `@exact` search beside n unread inputs", 1024, |n| {
            let (t, ds) = &made[&n];
            let p = exact_preimage(t, ds, &Classes::new(), &Demand::Bool(true));
            assert!(p.exact && p.domains.len() == n + 1);
        });
    }
}

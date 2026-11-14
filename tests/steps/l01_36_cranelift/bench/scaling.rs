//! The counting machine and the native code against the size of the program (the rule of low
//! complexity, DESIGN.md Part G): an atom of many named fields, many lookup ports,
//! many constants, many lambdas and one value used many times each run in time near linear in
//! their number (COMPLEXITY.md Z14); so do the runtime heap's match of a deep constant, many
//! matches of one, and the value of cells that share their parts (COMPLEXITY.md R3). The small
//! instances are in `scaling.rs`.

use std::sync::Mutex;

use zed_kernel::{Evaluator, Term, World};
use zed_rt::Paths;
use zed_tests::scaling;

use crate::planned;
use crate::scaling::{
    both, cases, consts, counted_in, curried, dups, fields, invoice, lambdas, list,
    matched_invoice, nest, on_big_stack, paired, ports, rate_table, read_to_the_end, strings,
    tiers, unused, world,
};

/// `make(n)` and `make(8n)` run by the counting machine and natively in `w`, on a thread with a
/// stack for the recursive passes over the larger.
fn check(what: &str, n: usize, w: &World, make: fn(usize) -> Term) {
    scaling::on_a_thread(1 << 29, || {
        scaling::check(what, n, |n| {
            both(&make(n), w);
        })
    })
}

#[test]
fn an_atom_of_many_named_fields_scales() {
    check(
        "an atom of n named fields, matched",
        2_500,
        &World::new(),
        fields,
    );
}

#[test]
fn a_tuple_of_many_lookup_ports_scales() {
    let n = 1_300;
    check(
        "a tuple of n lookup ports",
        n,
        &world(scaling::FACTOR * n),
        ports,
    );
}

#[test]
fn many_constants_scale() {
    check("a tuple of n constants", 18_000, &World::new(), consts);
}

#[test]
fn many_lambdas_scale() {
    check("n lambdas, each called", 500, &World::new(), lambdas);
}

#[test]
fn one_value_used_many_times_scales() {
    check(
        "one cell used n times by one node",
        13_000,
        &World::new(),
        dups,
    );
}

/// `make` at each of `n` and `8n`, planned ahead of the timing, with the object file of each
/// timed by `scaling::check`.
fn check_depth(what: &str, n: usize, make: fn(usize) -> Term) {
    on_big_stack(|| {
        let at = |m: usize| planned(&make(m));
        let (small, large) = (at(n), at(8 * n));
        scaling::check(what, n, |m| {
            let (g, p) = if m == n { &small } else { &large };
            std::hint::black_box(zed_native::object(g, p).unwrap());
        });
    });
}

#[test]
fn a_rate_table_of_many_tiers_scales() {
    check_depth("a chain of n `if`s, to an object file", 1_200, |d| {
        tiers(d, 0)
    });
}

/// The ratio grows with n: 8.49 at n = 125, 10.05 at 500 and 12.02 at 1,000 (2026-11-14), most
/// of the growth in the register allocator's dominator tree (plan row
/// CRANELIFT-nested-if-domtree); n stays at 500 until that is fixed.
#[test]
fn ifs_nested_through_the_first_arm_scale() {
    check_depth("n nested `if`s, to an object file", 500, nest);
}

#[test]
fn a_decoder_of_many_cases_scales() {
    check_depth("a chain of n `match`es, to an object file", 3_000, |d| {
        cases(d, 0)
    });
}

#[test]
fn a_curried_function_of_many_parameters_scales() {
    check_depth("n nested lambdas, to an object file", 1_200, curried);
}

/// `make(m)` for each run at each of `n` and `8n`, as many as the meter takes, built before any
/// timing starts; `run` is timed on one of them per run, and each is dropped after the timing
/// ends (COMPLEXITY.md R3).
fn heap_scales<T: Send>(
    what: &str,
    n: usize,
    make: impl Fn(usize) -> T,
    run: impl Fn(&mut T, usize) + Sync,
) {
    let (small_runs, large_runs) = scaling::Meter::new().runs();
    let made = Mutex::new(
        [(n, small_runs), (scaling::FACTOR * n, large_runs)]
            .map(|(m, runs)| (m, (0..runs).map(|_| make(m)).collect::<Vec<_>>())),
    );
    let used = Mutex::new(Vec::new());
    scaling::check_order(what, n, 1, |m| {
        let mut x = {
            let mut made = made.lock().unwrap();
            let at = made.iter_mut().find(|(k, _)| *k == m).unwrap();
            at.1.pop().expect("a heap for each run")
        };
        run(&mut x, m);
        used.lock().unwrap().push(x);
    });
}

#[test]
fn matching_a_deep_constant_scales() {
    heap_scales(
        "a match to the end of a constant n deep",
        400_000,
        rate_table,
        |(h, w, p), _| read_to_the_end(h, p, *w),
    );
}

#[test]
fn matching_one_constant_many_times_scales() {
    heap_scales(
        "n matches to the end of a constant 100 deep",
        100_000,
        |_| rate_table(100),
        |(h, w, p), n| {
            for _ in 0..n {
                read_to_the_end(h, p, *w);
            }
        },
    );
}

#[test]
fn reading_a_value_whose_parts_share_cells_scales() {
    heap_scales(
        "the value of n cells, each holding the one below twice",
        600_000,
        paired,
        |(h, w), _| {
            std::hint::black_box(h.value(*w).unwrap());
        },
    );
}

/// A binder at every level of a pattern `n` deep records its path without copying the path
/// above it (HEAP-binder-paths): a copy per binder made `n²/2` parts.
#[test]
fn a_binder_at_every_level_of_a_deep_pattern_scales() {
    heap_scales(
        "a match binding each of n levels",
        250_000,
        invoice,
        |(h, w, p), n| {
            let (mut paths, mut out) = (Paths::default(), Vec::new());
            assert!(h.matches(p, *w, &mut paths, &mut out).unwrap());
            assert_eq!(out.len(), n + 1);
        },
    );
}

/// The fused release of an invoice `n` deep keeping every line reads each node on the way to
/// a kept line once, not each line's path from the top (HEAP-binder-paths), with the invoice
/// held once (each spine cell freed) or held twice (each line given a reference).
fn releasing_a_binder_at_every_level(shared: bool) {
    heap_scales(
        &format!("a fused release keeping each of n levels, shared {shared}"),
        250_000,
        |n| {
            let (mut h, w, paths, out) = matched_invoice(n);
            if shared {
                h.inc(w).unwrap();
            }
            let kept: Vec<usize> = out.iter().map(|&(_, node)| node).collect();
            (h, w, paths, kept)
        },
        |(h, w, paths, kept), n| {
            h.release(*w, paths, kept).unwrap();
            let live = if shared { 2 * n + 1 } else { n + 1 };
            assert_eq!(h.live(), live as u64);
        },
    );
}

#[test]
fn releasing_a_binder_at_every_level_scales() {
    releasing_a_binder_at_every_level(false);
}

#[test]
fn releasing_a_binder_at_every_level_of_a_shared_invoice_scales() {
    releasing_a_binder_at_every_level(true);
}

/// The native run of `make` in `world` at `n` and `8n`, planned and with its world built
/// before the timing, against the counting machine's value and counts at `n`. The timed run
/// clones the world, which copies the ports' maps and shares their values.
pub(super) fn check_run(what: &str, n: usize, make: fn(usize) -> Term, world: fn(usize) -> World) {
    on_big_stack(|| {
        assert!(!counted_in(&make(n), world(n)).is_empty());
        let at = |m: usize| (planned(&make(m)), world(m));
        let (small, large) = (at(n), at(8 * n));
        scaling::check(what, n, |m| {
            let ((g, p), w) = if m == n { &small } else { &large };
            let o = zed_native::run(g, p, &mut Evaluator::new(w.clone())).unwrap();
            std::hint::black_box(o);
        });
    });
}

/// Each atom is made from its words, with no call to the kernel, which took the whole list
/// built so far as its payload (COMPLEXITY.md R2).
#[test]
fn a_list_of_many_atoms_scales() {
    check_run("a list of n atoms, built natively", 5_000, list, |_| {
        World::new()
    });
}

/// A binder the arm does not use is not copied out of the scrutinee (COMPLEXITY.md R7). The
/// tuple holds `64n` strings, so the copy would outweigh the `n` calls.
#[test]
fn many_matches_with_an_unused_binder_scale() {
    check_run(
        "n matches, each binding a tuple of 64n cells unused",
        1_200,
        unused,
        |n| strings(64 * n),
    );
}

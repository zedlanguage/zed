//! Benchmarks of `linked`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`). The sizes were set on 2026-11-14 so
//! that the run at `n` takes about 0.3 to 0.5 s and the run at `8n` about 3 to 4 s at load 20 to
//! 30 on 32 cores (TEST-bench-move-l0139); a test with several checks runs each a little
//! smaller.

use super::*;

#[test]
fn tests_assumed_one_by_one_on_one_linked_component_take_time_near_their_number() {
    // Each test projects the block it joins and the blocks a moved bound reaches, not the
    // whole component. The scopes and tests are built before the timing.
    for which in ["chain", "bounded chain", "star", "or chain"] {
        let what = format!("a {which} assumed one by one");
        scaling::check_inputs(
            &what,
            1000,
            |k| shape(which, k),
            |(s, ts)| {
                let p = Premises::new();
                ts.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
            },
        );
    }
}

/// A name `h` that `d` other blocks mention, and a block of five constraints on `h`, `a`, `b`
/// and `x` that loses `a - b >= 0` and gets it back `d` times. The searches that find the block
/// still whole without it (`Blocks::peel`) reach `h` off their path and read its conjuncts in
/// this block alone, so each removal costs near the block, not near the blocks of `h`. Reading
/// all of `h`'s conjuncts and skipping those of other blocks, as before, cost O(d) per removal:
/// 31.4 times the bytes at 64 and 512. Now 9.0 times the instructions and 7.9 times the bytes,
/// limit 13.2 (2026-11-09). 8.9 times the instructions and 8.0 times the bytes at 4096 and
/// 32768 (2026-11-14). COMPLEXITY.md C37.
#[test]
fn a_constraint_taken_from_a_block_beside_a_name_of_many_blocks_takes_time_near_the_block() {
    scaling::check(
        "a constraint taken from a block beside a name of many blocks and put back",
        4096,
        |d| {
            let mut b = Blocks::default();
            for i in 0..d {
                b.add(&at_least("h", &format!("y{i}")));
            }
            let ab = at_least("a", "b");
            for g in [
                at_least("h", "a"),
                ab.clone(),
                at_least("b", "h"),
                at_least("a", "x"),
                at_least("x", "b"),
            ] {
                b.add(&g);
            }
            for _ in 0..d {
                b.remove(std::slice::from_ref(&ab));
                b.add(&ab);
            }
        },
    );
}

#[test]
fn if_statements_joined_one_after_another_on_a_linked_chain_take_time_near_their_number() {
    // x0 - x1 >= 1, x1 - x2 >= 1, … then, for each link, an `if x_i - x_{i+1} >= 2` whose two
    // arms are joined. The arms differ in the link's conjunct, which the join replaces in its
    // block; removing it first would cut the chain in two and build its blocks again, which
    // made the joins quadratic (COMPLEXITY.md S20).
    let p = Premises::new();
    let make = |k: usize| {
        let (s, chain) = shape("chain", k);
        let s = chain.iter().fold(s, |s, t| s.assume(t, true, &p));
        let n = named(k + 1, "x");
        let tests: Vec<Term> = (0..k).map(|i| ge(&n[i], &n[i + 1], 2)).collect();
        (s, tests)
    };
    scaling::check_inputs(
        "if statements joined on a chain",
        1000,
        make,
        |(s, tests)| {
            tests.iter().fold(s.clone(), |s, t| {
                let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
                j.reduce();
                j
            });
        },
    );
}

#[test]
fn a_nested_or_and_formula_is_built_and_mapped_in_time_near_its_size() {
    // Each `Formula::or` looks up only the constraints among its disjuncts, never a compound
    // disjunct through its depth, so building and mapping a nest of depth d costs O(d).
    let at = |n: &str| Lin::atom(Atom::Sym(n.into()));
    let built: BTreeMap<usize, (Vec<Formula>, Vec<Formula>)> = [32000, 256000]
        .into_iter()
        .map(|d| {
            let side = |n: &str| -> Vec<Formula> {
                (0..d as i64)
                    .map(|i| Formula::Con(Con::ge(&at(n), &Lin::constant(i))))
                    .collect()
            };
            (d, (side("x"), side("y")))
        })
        .collect();
    let shift = |c: &Con| Formula::Con(Con::ge(&c.lin, &Lin::constant(1)));
    scaling::check_order("a nested or/and formula built and mapped", 32000, 1, |d| {
        let (xs, ys) = &built[&d];
        let f = nested(xs, ys);
        std::hint::black_box(f.map_cons(&shift));
    });
}

#[test]
fn if_statements_on_skip_links_of_a_chain_take_time_near_their_number() {
    // The chain, then for each i an `if x_i - x_{i+2} >= 3` whose two arms are joined. The
    // test and its complement made a disjunction `true` at every point that each later test
    // split into cases, about k^4 in all; and removing the test's conjunct from the cycle it
    // closed with x_{i+1} built the blocks of the whole chain again, k^2 (COMPLEXITY.md S20).
    let p = Premises::new();
    let make = |k: usize| {
        let (s, chain) = shape("chain", k);
        let s = chain.iter().fold(s, |s, t| s.assume(t, true, &p));
        let n = named(k + 1, "x");
        let tests: Vec<Term> = (0..k - 1).map(|i| ge(&n[i], &n[i + 2], 3)).collect();
        (s, tests)
    };
    let what = "if statements on skip links of a chain";
    scaling::check_inputs(what, 1000, make, |(s, tests)| {
        tests.iter().fold(s.clone(), |s, t| {
            let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
            j.reduce();
            j
        });
    });
}

#[test]
fn one_test_on_a_ladder_takes_time_near_its_size() {
    // The block's bounds come from one shortest-path pass over its difference constraints
    // (`presburger::difference_hulls`), not O(log d) solver questions per name, each over
    // the whole block (COMPLEXITY.md S25: 19/80/359/1,680 M at k = 10/20/40/80).
    let p = Premises::new();
    let built: BTreeMap<usize, (Scope, Term)> = [10, 80]
        .into_iter()
        .map(|k| {
            let n = named(k + 1, "x");
            (k, (ladder(k, &p), ge(&n[0], &n[k], k as i64)))
        })
        .collect();
    scaling::check("one test on a ladder of k rungs", 10, |k| {
        let (s, t) = &built[&k];
        s.assume(t, true, &p);
    });
}

#[test]
fn a_ladder_grown_by_k_if_statements_is_linear() {
    // Each `if x_i - x_(i+2) >= 2` on the chain is implied, so its join keeps the true arm and
    // the block grows by one rung. The chain holds difference constraints alone, so each test
    // repairs the scope's potential and moves the bounds by shortest paths from its own edge
    // (`Scope::shortest`), not by projecting the block: O(log k) each, in either order. It
    // was O(k^2) by projecting the whole block each time (COMPLEXITY.md S25), and O(k^3)
    // before (16/89/608/4,869 M at k = 5/10/20/40).
    let p = Premises::new();
    for reverse in [false, true] {
        let make = |k: usize| {
            let (s, chain) = shape("chain", k);
            let s = chain.iter().fold(s, |s, t| s.assume(t, true, &p));
            let n = named(k + 1, "x");
            let mut tests: Vec<Term> = (0..k - 1).map(|i| ge(&n[i], &n[i + 2], 2)).collect();
            if reverse {
                tests.reverse();
            }
            (s, tests)
        };
        let name = if reverse {
            "a ladder grown by k if statements, the last rung first"
        } else {
            "a ladder grown by k if statements"
        };
        // n 512 (SCALE-small-n-rest, b22-tests9): at 1000 a phase passed 20 s (job j4 on
        // hm4, 2026-11-24, rc 124).
        scaling::check_inputs(name, 512, make, |(s, tests)| {
            tests.iter().fold(s.clone(), |s, t| {
                let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
                j.reduce();
                j
            });
        });
    }
}

#[test]
fn if_statements_that_leave_a_ladder_block_by_block_between_rungs_are_linear() {
    // The chain from x0 within 0..=10^9, each rung's `if` after an `if` that leaves the tree to
    // the projection block by block in its arms: `x_i + w_i >= 0`, not a difference
    // constraint, with w_i unbounded. The edges that come while the tree goes block by block
    // are put in the potential all the same (`Scope::repair`), so no later test finds it again
    // from the whole tree (`Scope::reseed`). The same mix with a hole, `x_i != 5`, in place of
    // the sum, is quadratic in its output: the arm where x_i is 5 moves the bounds of the
    // names below it, which the ladder bounds from x0 alone (COMPLEXITY.md row S25).
    // `if_statements_that_put_a_hole_in_a_ladder_between_rungs_are_linear` bounds each name.
    let p = Premises::new();
    let make = |k: usize| {
        let n = named(k + 1, "x");
        let w = named(k, "w");
        let s = ints(&[n.clone(), w.clone()].concat())
            .assume(&prim(Prim::Ge, var("x0"), int(0)), true, &p)
            .assume(&prim(Prim::Le, var("x0"), int(1_000_000_000)), true, &p);
        let s = (0..k).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 1], 1), true, &p));
        let mut tests: Vec<Term> = Vec::new();
        for i in 0..k - 1 {
            tests.push(prim(
                Prim::Ge,
                prim(Prim::Add, var(&n[i]), var(&w[i])),
                int(0),
            ));
            tests.push(ge(&n[i], &n[i + 2], 2));
        }
        (s, tests)
    };
    let name = "a ladder grown by k if statements, each after an if on a sum";
    scaling::check_inputs(name, 777, make, |(s, tests)| {
        tests.iter().fold(s.clone(), |s, t| {
            let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
            j.reduce();
            j
        });
    });
}

#[test]
fn if_statements_that_put_a_hole_in_a_ladder_between_rungs_are_linear() {
    // The chain from x0 with each x_i within its own ten values, 10 (k - i) to 10 (k - i) + 9,
    // so that no edge moves a bound, each rung's `if` after an `if` that puts a hole in a name,
    // `x_i != 10 (k - i) + 5`. The arms are taken as the checker takes them
    // (`Scope::assume_case`), since the arm where a rung fails is empty. The arm where the
    // hole holds projects the tree by shortest paths, the gap of the name with the hole held in
    // the potential (`Scope::raise`), and the join keeps that arm's last projection, whose tree
    // had a hole and is still read by shortest paths (`Seeds::unsure`). 9.6 times the work and
    // 8.6 times the bytes from k = 40 to 320; on the code before, which projected the tree's
    // blocks one by one at each test, 62.2 times the bytes (COMPLEXITY.md row S25). 9.2 times the
    // work and 8.6 times the bytes from k = 400 to 3200 (2026-11-14).
    let p = Premises::new();
    let make = |k: usize| {
        let n = named(k + 1, "x");
        let base = |i: usize| (10 * (k - i)) as i64;
        let s = (0..=k).fold(ints(&n), |s, i| {
            s.assume(&prim(Prim::Ge, var(&n[i]), int(base(i))), true, &p)
                .assume(&prim(Prim::Le, var(&n[i]), int(base(i) + 9)), true, &p)
        });
        let s = (0..k).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 1], 1), true, &p));
        let mut tests: Vec<Term> = Vec::new();
        for i in 0..k - 1 {
            tests.push(prim(Prim::Ne, var(&n[i]), int(base(i) + 5)));
            tests.push(ge(&n[i], &n[i + 2], 2));
        }
        (s, tests)
    };
    let name = "a ladder grown by k if statements, each after an if that puts a hole in a name";
    scaling::check_inputs(name, 1000, make, |(s, tests)| {
        tests.iter().fold(s.clone(), |s, t| {
            let mut j = s
                .assume_case(t, true, &p)
                .join(&s.assume_case(t, false, &p));
            j.reduce();
            j
        });
    });
}

#[test]
fn holes_put_in_a_ladder_built_first_are_linear() {
    // The ladder of the test above, every rung in place before the first hole, so that its
    // names lie in one block from the start; then an `if x_i != 10 (k - i) + 5` for each name,
    // in either order, whose arms are joined. Each hole raises the gap of one name, which the
    // potential repairs within that name's component alone (`Scope::raise`). The bounds of
    // every name stay as they were.
    // The ladders are built by `check_inputs`, only at the sizes this process runs: built at
    // both before each check, under DynamoRIO, the piece passed the limit of a phase at 57.1 s
    // (rc 124 on l43, b22-tests8 job f2, FAIL-bench-pieces-past-limit-on-main).
    let p = Premises::new();
    for reverse in [false, true] {
        let ladder = |k: usize| -> (usize, (Scope, Vec<Term>)) {
            let n = named(k + 1, "x");
            let base = |i: usize| (10 * (k - i)) as i64;
            let s = (0..=k).fold(ints(&n), |s, i| {
                s.assume(&prim(Prim::Ge, var(&n[i]), int(base(i))), true, &p)
                    .assume(&prim(Prim::Le, var(&n[i]), int(base(i) + 9)), true, &p)
            });
            let s = (0..k).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 1], 1), true, &p));
            let s = (0..k - 1).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 2], 2), true, &p));
            let mut tests: Vec<Term> = (0..=k)
                .map(|i| prim(Prim::Ne, var(&n[i]), int(base(i) + 5)))
                .collect();
            if reverse {
                tests.reverse();
            }
            (k, (s, tests))
        };
        let name = if reverse {
            "holes put in a ladder built first, the last name first"
        } else {
            "holes put in a ladder built first"
        };
        // n 512 (SCALE-small-n-rest, b22-tests9): at 777 a phase passed 20 s (job j4 on hm4,
        // 2026-11-24, rc 124).
        scaling::check_inputs(name, 512, ladder, |(k, (s, tests))| {
            let k = *k;
            let s = tests.iter().fold(s.clone(), |s, t| {
                let mut j = s
                    .assume_case(t, true, &p)
                    .join(&s.assume_case(t, false, &p));
                j.reduce();
                j
            });
            assert!(!s.bottom);
            for i in 0..=k {
                let base = (10 * (k - i)) as i64;
                assert_eq!(
                    s.get(&format!("x{i}")).ints(),
                    &zedc::store::interval::IntervalSet::range(End::of(base), End::of(base + 9))
                );
            }
        });
    }
}

#[test]
fn a_chain_linked_from_a_source_made_later_is_linear() {
    // The chain of the first test, then u - v >= 0 and v - x0 >= 0: u and v are named after
    // the chain, so their edge into its head runs against the order the potential keeps its
    // names in, and every later repair at the chain's head must not search the chain through
    // them. u and v are pinned, as a bounded name is, so that they stay in the potential.
    // Each if statement is the chain test's `if x_i - x_{i+1} >= 2`. 9.2 times the work and 8.4
    // times the bytes from k = 50 to 400; on the code before, 17.7 times the work. 9.0 times the
    // work and 8.4 times the bytes from k = 240 to 1920 (2026-11-14).
    let p = Premises::new();
    let make = |k: usize| {
        let n = named(k + 1, "x");
        let mut s = ints(&[n.clone(), vec!["u".into(), "v".into()]].concat());
        s.relation.pin(&"u".into(), true);
        s.relation.pin(&"v".into(), true);
        let s = (0..k).fold(s, |s, i| s.assume(&ge(&n[i], &n[i + 1], 1), true, &p));
        let s = s
            .assume(&ge("u", "v", 0), true, &p)
            .assume(&ge("v", "x0", 0), true, &p);
        assert!(!s.bottom);
        let tests: Vec<Term> = (0..k).map(|i| ge(&n[i], &n[i + 1], 2)).collect();
        (s, tests)
    };
    let what = "a chain linked from a source made later";
    scaling::check_inputs(what, 777, make, |(s, tests)| {
        tests.iter().fold(s.clone(), |s, t| {
            let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
            j.reduce();
            j
        });
    });
}

/// A satellite related to `d + 1` hubs, each a hub of leaves of two hubs, costs near `d` in
/// the names the hubs need, not `d` at each hub, and building the conjunction is linear. Its
/// stars and the needs held across the hubs are checked by the test of the same name in
/// `linked`. COMPLEXITY.md C37.
#[test]
fn a_satellite_of_every_hub_costs_its_related_names_once() {
    for first in [true, false] {
        scaling::check(
            &format!("a satellite of every hub (satellite first: {first})"),
            1024,
            |d| {
                std::hint::black_box(satellite_of_every_hub(d, first));
            },
        );
    }
}

/// With bounds on the hubs ([`satellite_conjuncts`]), a leaf that becomes a star while its
/// conjuncts are in the one block that the satellite and the other leaves make takes its
/// conjuncts out of that block. Each is a constraint on two names, which `Blocks::remove` takes
/// out alone (`Blocks::cut`), in time near the smaller side of each split it makes; building
/// the blocks of the whole component again, as before, cost O(d) for each such star, and in a
/// random order the number of such stars grows with `d`. Built at 64 and 512 in a random
/// order: 10.7 times the instructions and 8.4 times the bytes, limit 13.2 of 2026-11-09; before,
/// 22.5 and 16.6 times (2026-11-09). At 64 and 512 it measured 11.3 times, over the limit of 10.5,
/// so it is built at 512 and 4096: 10.4 times the instructions and 8.3 times the bytes
/// (2026-11-13). Without the bounds no leaf becomes a star
/// (`a_satellite_of_every_hub_costs_its_related_names_once_in_any_order` in `linked`).
/// COMPLEXITY.md C37. On
/// 2026-11-19, 10.03 times (663.3M and 6,650.9M instructions, load 35); what grows fastest is the
/// merge of blocks (`Blocks::merge`, 11.4 times at 512 to 4096): a conjunct is moved O(log d)
/// times, each move O(log d) in the persistent maps, O(d log² d) in all, as `Blocks` states
/// (COMPLEXITY.md row PERF-satellite-random-under9).
#[test]
fn stars_formed_in_the_block_of_a_satellite_take_time_near_the_block() {
    satellite_built_in_a_random_order(512, true);
}

/// The satellite of every hub without bounds on the hubs built in a seeded random order: no
/// leaf becomes a star, and the build is linear. Deferred by TESTS-scaling-limit-10_5 at 64 and
/// 512 (11.0 times the instructions on cdf07ac4f); back with row RP-scaling-10_5 at the sizes
/// of the test above, 512 and 4096.
#[test]
fn a_satellite_of_every_hub_built_in_a_random_order_is_linear() {
    satellite_built_in_a_random_order(512, false);
}

/// The conjuncts of [`satellite_conjuncts`] without bounds, built and then taken away one at a
/// time in a random order. All of them are one block. Each is a constraint on two names, which
/// `Blocks::remove` takes out alone (`Blocks::cut`): the block splits along a path of pieces
/// found by searches from both ends of the constraint run in turn (`Blocks::peel`), in time near
/// the pieces split off rather than the block. Splitting the block by placing its other
/// conjuncts again (`Blocks::split`), as before, cost O(d) for each conjunct taken away, so
/// O(d^2) in all. Built and taken apart at 64 and 512: 148 M and 1,582 M instructions, 10.7
/// times, and 8.8 times the bytes, limit 13.2; before, 374 M and 16,472 M, 44.0 times, and 34.0
/// times the bytes (2026-11-09). Deferred by TESTS-scaling-limit-10_5 (11.2 times at 64 and 512
/// on cdf07ac4f); back with row RP-scaling-10_5 at 512 and 4096. The star index is not the
/// cost: the needs stay within three per hub
/// (`a_satellite_of_every_hub_costs_its_related_names_once_in_any_order` in `linked`).
/// COMPLEXITY.md C37.
#[test]
fn a_satellite_of_every_hub_taken_apart_takes_time_near_the_block_per_conjunct() {
    let orders = satellite_orders(512, false);
    scaling::check(
        "a satellite of every hub built and taken apart in random orders",
        512,
        |d| {
            let mut c = built(&orders, d);
            for &i in &orders[&d].2 {
                take_out(&mut c, &orders[&d].0[i]);
            }
            assert!(c.set().is_empty(), "{c}");
        },
    );
}

/// Holes that pile up in the names of one chain stay on shortest paths, and each name keeps its
/// hole. Quadratic, open as item ST-holes-moves (COMPLEXITY.md S25): each hole lowers the
/// potential at its name, and on a chain whose edges have no slack in the potential every name
/// below it moves too, about k/2 names a hole (`Scope::raise`). Before, block by block, cubic.
/// The holes each name keeps are checked by the test of the same name in `linked`.
#[test]
fn holes_piled_in_the_names_of_a_chain_take_quadratic_time() {
    let p = Premises::new();
    scaling::check_order("holes piled in the names of a chain", 192, 2, |k| {
        piled_holes_run(k, &p);
    });
}

/// The band of ST-band-quintic ([`band_holes_run`]): its ends found by snap-Dijkstra
/// (`Scope::by_holes`, `holes::Run::snaps`) and each block due projected for the values between
/// them (D3). Red controls: 45.6 at 16 to 128 on a54e9543a (instructions, measured 2026-11-23;
/// refused, narrowed by the hulls, inexact) and 60.4 on main ca8d53547 (64.7 with chords; block
/// by block, measured 2026-11-23); before ST-band-quintic, block by block at k = 5, 10 and 20,
/// 138 M, 4,115 M and 110,524 M instructions, about k^5 (COMPLEXITY.md S25).
#[test]
fn a_band_with_holes_and_joined_rungs_takes_near_linear_time() {
    let p = Premises::new();
    scaling::check("a band with holes and joined rungs", 16, |k| {
        std::hint::black_box(band_holes_run(k, &p));
    });
}

/// The band with its rungs as plain conjuncts and chords `x_i - x_(i+3) >= 30`
/// ([`band_chords_run`], XR-st-band-quintic D6). Its chords are implied by the steps; a chord
/// that is not is tested in `linked` against enumeration (row XR-st-band-quintic-rtscc).
#[test]
fn a_band_with_chords_takes_near_linear_time() {
    let p = Premises::new();
    scaling::check("a band with holes, rungs and chords", 16, |k| {
        std::hint::black_box(band_chords_run(k, &p));
    });
}

/// The moving top ([`moving_top_run`], `w = k / 4` holes): each hole moves the greatest value
/// of all `k + 1` names, so the ends change about `k² / 4` times and the work is of order 2 by
/// its output (about 64 at 8 times the size), not held to the near-linear limit (XR-st-band-
/// quintic D6: the lower bound is the output, not a refusal).
#[test]
fn a_moving_top_takes_time_of_order_its_end_changes() {
    let p = Premises::new();
    scaling::check_order("a moving top, by the length of its chain", 16, 2, |k| {
        std::hint::black_box(moving_top_run(k, k / 4, &p));
    });
}

/// The moving top with three holes inside the chain ([`holed_moving_top_run`]), so that its
/// ends go through `Scope::by_holes` (XR-st-band-quintic r2, Gemini finding 2); of order 2 by
/// its output, as [`a_moving_top_takes_time_of_order_its_end_changes`].
#[test]
fn a_holed_moving_top_takes_time_of_order_its_end_changes() {
    let p = Premises::new();
    scaling::check_order(
        "a holed moving top, by the length of its chain",
        16,
        2,
        |k| {
            std::hint::black_box(holed_moving_top_run(k, k / 4, &p));
        },
    );
}

/// Holes inside `x_0` that move no other name ([`interior_holes_run`], `w = k / 4` holes;
/// XR-st-band-quintic r2, Claude finding 2): the output is the `w` holes, so a method that
/// reads the whole chain at each hole costs about `k w` and fails the near-linear limit. Model
/// of method (T): 8.00 at 8 times the size, and 57.15 for the re-reading control (computed in
/// the cross-review's model, r2/claude/model/full.rs).
#[test]
fn interior_holes_take_near_linear_time() {
    let p = Premises::new();
    scaling::check("holes inside the first name of a chain", 16, |k| {
        std::hint::black_box(interior_holes_run(k, k / 4, &p));
    });
}

/// Holes in every name of a grid of difference constraints: each hole moves about `m - 1`
/// names of the potential, so `m^3`, `n^1.5` in the `n = m^2` names (order 3 in `m`). Open as
/// item ST-holes-moves (COMPLEXITY.md S25): the names a hole moves are those within its shift
/// of it by reduced distance, which on a grid are no range of one order of the names.
/// The holes each name keeps are checked by the test of the same name in `linked`.
#[test]
fn holes_in_every_name_of_a_grid_take_time_m_cubed() {
    let p = Premises::new();
    scaling::check_order("holes in every name of a grid, by its side", 6, 3, |m| {
        grid_holes(m, &p);
    });
}

#[test]
fn a_chain_put_in_against_the_order_reads_only_what_it_moves() {
    // The bounds rank each x{i+1} after x{i}, so the edge of `x{i+1} - x{i} >= 1` goes against
    // the order: the search back from x{i+1} finds it alone, the one forward from x{i} the i
    // names before it. The search that ends first decides, and x{i+1} alone moves, to just
    // before x{i}. 9.2 times the work and 8.7 times the bytes from k = 64 to 512 (item
    // PERF-pk-one-sided); on the code before, which ran both searches to their ends, 36 times
    // the work and 22.7 times the bytes (1,767 and 99,933 components read). 8.7 times the work and
    // 8.3 times the bytes from k = 2048 to 16384 (2026-11-14). At 8192 and 65536, and at 16384
    // and 131072, the run overflowed the stack of its thread as the scope was dropped: each
    // `Arc<Pending>` dropped the next in turn, one frame each, until `Drop for Pending`
    // (`zedc_preimage::product`) took the list apart in a loop.
    let p = Premises::new();
    let built: BTreeMap<usize, (Scope, Vec<Term>)> = [2048, 16384]
        .into_iter()
        .map(|k| (k, chain_against_the_order(k)))
        .collect();
    scaling::check_order("a chain put in against the order", 2048, 1, |k| {
        let (s, tests) = &built[&k];
        tests.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
    });
}

/// The bounded chain, then for each link `x_i != 2*10^9 && x_i - x_{i+1} >= 2` assumed false:
/// the case `x_i == 2*10^9` is empty, so each test leaves one case, `x_i - x_{i+1} <= 1`, which
/// stays, and its blocks are projected again outside the cases with the groups read
/// (`Scope::join_kept`, item FAIL-linked-case-group-wake). Each case pins `x_(i+1)` to
/// `x_i - 1`, so it ties a new name to the class of those before it: the potential is repaired
/// by raising `x_(i+1)` alone, not by lowering the class (`put_in`, item
/// FAIL-one-case-hole-chain-scaling). 8.5 times the instructions and 8.3 times the bytes at
/// 280 and 2240 (2026-11-14); with the search from `v` alone, 0.68, 2.43 and 8.53 s at 280, 560
/// and 1120, and past the time limit at 280 and 2240.
#[test]
fn holes_that_leave_one_case_on_a_chain_take_time_near_their_number() {
    let p = Premises::new();
    let make = |k: usize| {
        let (s, chain) = shape("bounded chain", k);
        let s = chain.iter().fold(s, |s, t| s.assume(t, true, &p));
        let n = named(k + 1, "x");
        let tests: Vec<Term> = (0..k)
            .map(|i| {
                let off = prim(Prim::Ne, var(&n[i]), int(2_000_000_000));
                prim(Prim::And, off, ge(&n[i], &n[i + 1], 2))
            })
            .collect();
        (s, tests)
    };
    let what = "holes that leave one case on a chain";
    scaling::check_inputs(what, 1000, make, |(s, tests)| {
        tests.iter().fold(s.clone(), |s, t| s.assume(t, false, &p));
    });
}

#[test]
fn disjunctions_over_four_names_take_time_near_their_number() {
    // k disjunctions over four names after one row on five (row
    // PERF-refused-shape-disjunctions-quadratic). Measured 7.76 at 8n, as on main (7.7);
    // waking every part reached through a group in the cases, with no certificate, gave 29.7.
    scaling::check_order("disjunctions over four names", 8, 1, four_name_run);
}

/// A binary tree of `k` names, each `x_i` tied to its parent `x_((i-1)/2)` by
/// `1 <= x_i - x_p <= 3`, one block each, which shares its parent's name with the block above
/// it; every name a hole one above its least value. `Scope::by_holes` is asked for the ends
/// once, over the whole tree; each block is then projected once (`Scope::project`, item
/// FAIL-linked-scratch-misses-hole). The work stays near the number of blocks (row
/// BENCH-scope-project-due-blocks). (Before ST-band-quintic D1 the tree was refused, and the
/// refusal's list of holed names, copied once for each name it was filed under, cost
/// Theta(k²) bytes until it was shared.)
#[test]
fn a_tree_of_blocks_with_holes_projected_from_scratch_takes_time_near_its_size() {
    let p = Premises::new();
    scaling::check_inputs(
        "a tree of blocks with holes projected from scratch",
        DUE_BLOCKS,
        |k| holed_tree_of_blocks(k, &p),
        |built| {
            let mut s = built.clone();
            s.forget_projections();
            s.reduce();
            assert!(!s.bottom);
        },
    );
}

/// The size of the benchmark above at 1x.
const DUE_BLOCKS: usize = 1200;

/// The scope of [`a_tree_of_blocks_with_holes_projected_from_scratch_takes_time_near_its_size`]
/// with `k` names: `x0` in `[0, 1000]`, each other name `1 <= x_i - x_p <= 3` with its parent,
/// and `x_i != d_i + 1` at depth `d_i`, which lies in its interval `[d_i, 1000 + 3 d_i]`.
fn holed_tree_of_blocks(k: usize, p: &Premises) -> Scope {
    let n = named(k, "x");
    let mut s = ints(&n)
        .assume(&prim(Prim::Ge, var("x0"), int(0)), true, p)
        .assume(&prim(Prim::Le, var("x0"), int(1000)), true, p);
    let mut depth = vec![0i64; k];
    for i in 1..k {
        let up = (i - 1) / 2;
        depth[i] = depth[up] + 1;
        s = s
            .assume(&ge(&n[i], &n[up], 1), true, p)
            .assume(&ge(&n[up], &n[i], -3), true, p);
    }
    for i in 0..k {
        s = s.assume(&prim(Prim::Ne, var(&n[i]), int(depth[i] + 1)), true, p);
    }
    assert!(!s.bottom);
    s
}

fn four_name_run(k: usize) {
    let ns = named(5, "x");
    let p = Premises::new();
    let base = row(&[-1, -1, -1, -1, 1], 0);
    let mut s = ints(&ns).assume(&base, true, &p);
    for j in 1..=k as i64 {
        let t = prim(
            Prim::Or,
            row(&[1, j, j + 1, j + 2, 0], -1),
            row(&[1, -j, -j - 1, -j - 2, 0], -1),
        );
        s = s.assume(&t, true, &p);
    }
    assert!(!s.bottom);
}

/// The row `c + sum(cs[i] * x_i) >= 0` over x0..x4.
fn row(cs: &[i64], c: i64) -> Term {
    let mut sum = int(c);
    for (i, k) in cs.iter().enumerate().filter(|(_, k)| **k != 0) {
        sum = prim(
            Prim::Add,
            sum,
            prim(Prim::Mul, int(*k), var(&format!("x{i}"))),
        );
    }
    prim(Prim::Ge, sum, int(0))
}

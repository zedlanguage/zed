//! The benchmarks of `group_oracle.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `group_oracle.rs`.

use super::*;

/// The verdicts of every type in `ts`, the emptiness memo cleared first.
fn every(ts: &[Type]) {
    Type::forget_emptiness();
    for t in ts {
        std::hint::black_box(t.verdict());
    }
}

/// The members of a chain group of `n` definitions.
fn chain(n: usize) -> Vec<Type> {
    kernel(&chain_of(&mut Rng::new(7), n), &format!("chain{n}"))
        .into_iter()
        .map(|t| t.expect("a chain group is admitted"))
        .collect()
}

/// The verdicts of every member of `n` random groups of the X14 family, the verdict of the
/// first member of one chain group of `n` definitions, which its search reads whole, and the
/// verdicts of every member of one group of `n` (plan item VERDICT-group-share), of the X14
/// family and of the chain family, at `n` and `8n`, the groups built before the runs: one test
/// for each. The first verdict asked of a member decides the whole group in one search
/// (`Type::verdict`), so the verdicts of all members cost what one does. Small instance
/// `small_random_groups_are_admitted`.
///
/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 4096; 1x 90 ms at load
/// 17.23.
#[test]
fn verdicts_of_random_groups_scale() {
    let many = |n: usize| -> Vec<Type> {
        (0..n as u64)
            .flat_map(|seed| kernel(&gen_claude(&mut Rng::new(seed)), &format!("many{n}_{seed}")))
            .map(|t| t.expect("every definition of the X14 family is admitted"))
            .collect()
    };
    let n = 4096;
    let groups = scaling::inputs(n, many);
    scaling::check("verdicts of the members of n random groups", n, |m| {
        every(&groups[&m])
    });
}

/// The verdict of the first member of one chain group, as in [`verdicts_of_random_groups_scale`].
///
/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 8192; 1x 106 ms at load
/// 17.08.
#[test]
fn the_verdict_of_one_member_of_a_chain_group_scales() {
    let n = 8192;
    let chains = scaling::inputs(n, chain);
    scaling::check("the verdict of one member of a chain group of n", n, |m| {
        Type::forget_emptiness();
        std::hint::black_box(chains[&m][0].verdict());
    });
}

/// The verdicts of every member of one chain group, as in [`verdicts_of_random_groups_scale`].
///
/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 8192; 1x 76 ms at load
/// 17.08.
#[test]
fn the_verdicts_of_every_member_of_a_chain_group_scale() {
    let n = 8192;
    let chains = scaling::inputs(n, chain);
    scaling::check(
        "the verdicts of every member of a chain group of n",
        n,
        |m| every(&chains[&m]),
    );
}

/// The verdicts of every member of one X14 group, as in [`verdicts_of_random_groups_scale`].
///
/// Size (TEST-bench-move-l0123, author P169): n 128 before, then 16384; 1x 104 ms at load
/// 16.99. Halved to 8192 by PERF-l01-23-bench-over-20s: at 16384 the piece took 19.3 s at load
/// 57 and 32 s at load 66, over its 20 s. Timed (2026-11-15): building the inputs took 4.6
/// to 8.7 s, nearly all of it `kernel` at 8n (4.2 to 7.7 s), and the check four runs, the
/// warm-up at n, n, and 8n twice (0.77, 0.27, 7.6 and 1.4 s): the cold first run at 8n fills
/// judgments its input keeps, so it is over the limit against the second run at n and is run
/// again (`Meter::again_when_over`, removed by author A160 on 2026-11-20: each size now runs
/// once, so the check is the two first runs). Every part is near linear in n, so the size sets
/// the time.
#[test]
fn the_verdicts_of_every_member_of_one_x14_group_scale() {
    let one = |n: usize| -> Vec<Type> {
        kernel(&claude_of(&mut Rng::new(3), n), &format!("one{n}"))
            .into_iter()
            .map(|t| t.expect("every definition of the X14 family is admitted"))
            .collect()
    };
    let n = 8192;
    let ones = scaling::inputs(n, one);
    scaling::check(
        "the verdicts of every member of one X14 group of n",
        n,
        |m| every(&ones[&m]),
    );
}

/// The verdicts of every member of one group of `n` that the decider refuses, of the chain
/// family and of the X14 family, at `n` and `8n`, the groups built before the runs: one search
/// with every member as a root decides them all (plan item VERDICT-group-roots), where a search
/// for each member read the group n times. Then, in
/// [`the_verdicts_of_every_definition_of_an_undecided_x14_system_scale`], the verdicts of every
/// definition of the X14 system, which read the group by its verdicts and values (plan item
/// VERDICT-group-readers). Small instance `small_undecided_groups_are_admitted`.
///
/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 8192; 1x 184 ms at load
/// 17.23.
#[test]
fn verdicts_of_undecided_groups_scale() {
    let chain = |n: usize| -> Vec<Type> {
        kernel(
            &undecided(chain_of(&mut Rng::new(7), n)),
            &format!("chainu{n}"),
        )
        .into_iter()
        .map(|t| t.expect("a chain group is admitted"))
        .collect()
    };
    let n = 8192;
    let chains = scaling::inputs(n, chain);
    scaling::check(
        "the verdicts of every member of an undecided chain group of n",
        n,
        |m| every(&chains[&m]),
    );
}

/// The verdicts of the members of the largest undecided X14 group, as in
/// [`verdicts_of_undecided_groups_scale`].
///
/// Size: n 128 until TEST-bench-move-l0123 (author P169), then 1024, held there because
/// `largest_group` walked from every definition, O(n²); now 8192 (TEST-largest-group-scc,
/// `largest_group` by Tarjan's algorithm, doi:10.1137/0201010, full comment in zed-graph
/// `lib.rs`, fn `tarjan`), 1x 85 to 106 ms, ratio 8.0 to 8.1 by instructions
/// and 7.9 by bytes, at load 31. The 1x stays short of 1 s because the whole test is held
/// under 20 s: at 65536 the 1x took 0.88 s (ratio 8.09) but the test 85 s, since the first
/// run of each size, which `scaling::check` also holds to the limit, does about 4 times the
/// work of the later runs, and the inputs at 524288 take seconds to build. With the old
/// helper, 8192 passed the 21 s limit before its first run.
///
/// Set-up and warm-up measured (TEST-l0124-fixed-seeds, load 41): at 1024, 8192 and 65536
/// definitions, making the system took 0.7, 4.8 and 26 ms, `largest_group` 0.6, 4.7 and 49 ms,
/// and building the group (`kernel`) 42 ms, 0.35 s and 3.28 s, 8.4 and 9.3 times per step of 8,
/// within O(n log n) (9.85 for n log n from 8192 to 65536). The first run of a size does about 4
/// times the instructions of the later ones, 8.0 times from n to 8n, so it is linear too and
/// done once; nothing is built twice. The test took 8.9 to 11.3 s at load 44 to 47. At 16384
/// it took 15.3 and 16.0 s at load 40 (1x 0.18 s, ratio 8.105), too close to the 20 s limit
/// at the usual load, so n stays 8192.
#[test]
fn the_verdicts_of_the_largest_undecided_x14_group_scale() {
    let one = |n: usize| -> Vec<Type> {
        let sys = undecided(claude_of(&mut Rng::new(3), n));
        let group = largest_group(&sys);
        let ts = kernel(&sys, &format!("oneu{n}"));
        (group.iter())
            .map(|&i| {
                ts[i]
                    .clone()
                    .expect("every definition of the X14 family is admitted")
            })
            .collect()
    };
    let n = 8192;
    let ones = scaling::inputs(n, one);
    scaling::check(
        "the verdicts of the members of the largest undecided X14 group of n definitions",
        n,
        |m| every(&ones[&m]),
    );
}

/// `largest_component` of a random graph of n nodes with 0 to 3 edges each, at n and 8n: one
/// pass of Tarjan's algorithm, O(n log n) with the sort of the largest component (which holds
/// about half the nodes here). Small instance `largest_component_agrees_with_walks`.
///
/// Size (TEST-largest-group-scc): n = 2^20, 1x 0.54 s, ratio 8.0 by instructions and bytes
/// at load 34; 6.3 by instructions under `tools/run_tests.sh` of that time, whose
/// `glibc.malloc.tcache_count=0` added work at 1x (1.21e9 against 0.69e9 instructions). On the
/// meter's own heap (TEST-meter-allocator-bias, 2026-11-15) 8.49 by instructions (0.367e9 and
/// 3.118e9) and 8.00 by bytes, at load 31. At
/// 2^21 the 1x took 1.07 s but the test 15 s, too close to the 20 s limit. The walk from each
/// node that this replaced took 62 times the instructions and 63 times the bytes at 1024 and
/// 8192.
///
/// The graphs were of the fixed seed 5 until TEST-l0124-fixed-seeds; now of a new seed each run,
/// printed (author P169: random tests take a new seed each run; `ZED_TEST_SEED` repeats it),
/// both sizes from the same seed, as `sum_chain` in the l01_24 benchmarks does.
#[test]
fn largest_component_scales() {
    let (_, seed) = Rng::fresh("random graphs for the largest component");
    let graph = |n: usize| -> Vec<Vec<usize>> {
        let mut rng = Rng::new(seed);
        (0..n)
            .map(|_| (0..rng.below(4)).map(|_| rng.below(n)).collect())
            .collect()
    };
    let n = 1 << 20;
    let graphs = scaling::inputs(n, graph);
    scaling::check(
        "the largest strongly connected component of a random graph of n nodes",
        n,
        |m| {
            std::hint::black_box(largest_component(&graphs[&m]));
        },
    );
}

/// Every definition, those outside the largest group too: such a definition reads the members
/// of that group by their group's verdicts, so the system's verdicts cost one search of the
/// group and one of each definition's own part (plan item VERDICT-group-readers), where a search
/// for each definition decided again the part of the group it reaches.
///
/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 8192; 1x 66 ms at load
/// 17.08.
#[test]
fn the_verdicts_of_every_definition_of_an_undecided_x14_system_scale() {
    let all = |n: usize| -> Vec<Type> {
        kernel(
            &undecided(claude_of(&mut Rng::new(3), n)),
            &format!("allu{n}"),
        )
        .into_iter()
        .map(|t| t.expect("every definition of the X14 family is admitted"))
        .collect()
    };
    let n = 8192;
    let alls = scaling::inputs(n, all);
    scaling::check(
        "the verdicts of every definition of an undecided X14 system of n",
        n,
        |m| every(&alls[&m]),
    );
}

/// `is_empty` of `R(n - 1)` of a key chain of `n`, at `n` and `8n`. The check that the empty
/// members are exactly those at even places, made here at 1 to 16 until TEST-bench-move-l0123
/// (author P169), is `every_second_member_of_a_key_chain_is_empty`.
///
/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 8192; 1x 130 ms at load
/// 17.01.
#[test]
fn a_chain_decided_again_scales() {
    let n = 8192;
    let chains = scaling::inputs(n, key_chain);
    for (&m, ts) in &chains {
        Type::forget_emptiness();
        assert!(!ts[m - 1].is_empty(), "R{} of a key chain of {m}", m - 1);
    }
    scaling::check("is_empty of R(n - 1) of a key chain of n", n, |m| {
        Type::forget_emptiness();
        std::hint::black_box(chains[&m][m - 1].is_empty());
    });
}

/// Builds the groups of `sys` under names of its own, so no run finds the groups of another,
/// and checks that every group is admitted.
fn build_groups(runs: &std::sync::atomic::AtomicUsize, sys: &[E]) {
    let run = runs.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let types = kernel(sys, &format!("built{run}"));
    assert!(types.iter().all(Option::is_some), "every group is admitted");
}

/// `kernel` builds the groups of a system in time linear in its definitions and references
/// (plan item VERDICT-meet-cost): a chain of n groups, each reading the next, here, and one
/// group of n definitions (`chain_of`) in [`one_group_of_n_definitions_is_built_in_its_size`],
/// at n and 8n, the systems written before the runs and each run under names of its own, so no
/// run finds the groups of another. A search from each definition for what it reaches cost the
/// square of the definitions, and a pass over every definition for each group built their
/// cube: 1.57 s for a chain of 1000 groups. Small instance
/// `the_groups_of_small_systems_are_built`.
///
/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 32768; 1x 405 ms at load
/// 17.08.
#[test]
fn the_groups_of_a_system_are_built_in_its_size() {
    let runs = std::sync::atomic::AtomicUsize::new(0);
    let n = 32768;
    let chains = scaling::inputs(n, |m| chain_of_groups(m, false));
    scaling::check("the groups of a chain of n groups", n, |m| {
        build_groups(&runs, &chains[&m])
    });
}

/// One group of n definitions, as in [`the_groups_of_a_system_are_built_in_its_size`].
///
/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 16384; 1x 157 ms at load
/// 17.01.
#[test]
fn one_group_of_n_definitions_is_built_in_its_size() {
    let runs = std::sync::atomic::AtomicUsize::new(0);
    let n = 16384;
    let groups = scaling::inputs(n, |m| chain_of(&mut Rng::new(7), m));
    scaling::check("one group of n definitions", n, |m| {
        build_groups(&runs, &groups[&m])
    });
}

/// The text of a chain of `n` cycles, each entered at a tuple part that a part kept
/// unevaluated shares, takes time and bytes of order `n log n`: the parts are ordered by their
/// contents, a sort. Small instance `a_short_chain_of_shared_tuple_parts_prints`.
///
/// Size (TEST-bench-move-l0123, author P169): n 64 before, then 4096, now 2048
/// (BENCH-l0139-follow-over-cap). At 4096 the test took 28.4 to 30.7 s at load 45 to 63, where
/// the runs took 0.05 s and 0.56 s: the rest was the set-up, built at both sizes in this
/// process and again in the new one of the run at `8 n` (`scaling::compare_by`). At 32,768 it
/// took, a process, 3.2 s for the kernel, 3.0 s for the first print and 3.7 s for parsing the
/// text back; the text is now parsed back only by the small instance.
#[test]
fn a_chain_of_shared_tuple_parts_prints_in_its_size() {
    let n = 2048;
    let chains = scaling::inputs(n, |n| shared_chain(n, true, &format!("chain{n}")));
    for (&n, t) in &chains {
        // `#a | #b`, the first pair and the part that names it, and one definition for each
        // other cycle, its pair written inside it: n + 2 in all. This first print makes the
        // unfoldings, once, before the runs.
        assert_eq!(t.surface().defs.len(), n + 2, "a chain of {n}");
    }
    scaling::check("the text of a chain of n shared tuple parts", n, |n| {
        std::hint::black_box(chains[&n].surface());
    });
}

/// The verdicts of every member of n copies of the group that hung the search, each its own
/// group, at n and 8n: the search takes each function type at most once for each value it
/// builds, and builds a value again only once a function taken after its build began holds it,
/// so each copy costs the same. Small instance
/// `a_few_copies_of_the_group_that_hung_the_search_are_refused`.
///
/// Size (TEST-bench-move-l0123, author P169): n 32 before, now 48; 1x 293 ms at load
/// 17.23.
#[test]
fn verdicts_of_copies_of_the_group_that_hung_the_search_scale() {
    verdicts_of_copies_scale(
        "the verdicts of every member of n copies of the group that hung the search",
        48,
        false,
    );
}

/// The verdicts of every member of a ring of n copies of the group that hung the search, at n
/// and 8n. Each copy's search tests whether two types overlap (COMPLEXITY.md K36), n tests
/// that each reach the whole ring through the first parts of tuples. The ring is one strongly
/// connected group of types, whose trie is made once and placed for each test, a node at a
/// time where it is read; its types
/// merge into one node, where a walk over the ring for each test cost n (GROUP-overlaps-unfold).
/// Small instance `a_ring_of_the_group_that_hung_the_search_is_refused`.
///
/// Size (TEST-bench-move-l0123, author P169): n 32 before, now 64; 1x 314 ms at load
/// 16.99.
#[test]
fn verdicts_of_a_ring_of_the_group_that_hung_the_search_scale() {
    verdicts_of_copies_scale(
        "the verdicts of every member of a ring of n copies of the group that hung the search",
        64,
        true,
    );
}

/// The first 36 tuples of a tuple type of `n` components with six values each, at `n` and `8n`:
/// the product has `6^n` tuples, and only the 36 kept are built. Small instance
/// `the_first_tuples_are_those_of_the_whole_product`.
///
/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 1048576; 1x 332 ms at load
/// 17.01.
#[test]
fn the_first_tuples_of_a_wide_tuple_type_scale() {
    let n = 1 << 20;
    let opts = scaling::inputs(n, |n| vec![(0..6).collect::<Vec<usize>>(); n]);
    scaling::check(
        "the first 36 tuples of a tuple type of n components",
        n,
        |m| {
            std::hint::black_box(first_tuples(&opts[&m], 36));
        },
    );
}

/// Moved from `group_oracle.rs` (TEST-bench-move-l0123, author P178): a chain of 512 is an
/// unusual size for a regular test. Small instance `every_member_of_a_short_chain_is_inhabited`.
#[test]
fn every_member_of_a_long_chain_is_inhabited() {
    every_member_of_a_chain_is_inhabited(512);
}

/// Moved from `group_oracle.rs` (TEST-bench-move-l0123, author P178): a chain of 512 is an
/// unusual size for a regular test. Small instance
/// `every_member_of_an_undecided_short_chain_is_inhabited`.
#[test]
fn every_member_of_an_undecided_long_chain_is_inhabited() {
    every_member_of_an_undecided_chain_is_inhabited(512);
}

/// A chain of 1000 groups (`chain_of_groups`), as the decider decides them and with every body
/// written `b \ #none`, is decided on a thread of 1 MiB, asked of the first member and of a
/// tuple outside the groups that holds it. Each group is decided before the group that reads it
/// (`Type::decide_groups_read`), so no search starts inside another: deciding each group as the
/// search above it reads it nested one search per group on the thread's stack, as the decider's
/// verdicts of the parts it reads already did (plan item VERDICT-group-readers). The tuple runs
/// first only the groups' deciders, and the groups' verdicts are decided when its search reads
/// the first member (plan item VERDICT-meet-cost); asked first of the member's group, the
/// deciders called each other one group deep at a time and overflowed the stack.
///
/// Moved from `group_oracle.rs` (TEST-bench-move-l0123, author P178): a long chain on a thread
/// stack set smaller than the default. Small instance `a_short_chain_of_groups_is_decided`.
#[test]
fn a_chain_of_groups_is_decided_on_a_small_stack() {
    let n = 1000;
    for open in [false, true] {
        let sys = chain_of_groups(n, open);
        let first = kernel(&sys, "chain")[0].clone().expect("admitted");
        let outside = Type::tuple(vec![first.clone(), Type::int()]);
        for t in [first, outside] {
            let v = scaling::on_a_thread(1 << 20, move || {
                Type::forget_emptiness();
                t.verdict()
            });
            assert_eq!(v, Verdict::Inhabited, "with every body \\ #none: {open}");
        }
    }
}

/// The test before this one asked with `is_empty`: the same chain of 1000 groups, on the same
/// thread of 1 MiB, of the first member and of the tuple outside the groups. Since plan item
/// FAIL-meet-cycles-verdict-cost a group's own search for `is_empty` runs when a search first
/// reads one of its members (`Search::met`), not before the search (`fill_own`); the groups
/// below it run first from the heap (`Type::decide_groups_read`), so the reading search adds
/// one level to the stack, not one a group (step (3) at `own_emptiness`). Small instance
/// `a_short_chain_of_groups_is_decided`.
#[test]
fn a_chain_of_groups_is_found_inhabited_on_a_small_stack() {
    let n = 1000;
    for open in [false, true] {
        let sys = chain_of_groups(n, open);
        let first = kernel(&sys, "chain")[0].clone().expect("admitted");
        let outside = Type::tuple(vec![first.clone(), Type::int()]);
        for t in [first, outside] {
            let empty = scaling::on_a_thread(1 << 20, move || {
                Type::forget_emptiness();
                t.is_empty()
            });
            assert!(!empty, "with every body \\ #none: {open}");
        }
    }
}

/// The two tests before this one ask the tuple outside the chain after its first member, whose
/// verdict decides every group of the chain first; a group's judgment is kept past
/// `Type::forget_emptiness`, so they never ask the tuple of a chain no search has read. This
/// test does: a chain of 1003 groups asked only the verdict of the tuple, and one of 1005 asked
/// only its emptiness (lengths no other test builds, so no judgment is kept from one), each on a
/// thread of 1 MiB. The tuple's search reads the first member, whose group's decider reads the
/// verdict of the tuple of the next member (`system`), and so on down the chain: the groups below
/// are decided first from the heap (`Type::decide_groups_read`), not by one search a group nested
/// on the thread's stack (plan item FAIL-meet-cycles-verdict-cost). Small instance
/// `a_short_chain_of_groups_is_decided`.
#[test]
fn a_tuple_holding_a_chain_of_groups_is_decided_on_a_small_stack() {
    for open in [false, true] {
        for (n, verdict) in [(1003, true), (1005, false)] {
            let sys = chain_of_groups(n, open);
            let first = kernel(&sys, "chain")[0].clone().expect("admitted");
            let outside = Type::tuple(vec![first, Type::int()]);
            let inhabited = scaling::on_a_thread(1 << 20, move || {
                Type::forget_emptiness();
                match verdict {
                    true => outside.verdict() == Verdict::Inhabited,
                    false => !outside.is_empty(),
                }
            });
            assert!(
                inhabited,
                "n {n}, verdict {verdict}, with every body \\ #none: {open}"
            );
        }
    }
}

/// Q2 C_group 6-tuples with many diffs at `n = 8` and `8n = 64`, inhabited and empty. A
/// benchmark, moved here from the correctness tests of `group_oracle.rs` (TEST-bench-split,
/// MEM-l0126-40gb).
#[test]
fn xr_r2_bench_cgroup_long_tuples_and_many_diffs_scales() {
    for inhabited in [true, false] {
        let n = 8usize;
        // One group held at a time, built before its run (MEM-l0126-40gb).
        let make = |k: usize, r: usize| {
            let size = if k == n { "s" } else { "l" };
            xr_r2_build_long_tuple_cgroup(k, inhabited, &format!("_{size}_{inhabited}_{r}"))
        };
        let want = if inhabited {
            Verdict::Inhabited
        } else {
            Verdict::Empty
        };
        scaling::check_order_fresh(
            if inhabited {
                "Q2 C_group 6-tuples with many diffs (inhabited)"
            } else {
                "Q2 C_group 6-tuples with many diffs (empty)"
            },
            n,
            1,
            make,
            |_, ts: Vec<Type>| {
                Type::forget_emptiness();
                for t in &ts {
                    assert_eq!(t.verdict(), want);
                }
                ts
            },
        );
    }
}

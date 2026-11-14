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
/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 16384; 1x 104 ms at load
/// 16.99.
#[test]
fn the_verdicts_of_every_member_of_one_x14_group_scale() {
    let one = |n: usize| -> Vec<Type> {
        kernel(&claude_of(&mut Rng::new(3), n), &format!("one{n}"))
            .into_iter()
            .map(|t| t.expect("every definition of the X14 family is admitted"))
            .collect()
    };
    let n = 16384;
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
/// Size (TEST-bench-move-l0123, author P169): n 128 before, now 1024; 1x 5.1 ms at load
/// 16.99. The 1x stays far under 0.5 s because the inputs set the size: `largest_group`
/// (in `group_oracle.rs`) walks from every definition and keeps an n-by-n table, O(n²), so
/// at 4096 (inputs at 32768) and 16384 the test passed the 25 s limit before its first run.
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
    let n = 1024;
    let ones = scaling::inputs(n, one);
    scaling::check(
        "the verdicts of the members of the largest undecided X14 group of n definitions",
        n,
        |m| every(&ones[&m]),
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
/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 4096; 1x 75 ms at load
/// 17.01.
#[test]
fn a_chain_of_shared_tuple_parts_prints_in_its_size() {
    let n = 4096;
    let chains = scaling::inputs(n, |n| {
        let t = shared_chain(n, true, &format!("chain{n}"));
        // The unfoldings are made once, before the runs.
        prints_as_syntax(&t, &format!("a chain of {n}"));
        t
    });
    for (&n, t) in &chains {
        // `#a | #b`, the first pair and the part that names it, and one definition for each
        // other cycle, its pair written inside it: n + 2 in all.
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

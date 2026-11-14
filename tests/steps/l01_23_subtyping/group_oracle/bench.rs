//! The benchmarks of `group_oracle.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `group_oracle.rs`.

use super::*;

/// The verdicts of every member of `n` random groups of the X14 family, the verdict of the
/// first member of one chain group of `n` definitions, which its search reads whole, and the
/// verdicts of every member of one group of `n` (plan item VERDICT-group-share), of the X14
/// family and of the chain family, at `n` and `8n`, the groups built before the runs. The first
/// verdict asked of a member decides the whole group in one search (`Type::verdict`), so the
/// verdicts of all members cost what one does. Small instance
/// `small_random_groups_are_admitted`.
#[test]
fn verdicts_of_random_groups_scale() {
    let many = |n: usize| -> Vec<Type> {
        (0..n as u64)
            .flat_map(|seed| kernel(&gen_claude(&mut Rng::new(seed)), &format!("many{n}_{seed}")))
            .map(|t| t.expect("every definition of the X14 family is admitted"))
            .collect()
    };
    let chain = |n: usize| -> Vec<Type> {
        kernel(&chain_of(&mut Rng::new(7), n), &format!("chain{n}"))
            .into_iter()
            .map(|t| t.expect("a chain group is admitted"))
            .collect()
    };
    let one = |n: usize| -> Vec<Type> {
        kernel(&claude_of(&mut Rng::new(3), n), &format!("one{n}"))
            .into_iter()
            .map(|t| t.expect("every definition of the X14 family is admitted"))
            .collect()
    };
    let every = |ts: &[Type]| {
        Type::forget_emptiness();
        for t in ts {
            std::hint::black_box(t.verdict());
        }
    };
    let n = 64;
    let groups = scaling::inputs(n, many);
    scaling::check("verdicts of the members of n random groups", n, |m| {
        every(&groups[&m])
    });
    let n = 128;
    let chains = scaling::inputs(n, chain);
    scaling::check("the verdict of one member of a chain group of n", n, |m| {
        Type::forget_emptiness();
        std::hint::black_box(chains[&m][0].verdict());
    });
    scaling::check(
        "the verdicts of every member of a chain group of n",
        n,
        |m| every(&chains[&m]),
    );
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
/// for each member read the group n times. Then the verdicts of every definition of the X14
/// system, which read the group by its verdicts and values (plan item VERDICT-group-readers).
/// Small instance `small_undecided_groups_are_admitted`.
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
    // Every definition, those outside the largest group too: such a definition reads the
    // members of that group by their group's verdicts, so the system's verdicts cost one search
    // of the group and one of each definition's own part (plan item VERDICT-group-readers),
    // where a search for each definition decided again the part of the group it reaches.
    let all = |n: usize| -> Vec<Type> {
        kernel(
            &undecided(claude_of(&mut Rng::new(3), n)),
            &format!("allu{n}"),
        )
        .into_iter()
        .map(|t| t.expect("every definition of the X14 family is admitted"))
        .collect()
    };
    let every = |ts: &[Type]| {
        Type::forget_emptiness();
        for t in ts {
            std::hint::black_box(t.verdict());
        }
    };
    let n = 128;
    let chains = scaling::inputs(n, chain);
    scaling::check(
        "the verdicts of every member of an undecided chain group of n",
        n,
        |m| every(&chains[&m]),
    );
    let ones = scaling::inputs(n, one);
    scaling::check(
        "the verdicts of the members of the largest undecided X14 group of n definitions",
        n,
        |m| every(&ones[&m]),
    );
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
#[test]
fn a_chain_decided_again_scales() {
    let chains = scaling::inputs(64, key_chain);
    for (&m, ts) in &chains {
        Type::forget_emptiness();
        assert!(!ts[m - 1].is_empty(), "R{} of a key chain of {m}", m - 1);
    }
    scaling::check("is_empty of R(n - 1) of a key chain of n", 64, |m| {
        Type::forget_emptiness();
        std::hint::black_box(chains[&m][m - 1].is_empty());
    });
}

/// `kernel` builds the groups of a system in time linear in its definitions and references
/// (plan item VERDICT-meet-cost): a chain of n groups, each reading the next, and one group of
/// n definitions (`chain_of`), at n and 8n, the systems written before the runs and each run
/// under names of its own, so no run finds the groups of another. A search from each definition
/// for what it reaches cost the square of the definitions, and a pass over every definition for
/// each group built their cube: 1.57 s for a chain of 1000 groups. Small instance
/// `the_groups_of_small_systems_are_built`.
#[test]
fn the_groups_of_a_system_are_built_in_its_size() {
    let runs = std::sync::atomic::AtomicUsize::new(0);
    let build = |sys: &[E]| {
        let run = runs.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let types = kernel(sys, &format!("built{run}"));
        assert!(types.iter().all(Option::is_some), "every group is admitted");
    };
    let n = 128;
    let chains = scaling::inputs(n, |m| chain_of_groups(m, false));
    scaling::check("the groups of a chain of n groups", n, |m| {
        build(&chains[&m])
    });
    let groups = scaling::inputs(n, |m| chain_of(&mut Rng::new(7), m));
    scaling::check("one group of n definitions", n, |m| build(&groups[&m]));
}

/// The text of a chain of `n` cycles, each entered at a tuple part that a part kept
/// unevaluated shares, takes time and bytes of order `n log n`: the parts are ordered by their
/// contents, a sort. Small instance `a_short_chain_of_shared_tuple_parts_prints`.
#[test]
fn a_chain_of_shared_tuple_parts_prints_in_its_size() {
    let chains = scaling::inputs(64, |n| {
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
    scaling::check("the text of a chain of n shared tuple parts", 64, |n| {
        std::hint::black_box(chains[&n].surface());
    });
}

/// The verdicts of every member of n copies of the group that hung the search, each its own
/// group, at n and 8n: the search takes each function type at most once for each value it
/// builds, and builds a value again only once a function taken after its build began holds it,
/// so each copy costs the same. Small instance
/// `a_few_copies_of_the_group_that_hung_the_search_are_refused`.
#[test]
fn verdicts_of_copies_of_the_group_that_hung_the_search_scale() {
    verdicts_of_copies_scale(
        "the verdicts of every member of n copies of the group that hung the search",
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
#[test]
fn verdicts_of_a_ring_of_the_group_that_hung_the_search_scale() {
    verdicts_of_copies_scale(
        "the verdicts of every member of a ring of n copies of the group that hung the search",
        true,
    );
}

/// The first 36 tuples of a tuple type of `n` components with six values each, at `n` and `8n`:
/// the product has `6^n` tuples, and only the 36 kept are built. Small instance
/// `the_first_tuples_are_those_of_the_whole_product`.
#[test]
fn the_first_tuples_of_a_wide_tuple_type_scale() {
    let opts = scaling::inputs(64, |n| vec![(0..6).collect::<Vec<usize>>(); n]);
    scaling::check(
        "the first 36 tuples of a tuple type of n components",
        64,
        |m| {
            std::hint::black_box(first_tuples(&opts[&m], 36));
        },
    );
}

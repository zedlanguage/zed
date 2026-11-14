//! The benchmarks of `cycle_dup.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `cycle_dup.rs`.

use super::*;

#[test]
fn a_group_of_closures_is_witnessed_in_its_written_size() {
    let n = 64;
    let inputs = scaling::inputs(n, |k| {
        Group::new(
            (0..k)
                .map(|i| Def {
                    name: format!("Closure{i}"),
                    params: vec![],
                    body: f(r((i + 1) % k)),
                })
                .collect(),
        )
        .unwrap()
        .instance(vec![])
    });
    scaling::check_order("shared checked values for a group of closures", n, 1, |k| {
        Type::forget_emptiness();
        for t in &inputs[&k] {
            assert_eq!(t.verdict(), Verdict::Inhabited);
        }
    });
}

/// Deciding the group of [`wide`] at `n` and `8n` arms: each part is read once and a union's
/// arms sorted, so the work is within `n log n`. The definitions are checked before the runs are
/// timed; a run makes a fresh instance, whose group is decided anew. Building the instance
/// costs about 57k instructions an arm, which hides a quadratic merge of equal arms at small
/// `n`: one that looks each arm up in a list of the arms before it passed at `n` 1024 (10.2
/// times) and failed at 2048 and 4096 (12.2 times), against 8.1 times here.
#[test]
fn many_arms_scale() {
    let n = 4096;
    let groups = scaling::inputs(n, |m| {
        let defs = (["Node", "Tree", "Thunk"].into_iter().zip(wide(m)))
            .map(|(name, body)| Def {
                name: name.into(),
                params: vec![],
                body,
            })
            .collect();
        Group::new(defs).unwrap_or_else(|e| panic!("{}", e.message))
    });
    scaling::check_order("a union of n arms written twice and nested", n, 1, |m| {
        Type::forget_emptiness();
        for t in &groups[&m].instance(vec![]) {
            std::hint::black_box(t.decided_by_group());
        }
    });
}

/// Deciding the group of [`meets_in_orders`] with every meet written twice, at `n` and `8n`
/// arms: each part is read once and the operands of a meet are of one color, so building the
/// canonical form stays within `n log n` (item GROUP-search-canon-key).
#[test]
fn many_meets_in_two_orders_scale() {
    let n = 512;
    let groups = scaling::inputs(n, |m| {
        let defs = (["Node", "Tree", "Thunk"]
            .into_iter()
            .zip(meets_in_orders(m, true)))
        .map(|(name, body)| Def {
            name: name.into(),
            params: vec![],
            body,
        })
        .collect();
        Group::new(defs).unwrap_or_else(|e| panic!("{}", e.message))
    });
    scaling::check_order("a union of n meets each written in two orders", n, 1, |m| {
        Type::forget_emptiness();
        for t in &groups[&m].instance(vec![]) {
            std::hint::black_box(t.decided_by_group());
        }
    });
}

/// Deciding the group of a [`chain`] of `n` and `8n` names: one topological order, two trees
/// with lowest common ancestors in `log n`, and one sort of the arms, so within `n log n`.
#[test]
fn a_chain_of_names_scales() {
    let n = 128;
    let groups = scaling::inputs(n, |m| named(chain(m, false)));
    scaling::check_order("a chain of n names", n, 1, |m| {
        Type::forget_emptiness();
        for t in &groups[&m].instance(vec![]) {
            std::hint::black_box(t.decided_by_group());
        }
    });
}

/// Deciding [`copies`] of `n` and `8n`: one round of contraction, merging and dropping arms,
/// within `m log m`.
#[test]
fn copies_of_parts_equal_once_arms_are_dropped_scale() {
    let n = 64;
    let groups = scaling::inputs(n, |m| named(copies(m)));
    scaling::check_order("n copies of parts equal once arms are dropped", n, 1, |m| {
        Type::forget_emptiness();
        for t in &groups[&m].instance(vec![]) {
            std::hint::black_box(t.decided_by_group());
        }
    });
}

/// Deciding the group of [`two_chains`] of `n` and `8n` names, with the nodes that play alike
/// found by the refinement of `names::merged`, within `m log m`.
#[test]
fn two_chains_written_alike_scale() {
    let n = 512;
    let groups = scaling::inputs(n, |m| named(two_chains(m)));
    scaling::check_order("two chains of n names written alike", n, 1, |m| {
        Type::forget_emptiness();
        for t in &groups[&m].instance(vec![]) {
            std::hint::black_box(t.decided_by_group());
        }
    });
}

/// Deciding the groups of [`meets_in_orders`] at `n` and `8n` arms, every meet written twice:
/// the walk that finds the groups a type depends on reads each part of the diagrams the members
/// share once for the whole query, not once per member that holds it (item
/// GROUP-search-canon-key). With a fresh scan per member the larger run took 35.2 times the
/// work of the smaller, against a limit of 11.7. The groups are built before the work is
/// counted.
#[test]
fn shared_parts_are_read_once_when_deciding_their_groups() {
    let n = 512;
    let inputs = scaling::inputs(n, |m| {
        let defs = (["WalkNode", "WalkTree", "WalkThunk"]
            .into_iter()
            .zip(meets_in_orders(m, true)))
        .map(|(name, body)| Def {
            name: name.into(),
            params: vec![],
            body,
        })
        .collect();
        Group::new(defs)
            .unwrap_or_else(|e| panic!("{}", e.message))
            .instance(vec![])
    });
    scaling::check_order(
        "shared parts in the walk of group dependencies",
        n,
        1,
        |m| {
            Type::forget_emptiness();
            for t in &inputs[&m] {
                assert_eq!(t.verdict(), Verdict::Inhabited);
            }
        },
    );
}

/// [`morphisms_met_with_a_union`] at 64 and 512 arms, the groups built before the work is
/// counted.
#[test]
fn morphism_types_met_with_a_union_of_morphism_types_scale() {
    let n = 64;
    let groups = scaling::inputs(n, morphisms_met_with_a_union);
    scaling::check_order("n morphism types met with a union of n", n, 1, |m| {
        Type::forget_emptiness();
        assert_eq!(groups[&m][NODE].verdict(), Verdict::Inhabited);
    });
}

/// Every arm has the same function constraint in its second component. It must be tested
/// before unfolding each different literal context in its first component.
#[test]
fn shared_morphism_constraints_are_checked_in_the_size_of_the_union() {
    let inputs = scaling::inputs(16, |m| arm_family(false, m).instance(vec![]));
    scaling::check_order("shared morphism result constraints", 16, 1, |m| {
        Type::forget_emptiness();
        for t in &inputs[&m] {
            assert_eq!(t.verdict(), Verdict::Empty);
        }
    });
}

#[test]
fn shared_morphism_constraints_scale_without_a_group_query() {
    for route in ["empty", "tuple", "value"] {
        let inputs = scaling::inputs(16, |m| {
            arm_family(false, m)
                .instance(vec![])
                .into_iter()
                .map(|t| match route {
                    "tuple" => Type::tuple(vec![t]),
                    "value" => Type::morphism(Type::int(), Type::int(), t),
                    _ => t,
                })
                .collect::<Vec<_>>()
        });
        scaling::check_order(
            "shared morphism constraints outside group queries",
            16,
            1,
            |m| {
                Type::forget_emptiness();
                for t in &inputs[&m] {
                    if route == "empty" {
                        assert!(t.is_empty());
                    } else {
                        assert_eq!(t.verdict(), Verdict::Empty);
                    }
                }
            },
        );
    }
}

#[test]
fn shared_morphism_constraints_scale_beside_a_refused_member() {
    let n = 256;
    let inputs = scaling::inputs(n, |m| arm_family(true, m).instance(vec![]));
    for empty in [false, true] {
        scaling::check_order(
            "shared morphism constraints with a refused member",
            n,
            1,
            |m| {
                Type::forget_emptiness();
                for (t, want) in inputs[&m].iter().zip([
                    Verdict::Refused(Refusal::Fork),
                    Verdict::Empty,
                    Verdict::Empty,
                ]) {
                    if empty {
                        assert_eq!(t.is_empty(), want == Verdict::Empty);
                    } else {
                        assert_eq!(t.verdict(), want);
                    }
                }
            },
        );
    }
}

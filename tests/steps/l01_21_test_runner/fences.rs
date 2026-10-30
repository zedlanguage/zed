use zedc::testing::test;

/// The enabled fences run: each fence of layer L1 passes its checks but for what a fragment
/// leaves to the text around it, a name it does not bind. A fence with such a name is not
/// elaborated, so its ✗ marks are not checked.
#[test]
fn every_l1_fence_passes_but_for_its_free_names() {
    let mut clean = Vec::new();
    for f in zed_tests::fences::all()
        .iter()
        .filter(|f| f.layer <= 1 && !f.notation)
    {
        let outcomes = test(&f.text);
        let failures: Vec<&String> = outcomes.iter().filter_map(|o| o.failure.as_ref()).collect();
        let free = |w: &&String| w.ends_with("is not defined");
        if failures.is_empty() {
            clean.push((f.at.clone(), outcomes.len()));
            continue;
        }
        let unchecked = |w: &&String| w.as_str() == "the line is marked ✗ and has no diagnostic";
        assert!(
            failures.iter().any(free) && failures.iter().all(|w| free(w) || unchecked(w)),
            "{}: {failures:?}",
            f.at
        );
    }
    // The rebinding fence checks its one mark; the lambda fence binds every name it uses.
    assert_eq!(
        clean,
        [
            ("EXAMPLES.md:78".to_string(), 1),
            ("EXAMPLES.md:203".to_string(), 0)
        ]
    );
}

use zedc::testing::test;

/// The enabled fences run: each fence of layer L1 passes its checks but for what a fragment
/// leaves to the text around it, a name it does not bind. A fence with such a name is not
/// elaborated, so its ✗ marks are not checked.
#[test]
fn every_l1_fence_passes_but_for_its_free_names() {
    let (mut clean, mut rejection) = (Vec::new(), 0);
    for f in zed_tests::fences::all()
        .iter()
        .filter(|f| f.layer <= 1 && !f.notation)
    {
        let outcomes = test(&f.text);
        let failures: Vec<&String> = outcomes.iter().filter_map(|o| o.failure.as_ref()).collect();
        let free = |w: &&String| w.ends_with("is not defined");
        if failures.is_empty() {
            rejection += usize::from(!zedc::fence::marks(&f.text).lines.is_empty());
            clean.push((f.key.clone(), outcomes.len()));
            continue;
        }
        let unchecked = |w: &&String| w.as_str() == "the line is marked ✗ and has no diagnostic";
        assert!(
            failures.iter().any(free) && failures.iter().all(|w| free(w) || unchecked(w)),
            "{}: {failures:?}",
            f.at
        );
    }
    // A fence with a ✗ mark that compiles fails above, since its outcome is neither of the
    // two kinds allowed. The rebinding fence is the one rejection fence whose marks run.
    println!("{rejection} rejection fences run");
    assert_eq!(rejection, 1);
    // The rebinding fence checks its one mark; the lambda fence binds every name it uses.
    assert_eq!(
        clean,
        [
            ("EXAMPLES.md [2. Bindings and values] 2".to_string(), 1),
            ("EXAMPLES.md [6. Functions] 2".to_string(), 0)
        ]
    );
}

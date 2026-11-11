use zedc::testing::test;

/// The enabled fences run: each fence of layer L1 passes its checks but for what a fragment
/// leaves to the text around it, a name it does not bind. An elision `…` is such a name, `elided`,
/// as the spec tools read it. A fence with such a name is not elaborated, so its ✗ marks are not
/// checked.
#[test]
fn every_l1_fence_passes_but_for_its_free_names() {
    let (mut clean, mut rejection) = (Vec::new(), 0);
    let (mut alternatives, mut declared) = (Vec::new(), Vec::new());
    for f in zed_tests::fences::all()
        .iter()
        .filter(|f| f.layer <= 1 && !f.notation)
    {
        let outcomes = test(&f.text.replace('…', "elided"));
        let failures: Vec<&String> = outcomes.iter().filter_map(|o| o.failure.as_ref()).collect();
        let free = |w: &&String| w.contains(" is not defined: no ");
        if failures.is_empty() {
            rejection += usize::from(!zedc::fence::marks(&f.text).lines.is_empty());
            clean.push((f.key.clone(), outcomes.len()));
            continue;
        }
        // A fence that shows other forms of `main` side by side is refused as a program, and is
        // checked otherwise.
        let shown = |w: &&String| w.starts_with("this file declares 2 functions named `main`");
        if failures.iter().all(shown) {
            alternatives.push(f.key.clone());
            continue;
        }
        // DESIGN puts a declared result type at L1 (`Result = '->' Type`); zedc compiles it on
        // `main` only (MAIN-args), and rejects it elsewhere as a form it does not compile yet.
        let result = |w: &&String| w.starts_with("the declared result type ");
        if failures.iter().all(|w| result(w) || free(w)) && failures.iter().any(result) {
            declared.push(f.key.clone());
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
    assert_eq!(alternatives, ["DESIGN.md [sec:ports] 1"]);
    assert_eq!(declared, ["EXAMPLES.md [5. Conditionals] 1"]);
    assert_eq!(rejection, 1);
    // The rebinding fence checks its one mark; the lambda fence binds every name it uses, and
    // the environment fence reads only `m.env`, a field of `main`'s argument.
    assert_eq!(
        clean,
        [
            ("EXAMPLES.md [2. Bindings and values] 2".to_string(), 1),
            ("EXAMPLES.md [6. Functions] 2".to_string(), 0),
            (
                "EXAMPLES.md [18. Files, stores, and the world] 8".to_string(),
                0
            )
        ]
    );
}

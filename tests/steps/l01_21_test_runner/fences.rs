use zedc::testing::test;

/// The enabled fences run: each fence of layer L1 passes its checks but for what a fragment
/// leaves to the text around it, a name it does not bind. An elision `…` is such a name, `elided`,
/// as the spec tools read it. A fence with such a name is not elaborated, so its ✗ marks are not
/// checked.
#[test]
fn every_l1_fence_passes_but_for_its_free_names() {
    let (mut clean, mut rejection) = (Vec::new(), 0);
    let (mut alternatives, mut declared, mut ascribed) = (Vec::new(), Vec::new(), Vec::new());
    for f in zed_tests::fences::all()
        .iter()
        .filter(|f| f.layer <= 1 && !f.notation)
    {
        let text = f.text.replace('…', "elided");
        let outcomes = test(&text);
        let failures: Vec<&String> = outcomes.iter().filter_map(|o| o.failure.as_ref()).collect();
        let free = |w: &&String| w.contains(" is not defined.");
        if failures.is_empty() {
            rejection += usize::from(!zedc::fence::marks(&f.text).lines.is_empty());
            clean.push((f.key.clone(), outcomes.len()));
            continue;
        }
        // A fence that shows other forms of `main` side by side is refused as a program, and is
        // checked otherwise: as two functions named `main`, or, where two of them have the same
        // parameters, as a second `main` in one scope.
        let shown = |w: &&String| {
            w.starts_with("this file declares 2 functions named `main`")
                || w.starts_with("`main` is already declared in this scope")
        };
        if failures.iter().all(shown) {
            alternatives.push(f.key.clone());
            continue;
        }
        // DESIGN puts a declared result type at L1 (`Result = '->' Type`); zedc compiles it on
        // `main` only (MAIN-args), and rejects it elsewhere as a form it does not support.
        let result = |w: &&String| w.starts_with("the declared result type ");
        if failures.iter().all(|w| result(w) || free(w)) && failures.iter().any(result) {
            declared.push(f.key.clone());
            continue;
        }
        // The layer audit (DESIGN 23a88fd, author P254) puts `x: T = e` at L1, and with it the
        // range suffix (`port: int[1..=65535] = 8080;`); zedc refuses it as a form it does not
        // support until plan rows LAYER-L1-forms and RANGE-L1 build it.
        // A fence so refused is not elaborated, so its ✗ marks are not checked either: the
        // numbers fence, whose `b: u8 = 255;` is of L1 since the fixed-width aliases are names
        // of their ranges (step L1.12).
        let binding = |w: &&String| w.starts_with("the binding with a declared type ");
        let unchecked = |w: &&String| w.as_str() == "the line is marked ✗ and has no diagnostic";
        if failures
            .iter()
            .all(|w| binding(w) || free(w) || unchecked(w))
            && failures.iter().any(binding)
        {
            ascribed.push(f.key.clone());
            continue;
        }
        assert!(
            failures.iter().any(free) && failures.iter().all(|w| free(w) || unchecked(w)),
            "{}: {failures:?}",
            f.at
        );
    }
    // A fence with a ✗ mark that compiles fails above, since its outcome is neither of the
    // two kinds allowed. The rebinding fence is the one rejection fence whose marks run.
    println!("{rejection} rejection fences run");
    assert_eq!(
        alternatives,
        [
            "DESIGN.md [sec:ports] 4",
            "DESIGN.md [sec:checking_in_zed] 1"
        ]
    );
    assert_eq!(
        declared,
        [
            "DESIGN.md [sec:memory] 1",
            "EXAMPLES.md [5. Conditionals] 1"
        ]
    );
    assert_eq!(
        ascribed,
        [
            "EXAMPLES.md [2. Bindings and values] 1",
            "EXAMPLES.md [3. Numbers] 1"
        ]
    );
    assert_eq!(rejection, 1);
    // The rebinding fence checks its one mark; the lambda fence and the `origin` fence bind
    // every name they use, and hello world and the environment fence use only `m.stdout` and
    // `m.env`, fields of `main`'s argument (hello world and `origin` are of L1 since the array
    // and map displays are, step L1.16).
    assert_eq!(
        clean,
        [
            ("EXAMPLES.md [1. Programs and ports] 1".to_string(), 0),
            ("EXAMPLES.md [2. Bindings and values] 2".to_string(), 1),
            ("EXAMPLES.md [6. Functions] 2".to_string(), 0),
            ("EXAMPLES.md [10. Structs and updates] 5".to_string(), 0),
            (
                "EXAMPLES.md [18. Files, stores, and the world] 8".to_string(),
                0
            )
        ]
    );
}

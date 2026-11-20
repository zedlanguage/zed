//! The tests of `ty::tests` at unusual sizes (author P178), run by `tools/run_tests.sh --bench`
//! and left out of its default run (TEST-bench-move-crates). The correctness tests that keep
//! what each checks at small sizes are
//! `the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows` and
//! `the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows_on_wider_shapes`.

use super::*;

/// The comparisons of the index tests on large overloads: four cases of 300 arrows of the
/// plain shapes, and four of 90 arrows of the wider shapes, the largest sizes those tests had.
/// Each verdict is checked against every set of arrows as there; only the sizes differ.
#[test]
fn the_index_of_arrows_gives_the_verdict_on_large_overloads() {
    let mut rng = Rng::new(crate::seed::seed(
        "the_index_of_arrows_gives_the_verdict_on_large_overloads",
    ));
    let mut counts = Counts::default();
    for case in 0..4 {
        index_case(&mut rng, 300, case, &mut counts);
        wider_case(&mut rng, 90, case, &mut counts);
    }
}

/// The last wider case of seed 2929246812783321450 of the test above: an arrow of `q` that
/// arrows of `s` cover together, where trying another arrow of `s` for a part was refused
/// (a tuple `(B,)` a search of shapes gives up on). That refusal was kept, so the index
/// answered no where the search of every set of arrows answered yes. A refused attempt now
/// leaves that arrow out of the cover only ([`part_of_alone`]).
#[test]
fn a_refused_part_does_not_refuse_a_cover_other_arrows_give() {
    let mut rng = Rng::new(2929246812783321450);
    let mut counts = Counts::default();
    for case in 0..3 {
        index_case(&mut rng, 300, case, &mut counts);
        wider_case(&mut rng, 90, case, &mut counts);
    }
    index_case(&mut rng, 300, 3, &mut counts);
    let (s, qas, width, qm, _) = wider_input(&mut rng, 90);
    let q = sig_mask(qas, width, qm);
    let new = fits_sig(&s, &q);
    REFERENCE.set(Reference::Subsets);
    let subsets = fits_sig(&s, &q);
    REFERENCE.set(Reference::None);
    assert!(new && subsets, "index {new}, every set of arrows {subsets}");
}

/// The signature `(x: $0) -> ()` with `n` compact forwards on `$0`, the `j`th of one internal
/// result, the class `$(10 n + j)`, and `$0` solved to the tuple of the `n` classes `$1` to
/// `$n`, none of them internal: [`Settle::must_decode`] asks each of the n variables of the
/// solution against the n forwards, and answers no. The naive test made n² calls of
/// [`FwdNeed::holds_internal`]; the index of [`InternalResults`] costs O(n log n)
/// (PROOF-must-decode-no-compact-solved). Small instances:
/// `the_index_of_internal_results_holds_what_some_forward_holds`.
#[test]
fn n_forwards_with_internal_results_beside_a_class_solved_to_n_variables() {
    let make = |n: usize| {
        let mut sig = one_of(Ty::var("$0".into()), Ty::empty());
        sig.needs = (0..n)
            .map(|j| Need {
                on: Ty::var("$0".into()),
                kind: NeedKind::Fwd(Arc::new(compact_fwd(Some(10 * n + j), 1, &[], None, None))),
                result: None,
                span: Span { start: 0, end: 1 },
                alike: Arc::new([]),
                via: CallPath::default(),
            })
            .collect();
        let solution = Ty::tuple((1..=n).map(|k| Ty::var(format!("${k}").into())).collect());
        (Arc::new(sig), solution)
    };
    let inputs = crate::scaling::inputs(400, make);
    crate::scaling::check(
        "must_decode of n forwards beside n solved variables",
        400,
        |n| {
            let (sig, solution) = &inputs[&n];
            let solve = |v: &str| (v == "$0").then(|| solution.clone());
            let settle = Settle {
                solve: &solve,
                made: Vec::new(),
                kept: Vec::new(),
            };
            assert!(!settle.must_decode(sig));
        },
    );
}

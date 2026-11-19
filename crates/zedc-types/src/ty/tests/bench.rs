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

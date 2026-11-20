//! The tests of `check::fate::tests` at unusual sizes (author P178), run by `tools/run_tests.sh
//! --bench` and left out of its default run. The correctness tests that keep what this checks at
//! small sizes are `a_match_handles_the_atoms_its_arms_name_and_passes_on_the_rest` and
//! `a_name_arm_stops_the_atoms_left_and_a_guarded_arm_handles_none`.

use super::*;

/// Row CHK-fate-unwalked-forms: the scrutinee of a `match` of n arms, each naming an atom of its
/// own, then a name arm, which stops the atoms left. [`scrutinee`] makes one pass over the arms,
/// one union and one difference of atom sets an arm. The text is lexed, parsed and built before
/// timing; a run builds the table of the unit ([`Fates::build`]) and reads the scrutinee's fate.
#[test]
fn a_match_of_many_atom_arms_scales() {
    let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
    let inputs = crate::scaling::inputs(500, |n| {
        let arms: String = (0..n).map(|i| format!("#a{i} -> {i}, ")).collect();
        let text = format!("f(x) = match x {{ {arms}y -> y }};\n");
        let unit = parsed(&text);
        (text, unit)
    });
    crate::scaling::check(
        "the fate of the scrutinee of a match of n atom arms",
        500,
        |n| {
            let (text, unit) = &inputs[&n];
            let t = Tables::new(&[], &res);
            let f = Fates::build(&t, unit)
                .of(scrutinee_span(text))
                .expect("the scrutinee has a fate")
                .clone();
            assert!(handled(&f, "a0") && stopped(&f, "b"), "{f:?}");
        },
    );
}

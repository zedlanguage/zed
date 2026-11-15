//! What the checker refuses among the forms of this step, and the forms of step L3.2 not built
//! yet, each refused with the step named.

use super::run;

/// The first line of what `zedc run` writes for `body`, which it must refuse.
fn refused(name: &str, body: &str) -> String {
    let ran = run(name, body);
    assert_ne!(ran.status, 0, "{name}: {body} ran: {}", ran.stdout);
    ran.stderr
}

#[test]
fn a_key_disjoint_from_the_keys_is_refused() {
    // R11 (author): a key whose type shares no value with the keys is a static error.
    let e = refused("disjoint", "${[10, 20][5]}");
    assert!(e.contains("5"), "{e}");
}

#[test]
fn map_takes_one_function_by_position() {
    let e = refused("map_two", "${[1].map(x -> x, x -> x)}");
    assert!(
        e.contains("`map` takes one function, passed by position"),
        "{e}"
    );
    let e = refused("map_value", "${[1].map(3)}");
    assert!(
        e.contains("`map` takes a function, and this value is"),
        "{e}"
    );
}

#[test]
fn map_of_a_value_with_no_entries_is_refused() {
    let e = refused("map_int", "${(3).map(x -> x)}");
    assert!(e.contains("`map` works on each entry of a family"), "{e}");
}

#[test]
fn where_takes_a_function_giving_bool() {
    let e = refused("where_int", "${[10, 20].where(x -> x + 1)}");
    assert!(
        e.contains("`where` keeps the entries its function gives `true` for"),
        "{e}"
    );
}

#[test]
fn a_fold_of_a_row_that_may_be_empty_needs_else() {
    // In a function's body the fold takes no identity, so the empty row `[]` folds to `#empty`
    // alone, and `+` on a value that can only be an atom is an error.
    let e = refused(
        "empty_row",
        "${{0 -> [1], 1 -> []}.map(r -> (r >< (+)) + 1)}",
    );
    assert!(
        e.contains("the function given to `map` does not take"),
        "{e}"
    );
}

#[test]
fn a_fold_by_an_operator_without_a_built_in_identity_is_not_built() {
    let e = refused("minus", "${[1, 2] >< (-)}");
    assert!(e.contains("a fold `><` by `(-)`"), "{e}");
}

#[test]
fn the_forms_not_built_are_refused_as_not_built() {
    // The messages name no step: the program's words only. The steps are named at the
    // refusals in zedc-resolve: ranges and operator sections outside `><` are step L3.2's,
    // metadata reads steps L3.2 and L3.2a's.
    for (name, body, what) in [
        ("range", "${0 ..< 3}", "a range is part of the Zed language"),
        (
            "section",
            "${(+)}",
            "an operator section is part of the Zed language",
        ),
        (
            "read",
            "${[1]::len}",
            "a metadata read `::` is part of the Zed language",
        ),
    ] {
        let e = refused(name, body);
        assert!(e.contains(what), "{name}: {e}");
        assert!(e.contains("does not compile it yet"), "{name}: {e}");
    }
}

#[test]
fn where_over_loose_atoms_is_not_built() {
    // The test of `where` gives the atom, not a verdict, for an entry that is a loose atom,
    // and what `where` keeps then is not settled.
    let e = refused("where_atoms", "${{0 -> 1, 1 -> #oops}.where(x -> x > 0)}");
    assert!(
        e.contains("`where` over entries that may be the atoms"),
        "{e}"
    );
    assert!(e.contains("does not compile it yet"), "{e}");
}

use std::collections::BTreeMap;

use zed_tests::scaling;

use super::super::held_functions::{
    in_a_wide_payload, in_atoms, in_atoms_and_tuples, in_atoms_by_bindings, in_atoms_by_calls,
    in_atoms_twice, in_atoms_twice_in_a_function, in_calls, in_named_steps, in_one_expression,
    nested, notes_in_calls, notes_in_named_steps, notes_in_one_expression,
};
use super::super::{Resolved, type_errors};

#[test]
fn a_function_in_many_nested_tuples_is_one_error_in_linear_time() {
    type Family = fn(usize) -> String;
    type Count = fn(usize) -> usize;
    for (what, text, notes) in [
        (
            "a function n tuples deep in one expression",
            in_one_expression as Family,
            notes_in_one_expression as Count,
        ),
        (
            "a function put in a tuple by n bindings",
            in_named_steps,
            notes_in_named_steps,
        ),
        (
            "a function put in a tuple by n nested calls",
            in_calls,
            notes_in_calls,
        ),
    ] {
        let one = type_errors(&text(3));
        assert_eq!(one.len(), 1, "{what}: {one:?}");
        let units: BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
            .into_iter()
            .map(|n| (n, Resolved::new(&text(n))))
            .collect();
        scaling::check_order(what, 500, 1, |n| {
            let info = units[&n].check();
            // One error, with one note for each step the function passes through and none
            // that prints a type of the depth of the tuples.
            assert_eq!(info.errors.len(), 1, "{what} at {n}");
            assert_eq!(info.errors[0].notes.len(), notes(n), "{what} at {n}");
        });
    }
}

/// Besides its ratio: one error where a payload holds a function, none where none does. Small
/// instance: `held_functions::a_function_in_an_atom_s_payload_is_one_error`.
#[test]
fn a_function_in_payloads_is_found_in_linear_time() {
    // Each level makes a row, which reads the payload below it once; the payload walk reads
    // a row and does not enter it. Atoms nested directly in atoms are tested by
    // `atoms_nested_in_atoms_are_checked_in_linear_time` (COMPLEXITY.md, ATOM-nested-sq).
    type Family = fn(usize, &str) -> String;
    for (what, text, leaf, errors) in [
        (
            "a function n atoms and tuples deep",
            in_atoms_and_tuples as Family,
            "scale",
            1,
        ),
        (
            "an integer n atoms and tuples deep",
            in_atoms_and_tuples,
            "1",
            0,
        ),
        (
            "a function after n integers in a payload",
            in_a_wide_payload,
            "scale",
            1,
        ),
        (
            "an integer after n integers in a payload",
            in_a_wide_payload,
            "1",
            0,
        ),
    ] {
        let units: BTreeMap<usize, Resolved> = [2000, scaling::FACTOR * 2000]
            .into_iter()
            .map(|n| (n, Resolved::new(&text(n, leaf))))
            .collect();
        scaling::check_order(what, 2000, 1, |n| {
            let info = units[&n].check();
            assert_eq!(info.errors.len(), errors, "{what} at {n}");
        });
    }
}

#[test]
fn atoms_nested_in_atoms_are_checked_in_linear_time() {
    // The checker keeps the type of every expression it meets, and the type of the atom at
    // each level holds the level below as its payload: copying that payload at each level was
    // `O(n^2)`, and so were the walks that entered every payload at each level to find its
    // variables, replace them or find a function (ATOM-nested-sq). A payload is a shared
    // node now, copied in constant time, which keeps what it holds at any depth, so a walk
    // reads it and does not enter it; a payload holding the level below twice is a shared
    // node met twice, entered at most once, and made at most once where a call replaces the
    // variables it holds. The leaf is an integer: with a function there, the refusal of `==`
    // shows a note for each level with that level's type, `O(n^2)` characters of text, and
    // `2^n` for the payload held twice (COMPLEXITY.md, ATOM-nested-sq).
    type Family = fn(usize, &str) -> String;
    for (what, text) in [
        (
            "an integer n atoms deep in one expression",
            in_atoms as Family,
        ),
        (
            "an integer put in an atom by n bindings",
            in_atoms_by_bindings,
        ),
        (
            "an integer put in an atom by n nested calls",
            in_atoms_by_calls,
        ),
        (
            "an integer put twice in an atom by n bindings",
            in_atoms_twice,
        ),
        (
            "an integer put twice in an atom by n bindings in a generic function",
            in_atoms_twice_in_a_function,
        ),
    ] {
        let units: BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
            .into_iter()
            .map(|n| (n, Resolved::new(&text(n, "1"))))
            .collect();
        scaling::check_order(what, 500, 1, |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{what} at {n}");
        });
    }
}

#[test]
fn a_type_8000_tuples_deep_prints_and_drops_on_a_2_mib_stack() {
    // `Ty::write` recursed once a level and overflowed a 2 MiB stack below 8,000 deep, as did
    // the drop glue of the rows.
    assert_eq!(nested(2).to_string(), "((_, _), _)");
    scaling::on_a_thread(2 << 20, || {
        let n = 8000;
        let text = nested(n).to_string();
        assert_eq!(text, format!("{}_{}", "(".repeat(n), ", _)".repeat(n)));
    });
}

#[test]
fn a_type_31250_tuples_deep_prints_and_drops_on_a_256_kib_stack() {
    // It ran a million tuples deep on an 8 MiB stack, about 8 bytes a level; this is the same
    // stack a level at a thirty-second of the depth.
    scaling::on_a_thread((8 << 20) / 32, || {
        let n = 1_000_000 / 32;
        let text = nested(n).to_string();
        assert!(text == format!("{}_{}", "(".repeat(n), ", _)".repeat(n)));
    });
}

//! Printing and reading back types of `n` parts, at `n` and `8n` (`printed.rs`).

use zed_tests::scaling;

use crate::printed::*;

#[test]
fn reading_a_printed_type_back_scales() {
    let n = 16_000;
    let inputs = scaling::inputs(n, wide);
    scaling::check(
        "reading back a union of n atoms and a tuple of n components",
        n,
        |size| a_printed_type_read_back(&inputs[&size], size),
    );
}

/// Printing a union of `n` atoms, each with its payload type, and reading the text back, each
/// timed alone: the printer takes the payload atoms out of the kernel set in one difference.
#[test]
fn printing_atoms_with_payloads_scales() {
    let n = 2800;
    let inputs = scaling::inputs(n, |m| {
        let t = atoms_with_payloads(m);
        let text = t.to_string();
        (t, text)
    });
    scaling::check("printing a union of n atoms with payloads", n, |size| {
        atoms_with_payloads_printed(&inputs[&size].0, size);
    });
    scaling::check("reading back a union of n atoms with payloads", n, |size| {
        let (t, text) = &inputs[&size];
        assert_eq!(&back(text), t);
    });
}

/// Reading back an intersection of `n` function types of one parameter list: the parameter
/// lists are compared with the first once each, and the arrows joined into one signature.
#[test]
fn reading_an_overload_of_many_arrows_back_scales() {
    let n = 7100;
    let inputs = scaling::inputs(n, overload);
    scaling::check("reading back an overload of n arrows", n, |size| {
        an_overload_read_back(&inputs[&size], size);
    });
}

/// Reading back an overload of `n` arrows nested `n` deep in parentheses, to the left and to
/// the right: each intersection is read once, with the one around it, so the cost is linear
/// and not a walk of the inner arrows at each depth.
#[test]
fn reading_an_overload_nested_in_parentheses_back_scales() {
    let n = 3200;
    for (side, left) in [("left", true), ("right", false)] {
        let inputs = scaling::inputs(n, |m| nested_overload(m, left));
        scaling::check(
            &format!("reading back an overload of n arrows nested n deep to the {side}"),
            n,
            |size| an_overload_read_back(&inputs[&size], size),
        );
    }
}

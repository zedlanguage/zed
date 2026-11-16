use std::collections::BTreeMap;

use zed_tests::scaling;

use super::super::held_functions::{
    in_a_wide_payload, in_atoms, in_atoms_and_tuples, in_atoms_by_bindings, in_atoms_by_calls,
    in_atoms_twice, in_atoms_twice_in_a_function, in_calls, in_families_by_bindings,
    in_families_in_one_expression, in_named_steps, in_one_expression, nested, notes_in_calls,
    notes_in_named_steps, notes_in_one_expression, returned_by_lambdas,
};
use super::super::{Resolved, type_errors};

/// Each key of a display and each `in` test is checked as data, `O(1)` for a key whose
/// type's outer level is `O(1)` ([`Ck::data`] reads rows and families at their outer level),
/// so `n` keys cost `O(n)`; with a function in each key, `n` errors of `O(1)` notes each, each
/// headline naming its own entry and not the display. Small instances:
/// `held_functions::a_key_that_holds_a_function_is_rejected`.
#[test]
fn keys_of_a_display_and_in_tests_are_checked_as_data_in_linear_time() {
    // `n` keys `(leaf, i)`, then `n` tests `(leaf, i) in t`.
    let text = |n: usize, leaf: &str| {
        let keys: Vec<String> = (0..n).map(|i| format!("({leaf}, {i}) -> {i}")).collect();
        let tests: Vec<String> = (0..n).map(|i| format!("({leaf}, {i}) in t")).collect();
        format!(
            "scale(positional x) = x * int(2);\nt = {{ {} }};\nu = ({});\n",
            keys.join(", "),
            tests.join(", ")
        )
    };
    for (what, leaf, errors) in [
        (
            "n keys and n `in` tests, each holding a function",
            "scale",
            2,
        ),
        ("n keys and n `in` tests, each holding an integer", "1", 0),
    ] {
        let units: BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
            .into_iter()
            .map(|n| (n, Resolved::new(&text(n, leaf))))
            .collect();
        scaling::check_order(what, 500, 1, |n| {
            let info = units[&n].check();
            assert_eq!(info.errors.len(), errors * n, "{what} at {n}");
        });
    }
}

/// Each read of a family at a key is checked as data, at the read or, through a generic
/// function, at each call, which meets the data need of the key's class once: `O(1)` for a key
/// whose type's outer level is `O(1)`, so `n` reads cost `O(n)`; with a function in each key,
/// `n` errors of `O(1)` notes each. A walk of all earlier keys at each read would be `O(n^2)`.
/// Small instances: `l01_17_value_representation::function_in_family::
/// a_key_that_holds_a_function_is_rejected_at_a_read` (row FAIL-generic-get-function-key).
#[test]
fn keys_of_reads_are_checked_as_data_in_linear_time() {
    // `n` plain reads `c[(leaf, 1)]`, then `n` reads through `get`; with an integer leaf, each
    // key is found.
    let text = |n: usize, leaf: &str| {
        let reads = vec![format!("c[({leaf}, 1)] else 0"); n];
        let calls = vec![format!("get(c, ({leaf}, 1))"); n];
        format!(
            "scale(positional x) = x * int(2);\nget(positional c, positional k) = c[k] else 0;\n\
             c = {{ (1, 1) -> 1 }};\nu = ({});\nv = ({});\n",
            reads.join(", "),
            calls.join(", ")
        )
    };
    for (what, leaf, errors) in [
        (
            "n reads and n reads through a call, each key holding a function",
            "scale",
            2,
        ),
        ("n reads and n reads through a call, each key found", "1", 0),
    ] {
        let units: BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
            .into_iter()
            .map(|n| (n, Resolved::new(&text(n, leaf))))
            .collect();
        scaling::check_order(what, 500, 1, |n| {
            let info = units[&n].check();
            assert_eq!(info.errors.len(), errors * n, "{what} at {n}");
        });
    }
}

/// One expression of `n` parts can give `n` errors, each a use that needs data: a string of `n`
/// holes, each a function, and a chain of `n` merges, each of a failure that holds one. Each
/// headline names its own piece and no expression that holds all `n` (`Ck::data_headline`), so
/// the `n` messages are `O(n)` long in all; naming the whole string or chain in each was
/// `O(n^2)`, 51 times the bytes at `8n`. Small instances:
/// `l01_17_value_representation::function_in_family::a_value_that_may_hold_a_function_is_rejected_with_the_use_in_code`
/// and `held_functions::failures_holding_functions_that_merge_are_refused`.
#[test]
fn many_errors_in_one_expression_have_headlines_of_bounded_length() {
    type Text = fn(usize) -> String;
    fn string(n: usize) -> String {
        format!(
            "scale(positional x) = x * int(2);\na = \"{}\";\n",
            "${scale}".repeat(n)
        )
    }
    fn chain(n: usize) -> String {
        format!(
            "g(positional k: int) = k;\na(positional p: bool) = if p {{ 1 }} else {{ #errs(g) \
             }};\nx(positional p: bool) = a(p){};\n",
            " + a(p)".repeat(n)
        )
    }
    for (what, text, more) in [
        ("a string of n holes, each a function", string as Text, 0),
        (
            "a chain of n merges of failures holding a function",
            chain,
            1,
        ),
    ] {
        let units: BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
            .into_iter()
            .map(|n| (n, Resolved::new(&text(n))))
            .collect();
        scaling::check_order(what, 500, 1, |n| {
            let info = units[&n].check();
            assert_eq!(info.errors.len(), n + more, "{what} at {n}");
        });
    }
}

/// A function at the bottom of `n` families nested one in another is found by each use that
/// needs data in time linear in `n`: each family keeps what its entries hold ([`Entries`] in
/// crates/zedc-types/src/ty.rs), worked out once, so the type of each level is read at its
/// outer level. A walk to the bottom at each level would be `O(n^2)`. The derivation has a
/// step per family and name, with no type printed (CHK-held-cascade), so the one error is
/// `O(n)` notes. Small instance:
/// `held_functions::a_function_in_nested_families_is_one_error_with_the_path_to_it`.
#[test]
fn nested_families_are_checked_as_data_in_linear_time() {
    type Family = fn(usize, &str) -> String;
    for (what, text, leaf, errors, notes) in [
        (
            "a function n families deep in one expression",
            in_families_in_one_expression as Family,
            "scale",
            1,
            (|n| n + 6) as fn(usize) -> usize,
        ),
        (
            "an integer n families deep in one expression",
            in_families_in_one_expression,
            "1",
            0,
            |_| 0,
        ),
        (
            "a function put in a family by n bindings",
            in_families_by_bindings,
            "scale",
            1,
            |n| 3 * n + 4,
        ),
        (
            "an integer put in a family by n bindings",
            in_families_by_bindings,
            "1",
            0,
            |_| 0,
        ),
    ] {
        let units: BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
            .into_iter()
            .map(|n| (n, Resolved::new(&text(n, leaf))))
            .collect();
        scaling::check_order(what, 500, 1, |n| {
            let info = units[&n].check();
            assert_eq!(info.errors.len(), errors, "{what} at {n}");
            let got = info.errors.first().map_or(0, |e| e.notes.len());
            assert_eq!(got, notes(n), "{what} at {n}");
        });
    }
}

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

/// A power returned through n arrows and passed where a function n arrows deep is expected is
/// checked by one call per arrow (`needs_hold` in crates/zedc-check/src/check/walk.rs),
/// accepted at `f64` and rejected once at `int`, in linear time; `k * k`, which has no need,
/// is the control. Small instance:
/// `held_functions::a_power_returned_through_a_few_lambdas_is_checked_at_the_expected_type`.
#[test]
fn a_power_returned_n_deep_is_checked_in_linear_time() {
    for (body, c, errors) in [
        ("k * k", "f64", 0),
        ("2 ^ k", "f64", 0),
        ("2 ^ k", "int", 1),
    ] {
        let what = format!("`{body}` returned through n arrows, expected at {c}");
        let units: BTreeMap<usize, Resolved> = [200, scaling::FACTOR * 200]
            .into_iter()
            .map(|n| (n, Resolved::new(&returned_by_lambdas(n, c, body))))
            .collect();
        scaling::check_order(&what, 200, 1, |n| {
            let info = units[&n].check();
            assert_eq!(info.errors.len(), errors, "{what} at {n}");
        });
    }
}

/// `n` functions `r1` … `rn`, each returning the one before (`r{i}(x: int) = r{i-1}`), with
/// no call. The type of `ri` is `i` arrows deep, but each is the type of `r{i-1}` under one
/// more arrow, so held as shared parts the whole chain is linear in `n`. Measured on
/// 2026-11-14: sizes 200 and 1600 took 323202172 and 18840234371 instructions, 58.3 times
/// the work (limit 10.50). The same `n` arrows written as nested lambdas in one function
/// (`held_functions::returned_by_lambdas`) check in 7.85 times the work, so the cost is in
/// the chain of named definitions, not in the depth of the types. Cause (traced): each `ri`
/// still holds `w`'s class variable at its bottom, so the checker's last pass named the
/// variables of each by walking it whole and rebuilt it whole twice (`Ck::finished`). Now each
/// signature named keeps the order of its variables, which a later one holding it reads, and
/// the rebuilds share what they made of a function held by several (`ty::Renamings`): 7.86
/// times the work (FAIL-returned-chain-quadratic).
#[test]
fn a_chain_of_functions_returning_the_one_before_is_checked_in_linear_time() {
    let chain = |n: usize| {
        let mut text = "w(positional k) = k * k;\nr1(x: int) = w;\n".to_string();
        text.extend((2..=n).map(|i| format!("r{i}(x: int) = r{};\n", i - 1)));
        text
    };
    let what = "a chain of n functions, each returning the one before";
    let units: BTreeMap<usize, Resolved> = [200, scaling::FACTOR * 200]
        .into_iter()
        .map(|n| (n, Resolved::new(&chain(n))))
        .collect();
    scaling::check_order(what, 200, 1, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{what} at {n}");
    });
}

/// A type that holds one part twice at each of `d` levels, `t{i} = (t{i-1}, t{i-1})`, or
/// `u{i} = {u{i-1}}` (a function from `u{i-1}`'s type to itself), is `2^d` long written as a
/// tree. One error on `t{d} + 1` names it; each part written more than once is declared once
/// as `type Part<k> = …` under the message and named where it stands (`Shared` in
/// crates/zedc-types/src/ty.rs), so the message is `O(d)` bytes and the check `O(d)` work:
/// `T(8d)/T(d)` under the scaling limit in instructions and in bytes allocated, and under 9 in
/// bytes of message text, a count linear by construction ([`scaling::hold_linear`]). Before,
/// each part was written in full at each place, `2^d` times for the innermost
/// (FAIL-nested-display-headline-type-growth: a set display nested 16 deep gave messages of
/// 2165352 bytes).
#[test]
fn a_part_held_twice_at_each_level_gives_a_message_of_linear_length() {
    let tuples = |d: usize| {
        let mut text = "scale(positional x) = x * int(2);\nt1 = (scale, scale);\n".to_string();
        text.extend((2..=d).map(|i| format!("t{i} = (t{0}, t{0});\n", i - 1)));
        text + &format!("z = t{d} + 1;\n")
    };
    let sets = |d: usize| {
        let mut text = "u1 = {1};\n".to_string();
        text.extend((2..=d).map(|i| format!("u{i} = {{u{}}};\n", i - 1)));
        text + &format!("z = u{d} + 1;\n")
    };
    for (what, make) in [
        (
            "n tuples, each holding the one before twice",
            &tuples as &dyn Fn(usize) -> String,
        ),
        (
            "n sets, each holding the one before as key and value",
            &sets,
        ),
    ] {
        let units: BTreeMap<usize, Resolved> = [50, scaling::FACTOR * 50]
            .into_iter()
            .map(|n| (n, Resolved::new(&make(n))))
            .collect();
        let bytes = |n: usize| -> usize {
            let info = units[&n].check();
            assert_eq!(info.errors.len(), 1, "{what} at {n}");
            info.errors
                .iter()
                .map(|e| e.message.len() + e.menu.len())
                .sum()
        };
        let (small, large) = (bytes(50), bytes(scaling::FACTOR * 50));
        scaling::hold_linear(what, "message bytes", small as u64, large as u64);
        scaling::check_order(what, 50, 1, |n| {
            bytes(n);
        });
    }
}

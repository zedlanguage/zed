//! Names in a remap (DESIGN.md sec:remap_law): the `as` binders name the source's levels and
//! its value in the keys of the `into` levels, and nowhere else; the source and each `><`
//! operator are read outside them. An `into` without `as`, which binds by level name, waits
//! for the level names of step L7.1b and is refused naming that.

use zedc::ast::unit;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve_text;

/// The errors of the unit `text` from resolution, each as `message [text]` with its notes
/// after it as `; note [text]`.
fn resolved(text: &str) -> Vec<String> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    let errors = resolve_text(&stmts, Some(text)).err().unwrap_or_default();
    errors
        .iter()
        .map(|e| {
            let mut out = format!("{} [{}]", e.message, &text[e.span.start..e.span.end]);
            for n in &e.notes {
                out += &format!("; {} [{}]", n.text, &text[n.span.start..n.span.end]);
            }
            out
        })
        .collect()
}

#[test]
fn the_binders_name_the_levels_in_the_keys() {
    assert_eq!(
        resolved("m = 1;\nx = m as (k1 -> k2 -> v) into (k2 -> (k1, v) -> v);\n"),
        Vec::<String>::new()
    );
    assert_eq!(
        resolved("m = 1;\nx = m as (k -> v) into (c -> v);\n"),
        ["`c` is not defined. [c]"]
    );
}

#[test]
fn the_binders_do_not_reach_past_the_remap() {
    let es = resolved("m = 1;\nx = m as (k -> v) into (v -> k);\ny = k;\n");
    assert_eq!(es.len(), 1, "{es:?}");
    assert!(es[0].starts_with("`k` is not defined."), "{es:?}");
    // `as` alone binds its names for no key: they are not in scope after it either.
    let es = resolved("m = 1;\nx = m as (r -> v);\ny = v;\n");
    assert_eq!(es.len(), 1, "{es:?}");
    assert!(es[0].starts_with("`v` is not defined."), "{es:?}");
}

#[test]
fn the_source_and_the_reduction_operator_are_read_outside_the_binders() {
    // The source names an outer `m`, not the binder `m`.
    assert_eq!(
        resolved("m = 1;\nx = m as (m -> v) into (v -> m);\n"),
        Vec::<String>::new()
    );
    let es = resolved("m = 1;\nx = q as (k -> v);\n");
    assert!(es[0].starts_with("`q` is not defined."), "{es:?}");
    // `op` is no binder, and the binder `k` is not in scope at the `><`. A fold by a function
    // waits for a later step, and is refused naming that.
    let es = resolved("m = 1;\nx = m as (a -> k -> v) into (a >< k -> v);\n");
    assert_eq!(es.len(), 2, "{es:?}");
    assert!(
        es[0].starts_with("a reduction `><` by a function is part of"),
        "{es:?}"
    );
    assert!(es[1].starts_with("`k` is not defined. [k]"), "{es:?}");
    let es = resolved(
        "m = 1;\nop(a: int, b: int) = a + b;\nx = m as (a -> k -> v) into (a >< op -> v);\n",
    );
    assert_eq!(es.len(), 1, "{es:?}");
    assert!(
        es[0].starts_with("a reduction `><` by a function is part of"),
        "{es:?}"
    );
}

#[test]
fn a_binder_naming_a_type_is_rejected() {
    // Step L8.2a: the row "Binder naming a type" at the binders of a remap pattern.
    let es = resolved("m = 1;\nx = m as (int -> v) into (v -> int);\n");
    assert!(
        es.iter()
            .any(|e| e.starts_with("the pattern binder `int` names the type `int`")),
        "{es:?}"
    );
}

#[test]
fn a_binder_bound_twice_in_one_pattern_is_rejected() {
    let es = resolved("m = 1;\nx = m as (k -> k -> v) into (k -> v);\n");
    assert!(
        es.iter()
            .any(|e| e.starts_with("`k` is already bound in this scope")),
        "{es:?}"
    );
}

#[test]
fn into_without_as_waits_for_level_names() {
    let es = resolved("m = 1;\nx = m into (k -> v);\n");
    assert_eq!(es.len(), 1, "{es:?}");
    assert!(
        es[0].starts_with(
            "a remap `into` that names the source's levels by their level names is part of the \
             Zed language but is not supported by this version of zedc."
        ),
        "{es:?}"
    );
    assert!(
        es[0].contains("; repair: name the levels and the value with `as` before `into`"),
        "{es:?}"
    );
}

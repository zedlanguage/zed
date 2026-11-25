//! `x.tag(#a)` (step L4.1, plan row TAG-run; DESIGN.md sec:order, "`tag` adjoins the atom as
//! an outer key level"): the family `{#a -> x}`, read by its keys, nested, and refused for any
//! argument list other than one atom written by position. A loose atom passes through it, as
//! through every member call.

use crate::source::{prints, rejected, same};

#[test]
fn tag_adjoins_the_atom_as_an_outer_key_level() {
    let src = "x = [1, 2].tag(#left);\nwant = { #left -> [1, 2] };\n";
    same(src, "x", "want");
}

#[test]
fn tags_nest_outermost_last() {
    let src = "x = [1].tag(#a).tag(#b);\nwant = { #b -> { #a -> [1] } };\n";
    same(src, "x", "want");
}

#[test]
fn a_scalar_and_a_map_are_tagged_alike() {
    let src = "s = 5;\nx = s.tag(#a);\nwantX = { #a -> 5 };\n\
               m = { \"k\" -> 1 };\ny = m.tag(#b);\nwantY = { #b -> { \"k\" -> 1 } };\n";
    same(src, "x", "wantX");
    same(src, "y", "wantY");
}

// The tests that read a tagged family by its atom key, `x[#a]`, are parked in
// wt/failing-tests/KERNEL-atom-key-read.rs: the machines give an atom key back unchanged.

#[test]
fn a_loose_atom_passes_through_tag() {
    // `.first` of a family that may be empty is `#none` there (DESIGN.md sec:type_language,
    // the selection row), a loose atom: it is not tagged, and the `else` after the call, which
    // names the atom it takes, handles it.
    let src = "xs = [10, 20];\n\
               hit = xs.where(v -> v > 15).first.tag(#a) else #none -> 0;\n\
               wantHit = { #a -> 20 };\n\
               miss = xs.where(v -> v > 100).first.tag(#a) else #none -> 0;\n";
    same(src, "hit", "wantHit");
    prints(src, "miss", "0");
}

#[test]
fn tag_takes_only_an_atom_written_by_position() {
    for call in [
        "[1].tag(1)",
        "[1].tag(\"a\")",
        "[1].tag()",
        "[1].tag(#a, #b)",
        "[1].tag(key: #a)",
    ] {
        let src = format!("x = {call};\n");
        rejected(&src, &["`tag` takes one atom, written by position"]);
    }
}

#[test]
fn a_name_is_not_a_tag() {
    // The atom is read where it is written (a bare atom bound to a name would be a value that
    // is always a loose atom, refused on its own): a name is refused, with the repair that
    // writes the atom of the name's spelling. The rendered diagnostic holds the repair, a note.
    let src = "k = \"a\";\nx = [1].tag(k);\n";
    let out = zed_tests::step_helpers::l01_29_diagnostics::rejected(src);
    assert!(
        out.contains("`tag` takes one atom, written by position, as `[1].tag(#a)`"),
        "{out}"
    );
    assert!(out.contains("repair: write `[1].tag(#k)`"), "{out}");
    // No atom can be read from a string, so it has the headline's form only.
    let out = zed_tests::step_helpers::l01_29_diagnostics::rejected("x = [1].tag(\"a\");\n");
    assert!(!out.contains("repair:"), "{out}");
}

//! `x.tag(#a)` (step L4.1, plan row TAG-run; DESIGN.md sec:order, "`tag` adjoins the atom as
//! an outer key level"): the family `{#a -> x}`, read by its keys, nested, and refused for any
//! argument list other than one atom written by position. A loose atom passes through it, as
//! through every member call.

use crate::source::{prints, rejected, same};
use zed_tests::step_helpers::l01_26_type_resolution::sig;

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

// A read of a family by an atom it takes as a key, `x[#a]`, reads the entry (plan row
// KERNEL-atom-key-read): the checker records the read, and the elaborator writes the kernel's
// `GetAtomKey`, where `Get` gives an atom key back as it passes every atom.

#[test]
fn a_tagged_family_is_read_through_its_new_key() {
    let src = "x = [1, 2].tag(#left);\ny = x[#left][1];\nn = x.count;\n";
    prints(src, "y", "2");
    prints(src, "n", "1");
}

#[test]
fn two_tags_of_one_list_are_told_apart() {
    // The point of `s.tag(#a)` beside `s.tag(#b)` (sec:order): one value under two keys.
    let src = "s = [1, 2];\na = s.tag(#a);\nb = s.tag(#b);\nsame = a == b;\nsa = a[#a] == b[#b];\n";
    prints(src, "same", "false");
    prints(src, "sa", "true");
}

#[test]
fn a_loose_atom_key_the_family_does_not_take_passes_through() {
    // `k` is `10 | 20 | #none`, its ints inside the family's keys; the family takes no atom,
    // so `#none` passes through the read as through every primitive, and the read is `Get`
    // as before.
    let src = "xs = [10, 20];\nm = { 10 -> 5, 20 -> 6 };\n\
               k = xs.where(v -> v > 100).first;\ny = m[k];\n";
    prints(src, "y", "#none");
}

#[test]
fn a_key_that_may_be_an_atom_taken_or_one_passed_is_tested_first() {
    // `k` is `#a | 10 | 20 | #none`, inside the family's keys but for `#none`: the family
    // takes `#a`, read as a key, and passes `#none` through, so the read tests the key at run
    // time.
    let read = |count: &str, above: &str| {
        format!(
            "xs = [10, 20];\nm = {{ #a -> 1, 10 -> 2, 20 -> 3 }};\n\
             k = if xs.count > {count} {{ #a }} else {{ xs.where(v -> v > {above}).first }};\n\
             y = m[k];\n"
        )
    };
    prints(&read("1", "0"), "y", "1");
    prints(&read("5", "15"), "y", "3");
    prints(&read("5", "100"), "y", "#none");
}

#[test]
fn a_key_that_meets_the_keys_passes_the_atoms_it_does_not_take() {
    // `k` is `#a | 10 | 20 | #none`, meeting the family's keys `#a | 3` without lying inside
    // them, so the read gives an entry or `#notFound` (`key_overlaps`, author decision R11),
    // `#a` read as a key; `#none`, which the family does not take, passes through, as the key
    // of an index passes it (DESIGN.md sec:failure, "Where a loose atom stops").
    let read = |count: &str, above: &str| {
        format!(
            "xs = [10, 20];\nm = {{ #a -> 1, 3 -> 2 }};\n\
             k = if xs.count > {count} {{ #a }} else {{ xs.where(v -> v > {above}).first }};\n\
             y = m[k];\n"
        )
    };
    prints(&read("1", "0"), "y", "1");
    prints(&read("5", "0"), "y", "#notFound");
    prints(&read("5", "100"), "y", "#none");
    // The check's type holds the atom passed, beside the entries and the miss.
    let src = read("5", "100") + "g() = m[k];\n";
    let found = sig(&src, "g");
    let mut parts: Vec<&str> = found.trim_start_matches("() -> ").split(" | ").collect();
    parts.sort_unstable();
    assert_eq!(parts, ["#none", "#notFound", "1", "2"], "{found}");
}

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

//! Item LOOKUP-oob: a read that misses at a level whose keys are one integer interval, every key
//! present, is `#outOfBounds`, and a read that misses at any other level is `#notFound`
//! (DESIGN.md sec:type_language, the `m[k]` row). At L1 such levels are a tuple's positions,
//! the lines of a `Lines` input and the arguments of a `CommandLine` input. The atom follows
//! the type at the read: the arguments passed where `int ->? String` is wanted are read there
//! as that map is, with `#notFound`, and so is a read in a function whose parameter has no
//! written type, which the evaluator runs one way for every family.

use super::{sig, type_errors};
use zed_tests::step_helpers::l01_19_whole_file_ports::run;

/// A program that reads the line, the argument and the tuple component at the number on its
/// first line, key 0, each read written with the handler of its atom.
const READS: &str = "main(m: MainArgs) {\n  \
     t = (10, 20, 30);\n  \
     i = int(m.stdin[0]) else 0;\n  \
     line = m.stdin[i] else #outOfBounds -> \"no line\" else #ioError -> \"unreadable\";\n  \
     arg = m.args[i] else #outOfBounds -> \"no argument\";\n  \
     next = t[i] + 1 else #outOfBounds -> -1;\n  \
     m.stdout <- \"${line} | ${arg} | ${next}\";\n}\n";

/// What `READS` writes when its first line is `line`, with the arguments `a b`.
fn reads(name: &str, line: &str) -> String {
    let out = run(name, READS, &format!("{line}\nsecond\n"), &["--", "a", "b"]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{line}");
    out.stdout
}

#[test]
fn a_read_inside_the_interval_gives_the_entry() {
    assert_eq!(reads("oob_inside", "0"), "0 | a | 11\n");
    assert_eq!(reads("oob_inside", "1"), "second | b | 21\n");
}

#[test]
fn a_read_outside_the_interval_is_out_of_bounds() {
    // Past the end of the two lines and the two arguments at 2, and of the tuple at 3.
    assert_eq!(reads("oob_outside", "2"), "no line | no argument | 31\n");
    assert_eq!(reads("oob_outside", "3"), "no line | no argument | -1\n");
    // Below the first key of each, which is 0 for all three.
    assert_eq!(reads("oob_outside", "-1"), "no line | no argument | -1\n");
}

#[test]
fn the_read_is_typed_out_of_bounds_and_the_atom_passes_through_plus() {
    assert_eq!(
        sig("next(t: (int, int, int), i: int) = t[i] + 1;", "next"),
        "(t: (int, int, int), i: int) -> int | #outOfBounds"
    );
    // Its handler removes it.
    assert_eq!(
        sig(
            "next(t: (int, int, int), i: int) = t[i] + 1 else #outOfBounds -> 0;",
            "next"
        ),
        "(t: (int, int, int), i: int) -> int"
    );
}

#[test]
fn a_handler_for_not_found_leaves_out_of_bounds_in_the_type() {
    // A program written before the item: its arm names an atom the read cannot hold.
    assert_eq!(
        sig(
            "at(t: (int, int, int), i: int) = t[i] else #notFound -> 0;",
            "at"
        ),
        "(t: (int, int, int), i: int) -> int | #outOfBounds"
    );
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- m.args[0] else #notFound -> \"none\";\n}\n";
    let out = run("oob_old_handler", src, "", &["--", "a"]);
    assert_eq!(out.status, 1);
    assert!(
        out.stderr.contains(
            "a `Lines` port takes a `String` or a family of strings, not String | #outOfBounds"
        ),
        "{}",
        out.stderr
    );
}

#[test]
fn a_map_parameter_and_a_generic_read_keep_not_found() {
    assert_eq!(
        sig("get(m: int ->? String, k: int) = m(k);", "get"),
        "(m: int ->? String, k: int) -> String | #notFound"
    );
    // The arguments passed as an `int ->? String`, and to a function whose parameter has no
    // written type, are read with `#notFound`, at run time too.
    let src = "get(m: int ->? String, k: int) = m(k);\n\
               pick(a, k) = a[k];\n\
               main(m: MainArgs) {\n  \
               i = int(m.stdin[0]) else 0;\n  \
               viaMap = get(m: m.args, k: i) else #notFound -> \"map miss\";\n  \
               viaPick = pick(a: m.args, k: i) else #notFound -> \"generic miss\";\n  \
               m.stdout <- \"${viaMap} | ${viaPick}\";\n}\n";
    let at = |line: &str| {
        let out = run("oob_map_kept", src, &format!("{line}\n"), &["--", "a"]);
        assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{line}");
        out.stdout
    };
    assert_eq!(at("0"), "a | a\n");
    assert_eq!(at("1"), "map miss | generic miss\n");
}

#[test]
fn a_key_outside_every_key_is_rejected() {
    assert_eq!(
        type_errors("sixth(t: (int, int, int)) = t[5];"),
        [
            "(int, int, int) has no component 5: its components are at the positions 0 to 2, and this index is 5. [t[5]]"
        ]
    );
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- m.args[\"x\"] else \"none\";\n}\n";
    let out = run("oob_disjoint", src, "", &["--", "a"]);
    assert_eq!(out.status, 1);
    assert!(
        out.stderr
            .contains("this read can never find its key: the key is `\"x\"`"),
        "{}",
        out.stderr
    );
}

//! FAIL-zir-text-reader-messages (TEST-complete-zir, author P189). Drop into
//! tests/steps/l01_31_zir/ as a module (`mod fail_reader_messages;` in mod.rs) once the reader
//! in crates/zedc-zir/src/zir/text.rs is fixed.
//!
//! DESIGN.md L1.31: the text form is read back exactly, and a reader error names the line and
//! column and what is wrong. Four places where the reader of the text form says the wrong thing:
//! - `ty_form`'s arity message writes "takes 1 types";
//! - `(\)` is called "not a type form", while `\` is a form that needs one type or more;
//! - a node's region whose results line has no header line is reported as a line "not in the
//!   graph" of the region above it, where `head` has the right message ("region r.0/0 has no
//!   header line"), which only the root region reaches;
//! - whitespace changes a pattern: `#a()` reads as the fields pattern with no fields and
//!   `#a( )` as the bare atom pattern `#a`, which matches other values (crates/zed-kernel
//!   eval.rs `matches`: `#a` only the bare atom, `#a()` an atom with fields).

use zedc::zir::text::{parse, parse_pattern, parse_type};

#[test]
fn the_reader_names_the_real_cause() {
    let ty = |s: &str| parse_type(s).map(|t| t.to_string());
    let cases = [
        (ty("(! int bool)"), Err("column 13: `(! …)` takes 1 type, and has 2".to_string())),
        (ty("(#ok int int)"), Err("column 14: `(#ok …)` takes 1 type, and has 2".to_string())),
        (ty("(\\)"), Err("column 4: `(\\ …)` takes 1 type or more, and has 0".to_string())),
        (
            parse("zir 1\nr region function ()\nr.0 lambda () -> (_)\nr.0/0 results (1)\nr results (r.0^0)\n")
                .map(|_| String::new()),
            Err("line 4: region r.0/0 has no header line".to_string()),
        ),
        (
            parse_pattern("#a( )").map(|p| format!("{p:?}")),
            parse_pattern("#a()").map(|p| format!("{p:?}")),
        ),
    ];
    let wrong: Vec<String> = cases
        .iter()
        .filter(|(got, want)| got != want)
        .map(|(got, want)| format!("got  {got:?}\nwant {want:?}"))
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The neighbors of the four defects: each arity message with one type and with more, `\` with
/// one type, a headerless region reached through a node line and as a second region, and the
/// atom patterns with and without parentheses, spaces and parts.
#[test]
fn neighbors_of_the_reader_messages() {
    let ty = |s: &str| parse_type(s).map(|t| t.to_string());
    let pat = |s: &str| parse_pattern(s).map(|p| format!("{p:?}"));
    let header = |s: &str| parse(s).map(|_| String::new());
    let cases = [
        (
            ty("(!)"),
            Err("column 4: `(! …)` takes 1 type, and has 0".to_string()),
        ),
        (
            ty("(#ok)"),
            Err("column 6: `(#ok …)` takes 1 type, and has 0".to_string()),
        ),
        (
            ty("(-> int)"),
            Err("column 9: `(-> …)` takes 3 types, and has 1".to_string()),
        ),
        (ty("(\\ int)"), Ok("int".to_string())),
        (ty("(! int)"), parse_type("(! int)").map(|t| t.to_string())),
        (
            header(
                "zir 1\nr region function ()\nr.0 lambda () -> (_)\n\
                 r.0/0.0 prim + (1, 2) -> (int)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n",
            ),
            Err("line 4: region r.0/0 has no header line".to_string()),
        ),
        (
            header(
                "zir 1\nr region function (bool)\n\
                 r.0 match [=true, =false] (r^0) -> (int)\n\
                 r.0/0 region match ()\nr.0/0 results (1)\n\
                 r.0/1 results (2)\nr results (r.0^0)\n",
            ),
            Err("line 6: region r.0/1 has no header line".to_string()),
        ),
        (pat("#a"), Ok("Atom(\"a\", [])".to_string())),
        (pat("#a()"), Ok("Fields(\"a\", [])".to_string())),
        (pat("#a(  )"), Ok("Fields(\"a\", [])".to_string())),
        (pat("#a(_)"), Ok("Atom(\"a\", [Wild])".to_string())),
        (
            pat("#a(k: _)"),
            Ok("Fields(\"a\", [(\"k\", Wild)])".to_string()),
        ),
    ];
    let wrong: Vec<String> = cases
        .iter()
        .filter(|(got, want)| got != want)
        .map(|(got, want)| format!("got  {got:?}\nwant {want:?}"))
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

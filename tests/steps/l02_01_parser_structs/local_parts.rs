//! `with` lists and local part declarations (DESIGN.md, the `with` row of the operator table,
//! SPEC-with-list and SPEC-with-local-part). Several facets are one braced list, which may mix
//! field updates; a bare comma list is no `with`, so `f(x with units("m"), round(y))` passes
//! two arguments. In a type, `with type P = U` names a part that the type before `with` and
//! the later parts see, and nothing else; a `for` after it binds its variables in the parts.

use zed_tests::step_helpers::l02_01_parser_structs::{check_exprs, check_refused};
use zedc::lex::lex;
use zedc::parse::{TOP, parse};

use super::{check, fmt};

#[test]
fn a_local_part_nests_around_the_type_it_names_a_part_of() {
    check(&[
        (
            "type Pair2 = A -> (Part1, Part1) with type Part1 = (A, A) for A in int | rat;",
            "(type Pair2 (for (local (-> (A) (tuple Part1 Part1)) (Part1 (tuple A A))) (A (| int rat))))",
        ),
        (
            "type Q = (Part1, Part2) with { type Part1 = int, type Part2 = (Part1, Part1) };",
            "(type Q (local (tuple Part1 Part2) (Part1 int) (Part2 (tuple Part1 Part1))))",
        ),
        // Two `with` clauses nest: the second is around the first, and its part does not see
        // the first's.
        (
            "type R = Part1 with type Part1 = Part2 with type Part2 = int;",
            "(type R (local (local Part1 (Part1 Part2)) (Part2 int)))",
        ),
    ]);
}

#[test]
fn local_parts_format_to_one_layout() {
    for (text, want) in [
        (
            "type Pair2=A->(Part1,Part1) with type Part1=(A,A) for A in int|rat;",
            "type Pair2 = A -> (Part1, Part1) with type Part1 = (A, A) for A in int | rat;\n",
        ),
        (
            "type Q=(Part1,Part2) with{type Part1=int,type Part2=(Part1,Part1),};",
            "type Q = (Part1, Part2) with { type Part1 = int, type Part2 = (Part1, Part1) };\n",
        ),
        // A list of one part is written bare.
        (
            "type S = Part1 with { type Part1 = int };",
            "type S = Part1 with type Part1 = int;\n",
        ),
        (
            "type R = Part1 with type Part1 = Part2 with type Part2 = int;",
            "type R = Part1 with type Part1 = Part2 with type Part2 = int;\n",
        ),
        // An arrow before `with` needs no parentheses; local parts as an arrow's result or as
        // a part's type do, and so does a bounds clause as a part's type.
        (
            "type K = (int -> Part1) with type Part1 = int;",
            "type K = int -> Part1 with type Part1 = int;\n",
        ),
        (
            "type F = int -> (Part1 with type Part1 = int);",
            "type F = int -> (Part1 with type Part1 = int);\n",
        ),
        (
            "type G = Part1 with type Part1 = (Part2 with type Part2 = int);",
            "type G = Part1 with type Part1 = (Part2 with type Part2 = int);\n",
        ),
        (
            "type H = Part1 with type Part1 = ((T) -> T for T in int | rat);",
            "type H = Part1 with type Part1 = ((T) -> T for T in int | rat);\n",
        ),
        // A tuple's item followed by a comma is not parenthesized: the comma ends the part.
        (
            "type L = ((Part1 with type Part1 = int), int);",
            "type L = (Part1 with type Part1 = int, int);\n",
        ),
    ] {
        assert_eq!(fmt(text), want, "{text}");
    }
}

#[test]
fn name_resolution_refuses_a_local_part_and_reads_its_scope() {
    let part = zed_tests::not_yet!("a local part declaration");
    let decl = zed_tests::not_yet!("a type declaration");
    let at = |text: &str| format!("{part} [{text}]");
    let whole = |text: &str| format!("{decl} [{text}]");
    let cases: Vec<(&str, Vec<String>)> = vec![
        // The type before `with`, a later part and the bound variables see a part.
        {
            let t = "type T = A -> Part2 with { type Part1 = (A, A), type Part2 = (Part1, Part1) } \
                     for A in int | rat;";
            (
                t,
                vec![
                    whole(t),
                    at("A -> Part2 with { type Part1 = (A, A), type Part2 = (Part1, Part1) }"),
                ],
            )
        },
        // An earlier part, the part's own type and the text outside do not.
        {
            let t = "type T = Part1 with { type Part1 = Part2, type Part2 = int };";
            (
                t,
                vec![
                    whole(t),
                    at("Part1 with { type Part1 = Part2, type Part2 = int }"),
                    "The type `Part2` is not defined. [Part2]".to_string(),
                ],
            )
        },
        {
            let t = "type T = Part1 with type Part1 = (Part1, int);";
            (
                t,
                vec![
                    whole(t),
                    at("Part1 with type Part1 = (Part1, int)"),
                    "The type `Part1` is not defined. [Part1]".to_string(),
                ],
            )
        },
        {
            let t = "type T = (Part1 with type Part1 = int, Part1);";
            (
                t,
                vec![
                    whole(t),
                    at("Part1 with type Part1 = int"),
                    "The type `Part1` is not defined. [Part1]".to_string(),
                ],
            )
        },
        // A part shadows a type of its name from outside; two parts of one name in one list
        // are a rebinding.
        {
            let t = "type Part1 = int;\ntype T = Part1 with type Part1 = rat;";
            (
                t,
                vec![
                    whole("type Part1 = int;"),
                    whole("type T = Part1 with type Part1 = rat;"),
                    at("Part1 with type Part1 = rat"),
                ],
            )
        },
        {
            let t = "type T = Part1 with { type Part1 = int, type Part1 = rat };";
            (
                t,
                vec![
                    whole(t),
                    at("Part1 with { type Part1 = int, type Part1 = rat }"),
                    "`Part1` is already bound in this scope [Part1]".to_string(),
                ],
            )
        },
    ];
    let cases: Vec<(&str, Vec<&str>)> = (cases.iter())
        .map(|(t, want)| (*t, want.iter().map(String::as_str).collect()))
        .collect();
    let cases: Vec<(&str, &[&str])> = cases.iter().map(|(t, w)| (*t, &w[..])).collect();
    check_refused(&cases);
}

#[test]
fn a_braced_list_of_facets_is_the_facet_attachment_of_its_layer() {
    check_exprs(&[
        (
            "v with { units(\"km/s\"), target(#gpu) }",
            concat!(
                "error: ",
                zed_tests::not_yet!(
                    "the facet attachment `with { units(\"km/s\"), target(#gpu) }`"
                )
            ),
        ),
        // Updates and facets mix in one list.
        (
            "p with { x = 1, units(\"m\") }",
            concat!(
                "error: ",
                zed_tests::not_yet!("the facet attachment `with { x = 1, units(\"m\") }`")
            ),
        ),
        // A facet ends at its call: the comma after it separates two arguments.
        (
            "f(x with units(\"m\"), round(y))",
            concat!(
                "error: ",
                zed_tests::not_yet!("the facet attachment `with units(\"m\")`")
            ),
        ),
    ]);
    check(&[(
        "type S = int with { units(\"m\"), type Part1 = int };",
        concat!(
            "error: ",
            zed_tests::not_yet!("the facet `with { units(\"m\"), type Part1 = int }`")
        ),
    )]);
}

/// The texts of the kids of the outermost node named `rule`, the one that begins first, in the
/// parse tree of the expression `text`.
fn kids_of(text: &str, rule: &str) -> Vec<String> {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Expr", TOP).unwrap();
    let n = (0..tree.nodes.len())
        .filter(|&n| tree.name(n) == rule)
        .min_by_key(|&n| tree.nodes[n].start)
        .unwrap_or_else(|| panic!("no {rule} in {text}"));
    (tree.nodes[n].kids.iter())
        .map(|&k| {
            let (s, e) = (tree.nodes[k].start, tree.nodes[k].end);
            text[tokens[s].span.start..tokens[e - 1].span.end].to_string()
        })
        .collect()
}

#[test]
fn a_facet_in_an_argument_list_ends_before_the_comma() {
    assert_eq!(
        kids_of("f(x with units(\"m\"), round(y))", "Args"),
        ["x with units(\"m\")", "round(y)"]
    );
    assert_eq!(
        kids_of("f(x with { units(\"m\"), target(#gpu) }, round(y))", "Args"),
        ["x with { units(\"m\"), target(#gpu) }", "round(y)"]
    );
}

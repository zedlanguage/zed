//! Small cases of the trivial-model report (DESIGN.md sec:theories item 3), one rule or one
//! form each, with expected results from DESIGN.md or worked out by hand from it: how a law is
//! read, how fields are grouped, how each choice is written, and each form the report's text
//! takes. The case list is COMPLETENESS.md.

use super::brute::{check, expand, models};
use super::trivial::{End, Mode, Theory, choices, in_forest_fragment, render, report, show, split};

/// Whether law 0 of `t` holds on one value and on two values, read off both reports.
fn verdicts(t: &Theory) -> (bool, bool) {
    let (short, full) = (report(t, Mode::Default), report(t, Mode::Exhaustive));
    assert_eq!(short.one_value_fails, full.one_value_fails);
    assert_eq!(short.closed_fail, full.closed_fail);
    (
        short.one_value_fails.is_none(),
        short.closed_fail.is_empty(),
    )
}

/// Laws that name no field, over binders only, so each is checked once (DESIGN: "A law that
/// names no field is checked once"). Each expected pair is worked out by hand: on one value
/// every `==` holds and every `!=` fails; on two values the law must hold at every binding of
/// its binders to `#a` and `#b`. `!` is moved onto the comparisons and `(a).implies(b)` is
/// `!a || b`, and a method call applies to what precedes it, so `(p).implies(q).implies(r)` is
/// `((p).implies(q)).implies(r)`. `&&` binds tighter than `||`, as in DESIGN's
/// `(a && b) || (c && d)`.
#[test]
fn each_form_of_a_law_is_read_as_written() {
    let cases: &[(&str, &str, (bool, bool))] = &[
        ("a b", "a == b", (true, false)),
        ("a b", "a != b", (false, false)),
        ("a", "a == a", (true, true)),
        ("a", "a != a", (false, false)),
        ("a b", "a == b || a != b", (true, true)),
        ("a b", "a == b && a != b", (false, false)),
        ("a b", "!(a == b)", (false, false)),
        ("a b", "!(a != b)", (true, false)),
        ("a b", "!!(a == b)", (true, false)),
        ("a b", "((a == b))", (true, false)),
        ("a b", "!(a == b && a != b)", (true, true)),
        ("a b", "!(a == b || a != b)", (false, false)),
        // `&&` before `||`: `a == a || (a != a && a != a)` holds; read the other way it would
        // be `(a == a || a != a) && a != a`, which fails.
        ("a", "a == a || a != a && a != a", (true, true)),
        ("a", "(a == a || a != a) && a != a", (false, false)),
        ("a b", "(a == b).implies(a != b)", (false, false)),
        ("a b", "(a != b).implies(a == b)", (true, false)),
        ("a b", "(a == b).implies(a == b)", (true, true)),
        // Read from the left: at a != b, `(a == b).implies(a != b)` holds and `a == b` fails.
        // Read from the right it would hold at every binding.
        (
            "a b",
            "(a == b).implies(a != b).implies(a == b)",
            (true, false),
        ),
        (
            "a b",
            "(a == b).implies((a != b).implies(a == b))",
            (true, true),
        ),
        ("a b", "!((a == b).implies(a != b))", (true, false)),
        // On two values, two of three binders are equal.
        ("a b c", "a == b || b == c || a == c", (true, true)),
        ("a b c", "a != b || b != c", (false, false)),
        ("a b c", "(a == b && b == c).implies(a == c)", (true, true)),
        ("a, b", "a == b", (true, false)),
    ];
    for &(binders, body, want) in cases {
        let mut t = Theory::new("Closed");
        t.law("l", binders, body);
        assert!(!t.laws[0].refused(), "{body}");
        assert_eq!(verdicts(&t), want, "law l({binders}) = {body}");
        // A law that names no field leaves no group and no free field.
        let r = report(&t, Mode::Default);
        assert!(r.groups.is_empty() && r.free.is_empty(), "{body}");
    }
}

/// The same reading where the law names fields: each law's models on two values, by brute
/// force over the choices, against the models counted by hand.
#[test]
fn each_form_of_a_law_over_fields_is_read_as_written() {
    // One field `c` of no arguments: 2 choices. One field `f` of one argument: 3 choices
    // (#a, #b, x).
    let cases: &[(&str, &str, &str, usize)] = &[
        ("c", "", "c == c", 2),
        ("c", "x", "c == x", 0),
        ("c", "x", "c != x", 0),
        ("f/1", "x", "f(x) == x", 1),
        ("f/1", "x", "f(x) != x", 0),
        ("f/1", "x", "!(f(x) == x)", 0),
        ("f/1", "x y", "f(x) == f(y)", 2),
        ("f/1", "x y", "!(f(x) != f(y))", 2),
        ("f/1", "x", "f(f(x)) == f(x)", 3),
        // f(x) == x or f(x) is constant: every choice.
        ("f/1", "x y", "f(x) == x || f(x) == f(y)", 3),
        // f(x) == x implies f(x) == f(y): fails only for the identity.
        ("f/1", "x y", "(f(x) == x).implies(f(x) == f(y))", 2),
        // `!` applies to the whole call, `!((f(x) == x).implies(f(x) == f(y)))`: f is the
        // identity and f(x) != f(y) at x == y, so none. DESIGN sec:lexical, ladder row 3:
        // "`!x.isNaN` is `!(x.isNaN)`".
        ("f/1", "x y", "!(f(x) == x).implies(f(x) == f(y))", 0),
        ("f/1", "x y", "(!(f(x) == x)).implies(f(x) == f(y))", 3),
        ("f/1", "x", "f(x) == x && f(f(x)) == x", 1),
        // Two fields of no arguments, different: (#a, #b) and (#b, #a).
        ("c d", "", "c != d", 2),
        ("c d", "", "!(c == d)", 2),
        ("c d", "", "c == d", 2),
        // A field of two arguments: #a, #b, x, y. `p(x, y) == p(y, x)` holds for the constants.
        ("p/2", "x y", "p(x, y) == p(y, x)", 2),
        ("p/2", "x", "p(x, x) == x", 2),
        ("p/2", "x y", "p(x, p(x, y)) == p(x, y)", 4),
        // A field of three arguments: #a, #b, x, y, z.
        ("q/3", "x y z", "q(x, y, z) == q(y, x, z)", 3),
    ];
    for &(fields, binders, body, want) in cases {
        let mut t = Theory::new("Fields");
        for f in fields.split(' ') {
            let (name, arity) = f.split_once('/').unwrap_or((f, "0"));
            t.field(name, arity.parse().expect("an arity"));
        }
        t.law("l", binders, body);
        let got = models(&t);
        assert_eq!(
            got.len(),
            want,
            "fields {fields}, law l({binders}) = {body}"
        );
        let full = report(&t, Mode::Exhaustive);
        let mut got = got;
        got.sort();
        assert_eq!(expand(&t, &full), got, "{body}");
    }
}

/// DESIGN: "On one value every equation holds and every `!=` fails, so the model on one value,
/// every field returning it, is checked once per law." The report names the first law, in
/// declaration order, that fails there.
#[test]
fn the_model_on_one_value_names_the_first_law_that_fails() {
    let mut t = Theory::new("OneValue");
    t.field("f", 1)
        .law("holds", "x", "f(x) == f(x)")
        .law("first", "x", "f(x) != x")
        .law("second", "x y", "x != y");
    let r = report(&t, Mode::Default);
    assert_eq!(r.one_value_fails, Some(1));
    let text = render(&t, &r);
    assert!(
        text.contains(
            "  on one value, #a: law first (f(x) != x) does not hold, since on one value every \
             two values are equal.\n"
        ),
        "{text}"
    );
    // Every law holding on one value.
    let mut t = Theory::new("Holds");
    t.field("f", 1).law("idem", "x", "f(f(x)) == f(x)");
    let text = render(&t, &report(&t, Mode::Default));
    assert!(
        text.contains("  on one value, #a, with every field returning #a: every law holds.\n"),
        "{text}"
    );
}

/// DESIGN: "On two values, `#a | #b`, a field of n arguments has n + 2 choices, the two
/// constants and the n projections, and a field of no arguments has two." Each choice is
/// written as the report's examples write it: `#a`, `(x -> x)`, `((x, y) -> #a)`.
#[test]
fn each_choice_of_a_field_is_written_as_a_function() {
    let mut t = Theory::new("Shapes");
    t.field("c", 0)
        .field("f", 1)
        .field("g", 2)
        .field("h", 3)
        .field("k", 4);
    let all = |f: usize| -> Vec<String> {
        (0..choices(t.fields[f].arity))
            .map(|c| show(&t, f, c))
            .collect()
    };
    assert_eq!(all(0), ["#a", "#b"]);
    assert_eq!(all(1), ["(x -> #a)", "(x -> #b)", "(x -> x)"]);
    assert_eq!(
        all(2),
        [
            "((x, y) -> #a)",
            "((x, y) -> #b)",
            "((x, y) -> x)",
            "((x, y) -> y)"
        ]
    );
    assert_eq!(
        all(3),
        [
            "((x, y, z) -> #a)",
            "((x, y, z) -> #b)",
            "((x, y, z) -> x)",
            "((x, y, z) -> y)",
            "((x, y, z) -> z)"
        ]
    );
    // Four arguments: six choices, each written once. DESIGN names no parameters past three.
    let four = all(4);
    assert_eq!(four.len(), 6);
    let mut distinct = four.clone();
    distinct.sort();
    distinct.dedup();
    assert_eq!(distinct.len(), 6, "{four:?}");
}

/// DESIGN: "Two fields are linked when one law names both, and the report treats each
/// connected group of linked fields apart"; "A field that no law names is printed as free";
/// "A law that names no field is checked once"; "Fields are taken in the order the theory
/// declares them". A group is linked through a chain of laws, whatever order its fields are
/// declared in.
#[test]
fn fields_are_grouped_by_the_laws_that_name_them() {
    let mut t = Theory::new("Groups");
    t.field("f", 1)
        .field("g", 1)
        .field("free", 2)
        .field("h", 1)
        .field("k", 0)
        .law("hk", "x", "h(x) == k")
        .law("onlyG", "x", "g(g(x)) == g(x)")
        .law("closed", "x y", "x == x || x == y")
        .law("fh", "x", "f(x) == h(x)");
    let s = split(&t);
    // `f`, `h` and `k`, linked through `h`; then `g`; `free`; and the closed law.
    assert_eq!(s.groups, [vec![0, 3, 4], vec![1]]);
    assert_eq!(s.group_laws, [vec![0, 3], vec![1]]);
    assert_eq!(s.free, [2]);
    assert_eq!(s.closed, [2]);
    let r = report(&t, Mode::Exhaustive);
    let text = render(&t, &r);
    assert!(
        text.contains("    f, h, k, linked by laws hk, fh: "),
        "the group's fields and laws in declaration order\n{text}"
    );
    assert!(text.contains("    g, linked by law onlyG: "), "{text}");
    assert!(
        text.contains("    free is named by no law: it may be any constant or any projection.\n"),
        "{text}"
    );
    // The models are the product of the groups' models and the free field's four choices.
    let mut want = models(&t);
    want.sort();
    assert_eq!(expand(&t, &r), want);
}

/// DESIGN: "the trivial models are the product of the groups' models, and the report prints
/// the count as that product", as `2^20` for twenty free fields of no arguments. Each factor
/// is printed once with its power, and a factor 1 is left out.
#[test]
fn the_count_is_printed_as_a_product() {
    let count = |t: &Theory, mode: Mode| -> Option<String> {
        render(t, &report(t, mode))
            .lines()
            .find_map(|l| l.strip_prefix("  models on two values: ").map(String::from))
    };
    // Free fields of 0, 0, 1 and 2 arguments: 2 * 2 * 3 * 4.
    let mut t = Theory::new("Free");
    t.field("a", 0).field("b", 0).field("f", 1).field("g", 2);
    assert_eq!(count(&t, Mode::Default).as_deref(), Some("2^2 * 3 * 4."));
    // One free field.
    let mut t = Theory::new("One");
    t.field("f", 1);
    assert_eq!(count(&t, Mode::Default).as_deref(), Some("3."));
    // A group of exactly one model and a free field: the 1 is left out.
    let mut t = Theory::new("Codec");
    t.field("compress", 1)
        .field("decompress", 1)
        .field("extra", 0)
        .law("roundTrip", "x", "decompress(compress(x)) == x");
    assert_eq!(count(&t, Mode::Default).as_deref(), Some("2."));
    // Every group of exactly one model, no free field: 1.
    let mut t = Theory::new("Ids");
    t.field("f", 1)
        .field("g", 1)
        .law("fId", "x", "f(x) == x")
        .law("gId", "x", "g(x) == x");
    assert_eq!(count(&t, Mode::Default).as_deref(), Some("1."));
    // No field and no law: the one empty model.
    let t = Theory::new("Empty");
    assert_eq!(count(&t, Mode::Default).as_deref(), Some("1."));
    // Two groups of four models each (two semigroups), listed in full under `@exhaustive`.
    let mut t = Theory::new("TwoSemigroups");
    t.field("mul", 2).field("add", 2).law(
        "mulAssoc",
        "a b c",
        "mul(mul(a, b), c) == mul(a, mul(b, c))",
    );
    t.law(
        "addAssoc",
        "a b c",
        "add(add(a, b), c) == add(a, add(b, c))",
    );
    assert_eq!(count(&t, Mode::Exhaustive).as_deref(), Some("4^2."));
    // The default report lists two of each and prints no count.
    assert_eq!(count(&t, Mode::Default), None);
    // A group with no model: 0, whatever the other factors.
    let mut t = Theory::new("None");
    t.field("c", 0).field("f", 1).law("never", "x", "c != x");
    assert_eq!(count(&t, Mode::Default).as_deref(), Some("0."));
}

/// DESIGN: for each group the report prints "*no model*, with the law that rules out each
/// choice of one field; *exactly one model*, with it; or *several*, with two of them."
#[test]
fn each_group_prints_no_model_one_model_or_several() {
    // Several: a semigroup has four models on two values; the default report shows two.
    let mut t = Theory::new("Semigroup");
    t.field("mul", 2).law(
        "mulAssoc",
        "a b c",
        "mul(mul(a, b), c) == mul(a, mul(b, c))",
    );
    let r = report(&t, Mode::Default);
    assert!(matches!(r.groups[0].end, End::Several));
    assert_eq!(r.groups[0].models.len(), 2);
    let text = render(&t, &r);
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(
        lines[3], "    mul, linked by law mulAssoc: several models, for example",
        "{text}"
    );
    assert_eq!(lines.len(), 6, "two models and no count\n{text}");
    // Under `@exhaustive`: all four, and the count.
    let full = report(&t, Mode::Exhaustive);
    let text = render(&t, &full);
    assert!(
        text.contains("    mul, linked by law mulAssoc: 4 models,\n"),
        "{text}"
    );
    assert!(text.ends_with("  models on two values: 4.\n"), "{text}");
    // No model, ruled out before any choice: each choice of one field with its law.
    let mut t = Theory::new("NoModel");
    t.field("f", 1).law("swap", "x", "f(x) != x");
    let text = render(&t, &report(&t, Mode::Default));
    assert!(
        text.contains("    f, linked by law swap: no model.\n"),
        "{text}"
    );
    for c in ["(x -> #a)", "(x -> #b)", "(x -> x)"] {
        assert!(
            text.contains(&format!("f cannot be {c}, by law swap: f(x) != x")),
            "{c}\n{text}"
        );
    }
    assert!(text.contains("so no choice is left for f"), "{text}");
    // On one value `f(x) != x` fails, so the closing sentence about the model on one value is
    // left out.
    assert!(!text.contains("So the model on one value"), "{text}");
    assert!(text.ends_with("  models on two values: 0.\n"), "{text}");
}

/// A law that names no field and fails on two values leaves no model, whatever the groups
/// hold; one that holds changes nothing.
#[test]
fn a_law_that_names_no_field_decides_for_every_group() {
    let mut t = Theory::new("Closed");
    t.field("f", 1)
        .law("idem", "x", "f(f(x)) == f(x)")
        .law("allEqual", "a b", "a == b");
    let r = report(&t, Mode::Exhaustive);
    assert_eq!(r.closed_fail, [1]);
    assert!(r.one_value_fails.is_none());
    assert!(expand(&t, &r).is_empty());
    assert!(models(&t).is_empty());
    let text = render(&t, &r);
    assert!(
        text.contains(
            "    law allEqual (a == b) names no field and does not hold, so there is no model.\n"
        ),
        "{text}"
    );
    let mut t = Theory::new("ClosedHolds");
    t.field("f", 1)
        .law("idem", "x", "f(f(x)) == f(x)")
        .law("excluded", "a b", "a == b || a != b");
    let r = report(&t, Mode::Exhaustive);
    assert!(r.closed_fail.is_empty());
    assert_eq!(expand(&t, &r).len(), 3);
}

/// DESIGN: "`@exhaustive` on an interface lists every model of every group and counts the
/// choices that led to no model". On Fano there is no model, and the count of choices that led
/// to no model is printed.
#[test]
fn the_exhaustive_report_counts_its_wrong_turns() {
    let mut t = Theory::new("Fano");
    for i in 1..=7 {
        t.field(&format!("c{i}"), 0);
    }
    let lines = [
        [1, 2, 3],
        [1, 4, 5],
        [1, 6, 7],
        [2, 4, 6],
        [2, 5, 7],
        [3, 4, 7],
        [3, 5, 6],
    ];
    for (k, [a, b, c]) in lines.into_iter().enumerate() {
        t.law(
            &format!("line{}", k + 1),
            "",
            &format!("c{a} != c{b} || c{b} != c{c}"),
        );
    }
    let r = report(&t, Mode::Exhaustive);
    let g = &r.groups[0];
    let text = render(&t, &r);
    assert!(text.contains(": no model.\n"), "{text}");
    assert!(
        text.contains(&format!(
            "      The search made {} choices; {} of them led to no model.\n",
            g.nodes, g.dead_ends
        )),
        "{text}"
    );
    assert!(g.dead_ends > 0);
    assert!(text.ends_with("  models on two values: 0.\n"), "{text}");
}

/// DESIGN: "When every law of the group is an atom or a conjunction of atoms and this graph
/// has no cycle, no choice the search makes leads to no model." The fragment holds an atom
/// written with `!`, a conjunction of atoms, and an atom that names one field twice; it does
/// not hold an `||` of two atoms, or atoms that link two fields twice (a cycle).
#[test]
fn the_forest_fragment_is_atoms_and_conjunctions_without_a_cycle() {
    let theory = |laws: &[(&str, &str)]| {
        let mut t = Theory::new("Forest");
        t.field("f", 1).field("g", 1).field("c", 0);
        for (k, &(binders, body)) in laws.iter().enumerate() {
            t.law(&format!("l{k}"), binders, body);
        }
        t
    };
    let cases: &[(&[(&str, &str)], bool)] = &[
        (&[("x", "f(x) == x")], true),
        (&[("x", "!(f(x) != x)")], true),
        (&[("x", "f(x) == x && g(x) == c")], true),
        (&[("x", "f(f(x)) == f(x)")], true),
        (&[("x", "f(x) == g(x)"), ("x", "g(x) == c")], true),
        (&[("x", "f(x) == x || g(x) == x")], false),
        (&[("x", "f(x) == g(x)"), ("x", "f(g(x)) == x")], false),
        (&[("x", "f(x) == g(x) && g(f(x)) == x")], false),
        (&[], true),
    ];
    for &(laws, want) in cases {
        let t = theory(laws);
        assert_eq!(in_forest_fragment(&t), want, "{laws:?}");
        if want {
            let dead: u64 = report(&t, Mode::Exhaustive)
                .groups
                .iter()
                .map(|g| g.dead_ends)
                .sum();
            assert_eq!(dead, 0, "{laws:?}");
        }
    }
}

/// DESIGN: an atom whose two sides name a common field "is the pairs of paths that end at the
/// same symbol and agree on the common fields". When a choice of a field on one side leaves two
/// or more of its choices ending at one binder, as `q(x, x, …)` does for its first two
/// projections, the walk takes those choices together and walks the other side once under that
/// binder, holding the field to them; the other side then tests the field again. Checked
/// against brute force, in both orders of the other side's arguments.
#[test]
fn a_field_held_to_several_choices_is_tested_again_on_the_other_side() {
    for (binders, body) in [
        ("x y z", "q(x, x, f(y)) == f(q(x, y, z))"),
        ("x y", "q(x, x, f(y)) == f(q(y, x, x))"),
    ] {
        let mut t = Theory::new("Held");
        t.field("q", 3).field("f", 1).law("l", binders, body);
        check(&t);
        let atom = &t.laws[0].clauses()[0][0];
        let (pairs, runs, _) = t
            .shared_atom_size(atom)
            .expect("the sides share `q` and `f`");
        assert!(pairs > 0 && runs > 0, "{body}");
    }
    // Sides that name no common field are split by end symbol instead.
    let mut t = Theory::new("Apart");
    t.field("f", 1).field("g", 1).law("l", "x", "f(x) == g(x)");
    assert_eq!(t.shared_atom_size(&t.laws[0].clauses()[0][0]), None);
}

/// A law the prototype cannot read stops the test that wrote it, with the place it stopped at.
#[test]
#[should_panic(expected = "unexpected '+'")]
fn a_law_with_an_unknown_character_is_not_read() {
    Theory::new("Bad")
        .field("f", 1)
        .law("l", "x", "f(x) + x == x");
}

#[test]
#[should_panic(expected = "expected a name at token 5")]
fn a_law_with_a_missing_operand_is_not_read() {
    Theory::new("Bad").field("f", 1).law("l", "x", "f(x) ==");
}

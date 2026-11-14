//! Completeness (row TEST-complete-staging, author P189): coloring of the forms a definition
//! may take, the constants `mix` computes, the demand a test makes, and the Trick's domains at
//! their bounds and with values of other kinds passed. The case list is COMPLETENESS.md.

use std::collections::BTreeSet;

use zed_kernel::Value;
use zed_kernel::types::Type;
use zedc::stage::{Choice, Domain, Stage, color, passed, split, trick};

use zed_tests::step_helpers::l01_16_elaboration::elab;

use super::{out, staged, term};

fn ints(vs: &[i64]) -> BTreeSet<Value> {
    vs.iter().copied().map(Value::Int).collect()
}

const NONE_PASSED: &str = "no static call passes a value of the domain";

#[test]
fn a_definition_computed_from_build_stage_names_is_build_stage_and_built() {
    // The test of DESIGN.md step L1.40c.
    let src = "debug = false;\nmode = if debug { 1 } else { 2 };\n\
               main(m: MainArgs) {\n  m.stdout <- String(mode);\n}\n";
    let (p, s, report) = staged(src);
    let colors = color(p.unit());
    for name in ["debug", "mode"] {
        assert!(
            colors.contains(&(name.into(), Stage::Build)),
            "{name}: {colors:?}"
        );
    }
    assert!(
        report.built.contains(&"mode".to_string()),
        "{:?}",
        report.built
    );
    assert_eq!(term(&s, "mode"), "2");
    assert_eq!(out(&s, ""), "2\n");
    assert_eq!(out(&s, ""), out(&p, ""));
}

#[test]
fn the_constants_partial_evaluation_computes_are_built_and_write_as_the_program_does() {
    // DESIGN.md sec:staging: a constant is a result of partial evaluation, so a power past
    // every fixed width, a NaN and an infinity are computed by `mix` as any other value.
    let src = "big = 2 ^ 64;\nnan = f64(#NaN);\nninf = -f64(#inf);\n\
               main(m: MainArgs) {\n  \
               m.stdout <- String(big);\n  \
               m.stdout <- String(nan) else \"not a number\";\n  \
               m.stdout <- String(ninf) else \"minus infinity\";\n}\n";
    let (p, s, report) = staged(src);
    for name in ["big", "nan", "ninf"] {
        assert!(
            report.built.contains(&name.to_string()),
            "{name}: {:?}",
            report.built
        );
    }
    assert_eq!(term(&s, "big"), "18446744073709551616");
    assert!(report.left.is_empty(), "{:?}", report.left);
    assert_eq!(out(&s, ""), out(&p, ""));
}

#[test]
fn an_else_whose_value_fails_at_build_is_built_to_its_default() {
    let src = "lookup(positional k: int) = if k > 0 { k } else { #notFound };\n\
               v = lookup(-1) else 5;\nw = lookup(4) else 5;\n\
               main(m: MainArgs) {\n  m.stdout <- String(v + w);\n}\n";
    let (p, s, report) = staged(src);
    assert_eq!(term(&s, "v"), "5");
    assert_eq!(term(&s, "w"), "4");
    assert!(
        report.built.contains(&"v".to_string()),
        "{:?}",
        report.built
    );
    assert_eq!(out(&s, ""), "9\n");
    assert_eq!(out(&s, ""), out(&p, ""));
}

#[test]
fn a_tuple_a_lambda_and_a_cast_are_built() {
    let src = "pair = (1 + 1, \"a\");\ninc = (positional x: int) -> x + 1;\nr = rat(3) / 4;\n\
               main(m: MainArgs) {\n  \
               a, b = pair;\n  \
               m.stdout <- String(inc(a)) ++ b ++ String(r);\n}\n";
    let (p, s, report) = staged(src);
    for name in ["pair", "r"] {
        assert!(
            report.built.contains(&name.to_string()),
            "{name}: {:?}",
            report.built
        );
    }
    assert!(report.left.is_empty(), "{:?}", report.left);
    assert_eq!(out(&s, ""), out(&p, ""));
}

#[test]
fn a_definition_a_test_reads_is_demanded() {
    // DESIGN.md sec:staging: a node is demanded by the residual program or by an obligation
    // such as a test, so a definition only a test reads is not reported unread.
    let src = "k = 3;\ng(positional x: int) = x + k test { 1 -> 4, 2 -> 5 }\nidle = 7;\n\
               main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n";
    let (_, _, report) = staged(src);
    assert!(
        !report.unread.contains(&"g".to_string()),
        "{:?}",
        report.unread
    );
    assert!(
        !report.unread.contains(&"k".to_string()),
        "{:?}",
        report.unread
    );
    assert_eq!(report.unread, ["idle"]);
}

#[test]
fn an_integer_domain_at_its_bounds() {
    // (case, domain, values passed, choice)
    let split_on = |vs: &[i64]| Choice::Split(vs.iter().copied().map(Value::Int).collect());
    let keep = |why: &str| Choice::Keep(why.into());
    let cases = [
        (
            "no lower bound",
            Domain::Ints(None, Some(5)),
            ints(&[3]),
            keep("an unbounded integer domain is infinite"),
        ),
        (
            "no bound at all",
            Domain::Ints(None, None),
            ints(&[3]),
            keep("an unbounded integer domain is infinite"),
        ),
        (
            "one value",
            Domain::Ints(Some(3), Some(3)),
            ints(&[2, 3, 4]),
            split_on(&[3]),
        ),
        (
            "both bounds included",
            Domain::Ints(Some(0), Some(9)),
            ints(&[-1, 0, 9, 10]),
            split_on(&[0, 9]),
        ),
        (
            "negative bounds",
            Domain::Ints(Some(-5), Some(-1)),
            ints(&[-6, -5, -1, 0]),
            split_on(&[-5, -1]),
        ),
        (
            "lower above upper",
            Domain::Ints(Some(4), Some(1)),
            ints(&[1, 2, 4]),
            keep(NONE_PASSED),
        ),
        (
            "nothing passed",
            Domain::Ints(Some(0), Some(9)),
            ints(&[]),
            keep(NONE_PASSED),
        ),
    ];
    for (case, d, given, want) in cases {
        assert_eq!(trick(&d, &given), want, "{case}");
    }
    // A value of another kind is never split on, whatever the integer domain holds.
    let mixed: BTreeSet<Value> = [
        Value::Int(3),
        Value::Bool(true),
        Value::str("3"),
        Value::atom("x"),
    ]
    .into();
    assert_eq!(
        trick(&Domain::Ints(Some(0), Some(9)), &mixed),
        split_on(&[3]),
        "other kinds"
    );
}

#[test]
fn a_finite_type_domain_is_split_on_its_members_passed_and_nothing_else() {
    let lits = &Type::lit(&Value::Int(1)).unwrap() | &Type::lit(&Value::Int(2)).unwrap();
    let pairs = Type::tuple(vec![Type::bool(), Type::bool()]);
    let tf = Value::tuple(vec![Value::Bool(true), Value::Bool(false)]);
    // (case, domain, values passed, the values split on)
    let cases = [
        (
            "bool, given an int",
            Type::bool(),
            [Value::Int(1), Value::Bool(true)].into(),
            vec![Value::Bool(true)],
        ),
        (
            "a literal set",
            lits,
            ints(&[0, 1, 2, 3]),
            vec![Value::Int(1), Value::Int(2)],
        ),
        (
            "a bare atom",
            Type::atom("gold"),
            [Value::atom("gold"), Value::str("gold")].into(),
            vec![Value::atom("gold")],
        ),
        (
            "a tuple of bools",
            pairs,
            [tf.clone(), Value::Bool(true)].into(),
            vec![tf],
        ),
    ];
    for (case, t, given, want) in cases {
        assert_eq!(
            trick(&Domain::Type(t), &given),
            Choice::Split(want),
            "{case}"
        );
    }
    // A finite type passed none of its members.
    assert_eq!(
        trick(&Domain::Type(Type::bool()), &ints(&[0, 1])),
        Choice::Keep(NONE_PASSED.into())
    );
}

#[test]
fn the_values_of_test_cases_are_passed_as_static_calls_are() {
    // DESIGN.md sec:staging: the values passed are those of each call in the residual
    // program and each test case whose argument for that parameter is a literal.
    let src = "scale(positional x: int, positional by: int) = x * by test { (3, 2) -> 6, (5, 2) -> 10 }\n\
               use(positional n: int) = scale(7, n);\n";
    let u = elab(src).unwrap();
    assert_eq!(passed(&u, "scale", 0), ints(&[3, 5, 7]));
    assert_eq!(passed(&u, "scale", 1), ints(&[2]));
    // A parameter the function does not have, and a name the unit does not define.
    assert_eq!(passed(&u, "scale", 2), ints(&[]));
    assert_eq!(passed(&u, "nothing", 0), ints(&[]));
    // The split has an arm for each value passed, then the general body.
    let (lam, _) = split(&u, "scale", 0, &Domain::Ints(Some(0), Some(9))).unwrap();
    assert_eq!(
        lam.to_string(),
        "(x, by) -> match x { 3 -> (3 * by), 5 -> (5 * by), 7 -> (7 * by), _ -> (x * by) }"
    );
}

#[test]
fn a_family_domain_is_never_split() {
    // DESIGN.md sec:staging lists the finite domains (bools, finite literal sets, bare atoms,
    // tuples of these, bounded integer intervals); a family is not among them, even one whose
    // keys and values are bools.
    for t in [
        Type::exact(Type::bool(), Type::bool()),
        Type::partial(Type::bool(), Type::int()),
    ] {
        let Choice::Keep(why) = trick(&Domain::Type(t.clone()), &ints(&[1])) else {
            panic!("{t:?} is split");
        };
        assert!(why.ends_with("is not known to be finite"), "{why}");
    }
}

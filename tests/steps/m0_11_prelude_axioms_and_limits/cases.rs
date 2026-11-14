//! Completeness cases for step M0.11 (TEST-complete-m0, author P189): the axiom table holds
//! exactly the laws DESIGN.md M0.11 names, at each operator and carrier, and no other; the
//! constants an axiom names compare as the kernel's values do; and the prelude's limit of
//! nested calls is the Rust one. The case list is `COMPLETENESS.md`.

use zed_kernel::eval::MIN_NESTED_CALLS;
use zedc::axioms::{AXIOMS, Carrier, Const, Law, Tonicity::*, of};

use Carrier::{Bool, F64, Int, String};
use Law::*;

/// The laws DESIGN.md M0.11 gives each operator at each carrier, written from its text.
fn design() -> Vec<(&'static str, Carrier, Vec<Law>)> {
    let min_max = |op, inf: f64| {
        [
            (
                op,
                Int,
                vec![
                    Associative,
                    Commutative,
                    Idempotent,
                    Selective,
                    Monotone(&[Up, Up]),
                ],
            ),
            (
                op,
                F64,
                vec![
                    Associative,
                    Commutative,
                    Idempotent,
                    Selective,
                    Identity(Const::F64(inf)),
                    Zero(Const::F64(f64::NAN)),
                ],
            ),
        ]
    };
    // `&&` and `||` each distribute over the other; with commutativity one side is the other.
    let and_or = |op, id: bool, other| {
        (
            op,
            Bool,
            vec![
                Associative,
                Commutative,
                Idempotent,
                Identity(Const::Bool(id)),
                Zero(Const::Bool(!id)),
                LeftDistributesOver(other),
            ],
        )
    };
    let mut out = vec![
        (
            "+",
            Int,
            vec![
                Associative,
                Commutative,
                Identity(Const::Int(0)),
                Monotone(&[Up, Up]),
            ],
        ),
        ("+", F64, vec![Commutative, Identity(Const::F64(-0.0))]),
        ("-", Int, vec![Monotone(&[Up, Down])]),
        (
            "*",
            Int,
            vec![
                Associative,
                Commutative,
                Identity(Const::Int(1)),
                Zero(Const::Int(0)),
                LeftDistributesOver("+"),
                RightDistributesOver("+"),
            ],
        ),
        ("*", F64, vec![Commutative, Identity(Const::F64(1.0))]),
        (
            "neg",
            Int,
            vec![Inverse("neg"), Injective, Monotone(&[Down])],
        ),
        ("neg", F64, vec![Inverse("neg"), Injective]),
        ("++", String, vec![Associative, Identity(Const::Str(""))]),
        and_or("&&", true, "||"),
        and_or("||", false, "&&"),
        ("!", Bool, vec![Inverse("!"), Injective, Monotone(&[Down])]),
        ("bitAnd", Int, vec![Associative, Commutative, Idempotent]),
        ("bitOr", Int, vec![Associative, Commutative, Idempotent]),
        (
            "bitXor",
            Int,
            vec![
                Associative,
                Commutative,
                Identity(Const::Int(0)),
                SelfInverse(Const::Int(0)),
            ],
        ),
        ("shl", Int, vec![PowerOfTwo("*")]),
        ("shr", Int, vec![PowerOfTwo("div")]),
    ];
    out.extend(min_max("min", f64::INFINITY));
    out.extend(min_max("max", f64::NEG_INFINITY));
    // `==` an equivalence and `!=` irreflexive and symmetric, but at `f64` both only what a
    // NaN leaves.
    for c in [Int, Bool, String] {
        out.push(("==", c, vec![Reflexive, Symmetric, Transitive]));
        out.push(("!=", c, vec![Irreflexive, Symmetric]));
    }
    out.push(("==", F64, vec![Symmetric, Transitive]));
    out.push(("!=", F64, vec![Symmetric]));
    // The comparisons at `int`, `f64` and the strings, the carriers M0.11's chain laws name.
    for (strict, weak) in [("<", "<="), (">", ">=")] {
        for c in [Int, F64, String] {
            out.push((
                strict,
                c,
                vec![
                    Irreflexive,
                    Transitive,
                    Implies(weak),
                    Composes(weak, strict),
                ],
            ));
            let order = match c {
                F64 => vec![Transitive],
                _ => vec![Reflexive, Antisymmetric, Transitive, Total],
            };
            out.push((weak, c, [order, vec![Composes(strict, strict)]].concat()));
        }
    }
    out
}

#[test]
fn the_table_holds_exactly_the_laws_design_names() {
    let design = design();
    for (op, c, laws) in &design {
        let table: Vec<Law> = of(op, *c).copied().collect();
        for law in laws {
            assert!(
                table.contains(law),
                "{op} at {c:?} lacks {law:?}: {table:?}"
            );
        }
        for law in &table {
            assert!(
                laws.contains(law),
                "{op} at {c:?} has {law:?}, which DESIGN does not name"
            );
        }
        assert_eq!(
            table.len(),
            laws.len(),
            "{op} at {c:?} lists a law twice: {table:?}"
        );
    }
    for a in AXIOMS {
        assert!(
            design
                .iter()
                .any(|(op, c, _)| *op == a.op && *c == a.carrier),
            "{a:?}: DESIGN names no law of {} at {:?}",
            a.op,
            a.carrier
        );
    }
}

#[test]
fn operators_with_no_law_by_axiom_have_none() {
    // DESIGN.md M0.11: "`-` at `f64`, `/`, `div` and `mod` carry no law by axiom"; `min` and
    // `max` have no identity at `int`; `clamp` carries no law of its own.
    for c in [Int, F64, Bool, String] {
        for op in ["/", "div", "mod", "clamp", "noSuchOperator"] {
            assert_eq!(of(op, c).count(), 0, "{op} at {c:?}");
        }
    }
    assert_eq!(of("-", F64).count(), 0);
    for op in ["min", "max"] {
        assert!(!of(op, Int).any(|l| matches!(l, Identity(_))), "{op}");
    }
    // An operator at a carrier it has no arrow at.
    assert_eq!(of("++", Int).count(), 0);
    assert_eq!(of("&&", Int).count(), 0);
}

#[test]
fn constants_compare_as_the_kernels_values_do() {
    // A float by its bits: `-0.0` is not `0.0`, and the NaN is itself.
    assert_eq!(Const::F64(f64::NAN), Const::F64(f64::NAN));
    assert_ne!(Const::F64(-0.0), Const::F64(0.0));
    assert_eq!(Const::Int(0), Const::Int(0));
    assert_ne!(Const::Int(0), Const::Int(1));
    assert_eq!(Const::Bool(true), Const::Bool(true));
    assert_ne!(Const::Bool(true), Const::Bool(false));
    assert_eq!(Const::Str(""), Const::Str(""));
    assert_ne!(Const::Str(""), Const::Str("a"));
    // Constants of two carriers are never equal, even of one value.
    assert_ne!(Const::Int(0), Const::F64(0.0));
    assert_ne!(Const::Int(1), Const::Bool(true));
    assert_ne!(Const::Str(""), Const::Bool(false));
    assert!(of("min", F64).any(|l| *l == Zero(Const::F64(f64::NAN))));
}

#[test]
fn the_prelude_limit_of_nested_calls_is_the_rust_one() {
    // DESIGN.md M0.11: "The minimum is 20 000 nested calls".
    let prelude = include_str!("../../../zed/prelude/limits.zed");
    let value = prelude
        .lines()
        .find_map(|l| l.strip_prefix("minNestedCalls = "))
        .and_then(|v| v.strip_suffix(';'))
        .expect("limits.zed declares minNestedCalls");
    assert_eq!(value.parse::<usize>(), Ok(20_000));
    assert_eq!(MIN_NESTED_CALLS, 20_000);
}

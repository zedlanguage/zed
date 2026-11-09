//! A refusal names a primitive as the program writes it: `>` in `1 > "Oslo"`, `popCount` in
//! `popCount(x)`, never the evaluator's own name for it (repair PRIM-op-names). Each name is
//! read back by the parser and the elaborator, so a name a program cannot write fails here.

use zed_kernel::{Evaluator, KernelError, Prim, Term, Value, World};
use zedc::zir::text::PRIMS;

use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};

/// The primitives no program names by a word of its own: elaboration builds them from other
/// forms (a tuple, a component `p[0]`, an atom), or they belong to later layers. A refusal
/// names them by the form DESIGN.md writes, or else as the kernel's printer writes them.
const UNNAMED: [Prim; 9] = [
    Prim::Tuple,
    Prim::TupleGet,
    Prim::Atom,
    Prim::Get,
    Prim::Count,
    Prim::Union,
    Prim::Path,
    Prim::PathKey,
    Prim::PathLen,
];

/// `f` applied to `n` functions where data is needed: the one refusal every primitive has.
fn refusal(f: Term, n: usize) -> String {
    let lam = Term::Lam(vec!["y".into()], Term::Var("y".into()).into());
    match Evaluator::new(World::new()).run(&Term::App(f.clone().into(), vec![lam; n])) {
        Err(KernelError::Type(m)) => m,
        other => panic!("{f}: no type error but {other:?}"),
    }
}

/// The refusal of `p`, named `w`, given functions: `==` and `!=` have their own wording.
fn check_refusal(p: Prim, w: &str, message: &str) {
    match p {
        Prim::Eq | Prim::Ne => assert!(
            message.starts_with(&format!("`{w}` on functions")),
            "{p:?}: {message}"
        ),
        _ => assert_eq!(message, format!("`{w}` applied to a function"), "{p:?}"),
    }
}

#[test]
fn a_refusal_names_each_primitive_as_the_program_writes_it() {
    let mut named = 0;
    for p in PRIMS {
        let w = p.written();
        let n = p.arity().unwrap_or(1);
        let params: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
        let prim = Term::Prim(
            p,
            params
                .iter()
                .map(|a| Term::Var(a.as_str().into()))
                .collect(),
        );
        let lam = Term::Lam(
            params.iter().map(|a| a.as_str().into()).collect(),
            prim.into(),
        );
        check_refusal(p, w, &refusal(lam, n));
        if UNNAMED.contains(&p) {
            assert_eq!(zedc::interp::prim(w), None, "{p:?} is a word `{w}`");
            continue;
        }
        named += 1;
        // The name, written in a program: a prelude word alone, `-` and `!` before their
        // operand, any other operator between two operands.
        let word = zedc::interp::prim(w);
        let text = match (word, n) {
            (Some(q), _) => {
                assert_eq!(q, p, "the word `{w}`");
                format!("x = {w};\n")
            }
            (None, 1) => format!("x = (a0) -> {w}a0;\n"),
            _ => format!("x = (a0, a1) -> a0 {w} a1;\n"),
        };
        let unit = elab(&text).unwrap_or_else(|e| panic!("{text}: {e:?}"));
        let d = unit.defs.iter().find(|d| d.name == "x").expect("x");
        match (d.term.as_ref(), p) {
            // A prelude word elaborates to the word itself, which the prelude defines.
            (Term::Var(v), _) if word.is_some() => assert_eq!(&**v, w, "{text}"),
            (Term::Lam(_, body), _) => match (body.as_ref(), p) {
                // `&&` and `||` elaborate to an `if`, so the evaluator never refuses them by name.
                (Term::If(..), Prim::And | Prim::Or) => continue,
                (Term::Prim(q, _), _) => assert_eq!(*q, p, "{text}: {body}"),
                (t, _) => panic!("{text}: {p:?} elaborated to {t}"),
            },
            (t, _) => panic!("{text}: {p:?} elaborated to {t}"),
        }
        let x = unit.get("x").expect("x");
        check_refusal(p, w, &refusal(with_prelude(x), n));
    }
    assert_eq!(named, PRIMS.len() - UNNAMED.len());
}

/// The forms of the primitives with no word of their own: DESIGN.md's `(..)`, `p[0]`, `f[k]`,
/// `.count` and `.union`; `#_(..)`, any atom, whose name a fixed text cannot carry; and the
/// printer's words for the keypath primitives, which DESIGN.md does not write.
#[test]
fn a_primitive_with_no_word_is_named_by_its_written_form() {
    let forms = [
        "(..)", "[i]", "#_(..)", "[k]", ".count", ".union", "path", "pathKey", "pathLen",
    ];
    for (p, w) in UNNAMED.into_iter().zip(forms) {
        assert_eq!(p.written(), w, "{p:?}");
    }
}

/// The ZIR text form reads a primitive back by its printed name, so no two share one.
#[test]
fn each_primitive_has_its_own_printed_name() {
    let mut seen = std::collections::HashMap::new();
    for p in PRIMS {
        if let Some(q) = seen.insert(p.printed(), p) {
            panic!("{q:?} and {p:?} are both printed `{}`", p.printed());
        }
    }
}

/// An arity refusal counts its arguments in the singular for one.
#[test]
fn an_arity_refusal_says_one_argument() {
    let t = Term::Prim(
        Prim::PopCount,
        vec![Term::Lit(Value::Int(1)), Term::Lit(Value::Int(2))],
    );
    assert_eq!(
        Evaluator::new(World::new())
            .run(&t)
            .unwrap_err()
            .to_string(),
        zed_kernel::KernelError::Type("`popCount` takes 1 argument, given 2".into()).to_string()
    );
}

/// The example of the report: an int compared with a string, given past the checker as a
/// kernel term, is refused by `>`, the operator the program wrote.
#[test]
fn comparing_a_number_with_a_city_name_names_the_comparison() {
    let t = Term::Prim(
        Prim::Gt,
        vec![Term::Lit(Value::Int(1)), Term::Lit(Value::str("Oslo"))],
    );
    assert_eq!(
        Evaluator::new(World::new())
            .run(&t)
            .unwrap_err()
            .to_string(),
        zed_kernel::KernelError::Type("`>` applied to `int`, `String`".into()).to_string()
    );
}

/// A refusal names an atom by its name when it has one, `#err(..)`, and as any atom, `#_(..)`,
/// when its first argument is not a name (repair PRIM-hidden-names).
#[test]
fn a_refusal_names_an_atom_by_its_name() {
    use zed_kernel::term::build::{lam, lit, var};
    let run =
        |args: Vec<Term>| match Evaluator::new(World::new()).run(&Term::Prim(Prim::Atom, args)) {
            Err(KernelError::Type(m)) => m,
            other => panic!("no type error but {other:?}"),
        };
    let none = || lit(Value::tuple(Vec::new()));
    let f = || lam(&["y"], var("y"));
    assert_eq!(
        run(vec![lit("err"), none(), f()]),
        "`#err(..)` applied to a function"
    );
    assert_eq!(
        run(vec![lit("err"), lit(5), lit(1)]),
        "`#err(..)` applied to `String`, `int`, `int`"
    );
    assert_eq!(
        run(vec![lit(7), none(), lit(1)]),
        "`#_(..)` applied to `int`, `(..)`, `int`"
    );
}

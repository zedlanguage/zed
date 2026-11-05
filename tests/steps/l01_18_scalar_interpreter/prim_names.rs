//! A refusal names a primitive as the program writes it: `>` in `1 > "Oslo"`, `popCount` in
//! `popCount(x)`, never the evaluator's own name for it (repair PRIM-op-names). Each name is
//! read back by the parser and the elaborator, so a name a program cannot write fails here.

use zed_kernel::{Evaluator, KernelError, Prim, Term, Value, World};
use zedc::zir::text::PRIMS;

use crate::l01_16_elaboration::{elab, with_prelude};

/// The primitives no program names: elaboration builds them from other forms (a tuple, a
/// component `t.0`, an atom), or they belong to later layers. A refusal names them as the
/// kernel's printer writes them.
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
        "type error: `>` applied to `int`, `String`"
    );
}

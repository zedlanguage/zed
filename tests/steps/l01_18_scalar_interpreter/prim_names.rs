//! A refusal names a primitive as the program writes it: `>` in `1 > "Oslo"`, `popCount` in
//! `popCount(x)`, never the evaluator's own name for it (repair PRIM-op-names). Each name is
//! read back by the parser and the elaborator, so a name a program cannot write fails here.

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Evaluator, Family, KernelError, Prim, Term, Value, World};
use zedc::zir::text::PRIMS;

use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};

/// The primitives no program names by a word of its own: elaboration builds them from other
/// forms (a tuple, a component `p[0]`, an atom, a read of a family whose keys are one integer
/// interval), or they belong to later layers. A refusal names them by the form DESIGN.md writes,
/// or else as the kernel's printer writes them.
const UNNAMED: [Prim; 10] = [
    Prim::Tuple,
    Prim::TupleGet,
    Prim::Atom,
    Prim::Get,
    Prim::Count,
    Prim::Union,
    Prim::Path,
    Prim::PathKey,
    Prim::PathLen,
    Prim::At,
];

/// `f` applied to `n` functions where data is needed: the one refusal every primitive has.
fn refusal(f: Term, n: usize) -> String {
    let lam = Term::Lam(vec!["y".into()], Term::Var("y".into()).into());
    match Evaluator::new(World::new()).run(&Term::App(f.clone().into(), vec![lam; n])) {
        Err(KernelError::Type(m)) => m,
        other => panic!("{f}: no type error but {other:?}"),
    }
}

/// The refusal of `p`, named `w`, given functions: `==` and `!=` have their own wording, and a
/// step on key paths is named in words and says where it ran (here outside every call that
/// generates it).
fn check_refusal(p: Prim, w: &str, message: &str) {
    match p {
        Prim::Eq | Prim::Ne => assert!(
            message.starts_with(&format!("`{w}` on functions")),
            "{p:?}: {message}"
        ),
        Prim::Path | Prim::PathKey | Prim::PathLen => assert_eq!(
            message,
            format!("{w} applied to a function, {OUTSIDE}"),
            "{p:?}"
        ),
        _ => assert_eq!(message, format!("`{w}` applied to a function"), "{p:?}"),
    }
}

/// The end of the refusal of a step on key paths that ran in no call that generates one.
pub(crate) const OUTSIDE: &str = "outside every `reindex` key map and value map and `discard` test, the \
                       only places the compiler generates it";

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
/// three steps on key paths, which DESIGN.md does not write and the compiler generates, in
/// words (question A9, answer A); and `f[k]` again for `at`, the read of a family whose keys are
/// one integer interval.
#[test]
fn a_primitive_with_no_word_is_named_by_its_written_form() {
    let forms = [
        "(..)",
        "[i]",
        "#_(..)",
        "[k]",
        ".count",
        ".union",
        "the step that builds a key path from its keys",
        "the step that reads the key at a given position of a key path",
        "the step that counts the keys of a key path",
        "[k]",
    ];
    for (p, w) in UNNAMED.into_iter().zip(forms) {
        assert_eq!(p.written(), w, "{p:?}");
        // A sentence quotes code and leaves words unquoted.
        let named = p.named(None);
        match p.in_words() {
            Some(words) => assert_eq!(named, words, "{p:?}"),
            None => assert_eq!(named, format!("`{w}`"), "{p:?}"),
        }
    }
}

/// The kernel's own names of the steps on key paths, `path`, `pathKey` and `pathLen`, never
/// reach a message: no such word, and no quoted code (the English word "path" in "key path"
/// is not the name).
#[test]
fn no_message_names_a_key_path_step_by_the_kernel_word() {
    for p in [Prim::Path, Prim::PathKey, Prim::PathLen] {
        for w in [p.written(), &p.named(None)] {
            assert!(!w.contains('`'), "{p:?}: {w}");
            for kernel in ["pathKey", "pathLen", "path("] {
                assert!(!w.contains(kernel), "{p:?}: {w}");
            }
        }
    }
}

/// The swap of two key levels that `group` generates, as a kernel `reindex` (question A9's
/// example, `sales.group(s -> s.region)`): its key map builds the key path from the second
/// key and then the first. Here the generated map reads the second key of the leaf's value,
/// an `int`, instead of the key path, as a bug in the compiler would; the refusal states the
/// step in words and names the call it ran in, with the keys of the entry.
#[test]
fn a_key_path_step_in_a_generated_key_swap_is_stated_in_words() {
    use zed_tests::kernel::{func, key, path, reindex, s};
    let sales = Family::from_leaves([
        (vec![Value::Int(0), s("north")], Value::Int(3)),
        (vec![Value::Int(1), s("south")], Value::Int(4)),
    ])
    .unwrap();
    let run = |kf: Term| {
        let t = reindex(lit(sales.clone()), kf, func(|[_, v]| v));
        match Evaluator::new(World::new()).run(&t) {
            Err(KernelError::Type(m)) => m,
            other => panic!("no type error but {other:?}"),
        }
    };
    // The swap as generated runs: the second key first.
    let swap = reindex(
        lit(sales.clone()),
        func(|[p, _]| path(vec![key(p.clone(), 1), key(p, 0)])),
        func(|[_, v]| v),
    );
    assert_eq!(
        Evaluator::new(World::new()).run(&swap).unwrap().to_string(),
        r#"{"north" -> {0 -> 3}, "south" -> {1 -> 4}}"#
    );
    assert_eq!(
        run(func(|[p, v]| path(vec![key(v, 1), key(p, 0)]))),
        "the step that reads the key at a given position of a key path applied to `int`, \
         `int`, in the key map that a `reindex` runs on each entry, on the entry at the keys \
         `0`, `\"north\"`"
    );
    // The same step given a function, and the length of the key path with two arguments.
    assert_eq!(
        run(func(|[p, _]| path(vec![
            key(p.clone(), 1),
            key(func(|[x]| x), 0)
        ]))),
        "the step that reads the key at a given position of a key path applied to a function, \
         in the key map that a `reindex` runs on each entry, on the entry at the keys `0`, \
         `\"north\"`"
    );
    assert_eq!(
        run(func(|[p, _]| {
            path(vec![prim(Prim::PathLen, vec![p.clone(), p]), lit(0)])
        })),
        "the step that counts the keys of a key path takes 1 argument, given 2, in the key map \
         that a `reindex` runs on each entry, on the entry at the keys `0`, `\"north\"`"
    );
}

/// In the value map of a `reindex` and the test of a `discard`, the refusal names that part.
#[test]
fn a_key_path_step_names_the_value_map_and_the_discard_test() {
    use zed_tests::kernel::{discard, func, key, reindex};
    let m = Family::of([("a", 1i64)]);
    let refusal = |t: Term| match Evaluator::new(World::new()).run(&t) {
        Err(KernelError::Type(m)) => m,
        other => panic!("no type error but {other:?}"),
    };
    assert_eq!(
        refusal(reindex(
            lit(m.clone()),
            func(|[p, _]| p),
            func(|[_, v]| key(v, 0))
        )),
        "the step that reads the key at a given position of a key path applied to `int`, \
         `int`, in the value map that a `reindex` runs on each entry, on the entry at the key \
         `\"a\"`"
    );
    assert_eq!(
        refusal(discard(lit(m), func(|[_, v]| key(v, 0)))),
        "the step that reads the key at a given position of a key path applied to `int`, \
         `int`, in the test that a `discard` runs on each entry, on the entry at the key \
         `\"a\"`"
    );
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

/// A step on key paths under `n` calls of `y -> y` and no `reindex`.
pub(crate) fn key_path_step_under_calls(n: usize) -> Term {
    use zed_kernel::term::build::{app, lam, var};
    let mut t = prim(Prim::PathKey, vec![lit(1), lit(0)]);
    for _ in 0..n {
        t = app(lam(&["y"], var("y")), vec![t]);
    }
    t
}

/// The type error of running `t`.
pub(crate) fn type_error(t: &Term) -> String {
    match Evaluator::new(World::new()).run(t) {
        Err(KernelError::Type(m)) => m,
        other => panic!("no type error but {other:?}"),
    }
}

#[test]
fn a_key_path_step_under_calls_that_do_not_generate_it_says_so() {
    // The refusal looks down the calls running for the one that generated the step, and finds
    // none (the input of `bench::prim_names` at a small size).
    for n in [0, 3] {
        assert_eq!(
            type_error(&key_path_step_under_calls(n)),
            format!(
                "the step that reads the key at a given position of a key path applied to \
                 `int`, `int`, {OUTSIDE}"
            )
        );
    }
}

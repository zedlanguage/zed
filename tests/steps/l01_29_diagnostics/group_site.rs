//! A refused check that reads a recursive type group names the group's head definition and
//! lists the group's definitions, beside the message at the use site (DESIGN.md L1.29, item
//! REFUSE-group-site); zedc adds their places once a recursive `type` is lowered (L2.5).

use zed_kernel::Value;
use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_tests::scaling;
use zedc::check::ty::Ty;

fn r(i: usize) -> Expr {
    Expr::Ref(i, vec![])
}

fn int() -> Expr {
    Expr::Type(Type::int())
}

fn one(i: i64) -> Expr {
    Expr::Type(Type::lit(&Value::Int(i)).unwrap())
}

fn nil() -> Expr {
    Expr::Type(Type::atom("nil"))
}

fn cons(head: Expr, tail: Expr) -> Expr {
    Expr::Atom("cons".into(), vec![head, tail])
}

/// The members of the group of `defs`, named and in order.
fn group(defs: &[(&str, Expr)]) -> Vec<Type> {
    let defs = (defs.iter())
        .map(|(name, body)| Def {
            name: (*name).into(),
            params: vec![],
            body: body.clone(),
        })
        .collect();
    Group::new(defs).unwrap().instance(vec![])
}

/// The lists of `head` as a ring of `n` definitions, `{name}{i} = #nil | #cons(head,
/// {name}{i+1})`, or the one definition `{name} = #nil | #cons(head, {name})` when `n` is 1.
fn ring(name: &str, head: Expr, n: usize) -> Type {
    let names: Vec<String> = (0..n)
        .map(|i| match n {
            1 => name.to_owned(),
            _ => format!("{name}{i}"),
        })
        .collect();
    let defs: Vec<(&str, Expr)> = (0..n)
        .map(|i| {
            let body = Expr::Union(vec![nil(), cons(head.clone(), r((i + 1) % n))]);
            (names[i].as_str(), body)
        })
        .collect();
    group(&defs).remove(0)
}

/// The lists of `int` of even length and of odd length, as a ring of `2n` definitions that
/// alternate between `Even{k} = #nil | #cons(int, Odd{k})` and `Odd{k} = #cons(int,
/// Even{k+1})`, or the two definitions `Even` and `Odd` when `n` is 1.
fn parity(n: usize) -> Vec<Type> {
    let names: Vec<String> = (0..2 * n)
        .map(|i| {
            let kind = ["Even", "Odd"][i % 2];
            match n {
                1 => kind.to_owned(),
                _ => format!("{kind}{}", i / 2),
            }
        })
        .collect();
    let defs: Vec<(&str, Expr)> = (0..2 * n)
        .map(|i| {
            let next = cons(int(), r((i + 1) % (2 * n)));
            let body = match i % 2 {
                0 => Expr::Union(vec![nil(), next]),
                _ => next,
            };
            (names[i].as_str(), body)
        })
        .collect();
    group(&defs)
}

/// The test `fork_empty` of `l01_23_subtyping::refusals`, written with named definitions, each
/// list a ring of `n`: `(Ints, Ints)` within the pairs whose first list holds only 1s and whose
/// second has an even length, only 2s and odd, and the rest of each. It holds, but the excluded
/// first lists meet at `#nil` and differ, so deciding it follows both at once, which the
/// checker refuses.
fn fork_empty(n: usize) -> (Ty, Ty) {
    let lists = ring("Ints", int(), n);
    let ones = ring("Ones", one(1), n);
    let twos = ring("Twos", one(2), n);
    let parity = parity(n);
    let (even, odd) = (&parity[0], &parity[1]);
    let pair = |a: &Type, b: &Type| Type::tuple(vec![a.clone(), b.clone()]);
    let within = Type::union_all([
        pair(&ones, even),
        pair(&twos, odd),
        pair(&(&lists - &ones), even),
        pair(&(&lists - &twos), odd),
    ]);
    (Ty::set(pair(&lists, &lists)), Ty::set(within))
}

/// The message of the refused check `a <: b`, after the sentence that a type is not within
/// another.
fn refused(a: &Ty, b: &Ty) -> String {
    assert!(!a.subtype(b));
    a.refused(b)
}

const FORK: &str = "; the checker could not decide this, so it is not proved wrong\n  because no value of it was found, and two of the tuple types involved differ in a \
     component whose type refers back to itself; following both at once can take time \
     exponential in the size of the types, so the checker does not try; write the two tuple \
     types so that they agree in that component, or test the value with `is` first";

/// The head is a group of one definition: the first recursive definition the check reads.
#[test]
fn a_refused_check_names_the_head_of_the_group_it_reads() {
    Type::forget_emptiness();
    let (a, b) = fork_empty(1);
    assert_eq!(
        refused(&a, &b),
        format!(
            "{FORK}\n  \
             the check reads the recursive type `Ones`, defined by:\n    \
             type Ones = #nil | #cons(1, Ones);"
        )
    );
}

/// The head's group of four definitions is listed whole, the head first, then by name.
#[test]
fn a_refused_check_lists_every_definition_of_the_head_group() {
    Type::forget_emptiness();
    let (a, b) = fork_empty(2);
    assert_eq!(
        refused(&a, &b),
        format!(
            "{FORK}\n  \
             the check reads the recursive type `Odd0`, defined by:\n    \
             type Odd0 = #cons(int, Even1);\n    \
             type Even0 = #nil | #cons(int, Odd0);\n    \
             type Even1 = #nil | #cons(int, Odd1);\n    \
             type Odd1 = #cons(int, Even0);"
        )
    );
}

/// The message of a check that reads groups of n definitions, at n and 8n: the head group
/// grows with n and is listed whole, so the message grows too. A walk to the head and its
/// definitions sorted by name and written, `O(n log n)`.
#[test]
fn naming_the_head_group_scales() {
    let n = 64;
    scaling::check_order(
        "the message of a refused check reading n definitions",
        n,
        1,
        |n| {
            Type::forget_emptiness();
            let (a, b) = fork_empty(n);
            let text = a.refused(&b);
            assert_eq!(text.matches("\n    type ").count(), 2 * n);
            std::hint::black_box(text);
        },
    );
}

/// Item PRINT-group-site-defs: the definitions a refusal lists are declarations a user could
/// write, a line each: they read as the top level of a file, and each name they use is one
/// of them. That they read back as the same types waits for type declarations in zedc (L2.1),
/// which refuses them today, and the kernel has no reader of its own.
#[test]
fn the_listed_definitions_read_as_declarations() {
    Type::forget_emptiness();
    let (a, b) = fork_empty(2);
    let text = refused(&a, &b);
    let (_, listed) = text.split_once("defined by:\n").expect("the definitions");
    let decls: Vec<&str> = listed.lines().map(str::trim).collect();
    let unit = decls.join("\n");
    let tokens = zedc::lex::lex_fence(&unit).unwrap_or_else(|e| panic!("{unit}: {e:?}"));
    zedc::parse::parse(&unit, &tokens, "Unit", zedc::parse::TOP)
        .unwrap_or_else(|e| panic!("{unit}: {e:?}"));
    let declared: Vec<&str> = (decls.iter())
        .map(|d| d["type ".len()..].split_once(' ').expect("a name").0)
        .collect();
    assert_eq!(declared, ["Odd0", "Even0", "Even1", "Odd1"]);
    for word in unit.split(|c: char| !c.is_alphanumeric()) {
        let named = word.starts_with(['E', 'O']);
        assert!(!named || declared.contains(&word), "{word} in {unit}");
    }
}

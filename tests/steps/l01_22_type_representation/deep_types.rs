//! Types, terms and patterns as deep as a program builds them, on the default stack of a test
//! thread: a list type nested 200,000 deep, an atom payload as deep, a chain of morphism types,
//! a program of nested `let`s, built, compared, printed and released. No test here sets a stack
//! size, and no depth is refused.
//!
//! Each of these overflowed the 2 MiB stack at depth 100,000 when dropping, comparing or
//! printing was a recursion (COMPLEXITY.md K39). Deciding whether a deep type is empty is still
//! a recursion, and is not tested here.

use std::sync::Arc;

use zed_kernel::types::Type;
use zed_kernel::types::rec::Expr;
use zed_kernel::value::Value;
use zed_kernel::{Pattern, Term};
use zed_tests::scaling;

/// How deep the types go. At 1,000,000 every test here passes, but building and printing the
/// type takes up to 60 s at load 100, over the limit of a test.
const DEPTH: usize = 200_000;

/// How deep the chains of morphism types go: each level costs about 127,000 instructions to
/// build, 25 times a tuple's.
const MORPHISMS: usize = 100_000;

/// The size of the scaling tests, and 8 times it.
const N: usize = 20_000;

/// A list of integers as a type, `(… ((int, int), int) …, int)`, nested `d` deep.
fn list(d: usize) -> Type {
    (0..d).fold(Type::int(), |t, _| Type::tuple(vec![t, Type::int()]))
}

/// A list of integers as a value of [`list`].
fn list_value(d: usize) -> Value {
    (0..d).fold(Value::Int(1), |v, _| Value::tuple(vec![v, Value::Int(2)]))
}

/// A Peano numeral as a type, `#succ(#succ(… int …))`, nested `d` deep.
fn numeral(d: usize) -> Type {
    (0..d).fold(Type::int(), |t, _| {
        Type::atom_with("succ", &Type::tuple(vec![t]))
    })
}

/// A curried function of `d` integers, `int -> (int -> … int)`.
fn curried(d: usize) -> Type {
    (0..d).fold(Type::int(), |t, _| Type::exact(Type::int(), t))
}

#[test]
fn a_list_type_nested_deep_is_built_compared_and_released() {
    let (a, b) = (list(DEPTH), list(DEPTH));
    assert_eq!(a, b);
    assert!(a.subtype(&b));
    assert!(a.contains(&list_value(DEPTH)));
    assert!(!a.contains(&list_value(DEPTH - 1)));
    assert!((&a - &b).is_empty());
}

#[test]
fn the_text_of_a_list_type_nested_deep_is_made() {
    let t = list(DEPTH);
    let text = t.to_string();
    assert!(text.starts_with("(tuple (tuple (tuple"));
    assert!(text.ends_with("int) int) int)"));
    assert_eq!(text.matches("tuple").count(), DEPTH);
    assert!(t.surface().to_string().len() > DEPTH);
}

#[test]
fn a_numeral_type_nested_deep_is_built_compared_and_released() {
    let n = numeral(DEPTH);
    assert_eq!(n, numeral(DEPTH));
    assert_eq!(n.to_string().matches("#succ").count(), DEPTH);
}

#[test]
fn a_curried_function_type_is_built_compared_printed_and_released() {
    let f = curried(MORPHISMS);
    assert_eq!(f, curried(MORPHISMS));
    assert!(f.surface().to_string().len() > MORPHISMS);
}

/// `x = 0; x = x + 1; …; x`, `d` lets deep, as the elaborator builds a long block.
fn block(d: usize) -> Term {
    (0..d).fold(Term::Var("x".into()), |body, _| {
        Term::Let(
            "x".into(),
            Arc::new(Term::Lit(Value::Int(0))),
            Arc::new(body),
        )
    })
}

/// `match` arms nested `d` deep, each matching `(_, p)`, with a pattern as deep in its last arm.
fn matches(d: usize) -> Term {
    (0..d).fold(Term::Var("x".into()), |t, _| {
        Term::Match(
            Arc::new(Term::Var("x".into())),
            vec![(Pattern::Tuple(vec![Pattern::Wild, Pattern::Wild]), t)],
        )
    })
}

/// The pattern `(_, (_, … _))`, nested `d` deep.
fn pattern(d: usize) -> Pattern {
    (0..d).fold(Pattern::Wild, |p, _| Pattern::Tuple(vec![Pattern::Wild, p]))
}

#[test]
fn a_program_and_a_pattern_nested_deep_are_released() {
    drop(block(1_000_000));
    drop(matches(1_000_000));
    drop(pattern(1_000_000));
    drop(Term::App(
        Arc::new(Term::Var("f".into())),
        vec![block(1_000_000), matches(1_000_000)],
    ));
}

/// `!(!(… int …))` and `(… (int,) …,)` in the body of a recursive definition, nested `d` deep.
fn bodies(d: usize) -> (Expr, Expr) {
    let not = (0..d).fold(Expr::Type(Type::int()), |e, _| Expr::Not(Box::new(e)));
    let tuple = (0..d).fold(Expr::Param(0), |e, _| Expr::Tuple(vec![e]));
    (not, tuple)
}

#[test]
fn the_body_of_a_definition_nested_deep_is_released() {
    drop(bodies(1_000_000));
}

#[test]
fn the_text_of_a_type_made_from_the_outside_in_is_its_text_made_from_the_inside_out() {
    // The text of a type is made in a loop that tries a type, makes the texts it found
    // missing, and tries again. Printing every part first makes each text at the first try,
    // as the recursion did; both must give the same text.
    let mut seed = 11;
    for _ in 0..4000 {
        let mut s = seed;
        let outside_in = random(&mut s, 5, false);
        let inside_out = random(&mut seed, 5, true);
        assert_eq!(outside_in.to_string(), inside_out.to_string());
        assert_eq!(
            outside_in.surface().to_string(),
            inside_out.surface().to_string()
        );
    }
}

fn next(s: &mut u64) -> u64 {
    *s = s
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *s >> 33
}

/// A random type `d` deep; with `print`, the text of each part is made before it is used.
fn random(s: &mut u64, d: u32, print: bool) -> Type {
    let k = next(s);
    let t = if d == 0 || k.is_multiple_of(7) {
        match k % 6 {
            0 => Type::int(),
            1 => Type::string(),
            2 => Type::bool(),
            3 => Type::lit(&Value::Int((k % 5) as i64)).unwrap(),
            4 => Type::atom(["a", "b"][(k % 2) as usize]),
            _ => Type::empty(),
        }
    } else {
        let mut part = || random(s, d - 1, print);
        match k % 9 {
            0 => Type::tuple(vec![part(), part()]),
            1 => Type::tuple(vec![part()]),
            2 => Type::atom_with(["a", "b"][(k % 2) as usize], &Type::tuple(vec![part()])),
            3 => Type::exact(part(), part()),
            4 => Type::partial(part(), part()),
            5 => &part() | &part(),
            6 => &part() & &part(),
            7 => &part() - &part(),
            _ => !part(),
        }
    };
    if print {
        let _ = t.to_string();
    }
    t
}

#[test]
fn building_printing_and_releasing_a_deep_type_scales() {
    scaling::check("a list type n deep, built and released", N, |d| {
        drop(list(d))
    });
    scaling::check("a list type n deep, built and printed", N, |d| {
        assert!(list(d).to_string().len() > d);
    });
    scaling::check("a numeral type n deep, built and released", N, |d| {
        drop(numeral(d));
    });
    scaling::check("a block of n lets, built and released", N, |d| {
        drop(block(d))
    });
    scaling::check("a definition body n deep, built and released", N, |d| {
        drop(bodies(d));
    });
}

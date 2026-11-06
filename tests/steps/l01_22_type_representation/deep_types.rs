//! Types, terms and patterns as deep as a program builds them, on the default stack of a test
//! thread: a list type nested 200,000 deep, an atom payload as deep, a chain of morphism types,
//! a program of nested `let`s, built, compared, printed and released. No test here sets a stack
//! size, and no depth is refused.
//!
//! Each of these overflowed the 2 MiB stack at depth 100,000 when dropping, comparing or
//! printing was a recursion (COMPLEXITY.md K39). Deciding whether a deep type is empty is still
//! a recursion, and is not tested here (ledger item T2-types-rest).

use std::cell::RefCell;
use std::sync::Mutex;
use zed_kernel::Shared;

use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};
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

#[path = "debug_samples.rs"]
mod debug_samples;

#[test]
fn debug_writes_the_derived_text() {
    // debug_text.txt is the text the derived `Debug`s wrote, a recursion, for these types.
    let expected = include_str!("debug_text.txt");
    let samples = debug_samples::samples();
    assert_eq!(samples.len(), expected.lines().count());
    for (t, line) in samples.iter().zip(expected.lines()) {
        assert_eq!(format!("{t:?}"), line);
        // On one line under `{:#?}` too, as `Value`'s and `Term`'s `Debug` write it.
        assert_eq!(format!("{t:#?}"), line);
    }
}

/// How deep the types whose `Debug` text is made go: each level of a list type writes about
/// 1,000 bytes. The recursion of the derived `Debug`s overflowed the 2 MiB stack at 2,000 levels of a list or a
/// curried function and at 1,000 of a numeral.
const DEBUG_DEPTH: usize = 20_000;

#[test]
fn the_debug_text_of_types_nested_deep_is_made() {
    let text = format!("{:?}", list(DEBUG_DEPTH));
    // Each level is a type with one tuple length, and the integers of each row are one more.
    assert_eq!(text.matches("Type(").count(), 2 * DEBUG_DEPTH + 1);
    assert!(text.ends_with("morphisms: Bdd(false) }))"));
    let text = format!("{:?}", numeral(DEBUG_DEPTH));
    assert_eq!(text.matches("\"succ\": AtomPart").count(), DEBUG_DEPTH);
    let text = format!("{:?}", curried(DEBUG_DEPTH));
    assert_eq!(text.matches("Morphism { guarantee: ").count(), DEBUG_DEPTH);
}

#[test]
fn the_debug_text_of_a_deep_type_scales() {
    scales_at(
        "the Debug text of a list type n deep",
        2_000,
        |n, i| list_on(i, n),
        |n, t| {
            let text = format!("{t:?}");
            assert!(text.len() > n);
            (t, text.len())
        },
    );
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
            Shared::new(Term::Lit(Value::Int(0))),
            Shared::new(body),
        )
    })
}

/// `match` arms nested `d` deep, each matching `(_, p)`, with a pattern as deep in its last arm.
fn matches(d: usize) -> Term {
    (0..d).fold(Term::Var("x".into()), |t, _| {
        Term::Match(
            Shared::new(Term::Var("x".into())),
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
        Shared::new(Term::Var("f".into())),
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
    random_in(s, d, print, None)
}

/// The instances of a group built by [`random_in`], each with its argument.
struct Trees {
    group: Group,
    made: RefCell<Vec<(Type, Type)>>,
}

/// [`random`], with instances of `tree` among the parts when it is given.
fn random_in(s: &mut u64, d: u32, print: bool, tree: Option<&Trees>) -> Type {
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
        let mut part = || random_in(s, d - 1, print, tree);
        match k % 9 {
            _ if let Some(g) = tree
                && k.is_multiple_of(4) =>
            {
                let arg = part();
                let t = g.group.instance(vec![arg.clone()]).remove(0);
                g.made.borrow_mut().push((t.clone(), arg));
                t
            }
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

/// Checks that `run` scales as n log n at sizes [`N`] and 8 times it. Each run takes an input of
/// its own, `make(n, i)` for the `i`-th run at size `n`, all built before any run is timed, and
/// what it returns is kept until the check ends, so its release is not timed either.
fn scales<I: Send, O: Send>(
    what: &str,
    make: impl Fn(usize, usize) -> I,
    run: impl Fn(usize, I) -> O + Sync,
) {
    scales_at(what, N, make, run);
}

/// [`scales`] at sizes `n` and 8 times it.
fn scales_at<I: Send, O: Send>(
    what: &str,
    n: usize,
    make: impl Fn(usize, usize) -> I,
    run: impl Fn(usize, I) -> O + Sync,
) {
    let (small, large) = scaling::Meter::new().runs();
    let pool = |n: usize, runs: usize| (n, Mutex::new((0..runs).map(|i| make(n, i)).collect()));
    let pools: [(usize, Mutex<Vec<I>>); 2] = [pool(n, small), pool(scaling::FACTOR * n, large)];
    let kept = Mutex::new(Vec::new());
    scaling::check(what, n, |n| {
        let (_, inputs) = pools.iter().find(|(m, _)| *m == n).expect("a size checked");
        let input = inputs
            .lock()
            .expect("the inputs of a size")
            .pop()
            .expect("one input per run");
        let out = run(n, input);
        kept.lock().expect("the outputs kept").push(out);
    });
}

/// A list type `d` deep on the literal `leaf`: types built on different leaves share no part,
/// so no run finds the parts or texts of another made already.
fn list_on(leaf: usize, d: usize) -> Type {
    let leaf = Type::lit(&Value::Int(leaf as i64)).expect("an integer literal is a type");
    (0..d).fold(leaf, |t, _| Type::tuple(vec![t, Type::int()]))
}

#[test]
fn building_a_deep_type_scales() {
    scales("a list type n deep, built", |_, i| i, |n, i| list_on(i, n));
}

#[test]
fn printing_a_deep_type_scales() {
    scales(
        "the text of a list type n deep",
        |n, i| list_on(i, n),
        |n, t| {
            let text = t.to_string();
            assert!(text.len() > n);
            (t, text)
        },
    );
}

#[test]
fn releasing_deep_types_terms_and_patterns_scales() {
    // The thread's tables of diagram nodes hold a type's parts until the thread ends, so a type
    // dropped on this thread frees nearly nothing. Built and dropped on a thread of its own, it
    // is freed when that thread ends, and the freeing is measured with the building.
    let on_a_thread = |make: fn(usize, usize) -> Type| {
        move |n: usize, i: usize| scaling::on_a_thread(2 << 20, || drop(make(i, n)))
    };
    scales(
        "a list type n deep, built and released on a thread of its own",
        |_, i| i,
        on_a_thread(list_on),
    );
    scales(
        "a numeral type n deep, built and released on a thread of its own",
        |_, i| i,
        on_a_thread(|i, n| {
            let leaf = Type::lit(&Value::Int(i as i64)).expect("an integer literal is a type");
            (0..n).fold(leaf, |t, _| Type::atom_with("succ", &Type::tuple(vec![t])))
        }),
    );
    scales(
        "a block of n lets, released",
        |n, _| block(n),
        |_, t| drop(t),
    );
    scales(
        "a pattern n deep, released",
        |n, _| pattern(n),
        |_, p| drop(p),
    );
    scales(
        "a definition body n deep, released",
        |n, _| bodies(n),
        |_, b| drop(b),
    );
}

#[test]
fn a_recursive_type_inside_a_type_is_named_with_its_arguments() {
    // `type Tree(A) = #leaf(A) | #fork(Tree(A), Tree(A))` at a type whose text is not made yet.
    // The name of `Tree(…)` prints its argument while the text of the tuple around it is being
    // made, and must print it in full.
    let t = || Expr::Ref(0, vec![Expr::Param(0)]);
    let tree = Group::new(vec![Def {
        name: "Tree".into(),
        params: vec!["A".into()],
        body: Expr::Union(vec![
            Expr::Atom("leaf".into(), vec![Expr::Param(0)]),
            Expr::Atom("fork".into(), vec![t(), t()]),
        ]),
    }])
    .unwrap();
    let arg = &Type::lit(&Value::Int(12_345)).unwrap() | &Type::string();
    let member = tree.instance(vec![arg]).remove(0);
    let pair = Type::tuple(vec![member, Type::int()]);
    assert_eq!(pair.to_string(), "(tuple Tree((| 12345 String)) int)");
}

/// How deep [`trees`] nests.
const TREES: usize = 10_000;

/// `type Tree(A) = #leaf(A) | #fork(Tree(A), Tree(A))`, its parameter named `param` and the
/// type `name`. Groups that differ in either have instances of their own.
fn tree(name: &str, param: &str) -> Group {
    let t = || Expr::Ref(0, vec![Expr::Param(0)]);
    Group::new(vec![Def {
        name: name.into(),
        params: vec![param.into()],
        body: Expr::Union(vec![
            Expr::Atom("leaf".into(), vec![Expr::Param(0)]),
            Expr::Atom("fork".into(), vec![t(), t()]),
        ]),
    }])
    .unwrap()
}

/// `Tree(Tree(… Tree(leaf) …))`, `d` instances of `group` nested in each other's argument.
fn trees(group: &Group, leaf: Type, d: usize) -> Type {
    (0..d).fold(leaf, |t, _| group.instance(vec![t]).remove(0))
}

#[test]
fn a_recursive_type_nested_deep_in_its_own_arguments_is_printed() {
    // The name of each `Tree(…)` holds the text of its argument, another `Tree(…)` whose name
    // is not made yet: the loop that makes texts takes each name as an item of its stack.
    let t = trees(&tree("Tree", "A"), Type::int(), TREES);
    let text = t.to_string();
    assert_eq!(
        text,
        format!("{}int{}", "Tree(".repeat(TREES), ")".repeat(TREES))
    );
    let pair = Type::tuple(vec![t, Type::int()]).to_string();
    assert_eq!(pair, format!("(tuple {text} int)"));
}

#[test]
fn printing_a_recursive_type_nested_deep_in_its_own_arguments_scales() {
    // Each input is built from a group of its own, so no run finds the names of another made.
    scales_at(
        "the text of Tree(Tree(..)) n deep",
        500,
        |n, i| trees(&tree(&format!("T{i}x{n}"), "A"), Type::int(), n),
        |n, t| {
            let text = t.to_string();
            assert!(text.len() > n);
            (t, text)
        },
    );
}

/// `type Big(A) = #nil | #cons(A, Big(A)) | #k0 | … | #k{s-1}`, a body of size `s`, named `name`.
fn big(name: &str, s: usize) -> Group {
    let mut arms = vec![
        Expr::Type(Type::atom("nil")),
        Expr::Atom(
            "cons".into(),
            vec![Expr::Param(0), Expr::Ref(0, vec![Expr::Param(0)])],
        ),
    ];
    arms.extend((0..s).map(|k| Expr::Type(Type::atom(&format!("k{k}")))));
    Group::new(vec![Def {
        name: name.into(),
        params: vec!["A".into()],
        body: Expr::Union(arms),
    }])
    .unwrap()
}

#[test]
fn instantiating_a_group_scales() {
    // An instance was found by a scan of every instance made at definitions of the same text,
    // keyed by the text of the definitions made anew at each call: nested instances took time
    // quadratic in their depth, and a body of size s instantiated s times took s² (ledger
    // INST-bucket). Each run has a group of its own, so no run finds another's instances.
    scales_at(
        "Tree(Tree(..)) n deep, instantiated",
        1000,
        |n, i| tree(&format!("N{i}x{n}"), "A"),
        |n, g| trees(&g, Type::int(), n),
    );
    let lits = |s: usize| -> Vec<Type> {
        (0..s)
            .map(|k| Type::lit(&Value::Int(k as i64)).expect("an integer literal is a type"))
            .collect()
    };
    scales_at(
        "a body of size n at n different arguments",
        500,
        |n, i| (big(&format!("D{i}x{n}"), n), lits(n)),
        |_, (g, args)| {
            let made: Vec<Type> = args
                .into_iter()
                .map(|a| g.instance(vec![a]).remove(0))
                .collect();
            made
        },
    );
    scales_at(
        "a body of size n at one argument n times",
        500,
        |n, i| big(&format!("S{i}x{n}"), n),
        |n, g| {
            let first = g.instance(vec![Type::int()]).remove(0);
            for _ in 1..n {
                assert!(g.instance(vec![Type::int()])[0] == first);
            }
            first
        },
    );
}

#[test]
fn the_text_of_a_type_with_recursive_types_is_the_same_made_outside_in_and_inside_out() {
    // `Tree(…)` stands among the other parts, its arguments random too. Two groups would give
    // two sets of recursive nodes, which order the parts of a type differently, so both texts
    // are made with one group: first from the outside in, the loop making every name, then for
    // the type built again with the text of each part made before it is used, which shares the
    // recursive nodes and makes the other parts' texts anew. Each name must spell out the text
    // of its argument. A group of its own for each type keeps the names of one from another.
    for k in 0..1500 {
        let trees = Trees {
            group: tree(&format!("T{k}"), "A"),
            made: RefCell::new(Vec::new()),
        };
        let mut seed = 23 + k;
        let outside_in = random_in(&mut seed.clone(), 5, false, Some(&trees));
        let text = outside_in.to_string();
        for (t, arg) in trees.made.borrow().iter() {
            assert_eq!(t.to_string(), format!("T{k}({arg})"));
        }
        let inside_out = random_in(&mut seed, 5, true, Some(&trees));
        assert_eq!(text, inside_out.to_string());
    }
}

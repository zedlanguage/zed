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

/// `text` with each diagram node written once, `#k=Node(..)` then `#k#`, written out in full at
/// each use, as the derived `Debug` wrote it. The samples hold no `#` and no unmatched
/// parenthesis but these.
fn unshared(text: &str) -> String {
    let (mut out, mut defs, mut open) = (String::new(), Vec::<String>::new(), Vec::new());
    let mut depth = 0;
    let mut rest = text;
    while let Some(c) = rest.chars().next() {
        if c == '#' {
            let digits = rest[1..].find(|c: char| !c.is_ascii_digit()).unwrap() + 1;
            let k: usize = rest[1..digits].parse().unwrap();
            match &rest[digits..digits + 1] {
                "=" => {
                    assert_eq!(defs.len(), k, "numbered in the order written");
                    defs.push(String::new());
                    open.push((k, out.len(), depth));
                }
                _ => out.push_str(&defs[k]),
            }
            rest = &rest[digits + 1..];
            continue;
        }
        out.push(c);
        rest = &rest[c.len_utf8()..];
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if let Some(&(k, at, d)) = open.last()
                    && d == depth
                {
                    open.pop();
                    defs[k] = out[at..].to_string();
                }
            }
            _ => {}
        }
    }
    out
}

#[test]
fn debug_writes_the_derived_text_with_each_shared_node_once() {
    // debug_text.txt is the text the derived `Debug`s wrote, a recursion, for these types; it
    // was written again by `unshared` when step CHAIN-zip-size changed the diagrams (decision
    // lists, with other digests) and the exclusive ors (one form, module `bdd::xor`), and again
    // for two later changes of digest (repair DEEP-types-regress): CHAIN-deep-atom (07d4247a)
    // made a decision list a treap of blocks, hashed as a tree, which changes the digests of
    // diagrams and so the order of a connective's operands (`Part::before`); REC-canon
    // (6cf6b730) hashes a recursive member by its group's canonical form, which changes the
    // digest of the one sample with a `Tree` instance. The text is the same when this test runs
    // alone, among the others and on one thread.
    let expected = include_str!("debug_text.txt");
    let samples = debug_samples::samples();
    assert_eq!(samples.len(), expected.lines().count());
    let mut shared = 0;
    for (t, line) in samples.iter().zip(expected.lines()) {
        let text = format!("{t:?}");
        assert_eq!(unshared(&text), line);
        assert!(text.len() <= line.len());
        shared += usize::from(text.contains("#0#"));
        // On one line under `{:#?}` too, as `Value`'s and `Term`'s `Debug` write it.
        assert_eq!(format!("{t:#?}"), text);
    }
    assert!(shared > 0, "some sample shares a node");
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
fn a_recursive_type_nested_deep_in_its_own_arguments_is_released() {
    // Each `Tree(…)` holds its argument, the instance below it, and was dropped by a recursion as
    // deep as the nesting once the end of its unit or of its thread freed it (repair
    // DEEP-types-regress). Freed both ways, on a thread of the usual 2 MiB stack.
    scaling::on_a_thread(2 << 20, || {
        drop(trees(&tree("Ended", "A"), Type::int(), TREES));
        Type::forget_emptiness();
    });
    scaling::on_a_thread(2 << 20, || {
        drop(trees(&tree("Exited", "A"), Type::int(), TREES));
    });
}

#[test]
fn releasing_a_recursive_type_nested_deep_in_its_own_arguments_scales() {
    // Built and freed on a thread of its own, at the end of its unit, from a group of its own.
    scales_at(
        "Tree(Tree(..)) n deep, built and released at the end of its unit",
        1000,
        |_, i| i,
        |n, i| {
            scaling::on_a_thread(2 << 20, || {
                drop(trees(&tree(&format!("R{i}x{n}"), "A"), Type::int(), n));
                Type::forget_emptiness();
            })
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

/// Operands of an xor chain on the default stack. The derived `Debug` wrote `2^n` copies of the
/// first operand: 2.9 MB at 12 operands, 183 MB in 1 s at 18; this size would never end.
const XORS: usize = 16_000;

#[test]
fn the_debug_text_of_an_expression_writes_each_shared_operand_once() {
    let text = format!("{:?}", xor_chain(0, XORS));
    // The chain is taken to the one form of the exclusive or of its atoms, built over a tree of
    // them (module `bdd::xor`): a few expressions for each atom, each shared one named once and
    // referred to once.
    let shared = text.matches('=').count();
    assert!(shared > XORS && shared < 4 * XORS);
    assert_eq!(text.matches("#0#").count(), 1);
    assert_eq!(text.matches('#').count(), 3 * shared);
    assert!(text.len() < 2_000 * XORS);
}

#[test]
fn the_debug_text_of_an_xor_chain_scales() {
    scales_at(
        "the Debug text of an xor chain",
        2_000,
        |n, i| xor_chain(i * 1_000_000, n),
        |_, t| format!("{t:?}"),
    );
}

/// The parity of `n` one-tuples of the literals from `leaf`, built as `t = (t - r) | (r - t)`
/// for each tuple `r` in turn. Built as it stands, its operand `t` is reached by two edges at
/// each step, `2^n` paths through `2n` expressions; the kernel keeps the one form of the
/// exclusive or instead, whose expressions share their operands too.
fn xor_chain(leaf: usize, n: usize) -> Type {
    let row = |i: usize| Type::tuple(vec![Type::lit(&Value::Int((leaf + i) as i64)).unwrap()]);
    (1..n).fold(row(0), |t, i| {
        let r = row(i);
        &(&t - &r) | &(&r - &t)
    })
}

/// The type `t_d`, with `t_0` the literal `leaf` and `t_k = (t_{k-1}, t_{k-1})`: each `t_k` is
/// one shared value reached by two edges, `2^d` paths through `d + 1` types.
fn doubled(leaf: usize, d: usize) -> Type {
    let leaf = Type::lit(&Value::Int(leaf as i64)).expect("an integer literal is a type");
    (0..d).fold(leaf, |t, _| Type::tuple(vec![t.clone(), t]))
}

/// How deep [`doubled`] goes on the default stack. The `Debug` that wrote a type once per path
/// wrote `2^d` copies of the leaf; this depth would never end.
const DOUBLINGS: usize = 20_000;

#[test]
fn the_debug_text_of_a_shared_type_writes_it_once() {
    let text = format!("{:?}", doubled(0, DOUBLINGS));
    // Each `t_k` below the top is numbered where first written and referred to once after.
    assert_eq!(text.matches('=').count(), DOUBLINGS - 1);
    assert_eq!(text.matches('#').count(), 3 * (DOUBLINGS - 1));
    assert!(text.len() < 1_000 * DOUBLINGS);
}

#[test]
fn the_debug_text_of_a_shared_type_scales() {
    scales_at(
        "the Debug text of a type with each level shared",
        2_000,
        |n, i| doubled(i * 1_000_000 + n, n),
        |_, t| format!("{t:?}"),
    );
}

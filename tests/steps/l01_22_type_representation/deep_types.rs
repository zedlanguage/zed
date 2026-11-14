//! Types, terms and patterns as deep as a program builds them, on the default stack of a test
//! thread: a list type nested 100,000 deep, an atom payload as deep, a chain of morphism types,
//! a program of nested `let`s, built, compared, printed and released. No test here sets a stack
//! size other than the 2 MiB of a test thread, and no depth is refused.
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

/// How deep the types, terms, patterns and definition bodies go: 100,000, the depth at which
/// each overflowed the 2 MiB stack when its release, comparison or text was a recursion (file
/// header, COMPLEXITY.md K39), the smallest depth that record shows overflowing. It was 200,000
/// for types and 1,000,000 for terms, patterns and bodies, which took 4 to 10 s a test under
/// load (TEST-bench-move-l0123, author P169: a deep-stack test uses the smallest depth that
/// still overflows a default stack). At 1,000,000 every test here passes too.
const DEPTH: usize = 100_000;

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

/// A list type [`DEPTH`] deep built twice, compared, and released, on a thread of the usual
/// 2 MiB stack of its own, so that the thread's tables of diagram nodes free the type when the
/// thread ends, as `bench::releasing_deep_types_terms_and_patterns_scales` frees it.
/// TEST-bench-move-l0123 (author P169): was 200,000 deep on the test's own thread; now 100,000
/// deep (see [`DEPTH`]), and released at the end of a thread of its own, a path that only the
/// benchmark checked before.
#[test]
fn a_list_type_nested_deep_is_built_compared_and_released() {
    scaling::on_a_thread(2 << 20, || {
        let (a, b) = (list(DEPTH), list(DEPTH));
        assert_eq!(a, b);
        assert!(a.subtype(&b));
        assert!(a.contains(&list_value(DEPTH)));
        assert!(!a.contains(&list_value(DEPTH - 1)));
        assert!((&a - &b).is_empty());
    });
}

/// TEST-bench-move-l0123 (author P169): was 200,000 deep, now 100,000 (see [`DEPTH`]).
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
    // digest of the one sample with a `Tree` instance; EMPTY-normalize makes a tuple with an
    // empty component empty, which drops the member `#b((Never))` from one random sample's
    // union (line 29); GSX-unsolved hashes a recursive member without its definitions' names,
    // which changes the digests of the `Tree` sample again (line 16) and nothing else. The
    // text is the same when this test runs
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
/// curried function and at 1,000 of a numeral. TEST-bench-move-l0123 (author P169): was
/// 20,000; now 2,000, the smallest depth this record shows overflowing for each of the three.
/// The text of each nests as deep as when the derived `Debug`s overflowed: measured on the
/// code of 2026-11-14, the text nests 16,005 brackets deep for a list 2,000 deep, 28,005 for a
/// numeral (14,005 at 1,000) and 12,005 for a curried function.
const DEBUG_DEPTH: usize = 2_000;

/// TEST-bench-move-l0123 (author P169): was 20,000 levels, now 2,000 (see [`DEBUG_DEPTH`]).
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

/// A numeral type [`DEPTH`] deep built twice, compared, printed and released, on a thread of the
/// usual 2 MiB stack of its own, so that the thread's tables free it when the thread ends, as
/// `bench::releasing_deep_types_terms_and_patterns_scales` frees it. TEST-bench-move-l0123
/// (author P169): was 200,000 deep on the test's own thread; now 100,000 deep (see [`DEPTH`]),
/// and released at the end of a thread of its own, a path only the benchmark checked before.
#[test]
fn a_numeral_type_nested_deep_is_built_compared_and_released() {
    scaling::on_a_thread(2 << 20, || {
        let n = numeral(DEPTH);
        assert_eq!(n, numeral(DEPTH));
        assert_eq!(n.to_string().matches("#succ").count(), DEPTH);
    });
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

/// TEST-bench-move-l0123 (author P169): was 1,000,000 deep, now [`DEPTH`], 100,000, the depth
/// at which a term and a pattern overflowed the 2 MiB stack when their release was a recursion
/// (COMPLEXITY.md K39).
#[test]
fn a_program_and_a_pattern_nested_deep_are_released() {
    drop(block(DEPTH));
    drop(matches(DEPTH));
    drop(pattern(DEPTH));
    drop(Term::App(
        Shared::new(Term::Var("f".into())),
        vec![block(DEPTH), matches(DEPTH)],
    ));
}

/// `!(!(… int …))` and `(… (int,) …,)` in the body of a recursive definition, nested `d` deep.
fn bodies(d: usize) -> (Expr, Expr) {
    let not = (0..d).fold(Expr::Type(Type::int()), |e, _| Expr::Not(Box::new(e)));
    let tuple = (0..d).fold(Expr::Param(0), |e, _| Expr::Tuple(vec![e]));
    (not, tuple)
}

/// TEST-bench-move-l0123 (author P169): was 1,000,000 deep, now [`DEPTH`], 100,000, the depth
/// at which a definition body overflowed the 2 MiB stack when its release was a recursion
/// (COMPLEXITY.md K39).
#[test]
fn the_body_of_a_definition_nested_deep_is_released() {
    drop(bodies(DEPTH));
}

/// TEST-bench-move-l0123 (author P169): was 4,000 types from the fixed seed 11; now 1,000 types
/// from a new seed each run, printed (`ZED_SEED=<seed>` repeats it).
#[test]
fn the_text_of_a_type_made_from_the_outside_in_is_its_text_made_from_the_inside_out() {
    // The text of a type is made in a loop that tries a type, makes the texts it found
    // missing, and tries again. Printing every part first makes each text at the first try,
    // as the recursion did; both must give the same text.
    let (mut rng, seed) = zed_tests::instances::Rng::fresh("types made outside in and inside out");
    for k in 0..1000 {
        let case = rng.next_u64();
        let outside_in = random(&mut case.clone(), 5, false);
        let inside_out = random(&mut case.clone(), 5, true);
        let why = format!("type {k}, case seed {case} (ZED_SEED={seed})");
        assert_eq!(outside_in.to_string(), inside_out.to_string(), "{why}");
        assert_eq!(
            outside_in.surface().to_string(),
            inside_out.surface().to_string(),
            "{why}"
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

/// Small instance of `bench::instantiating_a_group_scales` (TEST-bench-move-l0123, author
/// P169): a body of size 5 at 5 different arguments gives 5 different instances, each found
/// again at its own argument, and a body at one argument 5 times gives one instance.
#[test]
fn a_group_gives_one_instance_for_each_argument() {
    let g = big("SmallD", 5);
    let args: Vec<Type> = (0..5)
        .map(|k| Type::lit(&Value::Int(k)).expect("an integer literal is a type"))
        .collect();
    let made: Vec<Type> = args
        .iter()
        .map(|a| g.instance(vec![a.clone()]).remove(0))
        .collect();
    for (k, t) in made.iter().enumerate() {
        assert_eq!(t.to_string(), format!("SmallD({k})"));
        assert!(g.instance(vec![args[k].clone()])[0] == *t);
        for u in &made[k + 1..] {
            assert!(t != u, "{t} and {u}");
        }
    }
    let g = big("SmallS", 5);
    let first = g.instance(vec![Type::int()]).remove(0);
    for _ in 1..5 {
        assert!(g.instance(vec![Type::int()])[0] == first);
    }
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
/// TEST-bench-move-l0123 (author P169): was 16,000, now 256. What this guards is the size of
/// the text, not the stack: measured on the code of 2026-11-14, the `Debug` text of the chain
/// nests 93 brackets deep at 100 operands, 189 at 2,000 and 225 at 16,000 (the one form is
/// built over a tree of the operands), against 12,000 to 16,000 where the derived `Debug`s
/// overflowed the stack (see [`DEBUG_DEPTH`]). At 256 operands a `Debug` that writes a copy for
/// each path would write `2^256` copies, and the counts below still tell a text linear in the
/// operands from one that is not.
const XORS: usize = 256;

/// TEST-bench-move-l0123 (author P169): was 16,000 operands, now 256 (see [`XORS`]).
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

#[path = "deep_types/bench.rs"]
mod bench;

//! `print::written`: a term on one line with each binder by the name the program wrote and the
//! elaborated `&&` and `||` written back, for a message (NAME-at-print-warnings).

use zed_kernel::Term;
use zed_kernel::print::{pretty, written};
use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{Pattern, Prim, Value};

/// The part of a kernel name before `@`, as `zedc::elab::written_name` gives it.
pub(super) fn before_at(k: &str) -> &str {
    k.split_once('@').map_or(k, |(w, _)| w)
}

fn ge0(x: &str) -> Term {
    prim(Prim::Ge, vec![var(x), lit(0)])
}

/// Each place a binder is named is written through the function: a name read, a lambda's
/// parameters, a let's binder, the head of a call. A temporary `$k` has no `@` and stays.
#[test]
fn every_binder_is_named_through_the_function() {
    let t = let_(
        "g@1",
        lam(
            &["x@1", "y@1"],
            prim(Prim::Add, vec![var("x@1"), var("y@1")]),
        ),
        app(var("g@1"), vec![var("x@2"), var("$3")]),
    );
    assert_eq!(
        written(&t, before_at, &|_| true),
        "{ g = (x, y) -> (x + y); g(x, $3) }"
    );
    // Display is unchanged.
    assert_eq!(
        t.to_string(),
        "{ g@1 = (x@1, y@1) -> (x@1 + y@1); g@1(x@2, $3) }"
    );
}

/// `a && b` elaborates to `if a { b } else { false }` and `a || b` to `if a { true } else { b }`
/// (elab/walk.rs): written, each is the operator again, in parentheses as every binary
/// operator is. Any other `if` is written as it is, and `pretty` keeps the `if` form.
#[test]
fn the_elaborated_and_and_or_are_written_as_operators() {
    let and = if_(ge0("x@1"), ge0("y@2"), lit(false));
    assert_eq!(
        written(&and, before_at, &|_| true),
        "((x >= 0) && (y >= 0))"
    );
    let or = if_(ge0("x"), lit(true), ge0("y"));
    assert_eq!(written(&or, before_at, &|_| true), "((x >= 0) || (y >= 0))");
    let nested = if_(if_(ge0("a"), ge0("b"), lit(false)), lit(true), ge0("c"));
    assert_eq!(
        written(&nested, before_at, &|_| true),
        "(((a >= 0) && (b >= 0)) || (c >= 0))"
    );
    let other = if_(ge0("x"), lit(1), lit(0));
    assert_eq!(
        written(&other, before_at, &|_| true),
        "if (x >= 0) { 1 } else { 0 }"
    );
    assert_eq!(
        pretty(&and, usize::MAX),
        "if (x@1 >= 0) { (y@2 >= 0) } else { false }"
    );
}

/// `k` tests `v@i >= 0` joined by the elaborated `&&`, nested to the left or to the right.
pub(super) fn chain(k: usize, left: bool) -> Term {
    (1..k).fold(ge0("v@0"), |t, i| {
        let next = ge0(&format!("v@{i}"));
        if left {
            if_(t, next, lit(false))
        } else {
            if_(next, t, lit(false))
        }
    })
}

/// A chain of a few tests joined by `&&`, nested either way, is written with every `&&` and
/// each name renamed; `bench/written.rs` holds the timing of long chains.
#[test]
fn a_short_chain_of_and_is_written_with_each_operator() {
    for left in [true, false] {
        for k in [1, 2, 9] {
            let text = written(&chain(k, left), before_at, &|_| true);
            assert_eq!(text.matches("(v >= 0)").count(), k, "{text}");
            assert_eq!(text.matches(" && ").count(), k - 1, "{text}");
            assert!(!text.contains('@') && !text.contains("if"), "{text}");
        }
    }
    assert_eq!(
        written(&chain(3, true), before_at, &|_| true),
        "(((v >= 0) && (v >= 0)) && (v >= 0))"
    );
    assert_eq!(
        written(&chain(3, false), before_at, &|_| true),
        "((v >= 0) && ((v >= 0) && (v >= 0)))"
    );
}
/// A type test in a pattern writes `is T`, sec:grammar's `IsPat`, with its type as a program
/// writes it, the empty type as `Never` (DESIGN.md, the L1 row of "Defined words by layer"),
/// not in the kernel's prefix form, and the term reads back.
/// Before (item PRINT-is-pattern), each test stood in parentheses, `(is Never)`, which no
/// pattern of sec:grammar reads: a `TuplePat` has a comma.
#[test]
fn a_type_pattern_writes_its_type_in_type_syntax() {
    let small = &Type::int() - &Type::lit(&Value::Int(0)).expect("an int literal");
    let t = Term::Match(
        zed_tests::kernel::rc(var("v@1")),
        vec![
            (Pattern::Is(Type::empty()), lit("none")),
            (Pattern::Is(small), lit("nonzero")),
            (Pattern::Is(&Type::int() | &Type::bool()), lit("scalar")),
        ],
    );
    let shown = written(&t, before_at, &|_| true);
    assert_eq!(
        shown,
        "match v { is Never -> \"none\", is int \\ 0 -> \"nonzero\", \
         is int | bool -> \"scalar\" }"
    );
    assert!(!shown.contains("(|") && !shown.contains("(\\"), "{shown}");
    // `int \ 0` holds a literal type, a form of layer L10 that sec:grammar reads and this
    // zedc does not build yet, so the whole term is only parsed, and the term without that arm
    // is read back.
    let src = format!("x = {shown};\n");
    let tokens = zedc::lex::lex(&src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    zedc::parse::parse(&src, &tokens, "Unit", zedc::parse::TOP)
        .unwrap_or_else(|e| panic!("{src}: {e}"));
    let Term::Match(v, arms) = &t else {
        unreachable!()
    };
    let t = Term::Match(v.clone(), vec![arms[0].clone(), arms[2].clone()]);
    assert_eq!(
        reads_back(&t, &written(&t, before_at, &|_| true)),
        Seen {
            same: 2,
            ..Seen::default()
        }
    );
}

/// Item PRINT-group-site-defs: a part a type test writes twice is declared once, on a line of
/// its own before the term, as a user declares it, and the term after it uses the name. The
/// declaration and the term read back as a unit, and the type tested as `(T1, T1)`.
/// Before, the definition stood inside the pattern: `(is type T1 = int | #x; (T1, T1))`.
#[test]
fn a_part_a_type_test_writes_twice_is_declared_before_the_term() {
    let int_or_x = &Type::int() | &Type::atom("x");
    let pair = Type::tuple(vec![int_or_x.clone(), int_or_x]);
    let t = Term::Match(
        zed_tests::kernel::rc(var("v@1")),
        vec![
            (Pattern::Is(pair.clone()), lit("pair")),
            (Pattern::Wild, lit("other")),
        ],
    );
    let want = "type T1 = int | #x;\nmatch v { is (T1, T1) -> \"pair\", _ -> \"other\" }";
    assert_eq!(written(&t, before_at, &|_| true), want);
    assert_eq!(t.to_string(), want.replace("match v ", "match v@1 "));
    assert_eq!(reads_back(&t, want).same, 1);
}

/// A type test stands where a pattern ends: before an arm's `->`, a tuple's or a payload's `,`
/// and its `)`, after a field's `:`. A function type is parenthesized there, since `->` would
/// otherwise end the pattern; a union, an intersection and a difference are not.
#[test]
fn a_type_test_inside_other_patterns_reads_back() {
    let f = Type::exact(Type::int(), Type::bool());
    let t = Term::Match(
        zed_tests::kernel::rc(var("v@1")),
        vec![
            (Pattern::Is(f.clone()), lit("function")),
            (
                Pattern::Tuple(vec![
                    Pattern::Is(&Type::int() | &Type::bool()),
                    Pattern::Wild,
                ]),
                lit("pair"),
            ),
            (Pattern::Tuple(vec![Pattern::Is(f)]), lit("one")),
            (
                Pattern::Atom("ok".into(), vec![Pattern::Is(Type::string())]),
                lit("ok"),
            ),
            (
                Pattern::Fields(
                    "err".into(),
                    vec![("code".into(), Pattern::Is(&Type::int() - &Type::atom("x")))],
                ),
                lit("err"),
            ),
            (Pattern::Bind("w@2".into()), lit("other")),
        ],
    );
    let shown = written(&t, before_at, &|_| true);
    assert_eq!(
        shown,
        "match v { is (int -> bool) -> \"function\", (is int | bool, _) -> \"pair\", \
         (is (int -> bool),) -> \"one\", #ok(is String) -> \"ok\", #err(code: is int) -> \"err\", \
         w -> \"other\" }"
    );
    assert_eq!(
        reads_back(&t, &shown),
        Seen {
            same: 3,
            functions: 2,
            payloads: 0
        }
    );
}

/// The kernel's pattern for any atom, which `else` and `?.` elaborate to, and its pattern for the
/// empty tuple are written as the type tests `is #_` and `is ()`, sec:grammar's `IsPat` with the
/// `AtomType` `#_` and the `TupleType` `()`, at the top of an arm and inside a tuple, a payload
/// and a field, and each reads back as a type holding exactly the values the pattern matches.
/// Before (item PRINT-anyatom-pattern), they were written `#_` and `()`, which no pattern of
/// sec:grammar reads: `#_` is a type, not an `AtomPattern`, and a `TuplePat` has a comma.
#[test]
fn any_atom_and_empty_tuple_patterns_read_back() {
    let t = Term::Match(
        zed_tests::kernel::rc(var("v@1")),
        vec![
            (Pattern::AnyAtom, lit("failed")),
            (Pattern::Tuple(vec![]), lit("unit")),
            (
                Pattern::Tuple(vec![Pattern::AnyAtom, Pattern::Tuple(vec![])]),
                lit("pair"),
            ),
            (Pattern::Tuple(vec![Pattern::Tuple(vec![])]), lit("one")),
            (
                Pattern::Atom("ok".into(), vec![Pattern::AnyAtom]),
                lit("ok"),
            ),
            (
                Pattern::Fields("err".into(), vec![("code".into(), Pattern::Tuple(vec![]))]),
                lit("err"),
            ),
            (Pattern::Wild, lit("other")),
        ],
    );
    let shown = written(&t, before_at, &|_| true);
    assert_eq!(
        shown,
        "match v { is #_ -> \"failed\", is () -> \"unit\", (is #_, is ()) -> \"pair\", \
         (is (),) -> \"one\", #ok(is #_) -> \"ok\", #err(code: is ()) -> \"err\", \
         _ -> \"other\" }"
    );
    assert_eq!(
        reads_back(&t, &shown),
        Seen {
            same: 7,
            ..Seen::default()
        }
    );
}

/// Values of each kind, for comparing what a pattern matches with what a type holds: atoms with
/// and without payloads, the empty tuple and longer ones, and scalars.
fn samples() -> Vec<Value> {
    vec![
        Value::atom("a"),
        Value::atom_with("a", vec![Value::Int(1)]),
        Value::atom_with("b", vec![]),
        Value::atom_named("c", vec![("x".into(), Value::Int(2))]).expect("a field"),
        Value::tuple(vec![]),
        Value::tuple(vec![Value::tuple(vec![])]),
        Value::tuple(vec![Value::atom("a"), Value::Int(0)]),
        Value::Int(0),
        Value::Bool(true),
        Value::str(""),
    ]
}

/// Seeded random terms: a `match` of up to four arms whose patterns nest tuples, atoms with
/// payloads by position and by name, names, literals and `_` up to three deep, with type tests
/// of random types among them, parts shared between them declared before the term. Each
/// printed term reads back, at each of the seeds 15 to 30, and so does each type test drawn,
/// whatever the seed (READ-atom-meet: the test ran seed 15 alone, and at seed 19 a payload
/// meet read back wrong, at seed 20 it read 50 payload tests and wanted more than 50).
#[test]
fn random_terms_with_type_tests_read_back() {
    for seed in 15..=30 {
        let mut rng = zed_tests::instances::Rng::new(seed);
        let mut seed_seen = Seen::default();
        let mut drawn = 0;
        for _ in 0..zed_tests::instances::RANDOM_INSTANCES {
            let arms: Vec<(Pattern, Term)> = (0..1 + rng.below(4))
                .map(|i| {
                    let p = match i {
                        // At least one type test, at the top of an arm.
                        0 => Pattern::Is(random_type(&mut rng, 3)),
                        _ => random_pattern(&mut rng, 3),
                    };
                    (p, lit(format!("arm {i}").as_str()))
                })
                .collect();
            drawn += arms.iter().map(|(p, _)| type_tests(p)).sum::<usize>();
            let t = Term::Match(zed_tests::kernel::rc(var("v@1")), arms);
            let seen = reads_back(&t, &written(&t, before_at, &|_| true));
            seed_seen.same += seen.same;
            seed_seen.functions += seen.functions;
            seed_seen.payloads += seen.payloads;
        }
        // Every type test drawn is read back one of the three ways, and each way is taken:
        // over the seeds 0 to 63 the fewest of a seed were 410, 228 and 44.
        let Seen {
            same,
            functions,
            payloads,
        } = seed_seen;
        assert_eq!(
            same + functions + payloads,
            drawn,
            "seed {seed}: {seed_seen:?}"
        );
        assert!(
            same > 0 && functions > 0 && payloads > 0,
            "seed {seed}: {seed_seen:?}"
        );
    }
}

/// How many type tests the pattern `p` holds, at any depth.
fn type_tests(p: &Pattern) -> usize {
    match p {
        Pattern::Is(_) => 1,
        Pattern::Atom(_, ps) | Pattern::Tuple(ps) => ps.iter().map(type_tests).sum(),
        Pattern::Fields(_, fs) => fs.iter().map(|(_, p)| type_tests(p)).sum(),
        Pattern::Wild | Pattern::Bind(_) | Pattern::Lit(_) | Pattern::AnyAtom => 0,
    }
}

/// A random pattern `d` deep, a type test one time in three.
fn random_pattern(rng: &mut zed_tests::instances::Rng, d: usize) -> Pattern {
    let leaf = d == 0 || rng.below(3) == 0;
    match rng.below(if leaf { 4 } else { 7 }) {
        0 => Pattern::Wild,
        1 => Pattern::Bind(["a@1", "b@2", "c@3"][rng.below(3)].into()),
        2 => Pattern::Lit(Value::Int(rng.int(-3, 3))),
        3 => Pattern::Is(random_type(rng, d)),
        4 => Pattern::Tuple(
            (0..1 + rng.below(3))
                .map(|_| random_pattern(rng, d - 1))
                .collect(),
        ),
        5 => Pattern::Atom(
            ["p", "q"][rng.below(2)].into(),
            (0..rng.below(3))
                .map(|_| random_pattern(rng, d - 1))
                .collect(),
        ),
        _ => Pattern::Fields(
            "r".into(),
            ["f", "g"][..1 + rng.below(2)]
                .iter()
                .map(|&k| (k.into(), random_pattern(rng, d - 1)))
                .collect(),
        ),
    }
}

/// Seeded random terms: a `match` of up to four arms whose patterns nest the any-atom pattern,
/// the empty tuple, other tuples, atoms with payloads by position and by name, names and `_` up
/// to three deep. Each printed term reads back, each `is #_` and `is ()` as a type holding the
/// values its pattern matches. The type tests of random types are left to the test above.
#[test]
fn random_terms_with_any_atom_and_empty_tuple_patterns_read_back() {
    let mut rng = zed_tests::instances::Rng::new(16);
    let mut same = 0;
    for _ in 0..zed_tests::instances::RANDOM_INSTANCES {
        let arms = (0..1 + rng.below(4))
            .map(|i| {
                let p = match i {
                    // At least one of the two, at the top of an arm.
                    0 if rng.below(2) == 0 => Pattern::AnyAtom,
                    0 => Pattern::Tuple(vec![]),
                    _ => random_kind_pattern(&mut rng, 3),
                };
                (p, lit(format!("arm {i}").as_str()))
            })
            .collect();
        let t = Term::Match(zed_tests::kernel::rc(var("v@1")), arms);
        same += reads_back(&t, &written(&t, before_at, &|_| true)).same;
    }
    // Each instance has at least one.
    assert!(same >= zed_tests::instances::RANDOM_INSTANCES, "{same}");
}

/// A random pattern `d` deep with no type test, the any-atom pattern or the empty tuple one
/// time in two at a leaf.
fn random_kind_pattern(rng: &mut zed_tests::instances::Rng, d: usize) -> Pattern {
    let leaf = d == 0 || rng.below(3) == 0;
    match rng.below(if leaf { 4 } else { 7 }) {
        0 => Pattern::AnyAtom,
        1 => Pattern::Tuple(vec![]),
        2 => Pattern::Wild,
        3 => Pattern::Bind(["a@1", "b@2", "c@3"][rng.below(3)].into()),
        4 => Pattern::Tuple(
            (0..1 + rng.below(3))
                .map(|_| random_kind_pattern(rng, d - 1))
                .collect(),
        ),
        5 => Pattern::Atom(
            ["p", "q"][rng.below(2)].into(),
            (0..1 + rng.below(2))
                .map(|_| random_kind_pattern(rng, d - 1))
                .collect(),
        ),
        _ => Pattern::Fields(
            "r".into(),
            ["f", "g"][..1 + rng.below(2)]
                .iter()
                .map(|&k| (k.into(), random_kind_pattern(rng, d - 1)))
                .collect(),
        ),
    }
}

/// A random type `d` deep, of the forms of l01_22's random types but literal types, which the
/// reader does not take yet: scalars, atoms with and without payload, tuples, functions total
/// and partial, and the three connectives.
fn random_type(rng: &mut zed_tests::instances::Rng, d: usize) -> Type {
    if d == 0 || rng.below(4) == 0 {
        return match rng.below(5) {
            0 => Type::int(),
            1 => Type::string(),
            2 => Type::bool(),
            3 => Type::atom(["a", "b"][rng.below(2)]),
            _ => Type::empty(),
        };
    }
    let form = rng.below(8);
    let mut part = || random_type(rng, d - 1);
    match form {
        0 => Type::tuple(vec![part(), part()]),
        1 => Type::tuple(vec![part()]),
        2 => Type::atom_with("a", &Type::tuple(vec![part()])),
        3 => Type::exact(part(), part()),
        4 => Type::partial(part(), part()),
        5 => &part() | &part(),
        6 => &part() & &part(),
        _ => &part() - &part(),
    }
}

/// `text`, the term `t` written with the declarations of its shared parts on the lines before
/// it, read back as the definition `x = …;` of a unit: it parses, has an arm for each arm of the
/// `match` `t`, each pattern of the shape of `t`'s, and each type test's type, read with the
/// declarations, is the type `t` tests: the same set of values; for a type that holds some
/// functions and not others, a type that reads back as itself; for a type with an atom with a
/// payload, a type within the kernel's that reads back as itself. Returns how many type tests
/// were read each way.
#[track_caller]
fn reads_back(t: &Term, text: &str) -> Seen {
    let mut seen = Seen::default();
    use zedc::ast::{ExprKind, Pattern as Read, StmtKind};
    let Term::Match(_, arms) = t else {
        panic!("{text}: not a match")
    };
    let decls = text.rsplit_once('\n').map_or("", |(d, _)| d);
    let decls = if decls.is_empty() {
        String::new()
    } else {
        format!("{decls}\n")
    };
    let term = &text[decls.len()..];
    let src = format!("{decls}x = {term};\n");
    let tokens = zedc::lex::lex(&src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let tree = zedc::parse::parse(&src, &tokens, "Unit", zedc::parse::TOP)
        .unwrap_or_else(|e| panic!("{src}: {e}"));
    let stmts = zedc::ast::unit(&src, &tokens, &tree).unwrap_or_else(|e| panic!("{src}: {e}"));
    let value = (stmts.iter())
        .find_map(|s| match &s.kind {
            StmtKind::Bind { value, .. } => Some(value),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{src}: no definition"));
    let ExprKind::Match { arms: read, .. } = &value.kind else {
        panic!("{src}: not read as a match")
    };
    assert_eq!(read.len(), arms.len(), "{src}");
    let mut todo: Vec<(&Pattern, &Read)> = (arms.iter().zip(read))
        .map(|((p, _), a)| (p, &a.pattern))
        .collect();
    while let Some((p, q)) = todo.pop() {
        match (p, q) {
            (Pattern::Wild, Read::Wild(_)) => {}
            (Pattern::Bind(x), Read::Name(n, _)) => assert_eq!(before_at(x), n, "{src}"),
            (Pattern::Lit(v), Read::Lit(e)) => {
                assert_eq!(&src[e.span.start..e.span.end], v.to_string(), "{src}")
            }
            (Pattern::Tuple(ps), Read::Tuple(qs, _)) if ps.len() == qs.len() => {
                todo.extend(ps.iter().zip(qs))
            }
            (
                Pattern::Atom(name, ps),
                Read::Atom {
                    name: n,
                    fields,
                    items,
                    ..
                },
            ) if **name == *n && fields.is_empty() && ps.len() == items.len() => {
                todo.extend(ps.iter().zip(items))
            }
            (
                Pattern::Fields(name, fs),
                Read::Atom {
                    name: n,
                    fields,
                    items,
                    ..
                },
            ) if **name == *n && items.is_empty() && fs.len() == fields.len() => {
                for ((k, p), (m, q)) in fs.iter().zip(fields) {
                    assert_eq!(**k, *m, "{src}");
                    todo.push((p, q.as_ref().unwrap_or_else(|| panic!("{src}: `{m}:`"))));
                }
            }
            (
                Pattern::Is(ty),
                Read::Is {
                    name: None, ty: r, ..
                },
            ) => {
                let part = format!("{decls}{}", &src[r.span.start..r.span.end]);
                let back = zedc::check::read::parse_type(&part)
                    .unwrap_or_else(|e| panic!("{src}: `{part}`: {e}"));
                // An atom with a payload, `#a(T)`: the checker's set holds it with any
                // payload, and its payload apart, so the type read is within the kernel's but
                // the kernel's is not found within it (l01_22 `kinds` leaves such atoms out).
                let payload = (part.split('#').skip(1)).any(|s| {
                    s.trim_start_matches(|c: char| c.is_alphanumeric() || c == '_')
                        .starts_with('(')
                });
                let want = zedc::check::ty::Ty::set(ty.clone());
                if ty.decidable() && !payload {
                    assert!(
                        back.subtype(&want) && want.subtype(&back),
                        "{src}: `{part}` reads back as {back}"
                    );
                    seen.same += 1;
                    continue;
                }
                if ty.decidable() {
                    assert!(back.subtype(&want), "{src}: `{part}` reads back as {back}");
                    // With its payloads read, the type read is the kernel's set, where it has a
                    // kernel type (READ-atom-meet: `#a(bool) & #a(int)` read as `#a(bool)`, and
                    // `#a(#a(int)) \ #a((int,))` as `Never`).
                    if let Some(k) = back.exact_kernel() {
                        assert!(k.equiv(ty), "{src}: `{part}` reads back as {back}");
                    }
                    seen.payloads += 1;
                } else {
                    // A type that holds some functions and not others reads back as the
                    // checker's own function type, not as the kernel's set (l01_22 `kinds`).
                    seen.functions += 1;
                }
                // Either way the type read is read again from its own text, which must give
                // that text.
                let text = back.to_string();
                let again = zedc::check::read::parse_type(&text)
                    .unwrap_or_else(|e| panic!("{src}: `{part}` read as {text}: {e}"));
                assert_eq!(again.to_string(), text, "{src}: `{part}`");
            }
            // `is #_` and `is ()`: the kernel's any-atom and empty-tuple patterns, which no
            // other pattern of sec:grammar reads (item PRINT-anyatom-pattern).
            (
                Pattern::AnyAtom | Pattern::Tuple(_),
                Read::Is {
                    name: None, ty: r, ..
                },
            ) => {
                let want = match p {
                    Pattern::AnyAtom => zedc::check::ty::atoms(),
                    _ => Type::tuple(vec![]),
                };
                let part = format!("{decls}{}", &src[r.span.start..r.span.end]);
                let back = zedc::check::read::parse_type(&part)
                    .unwrap_or_else(|e| panic!("{src}: `{part}`: {e}"));
                let set = zedc::check::ty::Ty::set(want);
                assert!(
                    back.subtype(&set) && set.subtype(&back),
                    "{src}: `{part}` reads back as {back}"
                );
                // The type read holds exactly the values the kernel's pattern matches.
                let kernel = back.kernel().unwrap_or_else(|| panic!("{src}: {back}"));
                for v in samples() {
                    let t = Term::Match(
                        zed_tests::kernel::rc(Term::Lit(v.clone())),
                        vec![(p.clone(), lit(true)), (Pattern::Wild, lit(false))],
                    );
                    let hit = zed_kernel::eval::eval(&t).expect("a match on a value");
                    assert_eq!(hit, Value::Bool(kernel.contains(&v)), "{src}: `{p}` at {v}");
                }
                seen.same += 1;
            }
            _ => panic!("{src}: the pattern `{p}` reads back as {q}"),
        }
    }
    seen
}

/// How many type tests [`reads_back`] read as the same set, as a type that holds some functions
/// and not others, and as a type with an atom with a payload.
#[derive(Default, Debug, PartialEq, Eq)]
struct Seen {
    same: usize,
    functions: usize,
    payloads: usize,
}

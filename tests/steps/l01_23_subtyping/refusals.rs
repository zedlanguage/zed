//! Refusals: a check the strict search does not decide, and for which no value is found, is
//! refused with its cause, and claims nothing about the type. A value is sought before any
//! refusal, so an inhabited type is never refused when a value is in reach. Each cause has its
//! own message, and the checker adds it to a message that a type is not within another, so a
//! refusal never reads as a counterexample. Equal plain definitions of different groups are
//! one type.

use std::collections::BTreeSet;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

use zed_kernel::Value;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Refusal, Type, Verdict};
use zed_tests::scaling;
use zedc::check::ty::Ty;

fn r(i: usize) -> Expr {
    Expr::Ref(i, vec![])
}

fn cons(head: Expr, tail: Expr) -> Expr {
    Expr::Atom("cons".into(), vec![head, tail])
}

fn int() -> Expr {
    Expr::Type(Type::int())
}

fn nil() -> Expr {
    Expr::Type(Type::atom("nil"))
}

fn lit(i: i64) -> Type {
    Type::lit(&Value::Int(i)).unwrap()
}

fn def(name: &str, body: Expr) -> Def {
    Def {
        name: name.into(),
        params: vec![],
        body,
    }
}

/// The lists of elements of `head`.
fn list(head: Type) -> Type {
    let body = Expr::Union(vec![nil(), cons(Expr::Type(head), r(0))]);
    Group::new(vec![def("L", body)])
        .unwrap()
        .instance(vec![])
        .remove(0)
}

/// The lists of integers whose length is `k` modulo `p`: `P{i}` has `k - i` modulo `p`.
fn period(p: usize, k: usize) -> Type {
    let defs = (0..p)
        .map(|i| {
            let body = cons(int(), r((i + 1) % p));
            let body = if i == k {
                Expr::Union(vec![nil(), body])
            } else {
                body
            };
            def(&format!("P{i}"), body)
        })
        .collect();
    Group::new(defs).unwrap().instance(vec![]).remove(0)
}

/// The lists of integers whose length is in none of the classes `(period, at)`.
fn lengths_outside(classes: &[(usize, usize)]) -> Type {
    classes
        .iter()
        .fold(list(Type::int()), |t, &(p, k)| &t - &period(p, k))
}

/// No length is 0 modulo 2 or 3, or 1 or 5 modulo 6: the even lengths are 0 modulo 2 and the
/// odd ones 0, 1 or 2 modulo 3, so the type is empty. The shares sum to more than one, and a
/// split on the prime 2 decides it.
fn residues_cover() -> Type {
    lengths_outside(&[(2, 0), (3, 0), (6, 1), (6, 5)])
}

/// Without the class 5 modulo 6, a length 5 is left; the shares sum to one and two classes
/// meet at 0, so a length is left.
fn residues_left() -> Type {
    lengths_outside(&[(2, 0), (3, 0), (6, 1)])
}

/// Erdős's covering system, 0 modulo 2, 0 modulo 3, 1 modulo 4, 5 modulo 6 and 7 modulo 12,
/// covers every length, so the type is empty; no split on one prime decides it.
fn erdos_cover() -> Type {
    lengths_outside(&[(2, 0), (3, 0), (4, 1), (6, 5), (12, 7)])
}

/// Pairs of a list of integers and an integer, without those whose list holds only 1s or only
/// 2s: following both excluded lists is the subset construction, but `([0], 0)` is in it.
fn fork() -> Type {
    let pair = |l: Type| Type::tuple(vec![l, Type::int()]);
    &(&pair(list(Type::int())) - &pair(list(lit(1)))) - &pair(list(lit(2)))
}

/// Pairs of lists of integers, without those whose first list holds only 1s and whose second
/// has an even length, those whose first holds only 2s and whose second has an odd length, and
/// the rest of each: empty, but the excluded first lists meet at `[]` and differ, so following
/// them is the subset construction.
fn fork_empty() -> Type {
    let l = list(Type::int());
    let pair = |a: Type, b: Type| Type::tuple(vec![a, b]);
    let (ones, twos) = (list(lit(1)), list(lit(2)));
    [
        pair(ones.clone(), period(2, 0)),
        pair(twos.clone(), period(2, 1)),
        pair(&l - &ones, period(2, 0)),
        pair(&l - &twos, period(2, 1)),
    ]
    .iter()
    .fold(pair(l.clone(), l.clone()), |t, x| &t - x)
}

/// The lists of integers against those with a 1 at place 1 or 2 from the end, one further on,
/// or none: empty, but the decision would follow both places at once.
fn nfa() -> Type {
    &list_named(Type::int(), "_nfa") - &by_place_from_the_end(2, None, "_nfa")
}

/// The integers 1, 2 and 3 named by the bits of `m`.
fn small(m: u8) -> Type {
    (1..=3)
        .filter(|i| m >> (i - 1) & 1 == 1)
        .fold(Type::empty(), |t, i| &t | &lit(i))
}

/// Triples of 1, 2 and 3 less seven boxes that cover them: on each component the boxes' sets
/// meet without being equal, so no split of one component into disjoint pieces fits them, and
/// narrowing one piece at a time proves none empty. Whether boxes cover a product is the
/// tautology problem for formulas in disjunctive normal form, which is coNP-hard.
fn box_cover() -> Type {
    let boxes = [
        [3, 3, 3],
        [5, 5, 5],
        [6, 3, 5],
        [6, 4, 5],
        [4, 3, 6],
        [5, 6, 3],
        [3, 6, 6],
    ];
    boxes.iter().fold(Type::tuple(vec![small(7); 3]), |t, b| {
        &t - &Type::tuple(b.iter().map(|&m| small(m)).collect())
    })
}

/// The pinwheel: four boxes around the middle square of 1, 2 and 3 squared, each meeting two
/// others. Without the middle square the type holds `(2, 2)` alone, which only splitting
/// both components finds.
fn pinwheel(middle: bool) -> Type {
    let mut boxes = vec![[3, 1], [4, 3], [6, 4], [1, 6]];
    if middle {
        boxes.push([2, 2]);
    }
    boxes.iter().fold(Type::tuple(vec![small(7); 2]), |t, b| {
        &t - &Type::tuple(b.iter().map(|&m| small(m)).collect())
    })
}

fn morphism(result: Type) -> Type {
    Type::morphism(Type::empty(), Type::top(), result)
}

/// The morphisms into `int` that are neither into 1 nor into the other integers. It holds a
/// family with a key at 1 and one at 2, but a family is not checked against a morphism type
/// before L2, so no value is shown.
fn morphism_split() -> Type {
    &morphism(Type::int()) - &(&morphism(lit(1)) | &morphism(&Type::int() - &lit(1)))
}

/// The morphisms that must take 1 and may take any integer, into the integers. The identity
/// on the integers is one, but a closure is shown only for a type whose keys are all
/// permitted as written, and a family is not checked against a morphism type before L2.
fn morphism_between() -> Type {
    Type::morphism(lit(1), Type::int(), Type::int())
}

#[test]
fn each_refusal_names_its_cause() {
    for (t, why) in [
        (erdos_cover(), Refusal::Residues),
        (fork_empty(), Refusal::Fork),
        (nfa(), Refusal::Fork),
        (morphism_split(), Refusal::MorphismSplit),
        (box_cover(), Refusal::TupleSplit),
        (morphism_between(), Refusal::NoWitness),
    ] {
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Refused(why), "{t}");
    }
    // Decided checks of the same kinds.
    assert_eq!(
        (&period(2, 0) - &period(4, 0)).verdict(),
        Verdict::Inhabited
    );
    let both = &morphism(lit(1)) & &morphism(lit(2));
    assert_eq!((&both - &morphism(Type::empty())).verdict(), Verdict::Empty);
}

#[test]
fn a_value_is_sought_before_a_refusal() {
    Type::forget_emptiness();
    // The search stops at the fork, and the search for a value after it finds `([0], 0)`; the
    // lengths left by three classes hold 5, which is built.
    assert_eq!(fork().verdict(), Verdict::Inhabited);
    assert_eq!(residues_left().verdict(), Verdict::Inhabited);
    assert!(!residues_left().is_empty());
    // Only both splits find `(2, 2)`; the five boxes cover the square.
    assert_eq!(pinwheel(false).verdict(), Verdict::Inhabited);
    assert_eq!(pinwheel(true).verdict(), Verdict::Empty);
    // A pair of a list of odd length and an integer holds `([0], 0)`.
    let odd = Type::tuple(vec![period(2, 1), Type::int()]);
    assert_eq!(odd.verdict(), Verdict::Inhabited);
}

#[test]
fn covering_residues_are_decided_by_a_split_on_one_prime() {
    Type::forget_emptiness();
    assert_eq!(residues_cover().verdict(), Verdict::Empty);
    assert!(residues_cover().is_empty());
    // Each class left out of the cover leaves some lengths: 2, 3, 1 and 5.
    let cover = [(2, 0), (3, 0), (6, 1), (6, 5)];
    for i in 0..cover.len() {
        let mut classes = cover.to_vec();
        classes.remove(i);
        assert_eq!(
            lengths_outside(&classes).verdict(),
            Verdict::Inhabited,
            "{classes:?}"
        );
    }
}

#[test]
fn each_refusal_has_its_own_message() {
    let all = [
        Refusal::Fork,
        Refusal::Residues,
        Refusal::TupleSplit,
        Refusal::SharedCells(0),
        Refusal::MorphismSplit,
        Refusal::NoWitness,
    ];
    let messages: BTreeSet<String> = all.iter().map(|r| r.message()).collect();
    assert_eq!(messages.len(), all.len());
    assert!(messages.iter().all(|m| !m.is_empty()));
}

#[test]
fn the_checker_says_when_a_check_was_refused() {
    // Erdős's cover holds every list, but no split on one prime shows it.
    let lists = Ty::set(list(Type::int()));
    let cover = [(2, 0), (3, 0), (4, 1), (6, 5), (12, 7)].map(|(p, k)| period(p, k));
    let covered = Ty::set(Type::union_all(cover));
    assert!(!lists.subtype(&covered));
    assert_eq!(
        lists.refused(&covered),
        format!(
            "; this is not proved wrong: the checker could not decide whether it fits, because {}",
            Refusal::Residues.message()
        )
    );
    // The cover by 0 modulo 2 or 3 and 1 or 5 modulo 6 is decided, and holds.
    let cover = [period(2, 0), period(3, 0), period(6, 1), period(6, 5)];
    assert!(lists.subtype(&Ty::set(Type::union_all(cover))));
    // A decided failure adds nothing.
    let (ints, one) = (Ty::set(Type::int()), Ty::set(lit(1)));
    assert!(!ints.subtype(&one));
    assert_eq!(ints.refused(&one), "");
}

#[test]
fn equal_plain_definitions_of_different_groups_are_one_type() {
    // `R1` is on no cycle and names only plain definitions, so it is built as its body: the
    // lists of exactly one integer, the same type in both groups.
    let a = Group::new(vec![def("R0", nil()), def("R1", cons(int(), r(0)))])
        .unwrap()
        .instance(vec![]);
    let b = Group::new(vec![
        def("L", Expr::Union(vec![nil(), cons(int(), r(0))])),
        def("S0", nil()),
        def("S1", cons(int(), r(1))),
    ])
    .unwrap()
    .instance(vec![]);
    assert_eq!(a[1], b[2]);
    assert_eq!(a[0], b[1]);
    assert!(a[1].subtype(&b[0]) && !b[0].subtype(&a[1]));
}

/// `g` takes the triples of seven boxes, which cover every triple of `#a`, `#b` and `#c` only
/// together; without the last box, `(#c, #a, #b)` is outside them.
fn box_program(boxes: usize) -> String {
    let all = [
        "(#a | #b, #a | #b, #a | #b)",
        "(#a | #c, #a | #c, #a | #c)",
        "(#b | #c, #a | #b, #a | #c)",
        "(#b | #c, #c, #a | #c)",
        "(#c, #a | #b, #b | #c)",
        "(#a | #c, #b | #c, #a | #b)",
        "(#a | #b, #b | #c, #b | #c)",
    ];
    format!(
        "g(x: {}) = x;\nh(y: (#a | #b | #c, #a | #b | #c, #a | #b | #c)) = g(x: y);\nmain() = 0;\n",
        all[..boxes].join(" | ")
    )
}

/// The first line of the diagnostics of `src`, which must be rejected.
fn rejected(src: &str) -> String {
    match zedc::run::load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e.lines().next().unwrap_or_default().to_string(),
    }
}

#[test]
fn a_call_whose_check_was_refused_says_why() {
    let triple = "(#a | #b | #c, #a | #b | #c, #a | #b | #c)";
    assert_eq!(
        rejected(&box_program(7)),
        format!(
            "2:52: `g` does not take ({triple}); this is not proved wrong: the checker could not \
             decide whether it fits, because {}",
            Refusal::TupleSplit.message()
        )
    );
    // A decided failure names no cause.
    assert_eq!(
        rejected(&box_program(6)),
        format!(
            "2:52: `g` does not take ({triple}): these are the types of its arguments here, and `g` has no arrow that takes them all"
        )
    );
    // The declared type is printed as it is written.
    let Err(all) = zedc::run::load(box_program(7).as_bytes()) else {
        panic!("accepted")
    };
    assert!(
        all.contains(&format!("`y` is declared `{triple}`")),
        "{all}"
    );
}

#[test]
fn a_tuple_that_shapes_hold_only_together_is_taken() {
    // No one shape holds `(#a | #b, #c)`, and the kernel decides that the two do.
    let src = "g(x: (#a, #c) | (#b, #c)) = x;\nh(y: (#a | #b, #c)) = g(x: y);\nmain() = 0;\n";
    assert!(zedc::run::load(src.as_bytes()).is_ok(), "{src}");
    let src = "g(x: ((#a, #c) | (#b, #c),)) = x;\nh(y: ((#a | #b, #c),)) = g(x: y);\nmain() = 0;\n";
    assert!(zedc::run::load(src.as_bytes()).is_ok(), "{src}");
    let src = "g(x: (#a, #c) | (#b, #c)) = x;\nh(y: (#a | #b | #c, #c)) = g(x: y);\nmain() = 0;\n";
    assert_eq!(
        rejected(src),
        "2:28: `g` does not take ((#a | #b | #c, #c)): these are the types of its arguments here, and `g` has no arrow that takes them all"
    );
}

#[test]
fn a_morphism_type_whose_bound_check_was_refused_says_why() {
    // A function into `#a | #b` that gives both is in neither union member, but the kernel
    // shows no family against a morphism type before L2, and splits no function part. The
    // `is` is an error of its own: the bound check no longer stops elaboration of the type.
    let src = "f(x) = x is ((int -> #a | #b) .. ((int -> #a) | (int -> #b)) -> int);";
    assert_eq!(
        zed_tests::step_helpers::l01_16_elaboration::errors(src),
        [
            "`is` tests a value against a type when the program runs, and a function value does not show its type then. Test against a type that is not a function type, or remove the `is`. \
             [((int -> #a | #b) .. ((int -> #a) | (int -> #b)) -> int)]"
                .to_string(),
            format!(
                "in a function type `L .. U -> V`, every function the guarantee `L`, left of \
                 `..`, describes must also be allowed by the permission `U`, right of `..`, and \
                 the checker could not show that this one's guarantee is within its permission; \
                 this is not proved wrong: the checker could not decide whether it fits, because \
                 {}. To repair it, narrow the type left of `..`, or widen the type right of it \
                 [((int -> #a | #b) .. ((int -> #a) | (int -> #b)) -> int)]",
                Refusal::MorphismSplit.message()
            )
        ]
    );
}

/// The errors of the operator `op` applied to `args`, through the checker's `apply`.
fn operator_errors(op: &str, args: &[Ty]) -> Vec<String> {
    zedc::check::walk::operator(op, args).1
}

#[test]
fn an_overload_whose_check_was_refused_says_why() {
    // No source program reaches these paths with a refused check: the arrows of operators
    // and prelude words take carriers, and the checker's own types hold no difference of
    // tuples. The kernel types are given to the checker's `apply` directly. `neg`, `+` and
    // `<` have several arrows, `!` one. The seven-box cover's emptiness is refused
    // (`TupleSplit`); the six-box cover is inhabited, so its checks are decided.
    let cover6 = [
        [3, 3, 3],
        [5, 5, 5],
        [6, 3, 5],
        [6, 4, 5],
        [4, 3, 6],
        [5, 6, 3],
    ]
    .iter()
    .fold(Type::tuple(vec![small(7); 3]), |t, b| {
        &t - &Type::tuple(b.iter().map(|&m| small(m)).collect())
    });
    for (op, n) in [("neg", 1), ("+", 2), ("<", 2), ("!", 1)] {
        for (t, why) in [
            // No arrow meets the argument ...
            (box_cover(), Some(Refusal::TupleSplit)),
            (morphism_between(), Some(Refusal::NoWitness)),
            // ... and an arrow meets it and does not take it. The one arrow of `!` takes
            // `bool`, and `int` is a decided witness against it.
            (
                &box_cover() | &Type::int(),
                (op != "!").then_some(Refusal::TupleSplit),
            ),
            (cover6.clone(), None),
            (&cover6 | &Type::int(), None),
        ] {
            Type::forget_emptiness();
            let errors = operator_errors(op, &vec![Ty::set(t.clone()); n]);
            let first = errors.first().unwrap_or_else(|| panic!("`{op}` took {t}"));
            assert!(
                first.starts_with(&format!("`{op}` does not take (")),
                "{first}"
            );
            match why {
                Some(r) => {
                    let tail = format!(
                        "; this is not proved wrong: the checker could not decide whether it \
                         fits, because {}",
                        r.message()
                    );
                    assert!(first.ends_with(&tail), "{op} on {t}: {first}");
                }
                None => assert!(
                    !first.contains("this is not proved wrong"),
                    "{op} on {t}: {first}"
                ),
            }
        }
    }
}

#[test]
fn a_literal_argument_and_a_need_result_name_no_cause_when_decided() {
    // A literal's check is of a scalar against the parameter, whose tuple and morphism parts
    // it does not meet: it is always decided, so no refused input reaches this path.
    assert_eq!(
        rejected("g(x: #a | (int, int)) = x;\nmain() = g(x: 1);\n"),
        "2:10: `g` does not take (1): these are the types of its arguments here, and `g` has no arrow that takes them all"
    );
    // What a use of an argument gives against what the use needs: decided here. The
    // checker's own types hold no difference of tuples (a written `\` of tuples is dropped
    // from them), so no refused check reaches this path from a program.
    assert_eq!(
        rejected("f(x) = x[1] + 1;\nmain() = f(x: (1, \"s\"));\n"),
        "2:10: `f` gives \"s\" here, which is not int: the use requires a value of int"
    );
}

#[test]
fn a_cofinite_set_of_rationals_or_floats_has_a_value() {
    // Each carrier's cofinite set shows a value outside the ones it lists, so a number of one
    // kind is decided not to be of another: `f64 <: rat` failed with `NoWitness` before.
    let zero_r = Type::lit(&Value::rat(zed_kernel::Rat::int(0.into()))).unwrap();
    let zero_f = Type::lit(&Value::float(0.0)).unwrap();
    for (a, b) in [
        (Type::f64(), Type::int()),
        (Type::f64(), Type::rat()),
        (Type::rat(), Type::int()),
        (Type::rat(), Type::f64()),
        (Type::rat(), zero_r.clone()),
        (Type::f64(), zero_f.clone()),
        (&Type::rat() - &zero_r, Type::f64()),
        (&Type::f64() - &zero_f, Type::rat()),
    ] {
        Type::forget_emptiness();
        assert_eq!(a.subtype_verdict(&b), Verdict::Inhabited, "{a} <: {b}");
    }
}

#[test]
fn an_overload_rejected_by_a_decided_check_names_no_cause() {
    // The first argument's check is refused against every arrow, but the second is decided not
    // to be of any arrow's parameter, so the rejection rests on no refusal.
    for op in ["+", "*"] {
        Type::forget_emptiness();
        let errors = operator_errors(op, &[Ty::set(box_cover()), Ty::set(Type::bool())]);
        let first = errors.first().unwrap_or_else(|| panic!("`{op}` took it"));
        assert!(
            first.starts_with(&format!("`{op}` does not take (")),
            "{first}"
        );
        assert!(!first.contains("this is not proved wrong"), "{first}");
    }
}

// Scaling of each refusal cause (REFUSAL-cost). Each run names its groups apart and forgets
// the answers kept, so no run reads another's.

/// The lists of elements of `head`, its group named by `tag`.
fn list_named(head: Type, tag: &str) -> Type {
    let body = Expr::Union(vec![nil(), cons(Expr::Type(head), r(0))]);
    Group::new(vec![def(&format!("L{tag}"), body)])
        .unwrap()
        .instance(vec![])
        .remove(0)
}

/// [`period`] with its group named by `tag`.
fn period_named(p: usize, k: usize, tag: &str) -> Type {
    let defs = (0..p)
        .map(|i| {
            let body = cons(int(), r((i + 1) % p));
            let body = if i == k {
                Expr::Union(vec![nil(), body])
            } else {
                body
            };
            def(&format!("P{i}{tag}"), body)
        })
        .collect();
    Group::new(defs).unwrap().instance(vec![]).remove(0)
}

/// The Erdős cover of [`erdos_cover`], each class written `n` times in groups of its own.
fn erdos_cover_repeated(n: usize, tag: &str) -> Type {
    let classes = [(2, 0), (3, 0), (4, 1), (6, 5), (12, 7)];
    (0..n).fold(list_named(Type::int(), tag), |t, j| {
        classes.iter().fold(t, |t, &(p, k)| {
            &t - &period_named(p, k, &format!("{tag}_{j}"))
        })
    })
}

/// `n` copies of [`box_cover`] over disjoint values, joined.
fn box_covers(n: usize) -> Type {
    let boxes = [
        [3, 3, 3],
        [5, 5, 5],
        [6, 3, 5],
        [6, 4, 5],
        [4, 3, 6],
        [5, 6, 3],
        [3, 6, 6],
    ];
    let at = |m: u8, base: i64| {
        (1..=3)
            .filter(|i| m >> (i - 1) & 1 == 1)
            .fold(Type::empty(), |t, i| &t | &lit(base + i))
    };
    (0..n).fold(Type::empty(), |u, j| {
        let base = 3 * j as i64;
        let t = boxes
            .iter()
            .fold(Type::tuple(vec![at(7, base); 3]), |t, b| {
                &t - &Type::tuple(b.iter().map(|&m| at(m, base)).collect())
            });
        &u | &t
    })
}

/// [`morphism_split`] over 1 to `n`: morphisms into `int` in none of those into one of them
/// and that into the other integers.
fn morphism_split_by(n: usize) -> Type {
    let lits = (1..=n as i64).fold(Type::empty(), |t, i| &t | &lit(i));
    let parts = (1..=n as i64).fold(morphism(&Type::int() - &lits), |t, i| {
        &t | &morphism(lit(i))
    });
    &morphism(Type::int()) - &parts
}

/// [`morphism_between`] over 1 to `n`: morphisms that must take 1 to `n`.
fn morphism_between_by(n: usize) -> Type {
    let lits = (1..=n as i64).fold(Type::empty(), |t, i| &t | &lit(i));
    Type::morphism(lits, Type::int(), Type::int())
}

/// Runs `scaling::check` on the verdict of `make(n, tag)`, which must be refused for `cause`.
fn refusal_scales(
    what: &str,
    n: usize,
    cause: Refusal,
    make: impl Fn(usize, &str) -> Type + Sync + Send,
) {
    big(move || {
        let tag = AtomicUsize::new(0);
        scaling::check(what, n, |n| {
            Type::forget_emptiness();
            let tag = format!("_rc{}", tag.fetch_add(1, Relaxed));
            assert_eq!(
                make(n, &tag).verdict(),
                Verdict::Refused(cause),
                "{what} at {n}"
            );
        })
    });
}

fn big(f: impl FnOnce() + Send) {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 28)
            .spawn_scoped(s, f)
            .unwrap()
            .join()
            .unwrap()
    })
}

#[test]
fn a_residues_refusal_is_reached_in_the_size_of_the_classes() {
    // Θ(n) groups of periods. Measured on c881d28c: 10.0M instructions at n = 4, 81.9M at 32.
    refusal_scales(
        "Residues, by n copies of the classes",
        4,
        Refusal::Residues,
        erdos_cover_repeated,
    );
}

#[test]
fn a_tuple_split_refusal_is_reached_in_the_size_of_the_boxes() {
    // Θ(n) boxes. Measured on c881d28c: 4.4M instructions at n = 1, 159M at 32.
    refusal_scales(
        "TupleSplit, by n box covers",
        4,
        Refusal::TupleSplit,
        |n, _| box_covers(n),
    );
}

#[test]
fn a_morphism_split_refusal_is_reached_in_the_size_of_the_union() {
    // Θ(n) morphism types. Measured on c881d28c: 0.42M instructions at n = 1, 4.9M at 32.
    refusal_scales(
        "MorphismSplit, by n results",
        8,
        Refusal::MorphismSplit,
        |n, _| morphism_split_by(n),
    );
}

#[test]
fn a_no_witness_refusal_is_reached_in_the_size_of_the_keys() {
    // Θ(n) required keys. Measured on c881d28c: 87K instructions at n = 1, 302K at 32.
    refusal_scales(
        "NoWitness, by n required keys",
        8,
        Refusal::NoWitness,
        |n, _| morphism_between_by(n),
    );
}

/// [`fork_empty`] over 1 to `n`: pairs of lists of integers, without, for each `i`, those whose
/// first list holds only `i` and those whose first list holds some other integer, each with a
/// second list of the length parity of `i`. Empty for `n` of 2 or more; the excluded first lists
/// meet at `[]` and differ, so the strict search refuses it at the fork.
fn fork_by(n: usize, tag: &str) -> Type {
    let l = list_named(Type::int(), tag);
    let pair = |a: Type, b: Type| Type::tuple(vec![a, b]);
    (1..=n).fold(pair(l.clone(), l.clone()), |t, i| {
        let only = list_named(lit(i as i64), &format!("{tag}_{i}"));
        let parity = period_named(2, i % 2, &format!("{tag}_{i}"));
        let t = &t - &pair(only.clone(), parity.clone());
        &t - &pair(&l - &only, parity)
    })
}

#[test]
fn a_fork_refusal_is_reached_in_the_size_of_the_pairs() {
    // Θ(n) excluded pairs. Measured on c881d28c, before REFUSAL-fork-linear: 63M, 221M, 805M and
    // 3209M instructions at n 8, 16, 32 and 64, order n^2: the search for a value before the
    // refusal narrowed the box into each excluded pair and tested every other pair there. Now
    // (REFUSAL-fork-linear) 30.2M and 255.9M instructions at n 8 and 64, 8.5 times.
    refusal_scales("Fork, by n excluded pairs", 8, Refusal::Fork, fork_by);
}

/// The parts of `forked_differences`: for each `i` up to `n`, the pairs of a list of only `i`s
/// and a list of `i`'s parity, and the pairs of a list of only `i`s and any list of integers,
/// which hold them.
fn forked_pairs(n: usize, tag: &str) -> Vec<(Type, Type)> {
    let l = list_named(Type::int(), tag);
    let pair = |a: Type, b: Type| Type::tuple(vec![a, b]);
    (1..=n)
        .map(|i| {
            let only = list_named(lit(i as i64), &format!("{tag}_{i}"));
            let parity = period_named(2, i % 2, &format!("{tag}_{i}"));
            (pair(only.clone(), parity), pair(only, l.clone()))
        })
        .collect()
}

#[test]
fn a_difference_of_forked_unions_is_refused_in_its_size() {
    // The union of `n` pairs minus the union of `n` pairs that hold them, one each. Measured on
    // 8874023a, before REFUSAL-narrow-cells: 25.7M, 104M, 470M and 2396M instructions at n 8,
    // 16, 32 and 64, order n^2: each pair was a candidate for a value, whose narrowing tested
    // the `n` cells of its components and took the `n` excluded pairs out one by one, and the
    // search then refined the forked part, `n` searches of the whole part. Now 3.7M, 7.3M, 14.4M
    // and 28.8M (release probe): each pair is inside the pair that holds it, and the part, with
    // no value outside its pairs, is passed over as empty without refining (COMPLEXITY.md K80).
    refusal_scales(
        "Fork, by a difference of unions",
        8,
        Refusal::Fork,
        |n, tag| {
            let (ins, outs): (Vec<Type>, Vec<Type>) = forked_pairs(n, tag).into_iter().unzip();
            let union = |ts: Vec<Type>| ts.iter().fold(Type::empty(), |u, t| &u | t);
            &union(ins) - &union(outs)
        },
    );
}

#[test]
fn a_union_of_forked_differences_is_refused_in_its_size() {
    // The union of `n` differences, each a pair minus a pair that holds it. Measured on
    // 8874023a, before REFUSAL-narrow-cells: 64.6M, 264M, 1125M and 5123M instructions at n 8,
    // 16, 32 and 64, order n^2: the value search took all `2n` pairs on one box. Now 4.3M, 8.4M,
    // 16.7M and 33.4M (release probe), one box for each difference (COMPLEXITY.md K80).
    refusal_scales(
        "Fork, by a union of differences",
        8,
        Refusal::Fork,
        |n, tag| {
            forked_pairs(n, tag)
                .into_iter()
                .fold(Type::empty(), |u, (a, b)| &u | &(&a - &b))
        },
    );
}

#[test]
fn a_pair_type_met_with_forked_differences_is_refused_in_its_size() {
    // The union of `a_union_of_forked_differences_is_refused_in_its_size` met with the pairs of
    // lists of integers, so the union is not at the top of the part. On the box that the pair
    // type narrows to, the pair type holds every tuple and drops out, and the union is searched
    // one difference at a time. Release probe, instructions at n 8, 16, 32 and 64: on 3c251cd5,
    // which split only a union at the top, 33M to 1694M (its report); with that split and
    // forked parts refined, 75.0M, 342M, 1757M and 10334M; now 11.3M, 22.5M, 44.9M and 89.8M
    // (COMPLEXITY.md K80).
    refusal_scales(
        "Fork, by a pair type met with a union of differences",
        8,
        Refusal::Fork,
        |n, tag| {
            let l = list_named(Type::int(), tag);
            let union = forked_pairs(n, tag)
                .into_iter()
                .fold(Type::empty(), |u, (a, b)| &u | &(&a - &b));
            &Type::tuple(vec![l.clone(), l]) & &union
        },
    );
}

/// Pairs of lists of integers less two pairs: those whose first list holds only 1s and whose
/// second has an even length, and those whose first list holds some other integer and whose
/// second has an odd length. The two excluded first lists meet nowhere, and the two second
/// lists cover all lists, so no component alone leaves a value; `([], [0])` is one.
fn forked_pair_left() -> Type {
    let l = list(Type::int());
    let pair = |a: &Type, b: &Type| Type::tuple(vec![a.clone(), b.clone()]);
    let ones = list(lit(1));
    let (even, odd) = (period(2, 0), period(2, 1));
    &(&pair(&l, &l) - &pair(&ones, &even)) - &pair(&(&l - &ones), &odd)
}

#[test]
fn a_value_found_by_refining_a_forked_part_is_kept() {
    // Each type is inhabited, and the strict search stops at the fork in its first component.
    // No candidate of the search for values holds a value: a value is found only by splitting
    // the first component at a tuple type and narrowing the second (`Searching::refine`). The
    // answers are those of d5055bcf; 3c251cd5, which did not refine a forked part, refused all
    // three for Fork.
    let l = list(Type::int());
    let pair = |a: &Type, b: &Type| Type::tuple(vec![a.clone(), b.clone()]);
    let (ones, twos) = (list(lit(1)), list(lit(2)));
    let (even, odd) = (period(2, 0), period(2, 1));
    // Pairs of a list of only 1s or only 2s and any list, without those of only 1s and an even
    // length and those of only 2s and an odd length: `([1], [0])` is left.
    let ones_or_twos = &(&pair(&(&ones | &twos), &l) - &pair(&ones, &even)) - &pair(&twos, &odd);
    // `forked_pair_left` joined with an empty difference of pairs that shares no tuple type
    // with it, so the union is searched one part at a time.
    let joined = &forked_pair_left() | &(&pair(&twos, &even) - &pair(&twos, &l));
    for t in [forked_pair_left(), ones_or_twos, joined] {
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Inhabited, "{t}");
        assert!(!t.is_empty(), "{t}");
    }
}

/// Pairs of integers met with the union over `i` from 1 to `n` of the pairs of `0` or `i` and
/// `0`, less the pairs of `0` or `i` and any integer, which hold them: each difference is empty,
/// and so is the type. When `kept` is `Some(m)`, the `m`th difference takes out only the pairs
/// whose first is `m`, and leaves `(0, 0)`.
fn pairs_less_holders(n: usize, kept: Option<usize>) -> Type {
    let pair = |a: Type, b: Type| Type::tuple(vec![a, b]);
    let union = (1..=n).fold(Type::empty(), |u, i| {
        let zero_or_i = &lit(0) | &lit(i as i64);
        let first = match kept {
            Some(m) if m == i => lit(i as i64),
            _ => zero_or_i.clone(),
        };
        &u | &(&pair(zero_or_i, lit(0)) - &pair(first, Type::int()))
    });
    &pair(Type::int(), Type::int()) & &union
}

#[test]
fn a_union_of_pairs_less_pairs_holding_them_is_decided_operand_by_operand() {
    // Empty, and with one difference that leaves `(0, 0)`, wherever it stands, inhabited.
    for n in [1, 2, 5] {
        Type::forget_emptiness();
        let t = pairs_less_holders(n, None);
        assert_eq!(t.verdict(), Verdict::Empty, "{t}");
        assert!(t.is_empty(), "{t}");
        for m in 1..=n {
            Type::forget_emptiness();
            let t = pairs_less_holders(n, Some(m));
            assert_eq!(t.verdict(), Verdict::Inhabited, "{t}");
            assert!(!t.is_empty(), "{t}");
        }
    }
}

#[test]
fn a_union_of_pairs_less_pairs_holding_them_is_empty_in_its_size() {
    // The cells `0 | i` of the first components all share `0`, so they fall in one class, and
    // the part, false outside its tuple types, was split into its `2n` tuple types, each piece
    // deciding the whole part: 9.2M, 37.1M, 149.8M, 601.9M and 2392M instructions at n 8, 16,
    // 32, 64 and 128 on cf4e1fda, order n^2. The differences share no tuple type, so each is
    // now decided on the box alone: 1.27M, 2.45M, 4.77M, 9.56M and 18.8M (COMPLEXITY.md K80).
    big(|| {
        scaling::check(
            "Empty, by a union of n pairs less pairs that hold them",
            8,
            |n| {
                Type::forget_emptiness();
                assert_eq!(
                    pairs_less_holders(n, None).verdict(),
                    Verdict::Empty,
                    "at {n}"
                );
            },
        )
    });
}

/// The lists of integers with a 1 at each place `i` from the end, for `i` up to `n`, except
/// `skip`; with a 1 at a place beyond `n`; or with no 1: `R{k}` is the lists of length `k`,
/// `G{i}` those with a 1 at place `i` from the end, `A{k}` those of length at least `k`, and
/// `H` those with a 1 at a place beyond `n`. Every list is one of them when `skip` is none.
/// Read from the front, a list may still be in any of the `G{i}`, so a decision that follows
/// them all meets one set of places for each set the list's 1s leave: the subset construction.
fn by_place_from_the_end(n: usize, skip: Option<usize>, tag: &str) -> Type {
    let mut defs = vec![def(&format!("R0{tag}"), nil())];
    defs.extend((1..=n).map(|k| def(&format!("R{k}{tag}"), cons(int(), r(k - 1)))));
    defs.extend((1..=n).map(|i| {
        let body = Expr::Union(vec![
            cons(int(), r(n + i)),
            cons(Expr::Type(lit(1)), r(i - 1)),
        ]);
        def(&format!("G{i}{tag}"), body)
    }));
    let a = 2 * n + 1;
    let all = Expr::Union(vec![nil(), cons(int(), r(a))]);
    defs.push(def(&format!("A0{tag}"), all));
    defs.extend((1..=n).map(|k| def(&format!("A{k}{tag}"), cons(int(), r(a + k - 1)))));
    let far = Expr::Union(vec![
        cons(int(), r(a + n + 1)),
        cons(Expr::Type(lit(1)), r(a + n)),
    ]);
    defs.push(def(&format!("H{tag}"), far));
    let ts = Group::new(defs).unwrap().instance(vec![]);
    let no_one = list_named(&Type::int() - &lit(1), &format!("N{tag}"));
    (1..=n)
        .filter(|&i| Some(i) != skip)
        .map(|i| &ts[n + i])
        .chain([&ts[a + n + 1], &no_one])
        .fold(Type::empty(), |u, t| &u | t)
}

/// The lists of integers with a 1 at each place `i` from the front, for `i` up to `n`, except
/// `skip`, or with no 1 among the first `n` places: `F{i}` and `M{k}` (no 1 among the first `k`
/// places). Every list is one of them when `skip` is none. Read from the front, the places a
/// list may still meet move by one with each element and one tuple type is open on each, so
/// no two recursive tuple types are taken out of one component: no fork.
fn by_place_from_the_front(n: usize, skip: Option<usize>, tag: &str) -> Type {
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| def(&format!("F{i}{tag}"), cons(int(), r(i - 1)))));
    let not_one = Expr::Type(&Type::int() - &lit(1));
    defs.extend((1..=n).map(|k| {
        let rest = if k == 1 { r(0) } else { r(n + k - 1) };
        let body = Expr::Union(vec![nil(), cons(not_one.clone(), rest)]);
        def(&format!("M{k}{tag}"), body)
    }));
    let ts = Group::new(defs).unwrap().instance(vec![]);
    (1..=n)
        .filter(|&i| Some(i) != skip)
        .map(|i| &ts[i])
        .chain([&ts[2 * n]])
        .fold(Type::empty(), |u, t| &u | t)
}

/// The lists of integers with a 1 at place `n` from the front, or with no 1 there (shorter
/// lists too); with `two`, the lists with a 2 there are left out of the second. Read from the
/// front, the two tuple types taken out of the tail at each element are of `F{n-1}` and
/// `P{n-1}`, recursive types on no cycle, so they are no fork, and the search decides the
/// difference one place at a time.
fn by_one_place_from_the_front(n: usize, two: bool, tag: &str) -> Type {
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| def(&format!("F{i}{tag}"), cons(int(), r(i - 1)))));
    let mut other = &Type::int() - &lit(1);
    if two {
        other = &other - &lit(2);
    }
    defs.push(def(
        &format!("P1{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(other), r(0))]),
    ));
    defs.extend((2..=n).map(|k| {
        let body = Expr::Union(vec![nil(), cons(int(), r(n + k - 1))]);
        def(&format!("P{k}{tag}"), body)
    }));
    let ts = Group::new(defs).unwrap().instance(vec![]);
    &list_named(Type::int(), tag) - &(&ts[n] | &ts[2 * n])
}

#[test]
fn a_union_of_lists_by_the_place_of_a_one_is_refused_in_its_size() {
    // The lists of integers against those with a 1 at each place from the end up to `n`, with
    // one beyond `n`, or with none: every list. Deciding it follows every `G{i}` at once, one
    // type for each set of places a list's 1s leave (the subset construction): on a70df51b this
    // cost 26.6M, 310M and 15.5G instructions at n 1, 4 and 8 and no answer at 16 within 30 s.
    // Now the `G{i}` are taken out of the tail together, two cyclic recursive types in one
    // component, and the decision refuses there (COMPLEXITY.md K35).
    refusal_scales(
        "Fork, by the place of a 1 from the end",
        8,
        Refusal::Fork,
        |n, tag| &list_named(Type::int(), tag) - &by_place_from_the_end(n, None, tag),
    );
}

#[test]
fn a_list_by_one_place_from_the_front_is_decided_in_its_size() {
    // Two recursive types on no cycle taken out of one tail are no fork: decided at each size,
    // in time linear in `n`.
    for (two, verdict) in [(false, Verdict::Empty), (true, Verdict::Inhabited)] {
        big(move || {
            scaling::check("a 1 at place n from the front, or none", 8, |n| {
                Type::forget_emptiness();
                let tag = format!("_of{n}{two}");
                let t = by_one_place_from_the_front(n, two, &tag);
                assert_eq!(t.verdict(), verdict, "at {n}");
            })
        });
    }
}

#[test]
fn lists_by_the_place_of_a_one_are_decided_or_refused_by_their_cycles() {
    for n in [1, 2, 4] {
        Type::forget_emptiness();
        let tag = format!("_cyc{n}");
        let l = list_named(Type::int(), &tag);
        // From the front, the places left move by one with each element; the types taken out
        // of a tail are on no cycle but `L`, so every difference is decided.
        let front = &l - &by_place_from_the_front(n, None, &tag);
        assert_eq!(front.verdict(), Verdict::Empty, "front at {n}");
        assert!(front.is_empty(), "front at {n}");
        let skip = &l - &by_place_from_the_front(n, Some(n), &format!("{tag}s"));
        assert_eq!(skip.verdict(), Verdict::Inhabited, "front less {n} at {n}");
        // From the end, `G{i}` and `H` are cyclic: refused, even at 1, where the old search
        // proved it empty.
        let end = &l - &by_place_from_the_end(n, None, &format!("{tag}e"));
        assert_eq!(end.verdict(), Verdict::Refused(Refusal::Fork), "end at {n}");
        // `is_empty` stops at the same fork and counts the type as inhabited, so `<:` fails.
        assert!(!end.is_empty(), "end at {n}");
        assert!(!l.subtype(&by_place_from_the_end(n, None, &format!("{tag}e"))));
        // With `G1` left out, `[1]` is a value: found at 1, where the decision has no fork;
        // refused above it, where the fork comes first and the value search does not follow
        // the fork into a candidate's tail.
        let skip = &l - &by_place_from_the_end(n, Some(1), &format!("{tag}e1"));
        let want = if n == 1 {
            Verdict::Inhabited
        } else {
            Verdict::Refused(Refusal::Fork)
        };
        assert_eq!(skip.verdict(), want, "end less 1 at {n}");
    }
}

#[test]
fn emptiness_counts_a_fork_as_inhabited_in_its_size() {
    // `is_empty` meets the fork `verdict` refuses and counts the type as inhabited, in time
    // linear in `n`; on a70df51b it followed the fork: 8 ms, 277 ms and 32.5 s at `n` 1, 4 and
    // 6. The lists by one place from the front have no fork and are proved empty.
    big(|| {
        let tag = AtomicUsize::new(0);
        scaling::check("emptiness, a 1 at a place from the end", 8, |n| {
            Type::forget_emptiness();
            let tag = format!("_ie{}", tag.fetch_add(1, Relaxed));
            let t = &list_named(Type::int(), &tag) - &by_place_from_the_end(n, None, &tag);
            assert!(!t.is_empty(), "at {n}");
        });
        let tag = AtomicUsize::new(0);
        scaling::check("emptiness, a 1 at one place from the front", 8, |n| {
            Type::forget_emptiness();
            let tag = format!("_if{}", tag.fetch_add(1, Relaxed));
            assert!(
                by_one_place_from_the_front(n, false, &tag).is_empty(),
                "at {n}"
            );
        });
    });
}

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
        Refusal::Group,
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
            "; this is not proved wrong: the checker could not decide whether it fits, because {}\n  \
             the check reads the recursive type `L`, defined by:\n    \
             type L = #nil | #cons(int, L);",
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
    // Item PRINT-fmt-audit: the argument type is written with a definition for the part it uses
    // three times. Before: `((#a | #b | #c, #a | #b | #c, #a | #b | #c))`, the part at each
    // use. Item MSG-type-defs-layout: the definition stands on a line of its own after the
    // sentence, which names the part `T1`; before, the sentence read
    // `` `g` does not take (type T1 = #a | #b | #c; (T1, T1, T1)) ``.
    let shown = "(T1, T1, T1)";
    assert_eq!(
        rejected(&box_program(7)),
        format!(
            "2:52: `g` does not take ({shown}); this is not proved wrong: the checker could not \
             decide whether it fits, because {}",
            Refusal::TupleSplit.message()
        )
    );
    // A decided failure names no cause.
    assert_eq!(
        rejected(&box_program(6)),
        format!(
            "2:52: `g` does not take ({shown}): these are the types of its arguments here, and `g` has no arrow that takes them all"
        )
    );
    // The declared type is printed with the same definition, written once for the message.
    // Before: `` `y` is declared `(#a | #b | #c, #a | #b | #c, #a | #b | #c)` ``.
    let Err(all) = zedc::run::load(box_program(7).as_bytes()) else {
        panic!("accepted")
    };
    assert!(
        all.contains("\n  T1, T2, T3 and T4 stand for parts written more than once:\n    type T1 = #a | #b | #c;\n"),
        "{all}"
    );
    assert_eq!(all.matches("type T1").count(), 1, "{all}");
    assert!(all.contains(&format!("`y` is declared `{shown}`")), "{all}");
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
            // The sentence, before the lines that define the parts it writes twice.
            let first = first.lines().next().unwrap_or_default();
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
    // from them), so no refused check reaches this path from a program. The operand `n` is an
    // `int`: a literal there would make `f` generic over the carriers (DESIGN.md L1.26a), and
    // the call would be refused by each carrier's arrow instead.
    assert_eq!(
        rejected("n = 1;\nf(x) = x[1] + n;\nmain() = f(x: (1, \"s\"));\n"),
        "3:10: `f` gives \"s\" here, which is not int: the use requires a value of int"
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
    let ts = r3_instance(defs);
    let no_one = list_named(&Type::int() - &lit(1), &format!("N{tag}"));
    (1..=n)
        .filter(|&i| Some(i) != skip)
        .map(|i| &ts[n + i])
        .chain([&ts[a + n + 1], &no_one])
        .fold(Type::empty(), |u, t| r3_union(&u, t))
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
    let ts = r3_instance(defs);
    (1..=n)
        .filter(|&i| Some(i) != skip)
        .map(|i| &ts[i])
        .chain([&ts[2 * n]])
        .fold(Type::empty(), |u, t| r3_union(&u, t))
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
    let ts = r3_instance(defs);
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

/// `cons(head, tail)`, a type of its own.
fn cons_of(head: Type, tail: Type) -> Type {
    Group::new(vec![def("C", cons(Expr::Type(head), Expr::Type(tail)))])
        .unwrap()
        .instance(vec![])
        .remove(0)
}

/// The pairs of `W` and the lists of integers of length 2, less the pairs of
/// `Never ->? (L | (S, L))` and the lists `[1, _]`, the nonempty lists or `cons(int, E)`, with
/// `L` the lists of integers, `W = (W) -> int`, `S = (int) -> S` and `E` the end family of `n`
/// places ([`by_place_from_the_end`]; with `skip`, that place left out of it, and the
/// nonempty lists left out of the union).
fn refined_pairs(n: usize, skip: bool, tag: &str) -> Type {
    let ts = Group::new(vec![
        def(
            &format!("L{tag}"),
            Expr::Union(vec![nil(), cons(int(), r(0))]),
        ),
        def(&format!("W{tag}"), Expr::exact(r(1), int())),
        def(&format!("S{tag}"), Expr::exact(int(), r(2))),
    ])
    .unwrap()
    .instance(vec![]);
    let (l, w, s) = (&ts[0], &ts[1], &ts[2]);
    let int_then = |t: Type| cons_of(Type::int(), t);
    let two = int_then(int_then(l.clone()));
    let three = int_then(two.clone());
    let into = &l.clone() | &Type::tuple(vec![s.clone(), l.clone()]);
    let f = Type::morphism(Type::empty(), Type::empty(), into);
    let one_then = cons_of(lit(1), int_then(Type::atom("nil")));
    let y = if skip {
        &one_then | &int_then(by_place_from_the_end(n, Some(n), tag))
    } else {
        &(&one_then | &int_then(l.clone())) | &int_then(by_place_from_the_end(n, None, tag))
    };
    &Type::tuple(vec![w.clone(), &two - &three]) - &Type::tuple(vec![f, y])
}

#[test]
fn refining_a_box_follows_no_fork_in_its_size() {
    // The search of a value refines the box of these pairs (`Searching::refine`), and the
    // pieces it tries meet the fork of the end family in the second component. Refining
    // followed the fork, the subset construction: on 92e736cd the verdict took 28.5M, 320M and
    // 3.64G instructions at n 1, 2 and 3, `is_empty` 23.1M, 47.4M and 1.58G, and this test did
    // not end within 60 s. Now refining counts a forked piece as inhabited, as the search of a
    // value after a refused decision does: the verdict 22.5M, 27.3M, 39.1M, 62.1M, 110M, 211M
    // and 435M at n 1, 2, 4, 8, 16, 32 and 64 (7.0 times from 8 to 64, order n^0.94),
    // `is_empty` 54.8M and 396M at 8 and 64 (COMPLEXITY.md K35).
    for skip in [false, true] {
        big(move || {
            let tag = AtomicUsize::new(0);
            scaling::check("Fork, refining pairs by the end family", 8, |n| {
                Type::forget_emptiness();
                let tag = format!("_rf{skip}{}", tag.fetch_add(1, Relaxed));
                let t = refined_pairs(n, skip, &tag);
                assert_eq!(t.verdict(), Verdict::Refused(Refusal::Fork), "at {n}");
            });
        });
    }
    big(|| {
        let tag = AtomicUsize::new(0);
        scaling::check("emptiness, refining pairs by the end family", 8, |n| {
            Type::forget_emptiness();
            let tag = format!("_rfe{}", tag.fetch_add(1, Relaxed));
            assert!(!refined_pairs(n, false, &tag).is_empty(), "at {n}");
        });
    });
    // At n 1, without the nonempty lists and with the end family's one place left out, the
    // refusal names the fork refining meets, where following it named no value found.
    Type::forget_emptiness();
    let t = refined_pairs(1, true, "_rf1");
    assert_eq!(t.verdict(), Verdict::Refused(Refusal::Fork));
}

#[test]
fn each_refusal_message_reads_as_written() {
    // The tests above compare a refused check's message with `Refusal::message`; this pins
    // the text each cause gives.
    let pinned = [
        (
            Refusal::Fork,
            "no value of it was found, and two of the tuple types involved differ in a component \
             whose type refers back to itself; following both at once can take time exponential \
             in the size of the types, so the checker does not try; write the two tuple types so \
             that they agree in that component, or test the value with `is` first",
        ),
        (
            Refusal::Residues,
            "the types involved allow list lengths that repeat with a period, and telling whether \
             the lengths they exclude cover all the lengths left can take time exponential in the \
             number of periods, so the checker does not try; write the lengths allowed as one \
             list type, or test the length with `is` first",
        ),
        (
            Refusal::TupleSplit,
            "one part of the tuple types involved is decided only by splitting more than one of \
             its components into cases at once, which the checker does not do; write those cases \
             out as a union of tuple types",
        ),
        (
            Refusal::SharedCells(2),
            "the tuple types involved combine, with `&` or `|`, types that restrict component 2 \
             of a tuple in different ways, and comparing every pair of them takes time that grows \
             with the square of their number, so the checker does not try; write the combination \
             as a union of cases on component 2",
        ),
        (
            Refusal::MorphismSplit,
            "one part of the function types involved is decided neither by the types its \
             arguments must have nor by splitting it into its separate function types; write the \
             function type as one type `(…) -> …`, or as a union of them",
        ),
        (
            Refusal::NoWitness,
            "the checker could neither show that no value has the type nor build a value that \
             has it; write the type more simply, or test the value with `is` first",
        ),
        (
            Refusal::Group,
            "the type refers to recursive definitions that reach each other both through tuples, \
             which a value cannot go around forever, and through the results of function types, \
             which a value can; deciding such a group takes time that grows with the square of \
             its size, while the checker decides each group in time linear in it, and a search \
             for a value neither finds one nor shows that there is none, so it counts the type as \
             possibly having a value; add a case such as `| #end` to one of the definitions",
        ),
    ];
    for (r, text) in pinned {
        assert_eq!(r.message(), text, "{r:?}");
    }
}

#[test]
#[ignore]
fn rfx_probe() {
    let which = std::env::var("RFX").unwrap_or_default();
    let sizes: Vec<usize> = std::env::var("RFX_N")
        .unwrap_or("8,16,32,64".into())
        .split(',')
        .map(|s| s.parse().unwrap())
        .collect();
    big(move || {
        for n in sizes {
            Type::forget_emptiness();
            let tag = format!("_rfx{n}");
            let t = rfx_case(&which, n, &tag);
            if std::env::var("RFX_SWEEP").is_ok() {
                Type::forget_emptiness();
                eprintln!("rfx sweep {which} n {n} {:?} chains {:?}", t.sweep_verdict(), { Type::forget_emptiness(); t.chain_verdict() });
                Type::forget_emptiness();
            }
            let mut m = scaling::Meter::new();
            let mut v = None;
            let w = m.work(|| v = Some(t.verdict()));
            eprintln!("rfx {which} n {n} {:?} units {} bytes {}", v, w.units, w.bytes);
        }
    });
}

/// The probe's families: the lists of `all`, and the lists with a `one` at place `i` from the
/// front for each `i` up to `n` but `skip`, or with no `one` among the first `m` places;
/// `split` puts the `M{k}` in a group of their own, with its own `L`.
fn rfx_family(
    n: usize,
    skip: Option<usize>,
    m: usize,
    all: &Type,
    one: &Type,
    split: bool,
    tag: &str,
) -> (Type, Type) {
    let l = list_named(all.clone(), tag);
    let ldef = || {
        let body = Expr::Union(vec![nil(), cons(Expr::Type(all.clone()), r(0))]);
        def(&format!("L{tag}"), body)
    };
    let mut fdefs = vec![ldef()];
    fdefs.push(def(&format!("F1{tag}"), cons(Expr::Type(one.clone()), r(0))));
    fdefs.extend((2..=n).map(|i| {
        def(&format!("F{i}{tag}"), cons(Expr::Type(all.clone()), r(i - 1)))
    }));
    let not_one = Expr::Type(all - one);
    let base = if split { 0 } else { n };
    let mut mdefs = if split { vec![ldef()] } else { vec![] };
    mdefs.extend((1..=m).map(|k| {
        let rest = if k == 1 { r(0) } else { r(base + k - 1) };
        let body = Expr::Union(vec![nil(), cons(not_one.clone(), rest)]);
        def(&format!("M{k}{tag}"), body)
    }));
    let (fs, ms) = if split {
        let f = r3_instance(fdefs);
        (f, r3_instance(mdefs))
    } else {
        fdefs.extend(mdefs);
        let g = r3_instance(fdefs);
        (g.clone(), g)
    };
    let mi = base + m;
    let u = (1..=n)
        .filter(|&i| Some(i) != skip)
        .map(|i| &fs[i])
        .chain([&ms[mi]])
        .fold(Type::empty(), |u, t| r3_union(&u, t));
    (l, u)
}

/// The probe's cases at size `n`: `front` and `far` are the lists of integers less the lists
/// by the place of a 1 from the front ([`by_place_from_the_front`]), all places or all but `n`;
/// the others vary them ([`rfx_family`]): another place left out, booleans, a shorter or longer
/// `M`, the `M{k}` in a group of their own, a meet, a pair; and the lists by one place
/// ([`by_one_place_from_the_front`]) and by the place from the end ([`by_place_from_the_end`]).
fn rfx_case(which: &str, n: usize, tag: &str) -> Type {
    let l = list_named(Type::int(), tag);
    let (int, one, b, yes) = (Type::int(), lit(1), Type::bool(), Type::lit(&Value::Bool(true)));
    let yes = yes.unwrap();
    let fam = |skip, m, all: &Type, one: &Type, split| {
        let (l, u) = rfx_family(n, skip, m, all, one, split, tag);
        &l - &u
    };
    let half = (n / 2).max(1);
    match which {
        "far" => &l - &by_place_from_the_front(n, Some(n), tag),
        "skip1" => fam(Some(1), n, &int, &one, false),
        "skipmid" => fam(Some(half), n, &int, &one, false),
        "bool" => fam(None, n, &b, &yes, false),
        "boolfar" => fam(Some(n), n, &b, &yes, false),
        "mshort" => fam(None, half, &int, &one, false),
        "mlong" => fam(None, n + 1, &int, &one, false),
        "split" => fam(None, n, &int, &one, true),
        "splitfar" => fam(Some(n), n, &int, &one, true),
        "meet" => &fam(Some(n), n, &int, &one, false)
            & &fam(Some(n - 1).filter(|&k| k > 0), n, &int, &one, false),
        "pair" => Type::tuple(vec![
            fam(None, n, &int, &one, false),
            fam(Some(n), n, &int, &one, false),
        ]),
        "pairfar" => Type::tuple(vec![
            fam(Some(n), n, &int, &one, false),
            fam(Some(n), n, &int, &one, false),
        ]),
        "tuple" => {
            let pi = Type::tuple(vec![int.clone(), int.clone()]);
            let po = Type::tuple(vec![one.clone(), int.clone()]);
            fam(None, n, &pi, &po, false)
        }
        "tuplefar" => {
            let pi = Type::tuple(vec![int.clone(), int.clone()]);
            let po = Type::tuple(vec![one.clone(), int.clone()]);
            fam(Some(n), n, &pi, &po, false)
        }
        "tupleflip" => {
            let pi = Type::tuple(vec![int.clone(), int.clone()]);
            let po = Type::tuple(vec![int.clone(), one.clone()]);
            fam(None, n, &pi, &po, false)
        }
        "tupleflipfar" => {
            let pi = Type::tuple(vec![int.clone(), int.clone()]);
            let po = Type::tuple(vec![int.clone(), one.clone()]);
            fam(Some(n), n, &pi, &po, false)
        }
        "multi" => &l - &rfx_multi(n, half, tag),
        "multifar" => &l - &rfx_multi(n, n, tag),
        "groups" => &l - &rfx_groups(n, false, tag),
        "groupsfar" => &l - &rfx_groups(n, true, tag),
        "groupsholes" => &l - &rfx_groups_holes(n, false, tag),
        "groupsholesfar" => &l - &rfx_groups_holes(n, true, tag),
        "groupssingles" => &l - &rfx_groups_singles(n, false, tag),
        "groupssinglesfar" => &l - &rfx_groups_singles(n, true, tag),
        "cxstagger" => rfx_cx_stagger(n, false, tag),
        "cxstaggerfar" => rfx_cx_stagger(n, true, tag),
        "cxstaggerwide" => rfx_cx_stagger_wide(n, false, tag),
        "cxstaggerwidefar" => rfx_cx_stagger_wide(n, true, tag),
        "clmanyheads" => &l - &rfx_cl_many_heads(n, false, tag),
        "clmanyheadsfar" => &l - &rfx_cl_many_heads(n, true, tag),
        "clstagger" => &l - &rfx_cl_stagger(n, false, false, tag),
        "clstaggerfar" => &l - &rfx_cl_stagger(n, true, false, tag),
        "clstaggerholes" => &l - &rfx_cl_stagger(n, false, true, tag),
        "clcofront" => &l - &rfx_cl_cofront(n, tag),
        "clcofrontones" => rfx_cl_cofront_var(n, true, |i| i + 2, tag),
        "clcofrontsame" => rfx_cl_cofront_var(n, false, |_| 4, tag),
        "clcofrontsameones" => rfx_cl_cofront_var(n, true, |_| 4, tag),
        "clcofrontsameblock" => rfx_cl_cofront_block(n, true, |_| 4, true, tag),
        "clcofrontshared" => rfx_cl_cofront_var(n, false, |i| 4 + i % 2, tag),
        "emitheads" => rfx_cx_emitheads(n, false, tag),
        "emitheadsfar" => rfx_cx_emitheads(n, true, tag),
        "manyheads" => rfx_many_heads(n, false, tag),
        "manyheadsfar" => rfx_many_heads(n, true, tag),
        "stagger" => &l - &rfx_stagger(n, false, tag),
        "staggerfar" => &l - &rfx_stagger(n, true, tag),
        "chain" => &l - &rfx_chain(n, false, tag),
        "chainfar" => &l - &rfx_chain(n, true, tag),
        "boundaryinside" => &l - &r4_boundary(n, true, tag),
        "boundaryoutside" => &l - &r4_boundary(n, false, tag),
        "cxprivateheads" => r4_private_heads(n,false,tag),
        "cxprivateheadsfar" => r4_private_heads(n,true,tag),
        "manyheadsv0" => rfx_manyheads_v0(n,false,tag),
        "manyheadsfarv0" => rfx_manyheads_v0(n,true,tag),
        "clstaggerholesin" => &l - &rfx_cl_stagger_boundary(n, false, tag),
        "clstaggerholesout" => &l - &rfx_cl_stagger_boundary(n, true, tag),
        "u4cofrontones" => u4_cofront_block(n, true, |i| i + 2, false, tag),
        "u4cofrontsame" => u4_cofront_block(n, false, |_| 4, false, tag),
        "u4cofrontsameones" => u4_cofront_block(n, true, |_| 4, false, tag),
        "u4cofrontsameblock" => u4_cofront_block(n, true, |_| 4, true, tag),
        "u4cofrontshared" => u4_cofront_block(n, false, |i| 4 + i % 2, false, tag),
        "u4holesin" => u4_stagger_boundary(n, false, tag),
        "u4holesout" => u4_stagger_boundary(n, true, tag),
        "u4boundaryin" => u4_boundary(n, true, tag),
        "u4boundaryout" => u4_boundary(n, false, tag),
        "u4width" => u4_width(n, tag),
        "r5greedy" => r5_greedy(tag),
        // Round 5, Q2 boundary: the 3-SAT reduction's type for n copies of one clause (length
        // 2 + 3n, or 1 + 2n for `k1n`). With literals the case is in the remainder (no sweep
        // decides it); `r5satnone` (n empty clauses, the same shape without holes) is decided
        // by the front sweep.
        "r5sat2lit" => r5_sat_type(2, &vec![vec![(1, true), (2, true)]; n], tag),
        "r5sat1lit" => r5_sat_type(2, &vec![vec![(1, true)]; n], tag),
        "r5satnone" => r5_sat_type(2, &vec![vec![]; n], tag),
        "r5satk1n" => r5_sat_type(1, &vec![vec![(1, false)]; n], tag),
        "r5varywidth" => r5_varying_width(n),
        "r5slotsin" => r5_slots(n, false),
        "r5slotsout" => r5_slots(n, true),
        "r5remin" => r5_remainder_boundary(n, false, tag),
        "r5remout" => r5_remainder_boundary(n, true, tag),
        "r6two" => { let (k, c) = r6_two_clauses(n, 0); r5_sat_type(k, &c, tag) }
        "r6twoun" => { let (k, c) = r6_two_clauses(n, 1); r5_sat_type(k, &c, tag) }
        "r6twowide" => { let (k, c) = r6_two_clauses(n, 2); r5_sat_type(k, &c, tag) }
        "r6three" => r5_sat_type(3, &vec![vec![(1, true), (2, true), (3, true)]; n], tag),
        "r6threeun" => {
            let mut c = vec![vec![(1, true), (2, true), (3, true)]; n];
            c.extend([vec![(1, false)], vec![(2, false)], vec![(3, false)]]);
            r5_sat_type(3, &c, tag)
        }
        "r6wide" => r6_sat_type(2, &vec![vec![(1, true), (2, true)]; n], tag, &lit(0) | &lit(7), Type::int()),
        "r6comb" => r6_sat_type(2, &vec![vec![(1, true)]; n], tag, lit(7), &(&lit(0) | &lit(1)) | &(&lit(2) | &lit(7))),
        "r6parity" => r6_parity(n, tag),
        "r6repeat3" => r5_sat_type(3, &vec![vec![(1, true), (2, true), (3, true)]; n], tag),
        "r6distinct2" => r6_distinct_atoms(n, false, tag),
        "r6distinct3" => r6_distinct_atoms(n, true, tag),
        "one" => by_one_place_from_the_front(n, false, tag),
        "onetwo" => by_one_place_from_the_front(n, true, tag),
        "end" => &l - &by_place_from_the_end(n, None, tag),
        _ => &l - &by_place_from_the_front(n, None, tag),
    }
}

/// Lists with a 1 at a place up to `n`, or a 2 at a place up to `n / 2` (at least 1), or with
/// neither among the first `m` places: Empty for `m <= n / 2`, Inhabited for `m = n`.
fn rfx_multi(n: usize, m: usize, tag: &str) -> Type {
    let h = (n / 2).max(1);
    // 0: L; 1..=n: F; n+1..=n+h: G; n+h+1..=n+h+m: M
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| def(&format!("F{i}{tag}"), cons(Expr::Type(Type::int()), r(i - 1)))));
    defs.push(def(&format!("G1{tag}"), cons(Expr::Type(lit(2)), r(0))));
    defs.extend((2..=h).map(|i| def(&format!("G{i}{tag}"), cons(Expr::Type(Type::int()), r(n + i - 1)))));
    let neither = Expr::Type(&Type::int() - &(&lit(1) | &lit(2)));
    defs.extend((1..=m).map(|k| {
        let rest = if k == 1 { r(0) } else { r(n + h + k - 1) };
        def(&format!("M{k}{tag}"), Expr::Union(vec![nil(), cons(neither.clone(), rest)]))
    }));
    let ts = r3_instance(defs);
    (1..=n + h).map(|i| &ts[i]).chain([&ts[n + h + m]]).fold(Type::empty(), |u, t| r3_union(&u, t))
}

/// The front union written as one chain: `G1 = cons(1, L)`, `Gk = cons(1, L) | cons(int, G{k-1})`
/// (the same set as `F1 | .. | Fk`), with `M{n}`; `far` uses `G{n-1}` (n >= 2).
fn rfx_chain(n: usize, far: bool, tag: &str) -> Type {
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    defs.push(def(&format!("G1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| {
        def(&format!("G{i}{tag}"), Expr::Union(vec![cons(Expr::Type(lit(1)), r(0)), cons(Expr::Type(Type::int()), r(i - 1))]))
    }));
    let not_one = Expr::Type(&Type::int() - &lit(1));
    defs.extend((1..=n).map(|k| {
        let rest = if k == 1 { r(0) } else { r(n + k - 1) };
        def(&format!("M{k}{tag}"), Expr::Union(vec![nil(), cons(not_one.clone(), rest)]))
    }));
    let ts = r3_instance(defs);
    let g = if far { n - 1 } else { n };
    &ts[g] | &ts[2 * n]
}

/// The front family plus `cons(int, A_k)` for k = 1..n, `A_k = cons(int | #a_k, F1)`: n chains
/// of depth 3 whose second heads differ (each a 1 at place 3, so Empty; Inhabited with `far`).
fn rfx_groups(n: usize, far: bool, tag: &str) -> Type {
    // 0: L; 1..=n: F; n+1..=2n: M; 2n+1..=3n: A; 3n+1..=4n: B
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| def(&format!("F{i}{tag}"), cons(Expr::Type(Type::int()), r(i - 1)))));
    let not_one = Expr::Type(&Type::int() - &lit(1));
    defs.extend((1..=n).map(|k| {
        let rest = if k == 1 { r(0) } else { r(n + k - 1) };
        def(&format!("M{k}{tag}"), Expr::Union(vec![nil(), cons(not_one.clone(), rest)]))
    }));
    defs.extend((1..=n).map(|k| {
        let h = &Type::int() | &Type::atom(&format!("a{k}"));
        def(&format!("A{k}{tag}"), cons(Expr::Type(h), r(1)))
    }));
    defs.extend((1..=n).map(|k| def(&format!("B{k}{tag}"), cons(Expr::Type(Type::int()), r(2 * n + k)))));
    let ts = r3_instance(defs);
    let top = if far { n - 1 } else { n };
    (1..=top).chain([2 * n]).chain(3 * n + 1..=4 * n).map(|i| &ts[i]).fold(Type::empty(), |u, t| r3_union(&u, t))
}

/// Stress X3: redundant finite chains with distinct overlapping scalar heads.
fn rfx_groups_holes(n: usize, far: bool, tag: &str) -> Type {
    // 0: L; 1..=n: F; n+1..=2n: M; 2n+1..=3n: A; 3n+1..=4n: B
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| def(&format!("F{i}{tag}"), cons(Expr::Type(Type::int()), r(i - 1)))));
    let not_one = Expr::Type(&Type::int() - &lit(1));
    defs.extend((1..=n).map(|k| {
        let rest = if k == 1 { r(0) } else { r(n + k - 1) };
        def(&format!("M{k}{tag}"), Expr::Union(vec![nil(), cons(not_one.clone(), rest)]))
    }));
    defs.extend((1..=n).map(|k| {
        let h = &Type::int() - &lit(k as i64 + 2);
        def(&format!("A{k}{tag}"), cons(Expr::Type(h), r(1)))
    }));
    defs.extend((1..=n).map(|k| def(&format!("B{k}{tag}"), cons(Expr::Type(Type::int()), r(2 * n + k)))));
    let ts = r3_instance(defs);
    let top = if far { n - 1 } else { n };
    (1..=top).chain([2 * n]).chain(3 * n + 1..=4 * n).map(|i| &ts[i]).fold(Type::empty(), |u, t| r3_union(&u, t))
}

/// Stress X13: as `rfx_groups_holes` with singleton heads `{k + 2}`, so no union of them covers `int`.
fn rfx_groups_singles(n: usize, far: bool, tag: &str) -> Type {
    // 0: L; 1..=n: F; n+1..=2n: M; 2n+1..=3n: A; 3n+1..=4n: B
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| def(&format!("F{i}{tag}"), cons(Expr::Type(Type::int()), r(i - 1)))));
    let not_one = Expr::Type(&Type::int() - &lit(1));
    defs.extend((1..=n).map(|k| {
        let rest = if k == 1 { r(0) } else { r(n + k - 1) };
        def(&format!("M{k}{tag}"), Expr::Union(vec![nil(), cons(not_one.clone(), rest)]))
    }));
    defs.extend((1..=n).map(|k| {
        let h = lit(k as i64 + 2);
        def(&format!("A{k}{tag}"), cons(Expr::Type(h), r(1)))
    }));
    defs.extend((1..=n).map(|k| def(&format!("B{k}{tag}"), cons(Expr::Type(Type::int()), r(2 * n + k)))));
    let ts = r3_instance(defs);
    let top = if far { n - 1 } else { n };
    (1..=top).chain([2 * n]).chain(3 * n + 1..=4 * n).map(|i| &ts[i]).fold(Type::empty(), |u, t| r3_union(&u, t))
}

/// Codex R3 families (copied from its probe, renamed rfx_cx_*).
// n roots join a shared uniform chain at distinct depths. Supplementary rows
// are subsets of existing F rows, so truth remains front/far for n >= 3.
fn rfx_cx_stagger(n: usize, far: bool, tag: &str) -> Type {
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| def(&format!("F{i}{tag}"), cons(Expr::Type(Type::int()), r(i-1)))));
    defs.extend((1..=n).map(|i| def(&format!("M{i}{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(&Type::int()-&lit(1)), r(if i==1 {0} else {n+i-1}))]))));
    for i in 1..n-1 {
        defs.push(def(&format!("B{i}{tag}"), cons(Expr::Type(&Type::int()-&lit(i as i64+2)), r(i))));
    }
    let ts = r3_instance(defs);
    let top = if far { n-1 } else { n };
    let u = (1..=top).chain([2*n]).chain(2*n+1..ts.len()).fold(Type::empty(), |u,i| r3_union(&u, &ts[i]));
    &ts[0] - &u
}

// Linear-DAG encoding of the same positional exclusions, using carrier emits.
/// X10: `N_j = cons(int \ {j+2}, L) | cons({j+2}, N_{j+1})` for j = 1..n, `N_{n+1} = cons(int, L)`
/// (`cons(1, L)` with `far`), and `S_n` the lists of length at most n. `L` less `N_1 | S_n` is
/// Empty; with `far` its values are the lists starting 3, 4, .., n+2 and then not a 1: n + 1
/// runs, and n distinct cofinite negative heads, the j-th first read at step j.
fn rfx_cl_many_heads(n: usize, far: bool, tag: &str) -> Type {
    // 0: L; 1..=n+1: N; n+2..=2n+2: S_0..S_n
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    defs.extend((1..=n).map(|j| {
        let k = j as i64 + 2;
        let side = cons(Expr::Type(&Type::int() - &lit(k)), r(0));
        def(
            &format!("N{j}{tag}"),
            Expr::Union(vec![side, cons(Expr::Type(lit(k)), r(j + 1))]),
        )
    }));
    let last = if far { lit(1) } else { Type::int() };
    defs.push(def(
        &format!("N{}{tag}", n + 1),
        cons(Expr::Type(last), r(0)),
    ));
    defs.push(def(&format!("S0{tag}"), nil()));
    defs.extend((1..=n).map(|k| {
        def(
            &format!("S{k}{tag}"),
            Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(n + 1 + k))]),
        )
    }));
    let ts = r3_instance(defs);
    &ts[1] | &ts[2 * n + 2]
}

/// X12: one chain `Y_i = cons(int | #a_i, Y_{i+1})` for i = 1..2n, `Y_{2n+1} = cons(1, L)`,
/// entered at the n staggered roots `Y_1..Y_n` (`Y_k`: a 1 at place 2n - k + 2), every link
/// with its own head; `N` the lists with no 1 at places n+2..2n+1. `L` less the roots and `N`
/// is Empty; `far` leaves out `Y_n`, so `[0; n+1] ++ [1]` is a value. With `holes` the heads
/// are `int \ {i+2}` instead, distinct inside the integers, and `[n+2] ++ [0; n] ++ [1]` is a
/// value (the first head of `Y_n` leaves out n+2).
fn rfx_cl_stagger(n: usize, far: bool, holes: bool, tag: &str) -> Type {
    let m = 2 * n;
    // 0: L; 1..=m+1: Y; m+2..=2m+2: N_1..N_{m+1}
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    defs.extend((1..=m).map(|i| {
        let h = if holes {
            &Type::int() - &lit(i as i64 + 2)
        } else {
            &Type::int() | &Type::atom(&format!("a{i}"))
        };
        def(&format!("Y{i}{tag}"), cons(Expr::Type(h), r(i + 1)))
    }));
    defs.push(def(
        &format!("Y{}{tag}", m + 1),
        cons(Expr::Type(lit(1)), r(0)),
    ));
    defs.extend((1..=m + 1).map(|j| {
        let h = if j <= n + 1 {
            Type::int()
        } else {
            &Type::int() - &lit(1)
        };
        let next = if j == m + 1 { r(0) } else { r(m + 2 + j) };
        def(
            &format!("N{j}{tag}"),
            Expr::Union(vec![nil(), cons(Expr::Type(h), next)]),
        )
    }));
    let ts = r3_instance(defs);
    let top = if far { n - 1 } else { n };
    (1..=top)
        .map(|k| &ts[k])
        .chain([&ts[m + 2]])
        .fold(Type::empty(), |u, t| r3_union(&u, t))
}

/// The front family with distinct cofinite heads: `F_1 = cons(1, L)`,
/// `F_i = cons(int \ {i+2}, F_{i-1})`, and `M_n`. `L` less `F_1 | .. | F_n | M_n` holds `[4, 1]`
/// for n >= 2: n distinct heads at the first step, on n different links.
fn rfx_cl_cofront(n: usize, tag: &str) -> Type {
    // 0: L; 1..=n: F; n+1..=2n: M
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| {
        def(
            &format!("F{i}{tag}"),
            cons(Expr::Type(&Type::int() - &lit(i as i64 + 2)), r(i - 1)),
        )
    }));
    let not_one = Expr::Type(&Type::int() - &lit(1));
    defs.extend((1..=n).map(|k| {
        let rest = if k == 1 { r(0) } else { r(n + k - 1) };
        def(
            &format!("M{k}{tag}"),
            Expr::Union(vec![nil(), cons(not_one.clone(), rest)]),
        )
    }));
    let ts = r3_instance(defs);
    (1..=n)
        .chain([2 * n])
        .map(|i| &ts[i])
        .fold(Type::empty(), |u, t| r3_union(&u, t))
}
/// Q2 boundary families around [`rfx_cl_cofront`], whose rows `F_i` (a root each, and the tail
/// of `F_{i+1}`) are joins with a new signature at every link below: outside the sweep's bounded
/// class ([`Sweep::bounded`]). `excl` gives the value `F_i` leaves out of its head for i >= 2:
/// `same` leaves out 4 in every row, so the links below a join share its signature, inside the
/// class, and `[4, 1]` is a value; `shared` leaves out `4 + i mod 2`, outside the class, and
/// `[4, 1]` is a value. `ones`: the positive side is `P = cons(int, Q_2)`,
/// `Q_k = cons(1, Q_{k+1})` for k = 2..n, `Q_{n+1} = L`; with distinct exclusions `[x, 1, ..]`
/// escapes `F_2` only with x = 4 and is then in `F_3`, so it is empty for n >= 3.
fn rfx_cl_cofront_var(n: usize, ones: bool, excl: fn(usize) -> usize, tag: &str) -> Type {
    rfx_cl_cofront_block(n, ones, excl, false, tag)
}

/// [`rfx_cl_cofront_var`]; `block` also takes out `K = cons(int, cons(1, L))`, every list with
/// a 1 second, so with `ones` (each such list has one) the difference is empty.
fn rfx_cl_cofront_block(n: usize, ones: bool, excl: fn(usize) -> usize, block: bool, tag: &str) -> Type {
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| {
        let h = &Type::int() - &lit(excl(i) as i64);
        def(&format!("F{i}{tag}"), cons(Expr::Type(h), r(i - 1)))
    }));
    let not_one = Expr::Type(&Type::int() - &lit(1));
    defs.extend((1..=n).map(|k| {
        let rest = if k == 1 { r(0) } else { r(n + k - 1) };
        def(&format!("M{k}{tag}"), Expr::Union(vec![nil(), cons(not_one.clone(), rest)]))
    }));
    // 2n+1: P; 2n+k: Q_k for k = 2..n
    let next = |k: usize| if k <= n { r(2 * n + k) } else { r(0) };
    defs.push(def(&format!("P{tag}"), cons(int(), next(2))));
    defs.extend((2..=n).map(|k| def(&format!("Q{k}{tag}"), cons(Expr::Type(lit(1)), next(k + 1)))));
    // 3n+1: K1 = cons(1, L); 3n+2: K = cons(int, K1)
    defs.push(def(&format!("K1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.push(def(&format!("K{tag}"), cons(int(), r(3 * n + 1))));
    let ts = r3_instance(defs);
    let block = block.then_some(3 * n + 2);
    let u = (1..=n).chain([2 * n]).chain(block).map(|i| &ts[i]).fold(Type::empty(), |u, t| r3_union(&u, t));
    let pos = if ones { ts[2 * n + 1].clone() } else { ts[0].clone() };
    &pos - &u
}

fn rfx_cx_emitheads(n: usize, far: bool, tag: &str) -> Type {
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    for i in (1..=n).rev() {
        let h = if !far && i==n { Type::int() } else { &Type::int()-&lit(i as i64) };
        let mut branches = vec![cons(Expr::Type(h),r(0))];
        if i < n { branches.push(cons(Expr::Type(Type::int()),r(defs.len()-1))); }
        defs.push(def(&format!("G{i}{tag}"),Expr::Union(branches)));
    }
    let mut p = 0;
    for i in (1..=n).rev() {
        let idx=defs.len();
        defs.push(def(&format!("Q{i}{tag}"),cons(Expr::Type(Type::int()),r(p))));
        p=idx;
    }
    let ts=r3_instance(defs);
    &ts[p]-&ts[n]
}

// Shared staggered suffixes with heads containing the whole carrier.
fn rfx_cx_stagger_wide(n: usize, far: bool, tag: &str) -> Type {
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| def(&format!("F{i}{tag}"), cons(Expr::Type(Type::int()), r(i-1)))));
    defs.extend((1..=n).map(|i| def(&format!("M{i}{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(&Type::int()-&lit(1)), r(if i==1 {0} else {n+i-1}))]))));
    for i in 1..n-1 {
        defs.push(def(&format!("B{i}{tag}"), cons(Expr::Type(&Type::int() | &Type::atom(&format!("wide{i}"))), r(i))));
    }
    let ts = r3_instance(defs);
    let top = if far { n-1 } else { n };
    let u = (1..=top).chain([2*n]).chain(2*n+1..ts.len()).fold(Type::empty(), |u,i| r3_union(&u, &ts[i]));
    &ts[0] - &u
}


/// Stress X10: Theta(n) distinct heads along a positive chain `P1..P{n-1}` and negative chains
/// `C1..Cn` whose `far` witness `[n, n - 1, ..., 2, 1]` has Theta(n) distinct single-item runs.
fn rfx_many_heads(n: usize, far: bool, tag: &str) -> Type {
    let p_top = (n - 1).max(1);
    // 0: L; 1..=p_top: P; p_top+1..=p_top+n: F; p_top+n+1..=p_top+2n: M;
    // p_top+2n+1..=p_top+3n: B; p_top+3n+1..=p_top+4n: C
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    defs.extend((1..=p_top).map(|k| {
        let h = &lit(1) | &lit(k as i64 + 1);
        let rest = if k == 1 { r(0) } else { r(k - 1) };
        def(
            &format!("P{k}{tag}"),
            Expr::Union(vec![nil(), cons(Expr::Type(h), rest)]),
        )
    }));
    let f_base = p_top;
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| {
        def(
            &format!("F{i}{tag}"),
            cons(Expr::Type(Type::int()), r(f_base + i - 1)),
        )
    }));
    let m_base = f_base + n;
    let not_one = Expr::Type(&Type::int() - &lit(1));
    defs.extend((1..=n).map(|k| {
        let rest = if k == 1 { r(0) } else { r(m_base + k - 1) };
        def(
            &format!("M{k}{tag}"),
            Expr::Union(vec![nil(), cons(not_one.clone(), rest)]),
        )
    }));
    let b_base = m_base + n;
    let v0 = (p_top + 1) as i64;
    defs.extend((1..=n).map(|k| {
        let g = &(&lit(1) | &lit(v0)) | &lit((n + k) as i64 + 2);
        def(&format!("B{k}{tag}"), cons(Expr::Type(g), r(f_base + 1)))
    }));
    let c_base = b_base + n;
    defs.extend((1..=n).map(|k| {
        let g = &(&lit(1) | &lit(v0)) | &lit((n + k) as i64 + 2);
        def(
            &format!("C{k}{tag}"),
            cons(Expr::Type(g), r(b_base + k)),
        )
    }));
    let ts = r3_instance(defs);
    let top = if far { n - 1 } else { n };
    let u = (f_base + 1..=f_base + top)
        .chain([m_base + n])
        .chain(c_base + 1..=c_base + n)
        .map(|i| &ts[i])
        .fold(Type::empty(), |u, t| r3_union(&u, t));
    &(&ts[0] & &ts[p_top]) - &u
}

/// Stress X12: chains `R1..Rh` of distinct lengths sharing a staggered chain `P1..Ph` that
/// joins `Fd` at depth `d >= 2`.
fn rfx_stagger(n: usize, far: bool, tag: &str) -> Type {
    let d = ((n.saturating_sub(2)) / 2).max(1);
    let h = (n.saturating_sub(2).saturating_sub(d)).max(1);
    // 0: L; 1..=n: F; n+1..=2n: M; 2n+1..=2n+h: P; 2n+h+1..=2n+2h: R
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| {
        def(
            &format!("F{i}{tag}"),
            cons(Expr::Type(Type::int()), r(i - 1)),
        )
    }));
    let not_one = Expr::Type(&Type::int() - &lit(1));
    defs.extend((1..=n).map(|k| {
        let rest = if k == 1 { r(0) } else { r(n + k - 1) };
        def(
            &format!("M{k}{tag}"),
            Expr::Union(vec![nil(), cons(not_one.clone(), rest)]),
        )
    }));
    let ha = &Type::int() | &Type::atom("a");
    defs.extend((1..=h).map(|k| {
        let rest = if k == 1 { r(d) } else { r(2 * n + k - 1) };
        def(&format!("P{k}{tag}"), cons(Expr::Type(ha.clone()), rest))
    }));
    defs.extend((1..=h).map(|k| {
        let hb = &Type::int() | &Type::atom(&format!("b{k}"));
        def(
            &format!("R{k}{tag}"),
            cons(Expr::Type(hb), r(2 * n + k)),
        )
    }));
    let ts = r3_instance(defs);
    let top = if far { n - 1 } else { n };
    let r_indices = (1..=h)
        .filter(|&k| d + k + 1 <= top)
        .map(|k| 2 * n + h + k);
    (1..=top)
        .chain([2 * n])
        .chain(r_indices)
        .map(|i| &ts[i])
        .fold(Type::empty(), |u, t| r3_union(&u, t))
}

#[test]
fn a_union_of_lists_by_the_place_of_a_one_from_the_front_is_decided_in_its_size() {
    big(|| {
        for (case, want) in [
            ("front", Verdict::Empty),
            ("far", Verdict::Inhabited),
            ("tuple", Verdict::Empty),
            ("tuplefar", Verdict::Inhabited),
            ("tupleflip", Verdict::Empty),
            ("tupleflipfar", Verdict::Inhabited),
            ("multi", Verdict::Empty),
            ("multifar", Verdict::Inhabited),
            ("groups", Verdict::Empty),
            ("groupsfar", Verdict::Inhabited),
            ("groupsholes", Verdict::Empty),
            ("groupsholesfar", Verdict::Inhabited),
            ("manyheads", Verdict::Empty),
            ("manyheadsfar", Verdict::Inhabited),
            ("stagger", Verdict::Empty),
            ("staggerfar", Verdict::Inhabited),
            ("chain", Verdict::Empty),
            ("chainfar", Verdict::Inhabited),
        ] {
            let (s_runs, l_runs) = scaling::Meter::new().runs();
            let small: Vec<Type> = (0..s_runs)
                .map(|i| rfx_case(case, 8, &format!("_fs_{case}_8_{i}")))
                .collect();
            let large: Vec<Type> = (0..l_runs)
                .map(|i| rfx_case(case, 64, &format!("_fs_{case}_64_{i}")))
                .collect();
            let (si, li) = (AtomicUsize::new(0), AtomicUsize::new(0));
            scaling::check(&format!("front family {case}"), 8, |n| {
                Type::forget_emptiness();
                let t = if n == 8 {
                    &small[si.fetch_add(1, Relaxed)]
                } else {
                    &large[li.fetch_add(1, Relaxed)]
                };
                assert_eq!(t.verdict(), want, "{case} at {n}");
            });
        }
    });
}

/// Independent oracle: enumerates all lists of length `0..=max_len` over `samples` and tests
/// whether any list value is contained in `t` (`t.contains(&v)`).
fn list_oracle_inhabited(t: &Type, samples: &[Value], max_len: usize) -> bool {
    let mut cur = vec![Value::atom("nil")];
    if t.contains(&cur[0]) {
        return true;
    }
    for _ in 1..=max_len {
        let mut next = Vec::with_capacity(cur.len() * samples.len());
        for h in samples {
            for tl in &cur {
                let v = Value::atom_with("cons", vec![h.clone(), tl.clone()]);
                if t.contains(&v) {
                    return true;
                }
                next.push(v);
            }
        }
        cur = next;
    }
    false
}

/// Rewrites `Expr::Ref(i, args)` in `e` according to `inv_perm` (`old_index -> new_index`).
fn rewrite_expr_refs(e: &Expr, inv_perm: &[usize]) -> Expr {
    match e {
        Expr::Ref(i, args) => Expr::Ref(
            inv_perm[*i],
            args.iter().map(|a| rewrite_expr_refs(a, inv_perm)).collect(),
        ),
        Expr::Union(xs) => Expr::Union(
            xs.iter().map(|x| rewrite_expr_refs(x, inv_perm)).collect(),
        ),
        Expr::And(xs) => Expr::And(
            xs.iter().map(|x| rewrite_expr_refs(x, inv_perm)).collect(),
        ),
        Expr::Diff(a, b) => Expr::Diff(
            Box::new(rewrite_expr_refs(a, inv_perm)),
            Box::new(rewrite_expr_refs(b, inv_perm)),
        ),
        Expr::Not(a) => Expr::Not(Box::new(rewrite_expr_refs(a, inv_perm))),
        Expr::Tuple(xs) => Expr::Tuple(
            xs.iter().map(|x| rewrite_expr_refs(x, inv_perm)).collect(),
        ),
        Expr::Atom(name, xs) => Expr::Atom(
            name.clone(),
            xs.iter().map(|x| rewrite_expr_refs(x, inv_perm)).collect(),
        ),
        other => other.clone(),
    }
}

/// Permutes `defs` so that the new definition at position `j` is the old definition `perm[j]`,
/// rewriting all `Expr::Ref` indices so every member denotes the exact same recursive type.
fn permute_defs(defs: Vec<Def>, perm: &[usize]) -> (Vec<Def>, Vec<usize>) {
    let mut inv = vec![0; defs.len()];
    for (new_idx, &old_idx) in perm.iter().enumerate() {
        inv[old_idx] = new_idx;
    }
    let old: Vec<Def> = defs;
    let out = perm
        .iter()
        .map(|&old_idx| {
            let d = &old[old_idx];
            Def {
                name: d.name.clone(),
                params: d.params.clone(),
                body: rewrite_expr_refs(&d.body, &inv),
            }
        })
        .collect();
    (out, inv)
}

#[test]
fn lists_by_the_place_from_the_front_variants_agree_with_the_oracle() {
    big(|| {
        let int_samples = [Value::Int(0), Value::Int(1), Value::Int(2)];
        // X18: the random heads list 0, 1 and 2; 3 stands for every other integer.
        let random_int_samples = [Value::Int(0), Value::Int(1), Value::Int(2), Value::Int(3)];
        let bool_samples = [Value::Bool(false), Value::Bool(true)];
        let bool_tys = [
            Type::lit(&Value::Bool(false)).unwrap(),
            Type::lit(&Value::Bool(true)).unwrap(),
        ];
        let mut tag_id = 0usize;
        let mut next_tag = || {
            tag_id += 1;
            format!("_or{tag_id}")
        };

        for n in 1..=5 {
            for skip_idx in 0..=n {
                let skip = (skip_idx > 0).then_some(skip_idx);
                for m in 1..=n + 1 {
                    for split in [false, true] {
                        for (is_bool, all, one) in [
                            (false, Type::int(), lit(1)),
                            (true, Type::bool(), bool_tys[1].clone()),
                        ] {
                            Type::forget_emptiness();
                            let tag = next_tag();
                            let (l, u) = rfx_family(n, skip, m, &all, &one, split, &tag);
                            let t = &l - &u;
                            let samples: &[Value] = if is_bool {
                                &bool_samples[..]
                            } else {
                                &int_samples[..2]
                            };
                            let max_len = n.max(m) + 1;
                            let inhab = list_oracle_inhabited(&t, samples, max_len);
                            let want = if inhab {
                                Verdict::Inhabited
                            } else {
                                Verdict::Empty
                            };
                            assert_eq!(
                                t.verdict(),
                                want,
                                "rfx_family n={n} skip={skip:?} m={m} split={split} bool={is_bool}"
                            );
                            assert_eq!(
                                t.is_empty(),
                                !inhab,
                                "is_empty rfx_family n={n} skip={skip:?} m={m} split={split} bool={is_bool}"
                            );
                        }
                    }
                }
            }

            // Meet and pair combinations at size n.
            for (s1, s2) in [(None, Some(n)), (Some(1), Some(n)), (Some(n), Some(n))] {
                Type::forget_emptiness();
                let (t1, t2) = (next_tag(), next_tag());
                let (l1, u1) = rfx_family(n, s1, n, &Type::int(), &lit(1), false, &t1);
                let (l2, u2) = rfx_family(n, s2, n, &Type::int(), &lit(1), false, &t2);
                let f1 = &l1 - &u1;
                let f2 = &l2 - &u2;
                let meet = &f1 & &f2;
                let want_meet = if list_oracle_inhabited(&meet, &int_samples[..2], n + 1) {
                    Verdict::Inhabited
                } else {
                    Verdict::Empty
                };
                assert_eq!(meet.verdict(), want_meet, "meet n={n} s1={s1:?} s2={s2:?}");

                let pair = Type::tuple(vec![f1, f2]);
                let want_pair = if list_oracle_inhabited(&(&l1 - &u1), &int_samples[..2], n + 1)
                    && list_oracle_inhabited(&(&l2 - &u2), &int_samples[..2], n + 1)
                {
                    Verdict::Inhabited
                } else {
                    Verdict::Empty
                };
                assert_eq!(pair.verdict(), want_pair, "pair n={n} s1={s1:?} s2={s2:?}");
            }

            // Multi, groups, groupsholes, manyheads, stagger, and chain variants at small sizes.
            for m in 1..=n + 1 {
                Type::forget_emptiness();
                let tag = next_tag();
                let l = list_named(Type::int(), &tag);
                let t = &l - &rfx_multi(n, m, &tag);
                let want = if list_oracle_inhabited(&t, &int_samples, n.max(m) + 1) {
                    Verdict::Inhabited
                } else {
                    Verdict::Empty
                };
                assert_eq!(t.verdict(), want, "rfx_multi n={n} m={m}");
            }
            if n >= 2 {
                let mh_samples: Vec<Value> = (1..=n as i64).map(Value::Int).collect();
                for far in [false, true] {
                    Type::forget_emptiness();
                    let tag = next_tag();
                    let l = list_named(Type::int(), &tag);
                    let tg = &l - &rfx_groups(n, far, &tag);
                    let want_g = if list_oracle_inhabited(&tg, &int_samples[..2], n + 1) {
                        Verdict::Inhabited
                    } else {
                        Verdict::Empty
                    };
                    assert_eq!(tg.verdict(), want_g, "rfx_groups n={n} far={far}");

                    Type::forget_emptiness();
                    let tag = next_tag();
                    let l = list_named(Type::int(), &tag);
                    let tgh = &l - &rfx_groups_holes(n, far, &tag);
                    // X18: one value of every class: 1, each excluded `k + 2`, and 0 for the rest.
                    let gh_samples: Vec<Value> =
                        [0, 1].into_iter().chain(3..=n as i64 + 2).map(Value::Int).collect();
                    let want_gh = if list_oracle_inhabited(&tgh, &gh_samples, n + 1) {
                        Verdict::Inhabited
                    } else {
                        Verdict::Empty
                    };
                    assert_eq!(tgh.verdict(), want_gh, "rfx_groups_holes n={n} far={far}");

                    Type::forget_emptiness();
                    let tag = next_tag();
                    let tmh = rfx_many_heads(n, far, &tag);
                    let want_mh = if list_oracle_inhabited(&tmh, &mh_samples, n + 1) {
                        Verdict::Inhabited
                    } else {
                        Verdict::Empty
                    };
                    assert_eq!(tmh.verdict(), want_mh, "rfx_many_heads n={n} far={far}");

                    Type::forget_emptiness();
                    let tag = next_tag();
                    let l = list_named(Type::int(), &tag);
                    let tst = &l - &rfx_stagger(n, far, &tag);
                    let want_st = if list_oracle_inhabited(&tst, &int_samples[..2], n + 1) {
                        Verdict::Inhabited
                    } else {
                        Verdict::Empty
                    };
                    assert_eq!(tst.verdict(), want_st, "rfx_stagger n={n} far={far}");

                    Type::forget_emptiness();
                    let tag = next_tag();
                    let l = list_named(Type::int(), &tag);
                    let tc = &l - &rfx_chain(n, far, &tag);
                    let want_c = if list_oracle_inhabited(&tc, &int_samples[..2], n + 1) {
                        Verdict::Inhabited
                    } else {
                        Verdict::Empty
                    };
                    assert_eq!(tc.verdict(), want_c, "rfx_chain n={n} far={far}");
                }
            }

            // Tuple and tupleflip variants at small sizes.
            let pair_samples = [
                Value::tuple(vec![Value::Int(0), Value::Int(0)]),
                Value::tuple(vec![Value::Int(1), Value::Int(0)]),
                Value::tuple(vec![Value::Int(0), Value::Int(1)]),
                Value::tuple(vec![Value::Int(1), Value::Int(1)]),
            ];
            for case in ["tuple", "tuplefar", "tupleflip", "tupleflipfar"] {
                Type::forget_emptiness();
                let tag = next_tag();
                let t = rfx_case(case, n, &tag);
                let want = if list_oracle_inhabited(&t, &pair_samples, n + 1) {
                    Verdict::Inhabited
                } else {
                    Verdict::Empty
                };
                assert_eq!(t.verdict(), want, "{case} n={n}");
            }
        }

        // Random small prefix-chain families over int (including cofinite heads) and bool.
        let mut seed = 0x5eed_cafe_d00d_u64;
        let mut rng = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let head_for = |bits: u64, is_bool: bool| -> Type {
            if is_bool {
                match bits % 3 {
                    0 => bool_tys[0].clone(),
                    1 => bool_tys[1].clone(),
                    _ => Type::bool(),
                }
            } else {
                let mask = (bits % 7) + 1;
                if bits & 8 != 0 {
                    let mut t = Type::int();
                    for i in 0..3 {
                        if (mask >> i) & 1 == 0 {
                            t = &t - &lit(i as i64);
                        }
                    }
                    t
                } else {
                    let mut t = Type::empty();
                    for i in 0..3 {
                        if (mask >> i) & 1 != 0 {
                            t = &t | &lit(i as i64);
                        }
                    }
                    t
                }
            }
        };
        for _ in 0..40 {
            Type::forget_emptiness();
            let is_bool = (rng() & 1) != 0;
            let all = if is_bool { Type::bool() } else { Type::int() };
            let samples: &[Value] = if is_bool {
                &bool_samples
            } else {
                &random_int_samples
            };
            let tag = next_tag();
            let mut defs = vec![def(
                &format!("L{tag}"),
                Expr::Union(vec![nil(), cons(Expr::Type(all.clone()), r(0))]),
            )];
            let num_chains = 2 + (rng() % 3) as usize;
            let mut endpoints = Vec::new();
            let mut max_depth = 1usize;
            for c in 0..num_chains {
                let depth = 1 + (rng() % 4) as usize;
                max_depth = max_depth.max(depth);
                let allow_nil = (rng() & 1) != 0;
                for k in 1..=depth {
                    let h = head_for(rng(), is_bool);
                    let prev = if k == 1 { 0 } else { defs.len() - 1 };
                    let step = cons(Expr::Type(h), r(prev));
                    let body = if allow_nil && ((rng() & 1) != 0 || k == 1) {
                        Expr::Union(vec![nil(), step])
                    } else {
                        step
                    };
                    defs.push(def(&format!("C{c}_{k}{tag}"), body));
                }
                endpoints.push(defs.len() - 1);
            }
            let ts = Group::new(defs).unwrap().instance(vec![]);
            let u = endpoints
                .iter()
                .map(|&i| &ts[i])
                .fold(Type::empty(), |u, t| &u | t);
            let l = list_named(all, &tag);
            let t = &l - &u;
            let inhab = list_oracle_inhabited(&t, samples, max_depth + 1);
            let want = if inhab {
                Verdict::Inhabited
            } else {
                Verdict::Empty
            };
            assert_eq!(t.verdict(), want, "random chain seed={seed:#x}");
            assert_eq!(t.is_empty(), !inhab, "is_empty random chain seed={seed:#x}");
        }
    });
}

#[test]
fn lists_by_the_place_from_the_front_verdicts_are_independent_of_order() {
    big(|| {
        let int_samples = [Value::Int(0), Value::Int(1)];
        let mut tag_id = 0usize;
        let mut next_tag = || {
            tag_id += 1;
            format!("_ord{tag_id}")
        };
        for n in 2..=6 {
            for skip in [None, Some(1), Some(n / 2), Some(n)] {
                let tag_base = next_tag();
                let want = {
                    Type::forget_emptiness();
                    let (l, u) = rfx_family(n, skip, n, &Type::int(), &lit(1), false, &tag_base);
                    let t = &l - &u;
                    let v = t.verdict();
                    let oracle = if list_oracle_inhabited(&t, &int_samples, n + 1) {
                        Verdict::Inhabited
                    } else {
                        Verdict::Empty
                    };
                    assert_eq!(v, oracle, "base order n={n} skip={skip:?}");
                    v
                };

                // Test permutations of both Group definition indices and union operand order,
                // including staggered chains sharing `Fd` and holes chains.
                for perm_kind in 0..4 {
                    Type::forget_emptiness();
                    let tag = next_tag();
                    let mut defs = vec![def(
                        &format!("L{tag}"),
                        Expr::Union(vec![nil(), cons(int(), r(0))]),
                    )];
                    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
                    defs.extend((2..=n).map(|i| def(&format!("F{i}{tag}"), cons(int(), r(i - 1)))));
                    let not_one = Expr::Type(&Type::int() - &lit(1));
                    defs.extend((1..=n).map(|k| {
                        let rest = if k == 1 { r(0) } else { r(n + k - 1) };
                        def(
                            &format!("M{k}{tag}"),
                            Expr::Union(vec![nil(), cons(not_one.clone(), rest)]),
                        )
                    }));
                    let d = (n / 2).max(1);
                    let ha = &Type::int() | &Type::atom("a");
                    defs.push(def(&format!("P1{tag}"), cons(Expr::Type(ha.clone()), r(d))));
                    defs.push(def(&format!("P2{tag}"), cons(Expr::Type(ha), r(2 * n + 1))));

                    let k_len = defs.len();
                    let mut perm: Vec<usize> = (0..k_len).collect();
                    match perm_kind {
                        0 => perm.reverse(),
                        1 => perm.rotate_left(k_len / 2),
                        2 => {
                            perm = (0..k_len)
                                .step_by(2)
                                .chain((1..k_len).step_by(2))
                                .collect();
                        }
                        _ => {
                            perm[1..].reverse();
                        }
                    }
                    let (pdefs, inv) = permute_defs(defs, &perm);
                    let ts = Group::new(pdefs).unwrap().instance(vec![]);
                    let mut u_indices: Vec<usize> = (1..=n)
                        .filter(|&i| Some(i) != skip)
                        .chain([2 * n])
                        .collect();
                    if d + 1 <= n && skip != Some(d + 1) {
                        u_indices.push(2 * n + 1);
                    }
                    if d + 2 <= n && skip != Some(d + 2) {
                        u_indices.push(2 * n + 2);
                    }
                    if perm_kind % 2 == 1 {
                        u_indices.reverse();
                    } else {
                        let mid = u_indices.len() / 2;
                        u_indices.rotate_left(mid);
                    }
                    let u = u_indices
                        .iter()
                        .map(|&old_i| &ts[inv[old_i]])
                        .fold(Type::empty(), |acc, t| &acc | t);
                    let l = list_named(Type::int(), &tag);
                    let t = &l - &u;
                    assert_eq!(
                        t.verdict(),
                        want,
                        "order-independence n={n} skip={skip:?} perm_kind={perm_kind}"
                    );
                }
            }
        }
    });
}

// Ported from the round-3 peer patch (oracle, order and scaling tests).
// Independent finite-state oracle. A state is the set of still-matching negative
// equations; the positive carrier is implicit. This explores every class, not
// the sweep's selected class, and never calls emptiness or type membership.
#[derive(Clone)]
struct R3Node { stop: bool, mask: u64, next: usize }

fn r3_spec(n: usize, m: usize, skip: usize, holes: usize, stagger: bool) -> (Vec<R3Node>, Vec<usize>, u64) {
    let all = (1u64 << (n+3))-1;
    let mut ns = vec![R3Node { stop:true,mask:all,next:0 }];
    for i in 1..=n { ns.push(R3Node {stop:false,mask:if i==1 {2} else {all},next:if i==1 {0} else {i-1}}); }
    for i in 1..=m { ns.push(R3Node {stop:true,mask:all^2,next:if i==1 {0} else {n+i-1}}); }
    let mut roots: Vec<_> = (1..=n).filter(|&i|i!=skip).chain([n+m]).collect();
    for k in 0..holes {
        if stagger {
            let b=ns.len();
            ns.push(R3Node {stop:false,mask:all^(1 << (k+2)),next:1+k%n});
            roots.push(b);
            continue;
        }
        let a=ns.len();
        ns.push(R3Node {stop:false,mask:all^(1 << (k+2)),next:1});
        let b=ns.len();
        ns.push(R3Node {stop:false,mask:all,next:a});
        roots.push(b);
    }
    (ns,roots,all)
}

fn r3_oracle(ns: &[R3Node], roots: &[usize], all:u64) -> bool {
    let mut root=roots.to_vec(); root.sort_unstable(); root.dedup();
    let mut seen=BTreeSet::new(); let mut todo=vec![root];
    while let Some(state)=todo.pop() {
        if !seen.insert(state.clone()) {continue;}
        if state.iter().all(|&i| !ns[i].stop) {return true;}
        for bit in 0..64 {
            if all & (1u64 << bit)==0 {continue;}
            let mut next:Vec<_>=state.iter().filter(|&&i| ns[i].mask & (1u64<<bit)!=0).map(|&i|ns[i].next).collect();
            next.sort_unstable(); next.dedup(); todo.push(next);
        }
    }
    false
}

fn r3_build(ns:&[R3Node], roots:&[usize], all:u64, reverse:bool, tag:&str, mode:usize) -> Type {
    let size=ns.len();
    let index=|i|if reverse {size-1-i} else {i};
    let mut defs=Vec::new();
    for (i,nd) in ns.iter().enumerate() {
        let mut h=if nd.mask&1!=0 {Type::int()} else {Type::empty()};
        for bit in 1..64 {
            if all & (1u64<<bit)==0 {continue;}
            let v=lit(bit as i64);
            if nd.mask & (1u64<<bit)!=0 {h=&h|&v;} else {h=&h-&v;}
        }
        if mode==1 {h=Type::tuple(vec![h,Type::int()]);}
        if mode==2 {
            h=Type::empty();
            for (bit,value) in [(0,false),(1,true)] {
                if nd.mask & (1<<bit)!=0 {h=&h | &Type::lit(&Value::Bool(value)).unwrap();}
            }
        }
        let step=cons(Expr::Type(h),r(index(nd.next)));
        let body=if nd.stop {
            Expr::Union(if reverse {vec![step,nil()]} else {vec![nil(),step]})
        } else {step};
        defs.push(def(&format!("R3_{i}_{tag}"),body));
    }
    if reverse {defs.reverse();}
    let ts=Group::new(defs).unwrap().instance(vec![]);
    let mut order=roots.to_vec(); if reverse {order.reverse();}
    let u=order.iter().fold(Type::empty(),|u,&i|&u|&ts[index(i)]);
    &ts[index(0)]-&u
}

#[test]
fn r3_cofinite_redundant_oracle_and_order() {
    big(|| {
        let mut cases=0;
        for n in 1..=6 {
            for m in 1..=n+2 {
                for skip in 0..=n {
                    for (mode,holes,stagger) in [(0,0,false),(0,1,false),(0,n,false),(1,0,false),(1,1,false),(1,n,false),(2,0,false),(0,n,true),(1,n,true)] {
                        let (ns,roots,mut all)=r3_spec(n,m,skip,holes,stagger);
                        if mode==2 {all=3;}
                        let expected=if r3_oracle(&ns,&roots,all) {Verdict::Inhabited} else {Verdict::Empty};
                        let tag=format!("{n}_{m}_{skip}_{holes}_{stagger}");
                        let a=r3_build(&ns,&roots,all,false,&tag,mode);
                        let b=r3_build(&ns,&roots,all,true,&tag,mode);
                        Type::forget_emptiness();
                        let av=a.verdict(); let bv=b.verdict();
                        assert_eq!(av,expected,"oracle n={n} m={m} skip={skip} holes={holes} mode={mode} stagger={stagger}");
                        assert_eq!(bv,av,"definition/union order {tag}");
                        assert_eq!(a.is_empty(),expected==Verdict::Empty,"is_empty {tag}");
                        Type::forget_emptiness();
                        assert_eq!(b.verdict(),bv,"b first {tag}");
                        assert_eq!(a.verdict(),av,"a second {tag}");
                        cases+=1;
                    }
                }
            }
        }
        eprintln!("R3 cofinite oracle/order cases={cases}");
    });
}

#[test]
fn r3_stress_scale_prebuilt() {
    for (case,want) in [
        ("bool",Verdict::Empty),
        ("boolfar",Verdict::Inhabited),
        ("chain",Verdict::Empty),
        ("chainfar",Verdict::Inhabited),
        ("clmanyheads",Verdict::Empty),
        ("clmanyheadsfar",Verdict::Inhabited),
        ("clstagger",Verdict::Empty),
        ("clstaggerfar",Verdict::Inhabited),
        ("cxstagger",Verdict::Empty),
        ("cxstaggerfar",Verdict::Inhabited),
        ("cxstaggerwide",Verdict::Empty),
        ("cxstaggerwidefar",Verdict::Inhabited),
        ("emitheads",Verdict::Empty),
        ("emitheadsfar",Verdict::Inhabited),
        ("far",Verdict::Inhabited),
        ("front",Verdict::Empty),
        ("groups",Verdict::Empty),
        ("groupsfar",Verdict::Inhabited),
        ("groupsholes",Verdict::Empty),
        ("groupsholesfar",Verdict::Inhabited),
        ("groupssingles",Verdict::Empty),
        ("groupssinglesfar",Verdict::Inhabited),
        ("manyheads",Verdict::Empty),
        ("manyheadsfar",Verdict::Inhabited),
        ("meet",Verdict::Empty),
        ("mlong",Verdict::Inhabited),
        ("mshort",Verdict::Empty),
        ("multi",Verdict::Empty),
        ("multifar",Verdict::Inhabited),
        ("one",Verdict::Empty),
        ("onetwo",Verdict::Inhabited),
        ("pair",Verdict::Empty),
        ("pairfar",Verdict::Inhabited),
        ("skip1",Verdict::Inhabited),
        ("skipmid",Verdict::Inhabited),
        ("split",Verdict::Empty),
        ("splitfar",Verdict::Inhabited),
        ("stagger",Verdict::Empty),
        ("staggerfar",Verdict::Inhabited),
        ("tuple",Verdict::Empty),
        ("tuplefar",Verdict::Inhabited),
        ("tupleflip",Verdict::Empty),
        ("tupleflipfar",Verdict::Inhabited),
    ] {
        big(move || {
            let inputs:Vec<_>=[8,64].into_iter().map(|n| (n,rfx_case(case,n,&format!("_scale3_{case}_{n}")))).collect();
            scaling::check(case,8,|n| {
                Type::forget_emptiness();
                let t=&inputs.iter().find(|(k,_)|*k==n).unwrap().1;
                assert_eq!(t.verdict(),want,"{case} n={n}");
            });
        });
    }
}
// Test input construction only. The kernel reads neither this flag nor any
// environment variable. Reindex all references, then restore the returned
// vector's indexing so every caller denotes the same equations.
thread_local! { static R3_REVERSE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
fn r3_instance(mut defs: Vec<Def>) -> Vec<Type> {
    let reverse=R3_REVERSE.with(|x|x.get());
    if reverse {
        let count=defs.len();
        for d in &mut defs {
            let mut todo=vec![&mut d.body];
            while let Some(e)=todo.pop() {
                match e {
                    Expr::Ref(i,args)=>{*i=count-1-*i;todo.extend(args.iter_mut());},
                    Expr::Union(xs)=>{xs.reverse();todo.extend(xs.iter_mut());},
                    Expr::And(xs)|Expr::Tuple(xs)|Expr::Atom(_,xs)=>todo.extend(xs.iter_mut()),
                    Expr::Not(x)=>todo.push(x),
                    Expr::Diff(a,b)=>{todo.push(a);todo.push(b);},
                    Expr::Morphism(a,b,c)=>{todo.push(a);todo.push(b);todo.push(c);},
                    Expr::Type(_)|Expr::Param(_)=>{},
                }
            }
        }
        defs.reverse();
    }
    let mut ts=Group::new(defs).unwrap().instance(vec![]);
    if reverse {ts.reverse();}
    ts
}
fn r3_union(a:&Type,b:&Type)->Type {
    if R3_REVERSE.with(|x|x.get()) {b|a} else {a|b}
}

#[test]
fn r3_all_probe_and_family_orders() {
    big(|| {
        let cases=["front","far","skip1","skipmid","bool","boolfar","mshort","mlong","split","splitfar","meet","pair","pairfar","tuple","tuplefar","tupleflip","tupleflipfar","multi","multifar","groups","groupsfar","groupsholes","groupsholesfar","groupssingles","groupssinglesfar","cxstagger","cxstaggerfar","cxstaggerwide","cxstaggerwidefar","clmanyheads","clmanyheadsfar","clstagger","clstaggerfar","clstaggerholes","clcofront","clcofrontones","clcofrontsame","clcofrontsameones","clcofrontsameblock","clcofrontshared","emitheads","emitheadsfar","manyheads","manyheadsfar","stagger","staggerfar","chain","chainfar","one","onetwo","end","boundaryinside","boundaryoutside","cxprivateheads","cxprivateheadsfar","manyheadsv0","manyheadsfarv0"];
        let mut count=0;
        for case in cases {
            for n in 3..=6 {
                let tag=format!("_order3_{case}_{n}");
                R3_REVERSE.with(|x|x.set(false));
                let a=rfx_case(case,n,&tag);
                R3_REVERSE.with(|x|x.set(true));
                let b=rfx_case(case,n,&tag);
                R3_REVERSE.with(|x|x.set(false));
                Type::forget_emptiness(); let av=a.verdict();let bv=b.verdict();
                assert_eq!(av,bv,"probe definition/operand order {case} {n}");
                Type::forget_emptiness(); assert_eq!(b.verdict(),bv);assert_eq!(a.verdict(),av);
                count+=1;
            }
        }
        for (all,one) in [(Type::int(),lit(1)),(Type::bool(),Type::lit(&Value::Bool(true)).unwrap()),(Type::tuple(vec![Type::int(),Type::int()]),Type::tuple(vec![lit(1),Type::int()]))] {
            for n in 1..=6 {
                for skip in std::iter::once(None).chain((1..=n).map(Some)) {
                    for m in 1..=n+2 {
                        for split in [false,true] {
                            let tag=format!("_orderf3_{count}");
                            R3_REVERSE.with(|x|x.set(false));
                            let (l,u)=rfx_family(n,skip,m,&all,&one,split,&tag);let a=&l-&u;
                            R3_REVERSE.with(|x|x.set(true));
                            let (l,u)=rfx_family(n,skip,m,&all,&one,split,&tag);let b=&l-&u;
                            R3_REVERSE.with(|x|x.set(false));
                            Type::forget_emptiness();let av=a.verdict();let bv=b.verdict();
                            assert_eq!(av,bv,"family definitions/operands n={n} skip={skip:?} m={m} split={split}");
                            Type::forget_emptiness();assert_eq!(b.verdict(),bv);assert_eq!(a.verdict(),av);
                            count+=1;
                        }
                    }
                }
            }
        }
        eprintln!("R3 all-probe/family order cases={count}");
    });
}

#[test]
#[ignore]
fn r3_cofinite_survey() {
    big(|| {
        let (mut bad, mut cases) = (0, 0);
        for n in 1..=6 {
            for m in 1..=n+2 {
                for skip in 0..=n {
                    for (mode,holes,stagger) in [(0,0,false),(0,1,false),(0,n,false),(1,0,false),(1,1,false),(1,n,false),(2,0,false),(0,n,true),(1,n,true)] {
                        let (ns,roots,mut all)=r3_spec(n,m,skip,holes,stagger);
                        if mode==2 {all=3;}
                        let expected=if r3_oracle(&ns,&roots,all) {Verdict::Inhabited} else {Verdict::Empty};
                        let tag=format!("s{n}_{m}_{skip}_{holes}_{stagger}_{mode}");
                        let a=r3_build(&ns,&roots,all,false,&tag,mode);
                        let b=r3_build(&ns,&roots,all,true,&tag,mode);
                        Type::forget_emptiness();
                        let av=a.verdict(); Type::forget_emptiness(); let bv=b.verdict();
                        cases+=1;
                        if av!=expected || bv!=expected {
                            bad+=1;
                            eprintln!("MISMATCH n={n} m={m} skip={skip} mode={mode} holes={holes} stagger={stagger} want={expected:?} fwd={av:?} rev={bv:?}");
                        }
                    }
                }
            }
        }
        eprintln!("survey cases={cases} mismatches={bad}");
    });
}

// ---- Codex R4 tests and helpers, verbatim ----

#[test]
fn codex_r3_variants_agree_with_the_oracle() {
    big(|| {
        let int_ty = Type::int();
        let one_ty = lit(1);
        let bool_ty = Type::bool();
        let yes_ty = Type::lit(&Value::Bool(true)).unwrap();
        let tup_all = Type::tuple(vec![int_ty.clone(), int_ty.clone()]);
        let tup_one = Type::tuple(vec![one_ty.clone(), int_ty.clone()]);

        let carriers: [(&str, &Type, &Type, Vec<Value>); 3] = [
            ("int", &int_ty, &one_ty, vec![Value::Int(0), Value::Int(1)]),
            (
                "bool",
                &bool_ty,
                &yes_ty,
                vec![Value::Bool(false), Value::Bool(true)],
            ),
            (
                "tuple",
                &tup_all,
                &tup_one,
                vec![
                    Value::tuple(vec![Value::Int(0), Value::Int(0)]),
                    Value::tuple(vec![Value::Int(1), Value::Int(0)]),
                ],
            ),
        ];

        let mut seq = 0usize;
        for (cname, all, one, alpha) in &carriers {
            for n in 1..=6 {
                for skip in std::iter::once(None).chain((1..=n).map(Some)) {
                    for m in 1..=n + 2 {
                        for split in [false, true] {
                            seq += 1;
                            Type::forget_emptiness();
                            let tag = format!("_or_{cname}_{seq}");
                            let (l, u) = rfx_family(n, skip, m, all, one, split, &tag);
                            let t = &l - &u;
                            let inhab = oracle_inhabited(&t, alpha, n.max(m) + 1);
                            let want = if inhab {
                                Verdict::Inhabited
                            } else {
                                Verdict::Empty
                            };
                            assert_eq!(
                                t.verdict(),
                                want,
                                "carrier={cname} n={n} skip={skip:?} m={m} split={split}"
                            );
                            assert_eq!(
                                t.is_empty(),
                                !inhab,
                                "is_empty carrier={cname} n={n} skip={skip:?} m={m} split={split}"
                            );
                        }
                    }
                }
            }
        }

        let int_alpha = [Value::Int(0), Value::Int(1)];
        let multi_alpha = [Value::Int(0), Value::Int(1), Value::Int(2)];
        let group_alpha = [Value::Int(0), Value::Int(1), Value::atom("a1")];
        for n in 2..=6 {
            for m in 1..=n + 1 {
                seq += 1;
                Type::forget_emptiness();
                let tag = format!("_orm_{seq}");
                let l = list_named(Type::int(), &tag);
                let t = &l - &rfx_multi(n, m, &tag);
                let inhab = oracle_inhabited(&t, &multi_alpha, n.max(m) + 1);
                let want = if inhab {
                    Verdict::Inhabited
                } else {
                    Verdict::Empty
                };
                assert_eq!(t.verdict(), want, "multi n={n} m={m}");
                assert_eq!(t.is_empty(), !inhab, "multi is_empty n={n} m={m}");
            }
            for far in [false, true] {
                for which in ["chain", "groups", "one"] {
                    seq += 1;
                    Type::forget_emptiness();
                    let tag = format!("_orcg_{seq}");
                    let t = match (which, far) {
                        ("chain", false) => rfx_case("chain", n, &tag),
                        ("chain", true) => rfx_case("chainfar", n, &tag),
                        ("groups", false) => rfx_case("groups", n, &tag),
                        ("groups", true) => rfx_case("groupsfar", n, &tag),
                        ("one", false) => rfx_case("one", n, &tag),
                        _ => rfx_case("onetwo", n, &tag),
                    };
                    let alpha: &[Value] = if which == "groups" {
                        &group_alpha
                    } else if which == "one" {
                        &multi_alpha
                    } else {
                        &int_alpha
                    };
                    let inhab = oracle_inhabited(&t, alpha, n + 1);
                    let want = if inhab {
                        Verdict::Inhabited
                    } else {
                        Verdict::Empty
                    };
                    assert_eq!(t.verdict(), want, "{which} far={far} n={n}");
                    assert_eq!(t.is_empty(), !inhab, "{which} is_empty far={far} n={n}");
                }
            }
            for s1 in [None, Some(1), Some(n / 2), Some(n)] {
                for s2 in [None, Some(1), Some(n - 1), Some(n)] {
                    seq += 1;
                    Type::forget_emptiness();
                    let tag1 = format!("_ormp1_{seq}");
                    let tag2 = format!("_ormp2_{seq}");
                    let (l1, u1) = rfx_family(n, s1, n, &int_ty, &one_ty, false, &tag1);
                    let (l2, u2) = rfx_family(n, s2, n, &int_ty, &one_ty, false, &tag2);
                    let t1 = &l1 - &u1;
                    let t2 = &l2 - &u2;
                    let i1 = oracle_inhabited(&t1, &int_alpha, n + 1);
                    let i2 = oracle_inhabited(&t2, &int_alpha, n + 1);
                    let meet = &t1 & &t2;
                    let i_meet = oracle_inhabited(&meet, &int_alpha, n + 1);
                    assert_eq!(
                        meet.verdict(),
                        if i_meet {
                            Verdict::Inhabited
                        } else {
                            Verdict::Empty
                        },
                        "meet n={n} s1={s1:?} s2={s2:?}"
                    );
                    assert_eq!(meet.is_empty(), !i_meet, "meet is_empty n={n}");
                    let pair = Type::tuple(vec![t1, t2]);
                    let i_pair = i1 && i2;
                    assert_eq!(
                        pair.verdict(),
                        if i_pair {
                            Verdict::Inhabited
                        } else {
                            Verdict::Empty
                        },
                        "pair n={n} s1={s1:?} s2={s2:?}"
                    );
                    assert_eq!(pair.is_empty(), !i_pair, "pair is_empty n={n}");
                }
            }
        }

        // Random small chain families over `int` with predicates from `{1, 2, 1|2, int\1, int\2, int\(1|2), int}`.
        let preds = [
            lit(1),
            lit(2),
            &lit(1) | &lit(2),
            &Type::int() - &lit(1),
            &Type::int() - &lit(2),
            &Type::int() - &(&lit(1) | &lit(2)),
            Type::int(),
        ];
        let mut rng = 0x9e37_79b9_7f4a_7c15u64;
        let mut next_u64 = || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };
        for trial in 0..120 {
            Type::forget_emptiness();
            let tag = format!("_orr_{trial}");
            let mut defs = vec![def(
                &format!("L{tag}"),
                Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
            )];
            let num_neg = 1 + (next_u64() % 5) as usize;
            let mut neg_roots = Vec::new();
            let mut max_d = 1usize;
            for c in 0..num_neg {
                let d = 1 + (next_u64() % 5) as usize;
                max_d = max_d.max(d);
                let leaf_h = preds[(next_u64() as usize) % preds.len()].clone();
                let leaf_stop = (next_u64() & 1) != 0;
                let step_h = if (next_u64() % 4) == 0 {
                    preds[(next_u64() as usize) % preds.len()].clone()
                } else {
                    Type::int()
                };
                let step_stop = (next_u64() & 1) != 0;
                let base_idx = defs.len();
                let leaf_body = if leaf_stop {
                    Expr::Union(vec![nil(), cons(Expr::Type(leaf_h), r(0))])
                } else {
                    cons(Expr::Type(leaf_h), r(0))
                };
                defs.push(def(&format!("N{c}_1{tag}"), leaf_body));
                for k in 2..=d {
                    let step_body = if step_stop {
                        Expr::Union(vec![
                            nil(),
                            cons(Expr::Type(step_h.clone()), r(base_idx + k - 2)),
                        ])
                    } else {
                        cons(Expr::Type(step_h.clone()), r(base_idx + k - 2))
                    };
                    defs.push(def(&format!("N{c}_{k}{tag}"), step_body));
                }
                neg_roots.push(base_idx + d - 1);
            }
            let reverse_defs = defs.clone();
            let ts = r3_instance(defs);
            let u = neg_roots
                .iter()
                .map(|&i| &ts[i])
                .fold(Type::empty(), |acc, x| &acc | x);
            let t = &ts[0] - &u;
            let inhab = oracle_inhabited(&t, &multi_alpha, max_d + 1);
            match t.verdict() {
                Verdict::Empty => assert!(!inhab, "random trial {trial} unsound Empty"),
                Verdict::Inhabited => assert!(inhab, "random trial {trial} unsound Inhabited"),
                Verdict::Refused(_) => {}
            }
            if t.is_empty() {
                assert!(!inhab, "random trial {trial} unsound is_empty=true");
            }
            let original = t.verdict();
            R3_REVERSE.with(|x| x.set(true));
            let rev = r3_instance(reverse_defs);
            let ru = neg_roots.iter().fold(Type::empty(), |u, &i| r3_union(&u, &rev[i]));
            let rt = &rev[0] - &ru;
            R3_REVERSE.with(|x| x.set(false));
            Type::forget_emptiness();
            assert_eq!(rt.verdict(), original, "random definition/union order {trial}");
            assert_eq!(t.verdict(), original, "random query order {trial}");
        }
    });
}

fn oracle_inhabited(t: &Type, alphabet: &[Value], max_len: usize) -> bool {
    let mut lists = vec![Value::atom("nil")];
    if t.contains(&lists[0]) {
        return true;
    }
    for _ in 1..=max_len {
        let mut next = Vec::with_capacity(alphabet.len() * lists.len());
        for a in alphabet {
            for tail in &lists {
                let v = Value::atom_with("cons", vec![a.clone(), tail.clone()]);
                if t.contains(&v) {
                    return true;
                }
                next.push(v);
            }
        }
        lists = next;
    }
    false
}

// Inside the short-escape class even with one excluded value repeated at many heads.
// Outside removes the holes; it is exactly the ordinary Empty front family.
fn r4_boundary(n: usize, holes: bool, tag: &str) -> Type {
    let mut defs=vec![def(&format!("L{tag}"), Expr::Union(vec![nil(),cons(int(),r(0))]))];
    defs.push(def(&format!("F1{tag}"),cons(Expr::Type(lit(1)),r(0))));
    for i in 2..=n {
        let h=if holes {&Type::int()-&lit(4)} else {Type::int()};
        defs.push(def(&format!("F{i}{tag}"),cons(Expr::Type(h),r(i-1))));
    }
    for i in 1..=n {
        defs.push(def(&format!("M{i}{tag}"),Expr::Union(vec![nil(),cons(Expr::Type(&Type::int()-&lit(1)),r(if i==1 {0} else {n+i-1}))])));
    }
    let ts=r3_instance(defs);
    let u=(1..=n).chain([2*n]).fold(Type::empty(),|u,i|r3_union(&u,&ts[i]));
    u
}

#[test]
#[ignore]
fn r4_diagnostic_routes_and_head_width() {
    big(|| {
        for case in ["front","emitheads","emitheadsfar","cxstagger","clcofront","clstaggerholes"] {
            let t=rfx_case(case,8,&format!("route_{case}"));
            eprintln!("route {case} {:?}",t.sweep_verdict());
        }
        for width in [4,8,12,16] {
            let all=Type::tuple(vec![Type::bool();width]);
            let mut coords=vec![Type::bool();width];
            coords[0]=Type::lit(&Value::Bool(true)).unwrap();
            let one=Type::tuple(coords);
            let (l,u)=rfx_family(2,Some(2),2,&all,&one,false,&format!("width_{width}"));
            let t=&l-&u;
            Type::forget_emptiness();
            let mut got=None;
            let w=scaling::Meter::new().work(||got=Some(t.verdict()));
            eprintln!("headwidth {width} {:?} units {} bytes {}",got,w.units,w.bytes);
            assert_eq!(got,Some(Verdict::Inhabited));
        }
    });
}

#[test]
fn r4_exact_classes_random_and_short_escape() {
    big(|| {
        let mut seed=0x9183ab12u64;
        let mut rng=|| {seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;seed};
        let mut cases=0;
        for trial in 0..200 {
            let n=2+(rng()%4) as usize;
            let m=1+(rng()%(n+2) as u64) as usize;
            let (mut ns,roots,all)=r3_spec(n,m,0,n,true);
            // Bit zero is a fresh integer; bits 1..=n+2 are all listed literals.
            for nd in &mut ns[1..] { if rng()%3==0 {nd.mask=rng()&all;} }
            let inhab=r3_oracle(&ns,&roots,all);
            let a=r3_build(&ns,&roots,all,false,&format!("r4random{trial}"),0);
            let b=r3_build(&ns,&roots,all,true,&format!("r4random{trial}"),0);
            let av=a.sweep_verdict(); let bv=b.sweep_verdict();
            assert_eq!(av,bv,"sweep definition order trial {trial}");
            for t in [&a,&b] {
                Type::forget_emptiness();
                match t.verdict() {
                    Verdict::Empty=>assert!(!inhab,"oracle has witness {trial}"),
                    Verdict::Inhabited=>assert!(inhab,"oracle empty {trial}"),
                    Verdict::Refused(_)=>{},
                }
                assert!(!t.is_empty() || !inhab);
            }
            cases+=1;
        }
        for n in 2..=6 {
            for (case,want) in [("clcofront",Verdict::Inhabited),("clstaggerholes",Verdict::Inhabited),("boundaryinside",Verdict::Inhabited),("boundaryoutside",Verdict::Empty)] {
                let tag=format!("r4boundary{n}{case}");
                R3_REVERSE.with(|v|v.set(false)); let a=rfx_case(case,n,&tag);
                R3_REVERSE.with(|v|v.set(true)); let b=rfx_case(case,n,&tag);
                R3_REVERSE.with(|v|v.set(false));
                assert_eq!(a.sweep_verdict(),Some(want),"{case} {n}");
                assert_eq!(b.sweep_verdict(),Some(want),"reverse {case} {n}");
                Type::forget_emptiness();assert_eq!(a.verdict(),want);assert_eq!(b.verdict(),want);
                Type::forget_emptiness();assert_eq!(b.verdict(),want);assert_eq!(a.verdict(),want);
                cases+=1;
            }
        }
        eprintln!("R4 exact-class random/boundary cases={cases}");
    });
}

fn r4_private_heads(n: usize, far: bool, tag: &str) -> Type {
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    let mut roots = Vec::new();
    for i in 1..=n {
        let h = if !far && i == n { Type::int() } else { &Type::int() - &lit(i as i64) };
        let leaf = defs.len();
        defs.push(def(&format!("H{i}{tag}"), cons(Expr::Type(h), r(0))));
        for j in 1..i {
            let prev = defs.len() - 1;
            defs.push(def(&format!("P{i}_{j}{tag}"), cons(Expr::Type(Type::int()), r(prev))));
        }
        roots.push(leaf + i - 1);
    }
    // A positive uniform prefix supplies the minimum length requirement.
    let mut positive = 0;
    for i in (1..=n).rev() {
        let idx = defs.len();
        defs.push(def(&format!("Q{i}{tag}"), cons(Expr::Type(Type::int()), r(positive))));
        positive = idx;
    }
    let ts = r3_instance(defs);
    let u = roots.iter().fold(Type::empty(), |u, &i| r3_union(&u, &ts[i]));
    &(&ts[0] & &ts[positive]) - &u
}

fn rfx_manyheads_v0(n: usize, far: bool, tag: &str) -> Type {
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    let mut roots = Vec::new();
    for i in 1..=n {
        let h = if !far && i == n { Type::int() } else { &Type::int() - &lit(i as i64) };
        let leaf = defs.len();
        defs.push(def(&format!("H{i}{tag}"), cons(Expr::Type(h), r(0))));
        for j in 1..i {
            let prev = defs.len() - 1;
            defs.push(def(&format!("P{i}_{j}{tag}"), cons(Expr::Type(Type::int()), r(prev))));
        }
        roots.push(leaf + i - 1);
    }
    // A positive uniform prefix supplies the minimum length requirement.
    let mut positive = 0;
    for i in (1..=n).rev() {
        let idx = defs.len();
        defs.push(def(&format!("Q{i}{tag}"), cons(Expr::Type(Type::int()), r(positive))));
        positive = idx;
    }
    let ts = r3_instance(defs);
    let u = roots.iter().fold(Type::empty(), |u, &i| r3_union(&u, &ts[i]));
    &ts[positive] - &u
}


// ---- Gemini R4 tests and helpers ----

/// Q2 boundary families for the Disjoint-Hole Spine class:
/// - `overlap = false` (`clstaggerholesin`): just inside the class (link `2n` excludes `{2n+2, 2n+3}`,
///   disjoint from all earlier links' holes `{3}..{2n+1}`; decided in O(n log n)).
/// - `overlap = true` (`clstaggerholesout`): just outside the class (link `2n` excludes `{3}`,
///   overlapping link `1`'s hole `{3}`; rejected by the disjoint-hole check in O(n log n) and left
///   to the base search).
fn rfx_cl_stagger_boundary(n: usize, overlap: bool, tag: &str) -> Type {
    let m = 2 * n;
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    defs.extend((1..=m).map(|i| {
        let h = if i == m {
            if overlap {
                &Type::int() - &lit(3)
            } else {
                &(&Type::int() - &lit(m as i64 + 2)) - &lit(m as i64 + 3)
            }
        } else {
            &Type::int() - &lit(i as i64 + 2)
        };
        def(&format!("Y{i}{tag}"), cons(Expr::Type(h), r(i + 1)))
    }));
    defs.push(def(
        &format!("Y{}{tag}", m + 1),
        cons(Expr::Type(lit(1)), r(0)),
    ));
    defs.extend((1..=m + 1).map(|j| {
        let h = if j <= n + 1 {
            Type::int()
        } else {
            &Type::int() - &lit(1)
        };
        let next = if j == m + 1 { r(0) } else { r(m + 2 + j) };
        def(
            &format!("N{j}{tag}"),
            Expr::Union(vec![nil(), cons(Expr::Type(h), next)]),
        )
    }));
    let ts = Group::new(defs).unwrap().instance(vec![]);
    (1..=n)
        .map(|k| &ts[k])
        .chain([&ts[m + 2]])
        .fold(Type::empty(), |u, t| &u | t)
}

#[test]
fn lists_by_the_place_from_the_front_variants_agree_with_the_oracle_gemini() {
    big(|| {
        let int_samples = [Value::Int(0), Value::Int(1), Value::Int(2)];
        let bool_samples = [Value::Bool(false), Value::Bool(true)];
        let bool_tys = [
            Type::lit(&Value::Bool(false)).unwrap(),
            Type::lit(&Value::Bool(true)).unwrap(),
        ];
        let mut tag_id = 0usize;
        let mut next_tag = || {
            tag_id += 1;
            format!("_or{tag_id}")
        };

        for n in 1..=5 {
            for skip_idx in 0..=n {
                let skip = (skip_idx > 0).then_some(skip_idx);
                for m in 1..=n + 1 {
                    for split in [false, true] {
                        for (is_bool, all, one) in [
                            (false, Type::int(), lit(1)),
                            (true, Type::bool(), bool_tys[1].clone()),
                        ] {
                            Type::forget_emptiness();
                            let tag = next_tag();
                            let (l, u) = rfx_family(n, skip, m, &all, &one, split, &tag);
                            let t = &l - &u;
                            let samples: &[Value] = if is_bool {
                                &bool_samples[..]
                            } else {
                                &int_samples[..2]
                            };
                            let max_len = n.max(m) + 1;
                            let inhab = list_oracle_inhabited(&t, samples, max_len);
                            let want = if inhab {
                                Verdict::Inhabited
                            } else {
                                Verdict::Empty
                            };
                            assert_eq!(
                                t.verdict(),
                                want,
                                "rfx_family n={n} skip={skip:?} m={m} split={split} bool={is_bool}"
                            );
                            assert_eq!(
                                t.is_empty(),
                                !inhab,
                                "is_empty rfx_family n={n} skip={skip:?} m={m} split={split} bool={is_bool}"
                            );
                        }
                    }
                }
            }

            // Meet and pair combinations at size n.
            for (s1, s2) in [(None, Some(n)), (Some(1), Some(n)), (Some(n), Some(n))] {
                Type::forget_emptiness();
                let (t1, t2) = (next_tag(), next_tag());
                let (l1, u1) = rfx_family(n, s1, n, &Type::int(), &lit(1), false, &t1);
                let (l2, u2) = rfx_family(n, s2, n, &Type::int(), &lit(1), false, &t2);
                let f1 = &l1 - &u1;
                let f2 = &l2 - &u2;
                let meet = &f1 & &f2;
                let want_meet = if list_oracle_inhabited(&meet, &int_samples[..2], n + 1) {
                    Verdict::Inhabited
                } else {
                    Verdict::Empty
                };
                assert_eq!(meet.verdict(), want_meet, "meet n={n} s1={s1:?} s2={s2:?}");

                let pair = Type::tuple(vec![f1, f2]);
                let want_pair = if list_oracle_inhabited(&(&l1 - &u1), &int_samples[..2], n + 1)
                    && list_oracle_inhabited(&(&l2 - &u2), &int_samples[..2], n + 1)
                {
                    Verdict::Inhabited
                } else {
                    Verdict::Empty
                };
                assert_eq!(pair.verdict(), want_pair, "pair n={n} s1={s1:?} s2={s2:?}");
            }

            // Multi, groups, groupsholes, manyheads, stagger, and chain variants at small sizes.
            for m in 1..=n + 1 {
                Type::forget_emptiness();
                let tag = next_tag();
                let l = list_named(Type::int(), &tag);
                let t = &l - &rfx_multi(n, m, &tag);
                let want = if list_oracle_inhabited(&t, &int_samples, n.max(m) + 1) {
                    Verdict::Inhabited
                } else {
                    Verdict::Empty
                };
                assert_eq!(t.verdict(), want, "rfx_multi n={n} m={m}");
            }
            if n >= 2 {
                let mh_samples: Vec<Value> = (0..=(n as i64 + 3)).map(Value::Int).collect();
                for far in [false, true] {
                    for case in [
                        if far { "groupsfar" } else { "groups" },
                        if far { "groupsholesfar" } else { "groupsholes" },
                        if far { "groupssinglesfar" } else { "groupssingles" },
                        if far { "manyheadsfar" } else { "manyheads" },
                        if far { "staggerfar" } else { "stagger" },
                        if far { "chainfar" } else { "chain" },
                        if far { "cxstaggerfar" } else { "cxstagger" },
                        if far { "cxstaggerwidefar" } else { "cxstaggerwide" },
                        if far { "emitheadsfar" } else { "emitheads" },
                        if far { "clmanyheadsfar" } else { "clmanyheads" },
                    ] {
                        if n <= 3 || !matches!(case, "manyheads" | "manyheadsfar" | "groupsholes" | "groupsholesfar" | "groupssingles" | "groupssinglesfar" | "cxstagger" | "cxstaggerfar" | "emitheads" | "emitheadsfar" | "clmanyheads" | "clmanyheadsfar") {
                            Type::forget_emptiness();
                            let tag = next_tag();
                            let t = rfx_case(case, n, &tag);
                            let samples = if matches!(case, "manyheads" | "manyheadsfar" | "groupsholes" | "groupsholesfar" | "groupssingles" | "groupssinglesfar" | "cxstagger" | "cxstaggerfar" | "emitheads" | "emitheadsfar" | "clmanyheads" | "clmanyheadsfar") {
                                &mh_samples[..]
                            } else {
                                &int_samples[..2]
                            };
                            let want = if list_oracle_inhabited(&t, samples, n + 1) {
                                Verdict::Inhabited
                            } else {
                                Verdict::Empty
                            };
                            assert_eq!(t.sweep_verdict(), Some(want), "sweep {case} n={n}");
                            Type::forget_emptiness();
                            assert_eq!(t.verdict(), want, "{case} n={n}");
                        }
                    }
                }
                if n <= 2 {
                    let stag_samples: Vec<Value> =
                        (0..=(2 * n as i64 + 3)).map(Value::Int).collect();
                    for case in [
                        "clstagger",
                        "clstaggerfar",
                        "clstaggerholes",
                        "clstaggerholesin",
                        "clstaggerholesout",
                        "clcofront",
                    ] {
                        Type::forget_emptiness();
                        let tag = next_tag();
                        let t = rfx_case(case, n, &tag);
                        let samples = if matches!(case, "clstagger" | "clstaggerfar") {
                            &int_samples[..2]
                        } else if case == "clcofront" {
                            &mh_samples[..]
                        } else {
                            &stag_samples[..]
                        };
                        let max_l = if case == "clcofront" { n + 1 } else { 2 * n + 1 };
                        let want = if list_oracle_inhabited(&t, samples, max_l) {
                            Verdict::Inhabited
                        } else {
                            Verdict::Empty
                        };
                        if case == "clstaggerholesout" {
                            // The prefix chains leave this case to the search (Gemini R4); in the
                            // combined tree the front sweep decides it.
                            assert_eq!(t.chain_verdict(), None, "chains {case} n={n}");
                            assert_eq!(t.sweep_verdict(), Some(want), "sweep {case} n={n}");
                        } else {
                            assert_eq!(t.sweep_verdict(), Some(want), "sweep {case} n={n}");
                        }
                        Type::forget_emptiness();
                        assert_eq!(t.verdict(), want, "{case} n={n}");
                    }
                }
            }

            // Tuple and tupleflip variants at small sizes.
            let pair_samples = [
                Value::tuple(vec![Value::Int(0), Value::Int(0)]),
                Value::tuple(vec![Value::Int(1), Value::Int(0)]),
                Value::tuple(vec![Value::Int(0), Value::Int(1)]),
                Value::tuple(vec![Value::Int(1), Value::Int(1)]),
            ];
            for case in ["tuple", "tuplefar", "tupleflip", "tupleflipfar"] {
                Type::forget_emptiness();
                let tag = next_tag();
                let t = rfx_case(case, n, &tag);
                let want = if list_oracle_inhabited(&t, &pair_samples, n + 1) {
                    Verdict::Inhabited
                } else {
                    Verdict::Empty
                };
                assert_eq!(t.verdict(), want, "{case} n={n}");
            }
        }

        // Random small prefix-chain families over int (including cofinite heads) and bool.
        // Fix X18: heads exclude/include literals from 0..4, and `rand_int_samples` includes
        // every literal 0..4 plus one fresh integer 4 so every equivalence class of the head
        // predicates is sampled.
        let rand_int_samples = [
            Value::Int(0),
            Value::Int(1),
            Value::Int(2),
            Value::Int(3),
            Value::Int(4),
        ];
        let mut seed = 0x5eed_cafe_d00d_u64;
        let mut rng = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let head_for = |bits: u64, is_bool: bool| -> Type {
            if is_bool {
                match bits % 3 {
                    0 => bool_tys[0].clone(),
                    1 => bool_tys[1].clone(),
                    _ => Type::bool(),
                }
            } else {
                let mask = (bits % 15) + 1;
                if bits & 16 != 0 {
                    let mut t = Type::int();
                    for i in 0..4 {
                        if (mask >> i) & 1 == 0 {
                            t = &t - &lit(i as i64);
                        }
                    }
                    t
                } else {
                    let mut t = Type::empty();
                    for i in 0..4 {
                        if (mask >> i) & 1 != 0 {
                            t = &t | &lit(i as i64);
                        }
                    }
                    t
                }
            }
        };
        for _ in 0..60 {
            Type::forget_emptiness();
            let is_bool = (rng() & 1) != 0;
            let all = if is_bool { Type::bool() } else { Type::int() };
            let samples: &[Value] = if is_bool {
                &bool_samples
            } else {
                &rand_int_samples
            };
            let tag = next_tag();
            let mut defs = vec![def(
                &format!("L{tag}"),
                Expr::Union(vec![nil(), cons(Expr::Type(all.clone()), r(0))]),
            )];
            let num_chains = 2 + (rng() % 3) as usize;
            let mut endpoints = Vec::new();
            let mut max_depth = 1usize;
            for c in 0..num_chains {
                let depth = 1 + (rng() % 4) as usize;
                max_depth = max_depth.max(depth);
                let allow_nil = (rng() & 1) != 0;
                for k in 1..=depth {
                    let h = head_for(rng(), is_bool);
                    let prev = if k == 1 { 0 } else { defs.len() - 1 };
                    let step = cons(Expr::Type(h), r(prev));
                    let body = if allow_nil && ((rng() & 1) != 0 || k == 1) {
                        Expr::Union(vec![nil(), step])
                    } else {
                        step
                    };
                    defs.push(def(&format!("C{c}_{k}{tag}"), body));
                }
                endpoints.push(defs.len() - 1);
            }
            let ts = Group::new(defs).unwrap().instance(vec![]);
            let u = endpoints
                .iter()
                .map(|&i| &ts[i])
                .fold(Type::empty(), |u, t| &u | t);
            let l = list_named(all, &tag);
            let t = &l - &u;
            let inhab = list_oracle_inhabited(&t, samples, max_depth + 1);
            let want = if inhab {
                Verdict::Inhabited
            } else {
                Verdict::Empty
            };
            if let Some(sv) = t.sweep_verdict() {
                assert_eq!(sv, want, "sweep random chain seed={seed:#x}");
            }
            Type::forget_emptiness();
            match t.verdict() {
                Verdict::Empty => assert!(!inhab, "random chain seed={seed:#x}"),
                Verdict::Inhabited => assert!(inhab, "random chain seed={seed:#x}"),
                Verdict::Refused(_) => {}
            }
            assert!(!(t.is_empty() && inhab), "is_empty random chain seed={seed:#x}");
        }

        // Random in-class prefix-chain families (uniform carrier prefix per chain, cofinite/finite
        // leaf heads over 0..4, sampled over 0..=4): must be decided (Empty or Inhabited, never
        // Refused) and agree with the oracle.
        for _ in 0..60 {
            Type::forget_emptiness();
            let is_bool = (rng() & 1) != 0;
            let all = if is_bool { Type::bool() } else { Type::int() };
            let samples: &[Value] = if is_bool {
                &bool_samples
            } else {
                &rand_int_samples
            };
            let tag = next_tag();
            let mut defs = vec![def(
                &format!("L{tag}"),
                Expr::Union(vec![nil(), cons(Expr::Type(all.clone()), r(0))]),
            )];
            let num_chains = 2 + (rng() % 4) as usize;
            let mut endpoints = Vec::new();
            let mut max_depth = 1usize;
            for c in 0..num_chains {
                let depth = 1 + (rng() % 4) as usize;
                max_depth = max_depth.max(depth);
                let leaf_h = head_for(rng(), is_bool);
                let leaf_nil = c == 0 || (rng() & 1) != 0;
                let step_nil = c == 0 || (leaf_nil && (rng() & 1) != 0);
                for k in 1..=depth {
                    let h = if k == 1 { leaf_h.clone() } else { all.clone() };
                    let prev = if k == 1 { 0 } else { defs.len() - 1 };
                    let step = cons(Expr::Type(h), r(prev));
                    let has_nil = if k == 1 { leaf_nil } else { step_nil };
                    let body = if has_nil {
                        Expr::Union(vec![nil(), step])
                    } else {
                        step
                    };
                    defs.push(def(&format!("U{c}_{k}{tag}"), body));
                }
                endpoints.push(defs.len() - 1);
            }
            let ts = Group::new(defs).unwrap().instance(vec![]);
            let u = endpoints
                .iter()
                .map(|&i| &ts[i])
                .fold(Type::empty(), |u, t| &u | t);
            let l = list_named(all, &tag);
            let t = &l - &u;
            let inhab = list_oracle_inhabited(&t, samples, max_depth + 1);
            let want = if inhab {
                Verdict::Inhabited
            } else {
                Verdict::Empty
            };
            assert_eq!(t.sweep_verdict(), Some(want), "sweep uniform random seed={seed:#x}");
            Type::forget_emptiness();
            assert_eq!(t.verdict(), want, "uniform random seed={seed:#x}");
            assert_eq!(t.is_empty(), !inhab, "is_empty uniform random seed={seed:#x}");
        }
    });
}

#[test]
fn lists_by_the_place_from_the_front_verdicts_are_independent_of_order_gemini() {
    big(|| {
        let int_samples = [Value::Int(0), Value::Int(1)];
        let mut tag_id = 0usize;
        let mut next_tag = || {
            tag_id += 1;
            format!("_ord{tag_id}")
        };
        for n in 2..=6 {
            for skip in [None, Some(1), Some(n / 2), Some(n)] {
                let tag_base = next_tag();
                let want = {
                    Type::forget_emptiness();
                    let (l, u) = rfx_family(n, skip, n, &Type::int(), &lit(1), false, &tag_base);
                    let t = &l - &u;
                    let v = t.verdict();
                    let oracle = if list_oracle_inhabited(&t, &int_samples, n + 1) {
                        Verdict::Inhabited
                    } else {
                        Verdict::Empty
                    };
                    assert_eq!(v, oracle, "base order n={n} skip={skip:?}");
                    v
                };

                // Test permutations of both Group definition indices and union operand order,
                // including staggered chains sharing `Fd` and holes chains.
                for perm_kind in 0..4 {
                    Type::forget_emptiness();
                    let tag = next_tag();
                    let mut defs = vec![def(
                        &format!("L{tag}"),
                        Expr::Union(vec![nil(), cons(int(), r(0))]),
                    )];
                    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
                    defs.extend((2..=n).map(|i| def(&format!("F{i}{tag}"), cons(int(), r(i - 1)))));
                    let not_one = Expr::Type(&Type::int() - &lit(1));
                    defs.extend((1..=n).map(|k| {
                        let rest = if k == 1 { r(0) } else { r(n + k - 1) };
                        def(
                            &format!("M{k}{tag}"),
                            Expr::Union(vec![nil(), cons(not_one.clone(), rest)]),
                        )
                    }));
                    let d = (n / 2).max(1);
                    let ha = &Type::int() | &Type::atom("a");
                    defs.push(def(&format!("P1{tag}"), cons(Expr::Type(ha.clone()), r(d))));
                    defs.push(def(&format!("P2{tag}"), cons(Expr::Type(ha), r(2 * n + 1))));

                    let k_len = defs.len();
                    let mut perm: Vec<usize> = (0..k_len).collect();
                    match perm_kind {
                        0 => perm.reverse(),
                        1 => perm.rotate_left(k_len / 2),
                        2 => {
                            perm = (0..k_len)
                                .step_by(2)
                                .chain((1..k_len).step_by(2))
                                .collect();
                        }
                        _ => {
                            perm[1..].reverse();
                        }
                    }
                    let (pdefs, inv) = permute_defs(defs, &perm);
                    let ts = Group::new(pdefs).unwrap().instance(vec![]);
                    let mut u_indices: Vec<usize> = (1..=n)
                        .filter(|&i| Some(i) != skip)
                        .chain([2 * n])
                        .collect();
                    if d + 1 <= n && skip != Some(d + 1) {
                        u_indices.push(2 * n + 1);
                    }
                    if d + 2 <= n && skip != Some(d + 2) {
                        u_indices.push(2 * n + 2);
                    }
                    if perm_kind % 2 == 1 {
                        u_indices.reverse();
                    } else {
                        let mid = u_indices.len() / 2;
                        u_indices.rotate_left(mid);
                    }
                    let u = u_indices
                        .iter()
                        .map(|&old_i| &ts[inv[old_i]])
                        .fold(Type::empty(), |acc, t| &acc | t);
                    let l = list_named(Type::int(), &tag);
                    let t = &l - &u;
                    assert_eq!(
                        t.sweep_verdict(),
                        Some(want),
                        "sweep order-independence n={n} skip={skip:?} perm_kind={perm_kind}"
                    );
                    Type::forget_emptiness();
                    assert_eq!(
                        t.verdict(),
                        want,
                        "order-independence n={n} skip={skip:?} perm_kind={perm_kind}"
                    );
                }
            }
        }
    });
}

#[test]
fn a_union_of_lists_by_the_place_of_a_one_from_the_front_is_decided_in_its_size_gemini() {
    big(|| {
        for (case, want) in [
            ("front", Verdict::Empty),
            ("far", Verdict::Inhabited),
            ("tuple", Verdict::Empty),
            ("tuplefar", Verdict::Inhabited),
            ("tupleflip", Verdict::Empty),
            ("tupleflipfar", Verdict::Inhabited),
            ("multi", Verdict::Empty),
            ("multifar", Verdict::Inhabited),
            ("groups", Verdict::Empty),
            ("groupsfar", Verdict::Inhabited),
            ("groupsholes", Verdict::Empty),
            ("groupsholesfar", Verdict::Inhabited),
            ("groupssingles", Verdict::Empty),
            ("groupssinglesfar", Verdict::Inhabited),
            ("cxstagger", Verdict::Empty),
            ("cxstaggerfar", Verdict::Inhabited),
            ("cxstaggerwide", Verdict::Empty),
            ("cxstaggerwidefar", Verdict::Inhabited),
            ("clmanyheads", Verdict::Empty),
            ("clmanyheadsfar", Verdict::Inhabited),
            ("clstagger", Verdict::Empty),
            ("clstaggerfar", Verdict::Inhabited),
            ("clstaggerholes", Verdict::Inhabited),
            ("clstaggerholesin", Verdict::Inhabited),
            ("clcofront", Verdict::Inhabited),
            ("emitheads", Verdict::Empty),
            ("emitheadsfar", Verdict::Inhabited),
            ("manyheads", Verdict::Empty),
            ("manyheadsfar", Verdict::Inhabited),
            ("stagger", Verdict::Empty),
            ("staggerfar", Verdict::Inhabited),
            ("chain", Verdict::Empty),
            ("chainfar", Verdict::Inhabited),
        ] {
            let (s_runs, l_runs) = scaling::Meter::new().runs();
            let small: Vec<Type> = (0..s_runs)
                .map(|i| rfx_case(case, 8, &format!("_fs_{case}_8_{i}")))
                .collect();
            let large: Vec<Type> = (0..l_runs)
                .map(|i| rfx_case(case, 64, &format!("_fs_{case}_64_{i}")))
                .collect();
            let (si, li) = (AtomicUsize::new(0), AtomicUsize::new(0));
            scaling::check(&format!("front family {case}"), 8, |n| {
                Type::forget_emptiness();
                let t = if n == 8 {
                    &small[si.fetch_add(1, Relaxed)]
                } else {
                    &large[li.fetch_add(1, Relaxed)]
                };
                assert_eq!(t.verdict(), want, "{case} at {n}");
            });
        }
    });
}


// Round-4 union probe (orchestrator): the new families of all three reviewers under u4 names.
fn u4_inst(defs: Vec<Def>) -> Vec<Type> {
    Group::new(defs).unwrap().instance(vec![])
}

fn u4_cofront_block(n: usize, ones: bool, excl: fn(usize) -> usize, block: bool, tag: &str) -> Type {
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| {
        let h = &Type::int() - &lit(excl(i) as i64);
        def(&format!("F{i}{tag}"), cons(Expr::Type(h), r(i - 1)))
    }));
    let not_one = Expr::Type(&Type::int() - &lit(1));
    defs.extend((1..=n).map(|k| {
        let rest = if k == 1 { r(0) } else { r(n + k - 1) };
        def(&format!("M{k}{tag}"), Expr::Union(vec![nil(), cons(not_one.clone(), rest)]))
    }));
    let next = |k: usize| if k <= n { r(2 * n + k) } else { r(0) };
    defs.push(def(&format!("P{tag}"), cons(Expr::Type(Type::int()), next(2))));
    defs.extend((2..=n).map(|k| def(&format!("Q{k}{tag}"), cons(Expr::Type(lit(1)), next(k + 1)))));
    defs.push(def(&format!("K1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.push(def(&format!("K{tag}"), cons(Expr::Type(Type::int()), r(3 * n + 1))));
    let ts = u4_inst(defs);
    let block = block.then_some(3 * n + 2);
    let u = (1..=n).chain([2 * n]).chain(block).map(|i| &ts[i]).fold(Type::empty(), |u, t| &u | t);
    let pos = if ones { ts[2 * n + 1].clone() } else { ts[0].clone() };
    &pos - &u
}

fn u4_stagger_boundary(n: usize, overlap: bool, tag: &str) -> Type {
    let m = 2 * n;
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    defs.extend((1..=m).map(|i| {
        let h = if i == m {
            if overlap { &Type::int() - &lit(3) } else { &(&Type::int() - &lit(m as i64 + 2)) - &lit(m as i64 + 3) }
        } else {
            &Type::int() - &lit(i as i64 + 2)
        };
        def(&format!("Y{i}{tag}"), cons(Expr::Type(h), r(i + 1)))
    }));
    defs.push(def(&format!("Y{}{tag}", m + 1), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((1..=m + 1).map(|j| {
        let h = if j <= n + 1 { Type::int() } else { &Type::int() - &lit(1) };
        let next = if j == m + 1 { r(0) } else { r(m + 2 + j) };
        def(&format!("N{j}{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(h), next)]))
    }));
    let ts = u4_inst(defs);
    let l = ts[0].clone();
    let u = (1..=n).map(|k| &ts[k]).chain([&ts[m + 2]]).fold(Type::empty(), |u, t| &u | t);
    &l - &u
}

fn u4_boundary(n: usize, holes: bool, tag: &str) -> Type {
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]))];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    for i in 2..=n {
        let h = if holes { &Type::int() - &lit(4) } else { Type::int() };
        defs.push(def(&format!("F{i}{tag}"), cons(Expr::Type(h), r(i - 1))));
    }
    for i in 1..=n {
        defs.push(def(&format!("M{i}{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(&Type::int() - &lit(1)), r(if i == 1 { 0 } else { n + i - 1 }))])));
    }
    let ts = u4_inst(defs);
    let l = ts[0].clone();
    let u = (1..=n).chain([2 * n]).fold(Type::empty(), |u, i| &u | &ts[i]);
    &l - &u
}

fn u4_width(w: usize, tag: &str) -> Type {
    let all = Type::tuple(vec![Type::bool(); w]);
    let mut coords = vec![Type::bool(); w];
    coords[0] = Type::lit(&Value::Bool(true)).unwrap();
    let one = Type::tuple(coords);
    let (l, u) = rfx_family(2, Some(2), 2, &all, &one, false, tag);
    &l - &u
}

// Round 5: holes not nested as prefixes. P - (u3 | u4) has the one value class [4, 2, 1, 1, ..];
// a matching that gives step 1 to u3 (x1 = 3) leaves u4 unkillable and would answer Empty.
fn r5_greedy(tag: &str) -> Type {
    let not = |i: i64| Expr::Type(&Type::int() - &lit(i));
    let one = || Expr::Type(lit(1));
    let defs = vec![
        def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(int(), r(0))])),
        def(&format!("U1{tag}"), cons(one(), r(0))),
        def(&format!("U2{tag}"), cons(not(2), r(1))),
        def(&format!("U3{tag}"), cons(not(3), r(2))),
        def(&format!("U4{tag}"), cons(not(4), r(3))),
        def(&format!("P{tag}"), cons(int(), cons(Expr::Type(&lit(2) | &lit(5)), cons(one(), cons(one(), r(0)))))),
    ];
    let ts = u4_inst(defs);
    &ts[5] - &(&ts[3] | &ts[4])
}

// Round 5: the one-chain 3-SAT reduction of R4 (variable i at place i, clause c at place
// k + c(k+1)), checked against brute force over every set of distinct 3-literal clauses.
fn r5_sat_type(k: usize, cls: &[Vec<(usize, bool)>], tag: &str) -> Type {
    let rc = |c: usize| k + c * (k + 1);
    let len = rc(cls.len());
    let mut h = vec![Type::int(); len + 1];
    h[1] = lit(2);
    for (c, cl) in cls.iter().enumerate() {
        for &(i, pos) in cl {
            h[rc(c + 1) - i + 1] = &Type::int() - &lit(if pos { 0 } else { 1 });
        }
    }
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(int(), r(0))]))];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(h[1].clone()), r(0))));
    defs.extend((2..=len).map(|d| def(&format!("F{d}{tag}"), cons(Expr::Type(h[d].clone()), r(d - 1)))));
    let clause_place = |p: usize| p > k && (p - k) % (k + 1) == 0;
    let mut e = nil();
    for p in (1..=len).rev() {
        let head = if p <= k { &lit(0) | &lit(1) } else if clause_place(p) { lit(2) } else { lit(7) };
        e = cons(Expr::Type(head), e);
    }
    defs.push(def(&format!("P{tag}"), e));
    let ts = u4_inst(defs);
    let u = (1..=len).fold(Type::empty(), |u, d| &u | &ts[d]);
    &ts[len + 1] - &u
}

fn r5_sat(k: usize, cls: &[Vec<(usize, bool)>]) -> bool {
    // Value 0 at place i makes a positive literal true; value 1 a negative one.
    (0..1u32 << k).any(|a| cls.iter().all(|cl| cl.iter().any(|&(i, pos)| ((a >> (i - 1)) & 1 == 0) == pos)))
}

#[test]
#[ignore]
fn r5_sat_check() {
    let spec: Vec<usize> = std::env::var("R5SAT").unwrap_or("3,1,4,3,0,1".into()).split(',').map(|s| s.parse().unwrap()).collect();
    r5_sat_run(spec);
}

/// Round 6: every formula of three clauses over three variables (2,600), as in `r5_sat_check`.
/// Many have clauses of three literals, whose rows have three atoms in the escape solve, so a
/// solve that gave `Empty` from the first two atoms of such a row answers some of them wrongly.
#[test]
fn r6_every_three_clause_formula_on_three_variables_is_decided_correctly() {
    r5_sat_run(vec![3, 3, 3, 0, 0, 1]);
}

fn r5_sat_run(spec: Vec<usize>) {
    // k variables, mlo..=mhi clauses of wmin..=3 literals on distinct variables, shard of nsh.
    let (k, mlo, mhi, wmin, shard, nsh) = (spec[0], spec[1], spec[2], spec[3], spec[4], spec[5]);
    let mut all: Vec<Vec<(usize, bool)>> = vec![];
    for vs in 1u32..1 << k {
        let vars: Vec<usize> = (1..=k).filter(|i| vs >> (i - 1) & 1 == 1).collect();
        if vars.len() < wmin || vars.len() > 3 { continue; }
        for s in 0..1u32 << vars.len() {
            all.push(vars.iter().enumerate().map(|(j, &i)| (i, s >> j & 1 == 0)).collect());
        }
    }
    let mut seen = 0usize;
    big(move || {
        let mut counts = std::collections::BTreeMap::new();
        let (mut bad, mut units, mut most) = (0, 0u64, 0u64);
        let n = all.len();
        let mut stack: Vec<Vec<usize>> = vec![vec![]];
        while let Some(set) = stack.pop() {
            let mine = set.len() >= mlo && { seen += 1; seen % nsh == shard };
            if mine {
                let cls: Vec<_> = set.iter().map(|&i| all[i].clone()).collect();
                Type::forget_emptiness();
                let t = r5_sat_type(k, &cls, &format!("_sat{k}_{}", set.iter().map(|i| i.to_string()).collect::<Vec<_>>().join("_")));
                let sat = r5_sat(k, &cls);
                let mut m = scaling::Meter::new();
                let mut v = None;
                let w = m.work(|| v = Some(t.verdict()));
                let v = v.unwrap();
                units += w.units as u64;
                most = most.max(w.units as u64);
                let wrong = matches!((&v, sat), (Verdict::Empty, true) | (Verdict::Inhabited, false));
                if wrong { bad += 1; eprintln!("r5sat WRONG k {k} {cls:?} sat {sat} {v:?}"); }
                *counts.entry(format!("m{} sat {sat} {v:?}", set.len())).or_insert(0usize) += 1;
                // Which mechanism answers on its own: the front sweep, the prefix chains, or
                // neither (the instance is in the remainder and goes to the search).
                Type::forget_emptiness();
                let sw = t.sweep_verdict();
                Type::forget_emptiness();
                let ch = t.chain_verdict();
                let by = match (&sw, &ch) {
                    (None, _) => "none",
                    (Some(_), Some(_)) => "chains",
                    (Some(_), None) => "front",
                };
                if matches!((&sw, sat), (Some(Verdict::Empty), true) | (Some(Verdict::Inhabited), false)) {
                    bad += 1;
                    eprintln!("r5sat WRONG SWEEP k {k} {cls:?} sat {sat} {sw:?}");
                }
                if matches!((&ch, sat), (Some(Verdict::Empty), true) | (Some(Verdict::Inhabited), false)) {
                    bad += 1;
                    eprintln!("r5sat WRONG CHAINS k {k} {cls:?} sat {sat} {ch:?}");
                }
                *counts.entry(format!("mech m{} {by} {sw:?} chains {ch:?}", set.len())).or_insert(0usize) += 1;
            }
            if set.len() < mhi {
                let from = set.last().map_or(0, |&l| l + 1);
                for i in from..n { let mut s = set.clone(); s.push(i); stack.push(s); }
            }
        }
        for (key, c) in &counts { eprintln!("r5sat k {k} {key}: {c}"); }
        eprintln!("r5sat k {k} m {mlo}..{mhi} w {wmin} shard {shard}/{nsh} cases {} wrong {bad} units {units} most {most}", counts.iter().filter(|(k, _)| !k.starts_with("mech")).map(|(_, c)| c).sum::<usize>());
        assert_eq!(bad, 0);
    });
}

/// Round 5: every probe case of rounds 3 and 4 (and `u4width`, of `w` columns) is decided in
/// its size, with the verdict the round-5 measurements found. `end` is out of shape and kept
/// on the search, so it is not here.
fn r5_cases_scale(cases: &[(&str, Verdict)]) {
    cases_scale_from(cases, 8);
}

/// [`r5_cases_scale`] at the sizes `base` and `8 * base`.
fn cases_scale_from(cases: &[(&str, Verdict)], base: usize) {
    big(|| {
        for &(case, want) in cases {
            let (s_runs, l_runs) = scaling::Meter::new().runs();
            let small: Vec<Type> = (0..s_runs)
                .map(|i| rfx_case(case, base, &format!("_r5s_{case}_{base}_{i}")))
                .collect();
            let large: Vec<Type> = (0..l_runs)
                .map(|i| rfx_case(case, 8 * base, &format!("_r5s_{case}_{}_{i}", 8 * base)))
                .collect();
            let (si, li) = (AtomicUsize::new(0), AtomicUsize::new(0));
            scaling::check(&format!("probe case {case}"), base, |n| {
                Type::forget_emptiness();
                let t = if n == base {
                    &small[si.fetch_add(1, Relaxed)]
                } else {
                    &large[li.fetch_add(1, Relaxed)]
                };
                assert_eq!(t.verdict(), want, "{case} at {n}");
            });
        }
    });
}

#[test]
fn r5_probe_cases_are_decided_in_their_size_1() {
    r5_cases_scale(&[
        ("front", Verdict::Empty),
        ("far", Verdict::Inhabited),
        ("skip1", Verdict::Inhabited),
        ("skipmid", Verdict::Inhabited),
        ("bool", Verdict::Empty),
        ("boolfar", Verdict::Inhabited),
        ("mshort", Verdict::Empty),
        ("mlong", Verdict::Inhabited),
        ("split", Verdict::Empty),
        ("splitfar", Verdict::Inhabited),
        ("meet", Verdict::Empty),
        ("pair", Verdict::Empty),
        ("pairfar", Verdict::Inhabited),
        ("tuple", Verdict::Empty),
        ("tuplefar", Verdict::Inhabited),
        ("tupleflip", Verdict::Empty),
        ("tupleflipfar", Verdict::Inhabited),
        ("multi", Verdict::Empty),
        ("multifar", Verdict::Inhabited),
    ]);
}

#[test]
fn r5_probe_cases_are_decided_in_their_size_2() {
    r5_cases_scale(&[
        ("groups", Verdict::Empty),
        ("groupsfar", Verdict::Inhabited),
        ("groupsholes", Verdict::Empty),
        ("groupsholesfar", Verdict::Inhabited),
        ("groupssingles", Verdict::Empty),
        ("groupssinglesfar", Verdict::Inhabited),
        ("cxstagger", Verdict::Empty),
        ("cxstaggerfar", Verdict::Inhabited),
        ("cxstaggerwide", Verdict::Empty),
        ("cxstaggerwidefar", Verdict::Inhabited),
        ("emitheads", Verdict::Empty),
        ("emitheadsfar", Verdict::Inhabited),
        ("manyheads", Verdict::Empty),
        ("manyheadsfar", Verdict::Inhabited),
        ("stagger", Verdict::Empty),
        ("staggerfar", Verdict::Inhabited),
        ("clmanyheads", Verdict::Empty),
        ("clmanyheadsfar", Verdict::Inhabited),
        ("clstagger", Verdict::Empty),
    ]);
}

#[test]
fn r5_probe_cases_are_decided_in_their_size_3() {
    r5_cases_scale(&[
        ("clstaggerfar", Verdict::Inhabited),
        ("clstaggerholes", Verdict::Inhabited),
        ("clcofront", Verdict::Inhabited),
        ("chain", Verdict::Empty),
        ("chainfar", Verdict::Inhabited),
        ("one", Verdict::Empty),
        ("onetwo", Verdict::Inhabited),
        ("u4cofrontones", Verdict::Empty),
        ("u4cofrontsame", Verdict::Inhabited),
        ("u4cofrontsameones", Verdict::Inhabited),
        ("u4cofrontsameblock", Verdict::Empty),
        ("u4cofrontshared", Verdict::Inhabited),
        ("u4holesin", Verdict::Inhabited),
        ("u4holesout", Verdict::Inhabited),
        ("u4boundaryin", Verdict::Inhabited),
        ("u4boundaryout", Verdict::Empty),
        ("u4width", Verdict::Inhabited),
    ]);
}

/// Round 5: a greedy matching of non-nested holes to steps answered Empty here (Gemini R4
/// prefix chains); the value [4, 2, 1, 1] is in the type.
#[test]
fn holes_not_nested_as_prefixes_are_not_matched_greedily() {
    big(|| {
        let t = r5_greedy("_r5greedy_t");
        let v = [4, 2, 1, 1]
            .iter()
            .rev()
            .fold(Value::atom("nil"), |tl, &h| {
                Value::atom_with("cons", vec![Value::Int(h), tl])
            });
        assert!(t.contains(&v));
        Type::forget_emptiness();
        assert_ne!(t.chain_verdict(), Some(Verdict::Empty));
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Inhabited);
    });
}

/// Round 5: a negative chain group killed at one step and started again by a later token kept
/// the earlier token's scheduled jumps, which overflowed `active - jumping_next` in the prefix
/// chains. The formula is satisfiable (x2 = x3 = x4 = false).
#[test]
fn a_negative_chain_group_started_again_ignores_its_old_jumps() {
    big(|| {
        let cls = vec![
            vec![(2, false), (4, false)],
            vec![(1, false), (2, false), (4, true)],
            vec![(3, false), (4, false)],
        ];
        assert!(r5_sat(4, &cls));
        let t = r5_sat_type(4, &cls, "_r5_regroup");
        Type::forget_emptiness();
        assert_ne!(t.verdict(), Verdict::Empty);
    });
}

/// Round 5, Q2: the boundary of the sweeps on the 3-SAT reduction. Clauses without literals
/// (unsatisfiable) are decided by the front sweep; the same shape with one literal per clause
/// was left to the search in round 5 and is decided by the escape solve since round 6.
#[test]
fn the_reduction_without_literals_is_swept_and_with_literals_is_not() {
    big(|| {
        let none = r5_sat_type(2, &vec![vec![]; 4], "_r5_bnone");
        Type::forget_emptiness();
        assert_eq!(none.sweep_verdict(), Some(Verdict::Empty));
        Type::forget_emptiness();
        assert_eq!(none.verdict(), Verdict::Empty);
        let one = r5_sat_type(2, &vec![vec![(1, true)]; 4], "_r5_bone");
        Type::forget_emptiness();
        assert_eq!(one.sweep_verdict(), Some(Verdict::Inhabited));
        Type::forget_emptiness();
        assert_eq!(one.verdict(), Verdict::Inhabited);
    });
}

// rfx port (verification only)
fn r5_slots(n: usize, outside: bool) -> Type {
    let mut ds = vec![def("R5L", Expr::Union(vec![nil(),cons(int(),r(0))]))];
    ds.push(def("R5F1",cons(Expr::Type(lit(1)),r(0))));
    for k in 2..=6 { ds.push(def(&format!("R5F{k}"),cons(Expr::Type(&Type::int()-&lit(k as i64)),r(k-1)))); }
    let hs=[&lit(4)|&(&lit(5)|&lit(6)), if outside {&lit(4)|&lit(5)} else {Type::int()},if outside {lit(2)} else {Type::int()},lit(1),lit(1),lit(1)];
    let mut p=r(0);
    for _ in 0..n { p=cons(int(),p); }
    for h in hs.iter().rev() {p=cons(Expr::Type(h.clone()),p);}
    ds.push(def("R5P",p));
    let g=r3_instance(ds);
    &g[7]-&(&g[4]|&(&g[5]|&g[6]))
}
fn r5_varying_width(w: usize) -> Type {
    let all=Type::tuple(vec![Type::bool();w]);
    let mut defs=vec![def("R5WidthL",Expr::Union(vec![nil(),cons(Expr::Type(all.clone()),r(0))]))];
    for j in 0..w {
        let mut cs=vec![Type::bool();w];cs[j]=Type::lit(&Value::Bool(true)).unwrap();
        defs.push(def(&format!("R5WidthF{j}"),cons(Expr::Type(Type::tuple(cs)),r(0))));
    }
    defs.push(def("R5WidthP",cons(Expr::Type(all),r(0))));
    let g=Group::new(defs).unwrap().instance(vec![]);
    let u=(1..=w).fold(Type::empty(),|u,j|&u|&g[j]);
    &g[w+1]-&u
}
#[test]
fn rfxx_r5_matching_non_nested_slots() {
    let mut ds = vec![def("R5L", Expr::Union(vec![nil(),cons(int(),r(0))]))];
    ds.push(def("R5F1",cons(Expr::Type(lit(1)),r(0))));
    for k in 2..=6 { ds.push(def(&format!("R5F{k}"),cons(Expr::Type(&Type::int()-&lit(k as i64)),r(k-1)))); }
    let hs=[&lit(4)|&(&lit(5)|&lit(6)), &lit(4)|&lit(5),lit(2),lit(1),lit(1),lit(1)];
    let mut p=r(0);
    for h in hs.iter().rev() {p=cons(Expr::Type(h.clone()),p);}
    ds.push(def("R5P",p));
    let g=r3_instance(ds);
    let t=&g[7]-&(&g[4]|&(&g[5]|&g[6]));
    let witness=[5,5,2,1,1,1].iter().rev().fold(Value::atom("nil"),|tail,&x|Value::atom_with("cons",vec![Value::Int(x),tail]));
    assert!(t.contains(&witness));
    eprintln!("matching nonnested sweep={:?} verdict={:?} witness_checked=true",t.sweep_verdict(),t.verdict());
    assert_ne!(t.verdict(),Verdict::Empty);
    assert!(!t.is_empty());
}
#[test]
fn rfxx_r5_carrier_only_constrains_the_suffix() {
    let ds=vec![
        def("R5SuffixL",Expr::Union(vec![nil(),cons(int(),r(0))])),
        def("R5SuffixR",cons(int(),r(0))),
        def("R5SuffixQ",Expr::Union(vec![nil(),cons(Expr::Type(&Type::int()|&Type::atom("a")),r(1))])),
        def("R5SuffixP",cons(Expr::Type(&Type::int()-&lit(1)),r(2))),
        def("R5SuffixN",cons(Expr::Type(&Type::int()-&lit(1)),r(0))),
    ];
    let g=Group::new(ds).unwrap().instance(vec![]);
    let t=&g[3]-&g[4];
    let w=[Value::Int(0),Value::atom("a"),Value::Int(0)].into_iter().rev().fold(Value::atom("nil"),|tail,x|Value::atom_with("cons",vec![x,tail]));
    assert!(t.contains(&w));
    assert_ne!(t.sweep_verdict(),Some(Verdict::Empty));
    assert_ne!(t.verdict(),Verdict::Empty);
    assert!(!t.is_empty());
}
/// Q2 remainder boundary family:
/// Single spine `F_1 = cons(1, L)`, `F_i = cons(h_i, F_{i-1})` for `i = 2..=n` with roots
/// `F_1, F_3..=F_n`, `M_n` (no `1` in the first `n` steps), and positive chain
/// `P_1 = cons(int, cons(1, cons(1, L)))` forcing `1` at steps 2 and 3.
/// - When `in_remainder == false` (`r5remin`), `h_i = int \ {i + 2}` (all holes `E_i = {i + 2}`
///   pairwise disjoint): short-escape fails (positive side `P_1` is not `L` and forces `1` at
///   steps 2 and 3) and uniform-hole dominance fails (`E_2 = {4} != E_3 = {5}`), so it is decided
///   in `O(n log n)` specifically by disjoint-hole prefix matching (`Inhabited`, witness `[5, 1, 1]`).
/// - When `in_remainder == true` (`r5remout`), `F_2` has `h_2 = int \ {4, 5}` (`E_2 = {4, 5}`)
///   while `F_i` (`i >= 3`) has `h_i = int \ {i + 2}` (`E_3 = {5}`): at step 3, `E_2` and `E_3`
///   both contain `5` (`!spine_disjoint`) and `E_2 != E_3` (`!spine_same_hole`), placing it just
///   inside the coNP-hard remainder (`sweep_verdict() == None`, decided `Inhabited` by the base
///   search).
fn r5_remainder_boundary(n: usize, in_remainder: bool, tag: &str) -> Type {
    let n = n.max(3);
    // 0: L
    // 1..=n: F_1..F_n
    // n+1..=2n: M_1..M_n
    // 2n+1..=2n+3: P_1..P_3
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    for i in 2..=n {
        let h = if in_remainder && i == 2 {
            &(&Type::int() - &lit(4)) - &lit(5)
        } else {
            &Type::int() - &lit(i as i64 + 2)
        };
        defs.push(def(&format!("F{i}{tag}"), cons(Expr::Type(h), r(i - 1))));
    }
    let not_one = Expr::Type(&Type::int() - &lit(1));
    for k in 1..=n {
        let rest = if k == 1 { r(0) } else { r(n + k - 1) };
        defs.push(def(
            &format!("M{k}{tag}"),
            Expr::Union(vec![nil(), cons(not_one.clone(), rest)]),
        ));
    }
    let p_base = 2 * n;
    defs.push(def(
        &format!("P1{tag}"),
        cons(Expr::Type(Type::int()), r(p_base + 2)),
    ));
    defs.push(def(
        &format!("P2{tag}"),
        cons(Expr::Type(lit(1)), r(p_base + 3)),
    ));
    defs.push(def(&format!("P3{tag}"), cons(Expr::Type(lit(1)), r(0))));
    let ts = r3_instance(defs);
    let u = [1]
        .into_iter()
        .chain(3..=n)
        .chain([2 * n])
        .map(|i| &ts[i])
        .fold(Type::empty(), |u, t| r3_union(&u, t));
    &ts[p_base + 1] - &u
}

// Round 6: the boundary families of the escape solve (`empty/escape.rs`), on the one-chain
// encoding of `r5_sat_type` (variable i at place i, clause c at place k + c(k + 1)).

/// `n` distinct two-literal clauses over `k = isqrt(n) + 2` variables, each with a positive
/// literal, with the cycle `x_i | !x_(i+1)` (all variables equal) and `x_1 | x_2` among them:
/// satisfiable (all true) for `kind` 0; for `kind` 1 the last clause is `!x_1 | !x_2`
/// (unsatisfiable, two atoms per root); for `kind` 2 it is `!x_1 | !x_2 | !x_3`
/// (unsatisfiable, one root with three atoms, outside the 2-SAT `Empty`).
fn r6_two_clauses(n: usize, kind: u8) -> (usize, Vec<Vec<(usize, bool)>>) {
    let k = (n as f64).sqrt() as usize + 2;
    let mut cls: Vec<Vec<(usize, bool)>> = (1..=k).map(|i| vec![(i, true), (i % k + 1, false)]).collect();
    cls.push(vec![(1, true), (2, true)]);
    let mut seen: BTreeSet<Vec<(usize, bool)>> = cls.iter().map(|c| { let mut c = c.clone(); c.sort(); c }).collect();
    'fill: for a in 1..=k {
        for b in a + 1..=k {
            for (sa, sb) in [(true, true), (true, false), (false, true)] {
                if cls.len() >= n {
                    break 'fill;
                }
                let c = vec![(a, sa), (b, sb)];
                if seen.insert(c.clone()) {
                    cls.push(c);
                }
            }
        }
    }
    match kind {
        1 => *cls.last_mut().unwrap() = vec![(1, false), (2, false)],
        2 => *cls.last_mut().unwrap() = vec![(1, false), (2, false), (3, false)],
        _ => {}
    }
    (k, cls)
}

/// `r5_sat_type` with the positive head `filler` at the places that are neither variables nor
/// clauses (`r5_sat_type` has `{7}`), and the refused rows' heads drawn from `base` (`r5_sat_type`
/// has all integers): `base` less `{0}` or `{1}` at a literal.
fn r6_sat_type(k: usize, cls: &[Vec<(usize, bool)>], tag: &str, filler: Type, base: Type) -> Type {
    let rc = |c: usize| k + c * (k + 1);
    let len = rc(cls.len());
    let mut h = vec![base.clone(); len + 1];
    h[1] = lit(2);
    for (c, cl) in cls.iter().enumerate() {
        for &(i, pos) in cl {
            h[rc(c + 1) - i + 1] = &base - &lit(if pos { 0 } else { 1 });
        }
    }
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(int(), r(0))]))];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(h[1].clone()), r(0))));
    defs.extend((2..=len).map(|d| def(&format!("F{d}{tag}"), cons(Expr::Type(h[d].clone()), r(d - 1)))));
    let clause_place = |p: usize| p > k && (p - k) % (k + 1) == 0;
    let mut e = nil();
    for p in (1..=len).rev() {
        let head = if p <= k { &lit(0) | &lit(1) } else if clause_place(p) { lit(2) } else { filler.clone() };
        e = cons(Expr::Type(head), e);
    }
    defs.push(def(&format!("P{tag}"), e));
    let ts = u4_inst(defs);
    let u = (1..=len).fold(Type::empty(), |u, d| &u | &ts[d]);
    &ts[len + 1] - &u
}

#[test]
fn r5_probe_cases_are_decided_in_their_size_4() {
    r5_cases_scale(&[
        ("r5greedy", Verdict::Inhabited),
        ("r5sat1lit", Verdict::Inhabited),
        ("r5sat2lit", Verdict::Inhabited),
        ("r5satk1n", Verdict::Inhabited),
        ("r5satnone", Verdict::Empty),
        ("r5slotsin", Verdict::Inhabited),
        ("r5slotsout", Verdict::Inhabited),
        ("r5remin", Verdict::Inhabited),
        ("r5remout", Verdict::Inhabited),
    ]);
}

#[test]
fn r6_escape_families_are_decided_in_their_size() {
    r5_cases_scale(&[
        ("r6three", Verdict::Inhabited),
        ("r6wide", Verdict::Inhabited),
        ("r6comb", Verdict::Inhabited),
    ]);
}

/// The two families that were quadratic before rows were retired after four cells (round 6:
/// `r6wide` n^1.82, `r6comb` n^1.62 at 1024), at sizes large enough for that to show.
#[test]
fn r6_wide_rows_are_retired_and_decided_in_their_size() {
    cases_scale_from(&[("r6wide", Verdict::Inhabited), ("r6comb", Verdict::Inhabited)], 128);
}

#[test]
fn r6_two_atom_roots_over_many_variables_are_decided() {
    big(|| {
        for n in [8, 16, 64] {
            for (kind, want) in [(0, Verdict::Inhabited), (1, Verdict::Empty)] {
                let (k, cls) = r6_two_clauses(n, kind);
                assert_eq!(r5_sat(k, &cls), kind == 0, "the formula at {n} kind {kind}");
                Type::forget_emptiness();
                let t = r5_sat_type(k, &cls, &format!("_r6two_{n}_{kind}"));
                assert_eq!(t.chain_verdict(), Some(want), "chains at {n} kind {kind}");
                Type::forget_emptiness();
                assert_eq!(t.verdict(), want, "verdict at {n} kind {kind}");
            }
        }
    });
}

/// The 3-colouring reduction for crossing atoms: place `u` holds vertex `u`'s colour in
/// `{1, 2, 3}`; for each edge `uv` and colour `c` a refused row with the head `{c}` at `u` and at
/// `v` (all integers elsewhere). A list of `P` escapes that row exactly when `x_u != c` or
/// `x_v != c`, by the atoms `{1, 2, 3} \ {c}` at `u` and `v`, which cross; so `t` is inhabited
/// exactly when the graph has a proper 3-colouring.
fn r6_colour_type(nv: usize, edges: &[(usize, usize)], tag: &str) -> Type {
    let three = &(&lit(1) | &lit(2)) | &lit(3);
    let chain = |head: &dyn Fn(usize) -> Type| {
        let mut e = nil();
        for p in (1..=nv).rev() {
            e = cons(Expr::Type(head(p)), e);
        }
        e
    };
    let mut defs = vec![def(&format!("P{tag}"), chain(&|_| three.clone()))];
    for (i, &(u, v)) in edges.iter().enumerate() {
        for c in 1..=3 {
            let e = chain(&|p| if p == u || p == v { lit(c) } else { Type::int() });
            defs.push(def(&format!("N{i}_{c}{tag}"), e));
        }
    }
    let ts = u4_inst(defs);
    let u = ts[1..].iter().fold(Type::empty(), |u, t| &u | t);
    &ts[0] - &u
}

/// The same reduction on one comb, the shape the escape solve reads (as in `r5_sat_type`):
/// `F_d = link(h_d, F_(d-1))` over the carrier, one block of `nv + 1` places per edge and colour,
/// `P` with `{1, 2, 3}` at the vertex places, `0` at the end of each block and `7` elsewhere
/// (`F_d` has `{0}` at place `d`, so every row but the block ends is killed there).
/// The row ending block `b` (edge `uv`, colour `c`) has the head `int \ ({1, 2, 3} \ {c})` at
/// `u` and `v`, so its atoms there are `{1, 2, 3} \ {c}`, which cross. Returns the type and its
/// length.
fn r6_colour_comb(nv: usize, edges: &[(usize, usize)], tag: &str) -> (Type, usize) {
    let rc = |b: usize| nv + b * (nv + 1);
    let blocks: Vec<(usize, usize, i64)> = edges.iter().flat_map(|&(u, v)| (1..=3).map(move |c| (u, v, c))).collect();
    let len = rc(blocks.len());
    let three = &(&lit(1) | &lit(2)) | &lit(3);
    let mut h = vec![Type::int(); len + 1];
    h[1] = lit(0);
    for (b, &(u, v, c)) in blocks.iter().enumerate() {
        let others = (1..=3).filter(|&x| x != c).fold(Type::empty(), |s, x| &s | &lit(x));
        for p in [u, v] {
            h[rc(b + 1) - p + 1] = &Type::int() - &others;
        }
    }
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(int(), r(0))]))];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(h[1].clone()), r(0))));
    defs.extend((2..=len).map(|d| def(&format!("F{d}{tag}"), cons(Expr::Type(h[d].clone()), r(d - 1)))));
    let mut e = nil();
    for p in (1..=len).rev() {
        let head = if p <= nv { three.clone() } else if (p - nv) % (nv + 1) == 0 { lit(0) } else { lit(7) };
        e = cons(Expr::Type(head), e);
    }
    defs.push(def(&format!("P{tag}"), e));
    let ts = u4_inst(defs);
    let u = (1..=len).fold(Type::empty(), |u, d| &u | &ts[d]);
    (&ts[len + 1] - &u, len)
}

fn r6_colour_list(xs: &[i64]) -> Value {
    xs.iter().rev().fold(Value::atom("nil"), |tl, &h| Value::atom_with("cons", vec![Value::Int(h), tl]))
}

/// Every graph on `nv` vertices whose edge mask is `shard` mod `nsh`: the type is inhabited
/// exactly when brute force finds a proper colouring (each colouring is a list of `P`, tested by
/// membership), and no mechanism answers wrongly. With `comb`, also the comb form
/// ([`r6_colour_comb`]), which the escape solve reads and must decline (its atoms cross).
fn r6_colouring_check(nv: usize, shard: u32, nsh: u32, comb: bool) {
    big(move || {
        let mut counts = std::collections::BTreeMap::new();
        {
            let pairs: Vec<(usize, usize)> = (1..=nv).flat_map(|u| (u + 1..=nv).map(move |v| (u, v))).collect();
            for mask in 0u32..1 << pairs.len() {
                if mask % nsh != shard {
                    continue;
                }
                let edges: Vec<(usize, usize)> = pairs.iter().enumerate().filter(|(i, _)| mask >> i & 1 == 1).map(|(_, &e)| e).collect();
                if edges.is_empty() {
                    continue;
                }
                let t = r6_colour_type(nv, &edges, &format!("_r6col{nv}_{mask}"));
                let mut colourable = false;
                for code in 0..3u32.pow(nv as u32) {
                    let xs: Vec<i64> = (0..nv).map(|i| (code / 3u32.pow(i as u32) % 3) as i64 + 1).collect();
                    let proper = edges.iter().all(|&(u, v)| xs[u - 1] != xs[v - 1]);
                    assert_eq!(t.contains(&r6_colour_list(&xs)), proper, "nv {nv} mask {mask} {xs:?}");
                    colourable |= proper;
                }
                Type::forget_emptiness();
                let ch = t.chain_verdict();
                Type::forget_emptiness();
                let v = t.verdict();
                let wrong = |x: &Verdict| matches!((x, colourable), (Verdict::Empty, true) | (Verdict::Inhabited, false));
                assert!(!wrong(&v) && !ch.as_ref().is_some_and(wrong), "nv {nv} mask {mask} colourable {colourable} {v:?} {ch:?}");
                *counts.entry(format!("nv {nv} colourable {colourable} {v:?} chains {ch:?}")).or_insert(0usize) += 1;
                if !comb {
                    continue;
                }
                // The comb form: the same colourings, padded with the block values.
                let (t, len) = r6_colour_comb(nv, &edges, &format!("_r6cc{nv}_{mask}"));
                for code in 0..3u32.pow(nv as u32) {
                    let mut xs: Vec<i64> = (0..nv).map(|i| (code / 3u32.pow(i as u32) % 3) as i64 + 1).collect();
                    let proper = edges.iter().all(|&(u, v)| xs[u - 1] != xs[v - 1]);
                    xs.extend((nv + 1..=len).map(|p| if (p - nv) % (nv + 1) == 0 { 0 } else { 7 }));
                    assert_eq!(t.contains(&r6_colour_list(&xs)), proper, "comb nv {nv} mask {mask} {xs:?}");
                }
                Type::forget_emptiness();
                let ch = t.chain_verdict();
                Type::forget_emptiness();
                let v = t.verdict();
                assert!(!wrong(&v) && !ch.as_ref().is_some_and(wrong), "comb nv {nv} mask {mask} colourable {colourable} {v:?} {ch:?}");
                *counts.entry(format!("comb nv {nv} colourable {colourable} {v:?} chains {ch:?}")).or_insert(0usize) += 1;
            }
        }
        for (k, c) in &counts {
            eprintln!("r6 colouring {k}: {c}");
        }
    });
}

#[test]
fn r6_three_colouring_reduction_is_checked_by_brute_force_4() {
    r6_colouring_check(4, 0, 1, true);
}

#[test]
fn r6_three_colouring_reduction_is_checked_by_brute_force_5a() {
    r6_colouring_check(5, 0, 16, false);
}

#[test]
fn r6_three_colouring_reduction_is_checked_by_brute_force_5b() {
    r6_colouring_check(5, 7, 16, false);
}

/// A head of the random carrier-plus-chains inputs: `{0, 1, 2}` by `mask`, or all integers but
/// those (`cof`). The value 3 stands for every other integer.
#[derive(Clone, Copy, Debug)]
struct R6Head {
    cof: bool,
    mask: u8,
}

impl R6Head {
    fn holds(self, x: u8) -> bool {
        if x == 3 { self.cof } else { (self.mask >> x & 1 == 1) != self.cof }
    }
    fn ty(self) -> Type {
        let s = (0..3).filter(|&i| self.mask >> i & 1 == 1).fold(Type::empty(), |u, i| &u | &lit(i));
        if self.cof { &Type::int() - &s } else { s }
    }
}

/// Where a tail goes: a node of the pool, the end (`nil` only), or the carrier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum R6Tail {
    Node(usize),
    End,
    Car,
}

#[derive(Debug)]
struct R6Input {
    carrier: Option<R6Head>,
    /// Pool node `i`: holds `nil`, its head, its next (a node before it, or a terminal), and
    /// optionally the head of a second row `cons(alt, carrier)`.
    pool: Vec<(bool, R6Head, R6Tail, Option<R6Head>)>,
    taken: Vec<(R6Head, R6Tail)>,
    refused: Vec<(R6Head, R6Tail)>,
}

struct R6Rng(u64);

impl R6Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn r6_random_input(g: &mut R6Rng, np_max: u64, nr_max: u64, alt_rows: bool) -> R6Input {
    let head = |g: &mut R6Rng| {
        // Mostly one-value holes (`int \ {v}`) and small finite sets, sometimes all integers.
        match g.below(6) {
            0 => R6Head { cof: true, mask: 0 },
            1 | 2 => R6Head { cof: true, mask: 1 << g.below(3) },
            3 => R6Head { cof: true, mask: g.below(8) as u8 },
            _ => R6Head { cof: false, mask: 1 + g.below(7) as u8 },
        }
    };
    let carrier = (g.below(4) != 0).then(|| if g.below(2) == 0 { R6Head { cof: true, mask: 0 } } else { head(g) });
    let terminal = |g: &mut R6Rng| if carrier.is_some() && g.below(3) != 0 { R6Tail::Car } else { R6Tail::End };
    let np = 1 + g.below(np_max) as usize;
    let mut pool = Vec::new();
    for i in 0..np {
        let next = if i > 0 && g.below(3) != 0 { R6Tail::Node(g.below(i as u64) as usize) } else { terminal(g) };
        let (stop, h) = (g.below(3) == 0, head(g));
        // Drawn only when asked, so that the inputs of the other seeds stay as they were.
        let alt = (alt_rows && carrier.is_some() && g.below(3) == 0).then(|| head(g));
        pool.push((stop, h, next, alt));
    }
    if alt_rows {
        // A twin of every node without its second row, its next the twin of its next, so that a
        // row can follow a chain while the carrier rows of that chain stay open.
        let twin = |t: R6Tail| match t {
            R6Tail::Node(j) => R6Tail::Node(np + j),
            t => t,
        };
        for i in 0..np {
            let (stop, h, next, _) = pool[i];
            pool.push((stop, h, twin(next), None));
        }
    }
    let np = pool.len();
    let tail =|g: &mut R6Rng| if g.below(4) == 0 { terminal(g) } else { R6Tail::Node(g.below(np as u64) as usize) };
    let mut taken = vec![(head(g), tail(g))];
    if g.below(2) == 0 {
        // A second taken row: on the carrier (inside the class), or another chain (outside).
        let t = if carrier.is_some() && g.below(4) != 0 { R6Tail::Car } else { tail(g) };
        // With the carrier's own head this is a top carrier row, which bounds every item.
        let top = alt_rows && t == R6Tail::Car && g.below(2) == 0;
        taken.push((if top { carrier.unwrap() } else { head(g) }, t));
    }
    let refused = (0..1 + g.below(nr_max)).map(|_| (head(g), tail(g))).collect();
    R6Input { carrier, pool, taken, refused }
}

fn r6_input_type(x: &R6Input, tag: &str) -> Type {
    // Definitions: the carrier (if any), the pool nodes, then the rows.
    let base = usize::from(x.carrier.is_some());
    let tail = |t: R6Tail| match t {
        R6Tail::Node(i) => r(base + i),
        R6Tail::End => nil(),
        R6Tail::Car => r(0),
    };
    let mut defs = Vec::new();
    if let Some(h) = x.carrier {
        defs.push(def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(Expr::Type(h.ty()), r(0))])));
    }
    for (i, &(stop, h, next, alt)) in x.pool.iter().enumerate() {
        let mut alts = vec![cons(Expr::Type(h.ty()), tail(next))];
        if let Some(a) = alt {
            alts.push(cons(Expr::Type(a.ty()), r(0)));
        }
        if stop {
            alts.insert(0, nil());
        }
        let body = if alts.len() == 1 { alts.pop().unwrap() } else { Expr::Union(alts) };
        defs.push(def(&format!("V{i}{tag}"), body));
    }
    for (i, &(h, t)) in x.taken.iter().chain(&x.refused).enumerate() {
        defs.push(def(&format!("R{i}{tag}"), cons(Expr::Type(h.ty()), tail(t))));
    }
    let ts = u4_inst(defs);
    let rows = &ts[base + x.pool.len()..];
    let p = rows[1..x.taken.len()].iter().fold(rows[0].clone(), |u, t| &u & t);
    let n = rows[x.taken.len()..].iter().fold(Type::empty(), |u, t| &u | t);
    &p - &n
}

/// The brute-force oracle: a list over `{0, 1, 2, 3}` in every taken row and no refused row,
/// sought by depth-first search over the rows' positions, reading only `x`. A row's positions
/// are the set of types its rest may lie in (a node with a second row into the carrier can be
/// left two ways): `None` the row itself (before its head), `Some(t)` a tail; an empty set is a
/// dead row. Lists longer than the pool's depth plus two need not be tried: past it every live
/// position is at the carrier, and dropping an item there changes no row's answer.
fn r6_oracle(x: &R6Input) -> bool {
    type Pos = BTreeSet<Option<R6Tail>>;
    let accepts = |p: &Pos| {
        p.iter().any(|q| match q {
            Some(R6Tail::Node(i)) => x.pool[*i].0,
            Some(_) => true,
            None => false,
        })
    };
    let rows: Vec<(R6Head, R6Tail)> = x.taken.iter().chain(&x.refused).copied().collect();
    let nt = x.taken.len();
    // The longest chain of pool nodes (each next is an earlier node).
    let mut depth = vec![0usize; x.pool.len()];
    for i in 0..x.pool.len() {
        depth[i] = 1 + match x.pool[i].2 {
            R6Tail::Node(j) => depth[j],
            _ => 0,
        };
    }
    let max_len = depth.iter().max().unwrap_or(&0) + 3;
    fn go(
        x: &R6Input,
        rows: &[(R6Head, R6Tail)],
        nt: usize,
        pos: &[Pos],
        len: usize,
        max_len: usize,
        accepts: &dyn Fn(&Pos) -> bool,
    ) -> bool {
        if len > 0 && pos[..nt].iter().all(accepts) && !pos[nt..].iter().any(accepts) {
            return true;
        }
        if len == max_len {
            return false;
        }
        for v in 0..4u8 {
            let next: Vec<Pos> = pos
                .iter()
                .zip(rows)
                .map(|(p, &(h0, t0))| {
                    let mut out = Pos::new();
                    for &q in p {
                        match q {
                            None => {
                                if h0.holds(v) {
                                    out.insert(Some(t0));
                                }
                            }
                            Some(R6Tail::Node(i)) => {
                                let (_, h, nx, alt) = x.pool[i];
                                if h.holds(v) {
                                    out.insert(Some(nx));
                                }
                                if alt.is_some_and(|a| a.holds(v)) {
                                    out.insert(Some(R6Tail::Car));
                                }
                            }
                            Some(R6Tail::End) => {}
                            Some(R6Tail::Car) => {
                                if x.carrier.unwrap().holds(v) {
                                    out.insert(Some(R6Tail::Car));
                                }
                            }
                        }
                    }
                    out
                })
                .collect();
            if next[..nt].iter().all(|p| !p.is_empty()) && go(x, rows, nt, &next, len + 1, max_len, accepts) {
                return true;
            }
        }
        false
    }
    let start: Vec<Pos> = vec![Pos::from([None]); rows.len()];
    go(x, &rows, nt, &start, 0, max_len, &accepts)
}

fn r6_oracle_run(seed: u64, count: usize, np_max: u64, nr_max: u64) {
    r6_oracle_run_with(seed, count, np_max, nr_max, false);
}

fn r6_oracle_run_with(seed: u64, count: usize, np_max: u64, nr_max: u64, alt_rows: bool) {
    big(move || {
        let mut g = R6Rng(seed);
        let mut counts = std::collections::BTreeMap::new();
        for i in 0..count {
            let x = r6_random_input(&mut g, np_max, nr_max, alt_rows);
            let truth = r6_oracle(&x);
            let t = r6_input_type(&x, &format!("_r6o{seed}_{i}"));
            Type::forget_emptiness();
            let ch = t.chain_verdict();
            Type::forget_emptiness();
            let v = t.verdict();
            let wrong = |y: &Verdict| matches!((y, truth), (Verdict::Empty, true) | (Verdict::Inhabited, false));
            assert!(!wrong(&v), "verdict {v:?} truth {truth} on {x:?}");
            assert!(!ch.as_ref().is_some_and(wrong), "chains {ch:?} truth {truth} on {x:?}");
            *counts.entry(format!("truth {truth} {v:?} chains {ch:?}")).or_insert(0usize) += 1;
        }
        for (k, c) in &counts {
            eprintln!("r6 oracle seed {seed} {k}: {c}");
        }
    });
}

#[test]
fn r6_carrier_and_chains_against_brute_force_1() {
    r6_oracle_run(0x9e37_79b9_7f4a_7c15, 1500, 4, 6);
}

#[test]
fn r6_carrier_and_chains_against_brute_force_2() {
    r6_oracle_run(0x2545_f491_4f6c_dd1d, 1500, 4, 6);
}

/// Longer pools and more refused rows, so that rows with three or more atoms (whose `Empty` the
/// escape solve must not give from their first two) are common.
#[test]
fn r6_carrier_and_chains_against_brute_force_3() {
    r6_oracle_run(0x5851_f42d_4c95_7f2d, 600, 6, 12);
}

/// Pool nodes with a second row into the carrier, below the top of positive and refused chains.
#[test]
fn r6_carrier_and_chains_against_brute_force_4() {
    r6_oracle_run_with(0x1405_7b7e_f767_814f, 3000, 4, 6, true);
}

/// A comb where no place of a root separates except its first: `F_e = cons(int \ {e mod 2},
/// F_(e-1))`, roots `F_d` for even `d`, `P` of length `n` with `{0, 7}` first and `{j mod 2, 7}`
/// at place `j`. The node `F_e` separates the places `j` of parity `e`, which no even root
/// reaches through it; `x_1 = 0` escapes every root (`Inhabited`).
fn r6_parity(n: usize, tag: &str) -> Type {
    let n = n.max(2);
    let mut defs = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(), cons(int(), r(0))]))];
    for e in 1..=n {
        let h = &Type::int() - &lit((e % 2) as i64);
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if j == 1 { &lit(0) | &lit(7) } else { &lit((j % 2) as i64) | &lit(7) };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let u = (2..=n).step_by(2).fold(Type::empty(), |u, d| &u | &ts[d]);
    &ts[n + 1] - &u
}

/// Round 6: the prefix chains answered Empty when the carrier head was empty, also without a top
/// carrier row (Gemini R4 code, kept through round 5). Here the carrier `L` only ends the
/// positive chain, so it holds just `nil`, and [0, 0] is in the type.
#[test]
fn an_empty_carrier_head_bounds_only_a_top_carrier_row() {
    big(|| {
        // 0: L = nil | cons(E, L); 1: E = cons(int, E) (no finite value); 2: Q = cons(int, L);
        // 3: P = cons(int, Q); 4: N = cons(5, L).
        let ts = Group::new(vec![
            def("L_e0", Expr::Union(vec![nil(), cons(r(1), r(0))])),
            def("E_e0", cons(int(), r(1))),
            def("Q_e0", cons(int(), r(0))),
            def("P_e0", cons(int(), r(2))),
            def("N_e0", cons(Expr::Type(lit(5)), r(0))),
        ])
        .unwrap()
        .instance(vec![]);
        let t = &ts[3] - &ts[4];
        let v = [0, 0].iter().rev().fold(Value::atom("nil"), |tl, &h| {
            Value::atom_with("cons", vec![Value::Int(h), tl])
        });
        assert!(t.contains(&v));
        Type::forget_emptiness();
        assert_ne!(t.chain_verdict(), Some(Verdict::Empty));
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Inhabited);
    });
}

/// Round 6: the prefix chains followed only the chain row of a positive node that also has a row
/// into the carrier, and answered Empty; [0, 0, 1] is in the type through the carrier row.
#[test]
fn a_positive_row_into_the_carrier_below_the_top_is_not_dropped() {
    big(|| {
        // 0: L = nil | cons(int, L); 1: B = cons(3, L); 2: A = cons(1, L) | cons(2, B);
        // 3: Z = cons(int, A); 4: P = cons(int, Z); 5: N = cons(int, cons(int, cons(2, B))).
        let ts = Group::new(vec![
            def("L_pe", Expr::Union(vec![nil(), cons(int(), r(0))])),
            def("B_pe", cons(Expr::Type(lit(3)), r(0))),
            def(
                "A_pe",
                Expr::Union(vec![
                    cons(Expr::Type(lit(1)), r(0)),
                    cons(Expr::Type(lit(2)), r(1)),
                ]),
            ),
            def("Z_pe", cons(int(), r(2))),
            def("P_pe", cons(int(), r(3))),
            def(
                "N_pe",
                cons(int(), cons(int(), cons(Expr::Type(lit(2)), r(1)))),
            ),
        ])
        .unwrap()
        .instance(vec![]);
        let t = &(&ts[4] & &ts[0]) - &ts[5];
        for (xs, member) in [(vec![0, 0, 1], true), (vec![0, 0, 2, 3], false)] {
            let v = xs.iter().rev().fold(Value::atom("nil"), |tl, &h| {
                Value::atom_with("cons", vec![Value::Int(h), tl])
            });
            assert_eq!(t.contains(&v), member);
        }
        Type::forget_emptiness();
        assert_ne!(t.chain_verdict(), Some(Verdict::Empty));
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Inhabited);
    });
}
// R6 boundary: root at offset i escapes iff x_i=0 or x_(i+1)=1 (plus
// an additional x_(i+1)=0 before the final x_(i+2)=1 in the three-atom arm).
// All-zero words satisfy both arms.
fn r6_distinct_atoms(n: usize, three: bool, tag: &str) -> Type {
    let mut ds = vec![def(&format!("L{tag}"), Expr::Union(vec![nil(),cons(int(),r(0))]))];
    ds.push(def(&format!("B1{tag}"), cons(Expr::Type(&Type::int()-&lit(1)), r(0))));
    ds.push(def(&format!("B2{tag}"), cons(Expr::Type(&Type::int()-&lit(0)), r(1))));
    let base = if three {
        ds.push(def(&format!("B3{tag}"), cons(Expr::Type(&Type::int()-&lit(0)), r(2))));
        3
    } else { 2 };
    for i in 1..n { ds.push(def(&format!("A{i}{tag}"), cons(int(),r(base+i-1)))); }
    let mut p = r(0);
    for _ in 0..n+base { p=cons(Expr::Type(&lit(0)|&lit(1)),p); }
    ds.push(def(&format!("P{tag}"),p));
    let ts = r3_instance(ds);
    let u=(base..base+n).fold(Type::empty(),|u,i| &u|&ts[i]);
    &ts[base+n]-&u
}

#[test]
fn r6_remout_short_witness_and_negative_controls() {
    big(|| {
        let word = |x| [x,1,1].iter().rev().fold(Value::atom("nil"),
            |tail,&v| Value::atom_with("cons",vec![Value::Int(v),tail]));
        for n in [3,16,64,256,1024] {
            let t=r5_remainder_boundary(n,true,&format!("_r6remwit{n}"));
            assert!(t.contains(&word(5)),"short witness at {n}");
            assert!(!t.contains(&word(1)),"F1 captures the first negative control");
            assert!(!t.contains(&word(4)),"F3 captures the second negative control");
        }
    });
}

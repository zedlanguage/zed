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
use zedc::ast::{BinaryOp, UnaryOp};
use zedc::check::Operator;
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
pub(super) fn fork_empty() -> Type {
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

/// The morphisms that must take 1 and every list of 1s and may take any integer and any list of
/// integers, into the integers. A closure is shown only for a type whose required keys lie
/// within its permitted ones as written; the lists of 1s lie within the lists of integers only
/// by a search, and a family is not checked against a morphism type before L2. (Before round 10
/// this was `lit(1)` within `int`, now built: X45.)
fn morphism_between() -> Type {
    Type::morphism(
        &lit(1) | &list_named(lit(1), "_mb_ones"),
        &Type::int() | &list_named(Type::int(), "_mb_ints"),
        Type::int(),
    )
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
            "; the checker could not decide this, so it is not proved wrong\n  because {}\n  \
             the check reads the recursive type `P1`, defined by:\n    \
             type P1 = #cons(int, P2);\n    \
             type P0 = #cons(int, P1);\n    \
             type P2 = #cons(int, P3);\n    \
             type P3 = #cons(int, P4);\n    \
             type P4 = #cons(int, P5);\n    \
             type P5 = #nil | #cons(int, P0);",
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
    // Item TESTS-L1.23-refusal-text: a refused check is no proof that `g` does not take the
    // argument, so the headline says that the checker could not decide it, and the reason, with
    // its repair, stands on the line after it. Before, the one sentence read `` `g` does not
    // take ((T1, T1, T1)); this is not proved wrong: the checker could not decide whether it
    // fits, because one part of the tuple types involved is decided only by ... ``.
    let shown = "(T1, T1, T1)";
    let Err(all) = zedc::run::load(box_program(7).as_bytes()) else {
        panic!("accepted")
    };
    assert_eq!(
        all.lines().take(2).collect::<Vec<_>>(),
        [
            format!(
                "2:52: The checker could not decide whether `g` takes ({shown}), so it is not \
                 proved wrong."
            ),
            format!("  because {}", Refusal::TupleSplit.message()),
        ]
    );
    // A decided failure names no cause.
    assert_eq!(
        rejected(&box_program(6)),
        format!("2:52: `g` does not take ({shown}): no arrow of `g` takes these types.")
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
        "2:28: `g` does not take ((#a | #b | #c, #c)): no arrow of `g` takes these types."
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
                 the checker could not decide whether this one's guarantee is within its \
                 permission, so it is not proved wrong. To repair it, narrow the type left of \
                 `..`, or widen the type right of it.\n  because {} \
                 [((int -> #a | #b) .. ((int -> #a) | (int -> #b)) -> int)]",
                Refusal::MorphismSplit.message()
            )
        ]
    );
}

/// The errors of the operator `op` applied to `args`, through the checker's `apply`.
fn operator_errors(op: Operator, args: &[Ty]) -> Vec<String> {
    zedc::check::walk::operator(op, args).1
}

#[test]
fn an_overload_whose_check_was_refused_says_why() {
    // No source program reaches these paths with a refused check: the arrows of operators
    // and prelude words take carriers, and the checker's own types hold no difference of
    // tuples. The kernel types are given to the checker's `apply` directly. `-`, `+` and
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
    for (op, n) in [
        (Operator::Unary(UnaryOp::Neg), 1),
        (Operator::Binary(BinaryOp::Add), 2),
        (Operator::Binary(BinaryOp::Lt), 2),
        (Operator::Unary(UnaryOp::Not), 1),
    ] {
        for (t, why) in [
            // No arrow meets the argument ...
            (box_cover(), Some(Refusal::TupleSplit)),
            (morphism_between(), Some(Refusal::NoWitness)),
            // ... and an arrow meets it and does not take it. The one arrow of `!` takes
            // `bool`, and `int` is a decided witness against it.
            (
                &box_cover() | &Type::int(),
                (op != Operator::Unary(UnaryOp::Not)).then_some(Refusal::TupleSplit),
            ),
            (cover6.clone(), None),
            (&cover6 | &Type::int(), None),
        ] {
            Type::forget_emptiness();
            let errors = operator_errors(op, &vec![Ty::set(t.clone()); n]);
            let message = errors.first().unwrap_or_else(|| panic!("`{op}` took {t}"));
            // The headline, and the line after it, before the lines that define the parts it
            // writes twice.
            let mut lines = message.lines();
            let first = lines.next().unwrap_or_default();
            match why {
                // The headline says the check was not decided, with no reason; the reason
                // is the line after it.
                Some(r) => {
                    assert!(
                        first.starts_with(&format!(
                            "The checker could not decide whether `{op}` takes ("
                        )),
                        "{op} on {t}: {first}"
                    );
                    // The period ends the first line, before the reason (`Msg::written`).
                    assert!(
                        first.ends_with("), so it is not proved wrong."),
                        "{op} on {t}: {first}"
                    );
                    assert_eq!(
                        lines.next(),
                        Some(format!("  because {}", r.message()).as_str())
                    );
                }
                None => {
                    assert!(
                        first.starts_with(&format!("`{op}` does not take (")),
                        "{first}"
                    );
                    assert!(
                        !message.contains("not proved wrong"),
                        "{op} on {t}: {message}"
                    );
                }
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
        "2:10: `g` does not take (1): no arrow of `g` takes these types."
    );
    // What a use of an argument gives against what the use needs: decided here. The
    // checker's own types hold no difference of tuples (a written `\` of tuples is dropped
    // from them), so no refused check reaches this path from a program. The operand `n` is an
    // `int`: a literal there would make `f` generic over the carriers (DESIGN.md L1.26a), and
    // the call would be refused by each carrier's arrow instead.
    assert_eq!(
        rejected("n = 1;\nf(x) = x[1] + n;\nmain() = f(x: (1, \"s\"));\n"),
        "3:10: `f` gives \"s\" here, which is not int: the use requires a value of int."
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
    for op in [BinaryOp::Add, BinaryOp::Mul].map(Operator::Binary) {
        Type::forget_emptiness();
        let errors = operator_errors(op, &[Ty::set(box_cover()), Ty::set(Type::bool())]);
        let first = errors.first().unwrap_or_else(|| panic!("`{op}` took it"));
        assert!(
            first.starts_with(&format!("`{op}` does not take (")),
            "{first}"
        );
        assert!(!first.contains("not proved wrong"), "{first}");
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

/// [`morphism_between`] over 1 to `n`: morphisms that must take 1 to `n` and the lists of them.
fn morphism_between_by(n: usize) -> Type {
    let lits = (1..=n as i64).fold(Type::empty(), |t, i| &t | &lit(i));
    Type::morphism(
        &lits | &list_named(lits.clone(), "_mb_ones"),
        &Type::int() | &list_named(Type::int(), "_mb_ints"),
        Type::int(),
    )
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
    // Θ(n) required keys. Measured on c881d28c: 87K instructions at n = 1, 302K at 32. Round 10
    // (the keys also hold a list type, X45): 2.21M at n = 8, 2.88M at 64.
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
                eprintln!(
                    "rfx sweep {which} n {n} {:?} chains {:?}",
                    t.sweep_verdict(),
                    {
                        Type::forget_emptiness();
                        t.chain_verdict()
                    }
                );
                Type::forget_emptiness();
            }
            let mut m = scaling::Meter::new();
            let mut v = None;
            let w = m.work(|| v = Some(t.verdict()));
            eprintln!(
                "rfx {which} n {n} {:?} units {} bytes {}",
                v, w.units, w.bytes
            );
            if which == "r6parity"
                || ["r7", "r8", "r9", "r10"]
                    .iter()
                    .any(|p| which.starts_with(p))
            {
                eprintln!("escape cells {which} n {n} {:?}", t.escape_cell_counts());
                Type::forget_emptiness();
            }
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
    fdefs.push(def(
        &format!("F1{tag}"),
        cons(Expr::Type(one.clone()), r(0)),
    ));
    fdefs.extend((2..=n).map(|i| {
        def(
            &format!("F{i}{tag}"),
            cons(Expr::Type(all.clone()), r(i - 1)),
        )
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
    if let Some(c) = which.strip_prefix("deep:") {
        let mut t = rfx_case(c, 4, tag);
        for _ in 0..n {
            t = Type::tuple(vec![t]);
        }
        return t;
    }
    if let Some(c) = which.strip_prefix("deephead:") {
        let mut t = rfx_case(c, 4, tag);
        for _ in 0..n {
            t = cons_of(t, Type::atom("nil"));
        }
        return t;
    }
    if let Some(c) = which.strip_prefix("listtail:") {
        return cons_of(Type::int(), rfx_case(c, n, tag));
    }
    if let Some(c) = which.strip_prefix("atom2:") {
        return Type::atom_with("wrap", &Type::tuple(vec![Type::int(), rfx_case(c, n, tag)]));
    }
    if let Some(c) = which.strip_prefix("atom:") {
        return Type::atom_with("wrap", &Type::tuple(vec![rfx_case(c, n, tag)]));
    }
    if let Some(c) = which.strip_prefix("nested:") {
        return Type::tuple(vec![Type::exact(
            lit(0),
            Type::atom_with("wrap", &Type::tuple(vec![rfx_case(c, n, tag)])),
        )]);
    }
    if let Some(c) = which.strip_prefix("listhead:") {
        return cons_of(
            rfx_case(c, n, tag),
            list_named(Type::top(), &format!("outer{tag}")),
        );
    }
    if let Some(c) = which.strip_prefix("option:") {
        return &(&Type::atom("none")
            | &Type::atom_with("some", &Type::tuple(vec![rfx_case(c, n, tag)])))
            - &Type::atom("none");
    }
    if let Some(c) = which.strip_prefix("map:") {
        return Type::exact(Type::int(), rfx_case(c, n, tag));
    }
    // The case as a field of a tuple or a record.
    if let Some(c) = which.strip_prefix("tup:") {
        return Type::tuple(vec![Type::int(), rfx_case(c, n, tag)]);
    }
    if let Some(c) = which.strip_prefix("rec:") {
        return Type::exact(lit(0), rfx_case(c, n, tag));
    }
    // In a tagged atom's payload (X42), an option, a list of lists, a map from every integer.
    if let Some(c) = which.strip_prefix("atom:") {
        return Type::atom_with("wrap", &Type::tuple(vec![rfx_case(c, n, tag)]));
    }
    if let Some(c) = which.strip_prefix("opt:") {
        let some = Type::atom_with("some", &Type::tuple(vec![rfx_case(c, n, tag)]));
        return &Type::atom("none") | &some;
    }
    if let Some(c) = which.strip_prefix("lol:") {
        return list_named(rfx_case(c, n, tag), &format!("{tag}_lol"));
    }
    if let Some(c) = which.strip_prefix("map:") {
        return Type::exact(Type::int(), rfx_case(c, n, tag));
    }
    let l = list_named(Type::int(), tag);
    let (int, one, b, yes) = (
        Type::int(),
        lit(1),
        Type::bool(),
        Type::lit(&Value::Bool(true)),
    );
    let yes = yes.unwrap();
    let fam = |skip, m, all: &Type, one: &Type, split| {
        let (l, u) = rfx_family(n, skip, m, all, one, split, tag);
        &l - &u
    };
    let half = (n / 2).max(1);
    match which {
        "r10mapkeys" => Type::morphism(
            (0..n).fold(Type::empty(), |s, i| &s | &lit(i as i64)),
            Type::int(),
            Type::int(),
        ),
        "r10mapvalue" => Type::morphism(lit(0), Type::int(), rfx_case("r5remout", n, tag)),
        "r10padded" => r10_padded_congruence(n, tag),
        "r10sharedfront" => Type::tuple(vec![rfx_case("far", n, tag); n]),
        "r10big" => r10_big_congruence_cx(n, true, tag),
        "r10small" => r10_big_congruence_cx(n, false, tag),
        "r10alternating" => {
            let m = n.isqrt().max(4);
            let a = (0..m)
                .map(|i| (0..m).map(|q| i % 2 == 1 || q == m - 1).collect())
                .collect::<Vec<Vec<bool>>>();
            let b = vec![vec![true; m]; m];
            r9_bmm(&a, &b, tag)
        }
        "r9cosets" => r9_cosets(n, true, tag),
        "r9balanced" => r9_balanced(n, tag),
        "r9posswap" => r9_swapping_groups(n, false, tag),
        "r9negswap" => r9_swapping_groups(n, true, tag),
        "far" => &l - &by_place_from_the_front(n, Some(n), tag),
        "skip1" => fam(Some(1), n, &int, &one, false),
        "skipmid" => fam(Some(half), n, &int, &one, false),
        "bool" => fam(None, n, &b, &yes, false),
        "boolfar" => fam(Some(n), n, &b, &yes, false),
        "mshort" => fam(None, half, &int, &one, false),
        "mlong" => fam(None, n + 1, &int, &one, false),
        "split" => fam(None, n, &int, &one, true),
        "splitfar" => fam(Some(n), n, &int, &one, true),
        "meet" => {
            &fam(Some(n), n, &int, &one, false)
                & &fam(Some(n - 1).filter(|&k| k > 0), n, &int, &one, false)
        }
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
        "cxprivateheads" => r4_private_heads(n, false, tag),
        "cxprivateheadsfar" => r4_private_heads(n, true, tag),
        "manyheadsv0" => rfx_manyheads_v0(n, false, tag),
        "manyheadsfarv0" => rfx_manyheads_v0(n, true, tag),
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
        "r6two" => {
            let (k, c) = r6_two_clauses(n, 0);
            r5_sat_type(k, &c, tag)
        }
        "r6twoun" => {
            let (k, c) = r6_two_clauses(n, 1);
            r5_sat_type(k, &c, tag)
        }
        "r6twowide" => {
            let (k, c) = r6_two_clauses(n, 2);
            r5_sat_type(k, &c, tag)
        }
        "r6three" => r5_sat_type(3, &vec![vec![(1, true), (2, true), (3, true)]; n], tag),
        "r6threeun" => {
            let mut c = vec![vec![(1, true), (2, true), (3, true)]; n];
            c.extend([vec![(1, false)], vec![(2, false)], vec![(3, false)]]);
            r5_sat_type(3, &c, tag)
        }
        "r6wide" => r6_sat_type(
            2,
            &vec![vec![(1, true), (2, true)]; n],
            tag,
            &lit(0) | &lit(7),
            Type::int(),
        ),
        "r6comb" => r6_sat_type(
            2,
            &vec![vec![(1, true)]; n],
            tag,
            lit(7),
            &(&lit(0) | &lit(1)) | &(&lit(2) | &lit(7)),
        ),
        "r6parity" => r6_parity(n, tag),
        "r8heightin" => r8_height_boundary(n, false, tag),
        "r8heightout" => r8_height_boundary(n, true, tag),
        "r7congruencein" => r7_congruence(n, false, tag),
        "r7congruenceout" => r7_congruence(n, true, tag),
        "r10bigcongruenceout" => r10_big_congruence(n, tag),
        "r7aperiodic" => r7_aperiodic(n, tag),
        "r7bmmout" => r7_bmm_out(n, tag),
        "r8residues" => r8_residues(n, false, tag),
        "r8residuesout" => r8_residues(n, true, tag),
        "r8stagein" => r8_stage_boundary(n, false, tag),
        "r8stageout" => r8_stage_boundary(n, true, tag),
        "r9bmm" => {
            let m = (n.isqrt()).max(2);
            let (a, b) = r9_matrices(m, 4, 9);
            r9_bmm(&a, &b, tag)
        }
        "r9bmmlate" => {
            let (a, b) = r9_late_matrices(n.isqrt().max(4));
            r9_bmm(&a, &b, tag)
        }
        "r9bmmone" => {
            let (a, b) = r9_one_matrices(n.isqrt().max(4));
            r9_bmm(&a, &b, tag)
        }
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
    defs.push(def(&format!("G1{tag}"), cons(Expr::Type(lit(2)), r(0))));
    defs.extend((2..=h).map(|i| {
        def(
            &format!("G{i}{tag}"),
            cons(Expr::Type(Type::int()), r(n + i - 1)),
        )
    }));
    let neither = Expr::Type(&Type::int() - &(&lit(1) | &lit(2)));
    defs.extend((1..=m).map(|k| {
        let rest = if k == 1 { r(0) } else { r(n + h + k - 1) };
        def(
            &format!("M{k}{tag}"),
            Expr::Union(vec![nil(), cons(neither.clone(), rest)]),
        )
    }));
    let ts = r3_instance(defs);
    (1..=n + h)
        .map(|i| &ts[i])
        .chain([&ts[n + h + m]])
        .fold(Type::empty(), |u, t| r3_union(&u, t))
}

/// The front union written as one chain: `G1 = cons(1, L)`, `Gk = cons(1, L) | cons(int, G{k-1})`
/// (the same set as `F1 | .. | Fk`), with `M{n}`; `far` uses `G{n-1}` (n >= 2).
fn rfx_chain(n: usize, far: bool, tag: &str) -> Type {
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    defs.push(def(&format!("G1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.extend((2..=n).map(|i| {
        def(
            &format!("G{i}{tag}"),
            Expr::Union(vec![
                cons(Expr::Type(lit(1)), r(0)),
                cons(Expr::Type(Type::int()), r(i - 1)),
            ]),
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
    let g = if far { n - 1 } else { n };
    &ts[g] | &ts[2 * n]
}

/// The front family plus `cons(int, A_k)` for k = 1..n, `A_k = cons(int | #a_k, F1)`: n chains
/// of depth 3 whose second heads differ (each a 1 at place 3, so Empty; Inhabited with `far`).
fn rfx_groups(n: usize, far: bool, tag: &str) -> Type {
    // 0: L; 1..=n: F; n+1..=2n: M; 2n+1..=3n: A; 3n+1..=4n: B
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
    defs.extend((1..=n).map(|k| {
        let h = &Type::int() | &Type::atom(&format!("a{k}"));
        def(&format!("A{k}{tag}"), cons(Expr::Type(h), r(1)))
    }));
    defs.extend((1..=n).map(|k| {
        def(
            &format!("B{k}{tag}"),
            cons(Expr::Type(Type::int()), r(2 * n + k)),
        )
    }));
    let ts = r3_instance(defs);
    let top = if far { n - 1 } else { n };
    (1..=top)
        .chain([2 * n])
        .chain(3 * n + 1..=4 * n)
        .map(|i| &ts[i])
        .fold(Type::empty(), |u, t| r3_union(&u, t))
}

/// Stress X3: redundant finite chains with distinct overlapping scalar heads.
fn rfx_groups_holes(n: usize, far: bool, tag: &str) -> Type {
    // 0: L; 1..=n: F; n+1..=2n: M; 2n+1..=3n: A; 3n+1..=4n: B
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
    defs.extend((1..=n).map(|k| {
        let h = &Type::int() - &lit(k as i64 + 2);
        def(&format!("A{k}{tag}"), cons(Expr::Type(h), r(1)))
    }));
    defs.extend((1..=n).map(|k| {
        def(
            &format!("B{k}{tag}"),
            cons(Expr::Type(Type::int()), r(2 * n + k)),
        )
    }));
    let ts = r3_instance(defs);
    let top = if far { n - 1 } else { n };
    (1..=top)
        .chain([2 * n])
        .chain(3 * n + 1..=4 * n)
        .map(|i| &ts[i])
        .fold(Type::empty(), |u, t| r3_union(&u, t))
}

/// Stress X13: as `rfx_groups_holes` with singleton heads `{k + 2}`, so no union of them covers `int`.
fn rfx_groups_singles(n: usize, far: bool, tag: &str) -> Type {
    // 0: L; 1..=n: F; n+1..=2n: M; 2n+1..=3n: A; 3n+1..=4n: B
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
    defs.extend((1..=n).map(|k| {
        let h = lit(k as i64 + 2);
        def(&format!("A{k}{tag}"), cons(Expr::Type(h), r(1)))
    }));
    defs.extend((1..=n).map(|k| {
        def(
            &format!("B{k}{tag}"),
            cons(Expr::Type(Type::int()), r(2 * n + k)),
        )
    }));
    let ts = r3_instance(defs);
    let top = if far { n - 1 } else { n };
    (1..=top)
        .chain([2 * n])
        .chain(3 * n + 1..=4 * n)
        .map(|i| &ts[i])
        .fold(Type::empty(), |u, t| r3_union(&u, t))
}

/// Codex R3 families (copied from its probe, renamed rfx_cx_*).
// n roots join a shared uniform chain at distinct depths. Supplementary rows
// are subsets of existing F rows, so truth remains front/far for n >= 3.
fn rfx_cx_stagger(n: usize, far: bool, tag: &str) -> Type {
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
    defs.extend((1..=n).map(|i| {
        def(
            &format!("M{i}{tag}"),
            Expr::Union(vec![
                nil(),
                cons(
                    Expr::Type(&Type::int() - &lit(1)),
                    r(if i == 1 { 0 } else { n + i - 1 }),
                ),
            ]),
        )
    }));
    for i in 1..n - 1 {
        defs.push(def(
            &format!("B{i}{tag}"),
            cons(Expr::Type(&Type::int() - &lit(i as i64 + 2)), r(i)),
        ));
    }
    let ts = r3_instance(defs);
    let top = if far { n - 1 } else { n };
    let u = (1..=top)
        .chain([2 * n])
        .chain(2 * n + 1..ts.len())
        .fold(Type::empty(), |u, i| r3_union(&u, &ts[i]));
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
fn rfx_cl_cofront_block(
    n: usize,
    ones: bool,
    excl: fn(usize) -> usize,
    block: bool,
    tag: &str,
) -> Type {
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
        def(
            &format!("M{k}{tag}"),
            Expr::Union(vec![nil(), cons(not_one.clone(), rest)]),
        )
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
    let u = (1..=n)
        .chain([2 * n])
        .chain(block)
        .map(|i| &ts[i])
        .fold(Type::empty(), |u, t| r3_union(&u, t));
    let pos = if ones {
        ts[2 * n + 1].clone()
    } else {
        ts[0].clone()
    };
    &pos - &u
}

fn rfx_cx_emitheads(n: usize, far: bool, tag: &str) -> Type {
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    for i in (1..=n).rev() {
        let h = if !far && i == n {
            Type::int()
        } else {
            &Type::int() - &lit(i as i64)
        };
        let mut branches = vec![cons(Expr::Type(h), r(0))];
        if i < n {
            branches.push(cons(Expr::Type(Type::int()), r(defs.len() - 1)));
        }
        defs.push(def(&format!("G{i}{tag}"), Expr::Union(branches)));
    }
    let mut p = 0;
    for i in (1..=n).rev() {
        let idx = defs.len();
        defs.push(def(
            &format!("Q{i}{tag}"),
            cons(Expr::Type(Type::int()), r(p)),
        ));
        p = idx;
    }
    let ts = r3_instance(defs);
    &ts[p] - &ts[n]
}

// Shared staggered suffixes with heads containing the whole carrier.
fn rfx_cx_stagger_wide(n: usize, far: bool, tag: &str) -> Type {
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
    defs.extend((1..=n).map(|i| {
        def(
            &format!("M{i}{tag}"),
            Expr::Union(vec![
                nil(),
                cons(
                    Expr::Type(&Type::int() - &lit(1)),
                    r(if i == 1 { 0 } else { n + i - 1 }),
                ),
            ]),
        )
    }));
    for i in 1..n - 1 {
        defs.push(def(
            &format!("B{i}{tag}"),
            cons(
                Expr::Type(&Type::int() | &Type::atom(&format!("wide{i}"))),
                r(i),
            ),
        ));
    }
    let ts = r3_instance(defs);
    let top = if far { n - 1 } else { n };
    let u = (1..=top)
        .chain([2 * n])
        .chain(2 * n + 1..ts.len())
        .fold(Type::empty(), |u, i| r3_union(&u, &ts[i]));
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
        def(&format!("C{k}{tag}"), cons(Expr::Type(g), r(b_base + k)))
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
        def(&format!("R{k}{tag}"), cons(Expr::Type(hb), r(2 * n + k)))
    }));
    let ts = r3_instance(defs);
    let top = if far { n - 1 } else { n };
    let r_indices = (1..=h).filter(|&k| d + k < top).map(|k| 2 * n + h + k);
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
            args.iter()
                .map(|a| rewrite_expr_refs(a, inv_perm))
                .collect(),
        ),
        Expr::Union(xs) => Expr::Union(xs.iter().map(|x| rewrite_expr_refs(x, inv_perm)).collect()),
        Expr::And(xs) => Expr::And(xs.iter().map(|x| rewrite_expr_refs(x, inv_perm)).collect()),
        Expr::Diff(a, b) => Expr::Diff(
            Box::new(rewrite_expr_refs(a, inv_perm)),
            Box::new(rewrite_expr_refs(b, inv_perm)),
        ),
        Expr::Not(a) => Expr::Not(Box::new(rewrite_expr_refs(a, inv_perm))),
        Expr::Tuple(xs) => Expr::Tuple(xs.iter().map(|x| rewrite_expr_refs(x, inv_perm)).collect()),
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
                    let gh_samples: Vec<Value> = [0, 1]
                        .into_iter()
                        .chain(3..=n as i64 + 2)
                        .map(Value::Int)
                        .collect();
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
                            perm = (0..k_len).step_by(2).chain((1..k_len).step_by(2)).collect();
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
                    if d < n && skip != Some(d + 1) {
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
struct R3Node {
    stop: bool,
    mask: u64,
    next: usize,
}

fn r3_spec(
    n: usize,
    m: usize,
    skip: usize,
    holes: usize,
    stagger: bool,
) -> (Vec<R3Node>, Vec<usize>, u64) {
    let all = (1u64 << (n + 3)) - 1;
    let mut ns = vec![R3Node {
        stop: true,
        mask: all,
        next: 0,
    }];
    for i in 1..=n {
        ns.push(R3Node {
            stop: false,
            mask: if i == 1 { 2 } else { all },
            next: if i == 1 { 0 } else { i - 1 },
        });
    }
    for i in 1..=m {
        ns.push(R3Node {
            stop: true,
            mask: all ^ 2,
            next: if i == 1 { 0 } else { n + i - 1 },
        });
    }
    let mut roots: Vec<_> = (1..=n).filter(|&i| i != skip).chain([n + m]).collect();
    for k in 0..holes {
        if stagger {
            let b = ns.len();
            ns.push(R3Node {
                stop: false,
                mask: all ^ (1 << (k + 2)),
                next: 1 + k % n,
            });
            roots.push(b);
            continue;
        }
        let a = ns.len();
        ns.push(R3Node {
            stop: false,
            mask: all ^ (1 << (k + 2)),
            next: 1,
        });
        let b = ns.len();
        ns.push(R3Node {
            stop: false,
            mask: all,
            next: a,
        });
        roots.push(b);
    }
    (ns, roots, all)
}

fn r3_oracle(ns: &[R3Node], roots: &[usize], all: u64) -> bool {
    let mut root = roots.to_vec();
    root.sort_unstable();
    root.dedup();
    let mut seen = BTreeSet::new();
    let mut todo = vec![root];
    while let Some(state) = todo.pop() {
        if !seen.insert(state.clone()) {
            continue;
        }
        if state.iter().all(|&i| !ns[i].stop) {
            return true;
        }
        for bit in 0..64 {
            if all & (1u64 << bit) == 0 {
                continue;
            }
            let mut next: Vec<_> = state
                .iter()
                .filter(|&&i| ns[i].mask & (1u64 << bit) != 0)
                .map(|&i| ns[i].next)
                .collect();
            next.sort_unstable();
            next.dedup();
            todo.push(next);
        }
    }
    false
}

fn r3_build(
    ns: &[R3Node],
    roots: &[usize],
    all: u64,
    reverse: bool,
    tag: &str,
    mode: usize,
) -> Type {
    let size = ns.len();
    let index = |i| if reverse { size - 1 - i } else { i };
    let mut defs = Vec::new();
    for (i, nd) in ns.iter().enumerate() {
        let mut h = if nd.mask & 1 != 0 {
            Type::int()
        } else {
            Type::empty()
        };
        for bit in 1..64 {
            if all & (1u64 << bit) == 0 {
                continue;
            }
            let v = lit(bit as i64);
            if nd.mask & (1u64 << bit) != 0 {
                h = &h | &v;
            } else {
                h = &h - &v;
            }
        }
        if mode == 1 {
            h = Type::tuple(vec![h, Type::int()]);
        }
        if mode == 2 {
            h = Type::empty();
            for (bit, value) in [(0, false), (1, true)] {
                if nd.mask & (1 << bit) != 0 {
                    h = &h | &Type::lit(&Value::Bool(value)).unwrap();
                }
            }
        }
        let step = cons(Expr::Type(h), r(index(nd.next)));
        let body = if nd.stop {
            Expr::Union(if reverse {
                vec![step, nil()]
            } else {
                vec![nil(), step]
            })
        } else {
            step
        };
        defs.push(def(&format!("R3_{i}_{tag}"), body));
    }
    if reverse {
        defs.reverse();
    }
    let ts = Group::new(defs).unwrap().instance(vec![]);
    let mut order = roots.to_vec();
    if reverse {
        order.reverse();
    }
    let u = order.iter().fold(Type::empty(), |u, &i| &u | &ts[index(i)]);
    &ts[index(0)] - &u
}

#[test]
fn r3_cofinite_redundant_oracle_and_order() {
    big(|| {
        let mut cases = 0;
        for n in 1..=6 {
            for m in 1..=n + 2 {
                for skip in 0..=n {
                    for (mode, holes, stagger) in [
                        (0, 0, false),
                        (0, 1, false),
                        (0, n, false),
                        (1, 0, false),
                        (1, 1, false),
                        (1, n, false),
                        (2, 0, false),
                        (0, n, true),
                        (1, n, true),
                    ] {
                        let (ns, roots, mut all) = r3_spec(n, m, skip, holes, stagger);
                        if mode == 2 {
                            all = 3;
                        }
                        let expected = if r3_oracle(&ns, &roots, all) {
                            Verdict::Inhabited
                        } else {
                            Verdict::Empty
                        };
                        let tag = format!("{n}_{m}_{skip}_{holes}_{stagger}");
                        let a = r3_build(&ns, &roots, all, false, &tag, mode);
                        let b = r3_build(&ns, &roots, all, true, &tag, mode);
                        Type::forget_emptiness();
                        let av = a.verdict();
                        let bv = b.verdict();
                        assert_eq!(
                            av, expected,
                            "oracle n={n} m={m} skip={skip} holes={holes} mode={mode} stagger={stagger}"
                        );
                        assert_eq!(bv, av, "definition/union order {tag}");
                        assert_eq!(a.is_empty(), expected == Verdict::Empty, "is_empty {tag}");
                        Type::forget_emptiness();
                        assert_eq!(b.verdict(), bv, "b first {tag}");
                        assert_eq!(a.verdict(), av, "a second {tag}");
                        cases += 1;
                    }
                }
            }
        }
        eprintln!("R3 cofinite oracle/order cases={cases}");
    });
}

#[test]
fn r3_stress_scale_prebuilt() {
    for (case, want) in [
        ("bool", Verdict::Empty),
        ("boolfar", Verdict::Inhabited),
        ("chain", Verdict::Empty),
        ("chainfar", Verdict::Inhabited),
        ("clmanyheads", Verdict::Empty),
        ("clmanyheadsfar", Verdict::Inhabited),
        ("clstagger", Verdict::Empty),
        ("clstaggerfar", Verdict::Inhabited),
        ("cxstagger", Verdict::Empty),
        ("cxstaggerfar", Verdict::Inhabited),
        ("cxstaggerwide", Verdict::Empty),
        ("cxstaggerwidefar", Verdict::Inhabited),
        ("emitheads", Verdict::Empty),
        ("emitheadsfar", Verdict::Inhabited),
        ("far", Verdict::Inhabited),
        ("front", Verdict::Empty),
        ("groups", Verdict::Empty),
        ("groupsfar", Verdict::Inhabited),
        ("groupsholes", Verdict::Empty),
        ("groupsholesfar", Verdict::Inhabited),
        ("groupssingles", Verdict::Empty),
        ("groupssinglesfar", Verdict::Inhabited),
        ("manyheads", Verdict::Empty),
        ("manyheadsfar", Verdict::Inhabited),
        ("meet", Verdict::Empty),
        ("mlong", Verdict::Inhabited),
        ("mshort", Verdict::Empty),
        ("multi", Verdict::Empty),
        ("multifar", Verdict::Inhabited),
        ("one", Verdict::Empty),
        ("onetwo", Verdict::Inhabited),
        ("pair", Verdict::Empty),
        ("pairfar", Verdict::Inhabited),
        ("skip1", Verdict::Inhabited),
        ("skipmid", Verdict::Inhabited),
        ("split", Verdict::Empty),
        ("splitfar", Verdict::Inhabited),
        ("stagger", Verdict::Empty),
        ("staggerfar", Verdict::Inhabited),
        ("tuple", Verdict::Empty),
        ("tuplefar", Verdict::Inhabited),
        ("tupleflip", Verdict::Empty),
        ("tupleflipfar", Verdict::Inhabited),
    ] {
        big(move || {
            let inputs: Vec<_> = [8, 64]
                .into_iter()
                .map(|n| (n, rfx_case(case, n, &format!("_scale3_{case}_{n}"))))
                .collect();
            scaling::check(case, 8, |n| {
                Type::forget_emptiness();
                let t = &inputs.iter().find(|(k, _)| *k == n).unwrap().1;
                assert_eq!(t.verdict(), want, "{case} n={n}");
            });
        });
    }
}
// Test input construction only. The kernel reads neither this flag nor any
// environment variable. Reindex all references, then restore the returned
// vector's indexing so every caller denotes the same equations.
thread_local! { static R3_REVERSE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
fn r3_instance(mut defs: Vec<Def>) -> Vec<Type> {
    let reverse = R3_REVERSE.with(|x| x.get());
    if reverse {
        let count = defs.len();
        for d in &mut defs {
            let mut todo = vec![&mut d.body];
            while let Some(e) = todo.pop() {
                match e {
                    Expr::Ref(i, args) => {
                        *i = count - 1 - *i;
                        todo.extend(args.iter_mut());
                    }
                    Expr::Union(xs) => {
                        xs.reverse();
                        todo.extend(xs.iter_mut());
                    }
                    Expr::And(xs) | Expr::Tuple(xs) | Expr::Atom(_, xs) => {
                        todo.extend(xs.iter_mut())
                    }
                    Expr::Not(x) => todo.push(x),
                    Expr::Diff(a, b) => {
                        todo.push(a);
                        todo.push(b);
                    }
                    Expr::Morphism(a, b, c) => {
                        todo.push(a);
                        todo.push(b);
                        todo.push(c);
                    }
                    Expr::Type(_) | Expr::Param(_) => {}
                }
            }
        }
        defs.reverse();
    }
    let mut ts = Group::new(defs).unwrap().instance(vec![]);
    if reverse {
        ts.reverse();
    }
    ts
}
fn r3_union(a: &Type, b: &Type) -> Type {
    if R3_REVERSE.with(|x| x.get()) {
        b | a
    } else {
        a | b
    }
}

#[test]
fn r3_all_probe_and_family_orders() {
    big(|| {
        let cases = [
            "front",
            "far",
            "skip1",
            "skipmid",
            "bool",
            "boolfar",
            "mshort",
            "mlong",
            "split",
            "splitfar",
            "meet",
            "pair",
            "pairfar",
            "tuple",
            "tuplefar",
            "tupleflip",
            "tupleflipfar",
            "multi",
            "multifar",
            "groups",
            "groupsfar",
            "groupsholes",
            "groupsholesfar",
            "groupssingles",
            "groupssinglesfar",
            "cxstagger",
            "cxstaggerfar",
            "cxstaggerwide",
            "cxstaggerwidefar",
            "clmanyheads",
            "clmanyheadsfar",
            "clstagger",
            "clstaggerfar",
            "clstaggerholes",
            "clcofront",
            "clcofrontones",
            "clcofrontsame",
            "clcofrontsameones",
            "clcofrontsameblock",
            "clcofrontshared",
            "emitheads",
            "emitheadsfar",
            "manyheads",
            "manyheadsfar",
            "stagger",
            "staggerfar",
            "chain",
            "chainfar",
            "one",
            "onetwo",
            "end",
            "boundaryinside",
            "boundaryoutside",
            "cxprivateheads",
            "cxprivateheadsfar",
            "manyheadsv0",
            "manyheadsfarv0",
        ];
        let mut count = 0;
        for case in cases {
            for n in 3..=6 {
                let tag = format!("_order3_{case}_{n}");
                R3_REVERSE.with(|x| x.set(false));
                let a = rfx_case(case, n, &tag);
                R3_REVERSE.with(|x| x.set(true));
                let b = rfx_case(case, n, &tag);
                R3_REVERSE.with(|x| x.set(false));
                Type::forget_emptiness();
                let av = a.verdict();
                let bv = b.verdict();
                assert_eq!(av, bv, "probe definition/operand order {case} {n}");
                Type::forget_emptiness();
                assert_eq!(b.verdict(), bv);
                assert_eq!(a.verdict(), av);
                count += 1;
            }
        }
        for (all, one) in [
            (Type::int(), lit(1)),
            (Type::bool(), Type::lit(&Value::Bool(true)).unwrap()),
            (
                Type::tuple(vec![Type::int(), Type::int()]),
                Type::tuple(vec![lit(1), Type::int()]),
            ),
        ] {
            for n in 1..=6 {
                for skip in std::iter::once(None).chain((1..=n).map(Some)) {
                    for m in 1..=n + 2 {
                        for split in [false, true] {
                            let tag = format!("_orderf3_{count}");
                            R3_REVERSE.with(|x| x.set(false));
                            let (l, u) = rfx_family(n, skip, m, &all, &one, split, &tag);
                            let a = &l - &u;
                            R3_REVERSE.with(|x| x.set(true));
                            let (l, u) = rfx_family(n, skip, m, &all, &one, split, &tag);
                            let b = &l - &u;
                            R3_REVERSE.with(|x| x.set(false));
                            Type::forget_emptiness();
                            let av = a.verdict();
                            let bv = b.verdict();
                            assert_eq!(
                                av, bv,
                                "family definitions/operands n={n} skip={skip:?} m={m} split={split}"
                            );
                            Type::forget_emptiness();
                            assert_eq!(b.verdict(), bv);
                            assert_eq!(a.verdict(), av);
                            count += 1;
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
            for m in 1..=n + 2 {
                for skip in 0..=n {
                    for (mode, holes, stagger) in [
                        (0, 0, false),
                        (0, 1, false),
                        (0, n, false),
                        (1, 0, false),
                        (1, 1, false),
                        (1, n, false),
                        (2, 0, false),
                        (0, n, true),
                        (1, n, true),
                    ] {
                        let (ns, roots, mut all) = r3_spec(n, m, skip, holes, stagger);
                        if mode == 2 {
                            all = 3;
                        }
                        let expected = if r3_oracle(&ns, &roots, all) {
                            Verdict::Inhabited
                        } else {
                            Verdict::Empty
                        };
                        let tag = format!("s{n}_{m}_{skip}_{holes}_{stagger}_{mode}");
                        let a = r3_build(&ns, &roots, all, false, &tag, mode);
                        let b = r3_build(&ns, &roots, all, true, &tag, mode);
                        Type::forget_emptiness();
                        let av = a.verdict();
                        Type::forget_emptiness();
                        let bv = b.verdict();
                        cases += 1;
                        if av != expected || bv != expected {
                            bad += 1;
                            eprintln!(
                                "MISMATCH n={n} m={m} skip={skip} mode={mode} holes={holes} stagger={stagger} want={expected:?} fwd={av:?} rev={bv:?}"
                            );
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
            let ru = neg_roots
                .iter()
                .fold(Type::empty(), |u, &i| r3_union(&u, &rev[i]));
            let rt = &rev[0] - &ru;
            R3_REVERSE.with(|x| x.set(false));
            Type::forget_emptiness();
            assert_eq!(
                rt.verdict(),
                original,
                "random definition/union order {trial}"
            );
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
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    for i in 2..=n {
        let h = if holes {
            &Type::int() - &lit(4)
        } else {
            Type::int()
        };
        defs.push(def(&format!("F{i}{tag}"), cons(Expr::Type(h), r(i - 1))));
    }
    for i in 1..=n {
        defs.push(def(
            &format!("M{i}{tag}"),
            Expr::Union(vec![
                nil(),
                cons(
                    Expr::Type(&Type::int() - &lit(1)),
                    r(if i == 1 { 0 } else { n + i - 1 }),
                ),
            ]),
        ));
    }
    let ts = r3_instance(defs);

    (1..=n)
        .chain([2 * n])
        .fold(Type::empty(), |u, i| r3_union(&u, &ts[i]))
}

#[test]
#[ignore]
fn r4_diagnostic_routes_and_head_width() {
    big(|| {
        for case in [
            "front",
            "emitheads",
            "emitheadsfar",
            "cxstagger",
            "clcofront",
            "clstaggerholes",
        ] {
            let t = rfx_case(case, 8, &format!("route_{case}"));
            eprintln!("route {case} {:?}", t.sweep_verdict());
        }
        for width in [4, 8, 12, 16] {
            let all = Type::tuple(vec![Type::bool(); width]);
            let mut coords = vec![Type::bool(); width];
            coords[0] = Type::lit(&Value::Bool(true)).unwrap();
            let one = Type::tuple(coords);
            let (l, u) = rfx_family(2, Some(2), 2, &all, &one, false, &format!("width_{width}"));
            let t = &l - &u;
            Type::forget_emptiness();
            let mut got = None;
            let w = scaling::Meter::new().work(|| got = Some(t.verdict()));
            eprintln!(
                "headwidth {width} {:?} units {} bytes {}",
                got, w.units, w.bytes
            );
            assert_eq!(got, Some(Verdict::Inhabited));
        }
    });
}

#[test]
fn r4_exact_classes_random_and_short_escape() {
    big(|| {
        let mut seed = 0x9183ab12u64;
        let mut rng = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut cases = 0;
        for trial in 0..200 {
            let n = 2 + (rng() % 4) as usize;
            let m = 1 + (rng() % (n + 2) as u64) as usize;
            let (mut ns, roots, all) = r3_spec(n, m, 0, n, true);
            // Bit zero is a fresh integer; bits 1..=n+2 are all listed literals.
            for nd in &mut ns[1..] {
                if rng() % 3 == 0 {
                    nd.mask = rng() & all;
                }
            }
            let inhab = r3_oracle(&ns, &roots, all);
            let a = r3_build(&ns, &roots, all, false, &format!("r4random{trial}"), 0);
            let b = r3_build(&ns, &roots, all, true, &format!("r4random{trial}"), 0);
            let av = a.sweep_verdict();
            let bv = b.sweep_verdict();
            assert_eq!(av, bv, "sweep definition order trial {trial}");
            for t in [&a, &b] {
                Type::forget_emptiness();
                match t.verdict() {
                    Verdict::Empty => assert!(!inhab, "oracle has witness {trial}"),
                    Verdict::Inhabited => assert!(inhab, "oracle empty {trial}"),
                    Verdict::Refused(_) => {}
                }
                assert!(!t.is_empty() || !inhab);
            }
            cases += 1;
        }
        for n in 2..=6 {
            for (case, want) in [
                ("clcofront", Verdict::Inhabited),
                ("clstaggerholes", Verdict::Inhabited),
                ("boundaryinside", Verdict::Inhabited),
                ("boundaryoutside", Verdict::Empty),
            ] {
                let tag = format!("r4boundary{n}{case}");
                R3_REVERSE.with(|v| v.set(false));
                let a = rfx_case(case, n, &tag);
                R3_REVERSE.with(|v| v.set(true));
                let b = rfx_case(case, n, &tag);
                R3_REVERSE.with(|v| v.set(false));
                assert_eq!(a.sweep_verdict(), Some(want), "{case} {n}");
                assert_eq!(b.sweep_verdict(), Some(want), "reverse {case} {n}");
                Type::forget_emptiness();
                assert_eq!(a.verdict(), want);
                assert_eq!(b.verdict(), want);
                Type::forget_emptiness();
                assert_eq!(b.verdict(), want);
                assert_eq!(a.verdict(), want);
                cases += 1;
            }
        }
        eprintln!("R4 exact-class random/boundary cases={cases}");
    });
}

fn r4_private_heads(n: usize, far: bool, tag: &str) -> Type {
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    let mut roots = Vec::new();
    for i in 1..=n {
        let h = if !far && i == n {
            Type::int()
        } else {
            &Type::int() - &lit(i as i64)
        };
        let leaf = defs.len();
        defs.push(def(&format!("H{i}{tag}"), cons(Expr::Type(h), r(0))));
        for j in 1..i {
            let prev = defs.len() - 1;
            defs.push(def(
                &format!("P{i}_{j}{tag}"),
                cons(Expr::Type(Type::int()), r(prev)),
            ));
        }
        roots.push(leaf + i - 1);
    }
    // A positive uniform prefix supplies the minimum length requirement.
    let mut positive = 0;
    for i in (1..=n).rev() {
        let idx = defs.len();
        defs.push(def(
            &format!("Q{i}{tag}"),
            cons(Expr::Type(Type::int()), r(positive)),
        ));
        positive = idx;
    }
    let ts = r3_instance(defs);
    let u = roots
        .iter()
        .fold(Type::empty(), |u, &i| r3_union(&u, &ts[i]));
    &(&ts[0] & &ts[positive]) - &u
}

fn rfx_manyheads_v0(n: usize, far: bool, tag: &str) -> Type {
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    let mut roots = Vec::new();
    for i in 1..=n {
        let h = if !far && i == n {
            Type::int()
        } else {
            &Type::int() - &lit(i as i64)
        };
        let leaf = defs.len();
        defs.push(def(&format!("H{i}{tag}"), cons(Expr::Type(h), r(0))));
        for j in 1..i {
            let prev = defs.len() - 1;
            defs.push(def(
                &format!("P{i}_{j}{tag}"),
                cons(Expr::Type(Type::int()), r(prev)),
            ));
        }
        roots.push(leaf + i - 1);
    }
    // A positive uniform prefix supplies the minimum length requirement.
    let mut positive = 0;
    for i in (1..=n).rev() {
        let idx = defs.len();
        defs.push(def(
            &format!("Q{i}{tag}"),
            cons(Expr::Type(Type::int()), r(positive)),
        ));
        positive = idx;
    }
    let ts = r3_instance(defs);
    let u = roots
        .iter()
        .fold(Type::empty(), |u, &i| r3_union(&u, &ts[i]));
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
                        if far {
                            "groupssinglesfar"
                        } else {
                            "groupssingles"
                        },
                        if far { "manyheadsfar" } else { "manyheads" },
                        if far { "staggerfar" } else { "stagger" },
                        if far { "chainfar" } else { "chain" },
                        if far { "cxstaggerfar" } else { "cxstagger" },
                        if far {
                            "cxstaggerwidefar"
                        } else {
                            "cxstaggerwide"
                        },
                        if far { "emitheadsfar" } else { "emitheads" },
                        if far { "clmanyheadsfar" } else { "clmanyheads" },
                    ] {
                        if n <= 3
                            || !matches!(
                                case,
                                "manyheads"
                                    | "manyheadsfar"
                                    | "groupsholes"
                                    | "groupsholesfar"
                                    | "groupssingles"
                                    | "groupssinglesfar"
                                    | "cxstagger"
                                    | "cxstaggerfar"
                                    | "emitheads"
                                    | "emitheadsfar"
                                    | "clmanyheads"
                                    | "clmanyheadsfar"
                            )
                        {
                            Type::forget_emptiness();
                            let tag = next_tag();
                            let t = rfx_case(case, n, &tag);
                            let samples = if matches!(
                                case,
                                "manyheads"
                                    | "manyheadsfar"
                                    | "groupsholes"
                                    | "groupsholesfar"
                                    | "groupssingles"
                                    | "groupssinglesfar"
                                    | "cxstagger"
                                    | "cxstaggerfar"
                                    | "emitheads"
                                    | "emitheadsfar"
                                    | "clmanyheads"
                                    | "clmanyheadsfar"
                            ) {
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
                        let max_l = if case == "clcofront" {
                            n + 1
                        } else {
                            2 * n + 1
                        };
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
            assert!(
                !(t.is_empty() && inhab),
                "is_empty random chain seed={seed:#x}"
            );
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
            assert_eq!(
                t.sweep_verdict(),
                Some(want),
                "sweep uniform random seed={seed:#x}"
            );
            Type::forget_emptiness();
            assert_eq!(t.verdict(), want, "uniform random seed={seed:#x}");
            assert_eq!(
                t.is_empty(),
                !inhab,
                "is_empty uniform random seed={seed:#x}"
            );
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
                            perm = (0..k_len).step_by(2).chain((1..k_len).step_by(2)).collect();
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
                    if d < n && skip != Some(d + 1) {
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

fn u4_cofront_block(
    n: usize,
    ones: bool,
    excl: fn(usize) -> usize,
    block: bool,
    tag: &str,
) -> Type {
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
        def(
            &format!("M{k}{tag}"),
            Expr::Union(vec![nil(), cons(not_one.clone(), rest)]),
        )
    }));
    let next = |k: usize| if k <= n { r(2 * n + k) } else { r(0) };
    defs.push(def(
        &format!("P{tag}"),
        cons(Expr::Type(Type::int()), next(2)),
    ));
    defs.extend((2..=n).map(|k| def(&format!("Q{k}{tag}"), cons(Expr::Type(lit(1)), next(k + 1)))));
    defs.push(def(&format!("K1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    defs.push(def(
        &format!("K{tag}"),
        cons(Expr::Type(Type::int()), r(3 * n + 1)),
    ));
    let ts = u4_inst(defs);
    let block = block.then_some(3 * n + 2);
    let u = (1..=n)
        .chain([2 * n])
        .chain(block)
        .map(|i| &ts[i])
        .fold(Type::empty(), |u, t| &u | t);
    let pos = if ones {
        ts[2 * n + 1].clone()
    } else {
        ts[0].clone()
    };
    &pos - &u
}

fn u4_stagger_boundary(n: usize, overlap: bool, tag: &str) -> Type {
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
    let ts = u4_inst(defs);
    let l = ts[0].clone();
    let u = (1..=n)
        .map(|k| &ts[k])
        .chain([&ts[m + 2]])
        .fold(Type::empty(), |u, t| &u | t);
    &l - &u
}

fn u4_boundary(n: usize, holes: bool, tag: &str) -> Type {
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(Expr::Type(Type::int()), r(0))]),
    )];
    defs.push(def(&format!("F1{tag}"), cons(Expr::Type(lit(1)), r(0))));
    for i in 2..=n {
        let h = if holes {
            &Type::int() - &lit(4)
        } else {
            Type::int()
        };
        defs.push(def(&format!("F{i}{tag}"), cons(Expr::Type(h), r(i - 1))));
    }
    for i in 1..=n {
        defs.push(def(
            &format!("M{i}{tag}"),
            Expr::Union(vec![
                nil(),
                cons(
                    Expr::Type(&Type::int() - &lit(1)),
                    r(if i == 1 { 0 } else { n + i - 1 }),
                ),
            ]),
        ));
    }
    let ts = u4_inst(defs);
    let l = ts[0].clone();
    let u = (1..=n)
        .chain([2 * n])
        .fold(Type::empty(), |u, i| &u | &ts[i]);
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
        def(
            &format!("L{tag}"),
            Expr::Union(vec![nil(), cons(int(), r(0))]),
        ),
        def(&format!("U1{tag}"), cons(one(), r(0))),
        def(&format!("U2{tag}"), cons(not(2), r(1))),
        def(&format!("U3{tag}"), cons(not(3), r(2))),
        def(&format!("U4{tag}"), cons(not(4), r(3))),
        def(
            &format!("P{tag}"),
            cons(
                int(),
                cons(
                    Expr::Type(&lit(2) | &lit(5)),
                    cons(one(), cons(one(), r(0))),
                ),
            ),
        ),
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
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    defs.push(def(
        &format!("F1{tag}"),
        cons(Expr::Type(h[1].clone()), r(0)),
    ));
    defs.extend((2..=len).map(|d| {
        def(
            &format!("F{d}{tag}"),
            cons(Expr::Type(h[d].clone()), r(d - 1)),
        )
    }));
    let clause_place = |p: usize| p > k && (p - k).is_multiple_of(k + 1);
    let mut e = nil();
    for p in (1..=len).rev() {
        let head = if p <= k {
            &lit(0) | &lit(1)
        } else if clause_place(p) {
            lit(2)
        } else {
            lit(7)
        };
        e = cons(Expr::Type(head), e);
    }
    defs.push(def(&format!("P{tag}"), e));
    let ts = u4_inst(defs);
    let u = (1..=len).fold(Type::empty(), |u, d| &u | &ts[d]);
    &ts[len + 1] - &u
}

fn r5_sat(k: usize, cls: &[Vec<(usize, bool)>]) -> bool {
    // Value 0 at place i makes a positive literal true; value 1 a negative one.
    (0..1u32 << k).any(|a| {
        cls.iter()
            .all(|cl| cl.iter().any(|&(i, pos)| ((a >> (i - 1)) & 1 == 0) == pos))
    })
}

#[test]
#[ignore]
fn r5_sat_check() {
    let spec: Vec<usize> = std::env::var("R5SAT")
        .unwrap_or("3,1,4,3,0,1".into())
        .split(',')
        .map(|s| s.parse().unwrap())
        .collect();
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
        if vars.len() < wmin || vars.len() > 3 {
            continue;
        }
        for s in 0..1u32 << vars.len() {
            all.push(
                vars.iter()
                    .enumerate()
                    .map(|(j, &i)| (i, s >> j & 1 == 0))
                    .collect(),
            );
        }
    }
    let mut seen = 0usize;
    big(move || {
        let mut counts = std::collections::BTreeMap::new();
        let (mut bad, mut units, mut most) = (0, 0u64, 0u64);
        let n = all.len();
        let mut stack: Vec<Vec<usize>> = vec![vec![]];
        while let Some(set) = stack.pop() {
            let mine = set.len() >= mlo && {
                seen += 1;
                seen % nsh == shard
            };
            if mine {
                let cls: Vec<_> = set.iter().map(|&i| all[i].clone()).collect();
                Type::forget_emptiness();
                let t = r5_sat_type(
                    k,
                    &cls,
                    &format!(
                        "_sat{k}_{}",
                        set.iter()
                            .map(|i| i.to_string())
                            .collect::<Vec<_>>()
                            .join("_")
                    ),
                );
                let sat = r5_sat(k, &cls);
                let mut m = scaling::Meter::new();
                let mut v = None;
                let w = m.work(|| v = Some(t.verdict()));
                let v = v.unwrap();
                units += w.units;
                most = most.max(w.units);
                let wrong = matches!(
                    (&v, sat),
                    (Verdict::Empty, true) | (Verdict::Inhabited, false)
                );
                if wrong {
                    bad += 1;
                    eprintln!("r5sat WRONG k {k} {cls:?} sat {sat} {v:?}");
                }
                *counts
                    .entry(format!("m{} sat {sat} {v:?}", set.len()))
                    .or_insert(0usize) += 1;
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
                if matches!(
                    (&sw, sat),
                    (Some(Verdict::Empty), true) | (Some(Verdict::Inhabited), false)
                ) {
                    bad += 1;
                    eprintln!("r5sat WRONG SWEEP k {k} {cls:?} sat {sat} {sw:?}");
                }
                if matches!(
                    (&ch, sat),
                    (Some(Verdict::Empty), true) | (Some(Verdict::Inhabited), false)
                ) {
                    bad += 1;
                    eprintln!("r5sat WRONG CHAINS k {k} {cls:?} sat {sat} {ch:?}");
                }
                *counts
                    .entry(format!("mech m{} {by} {sw:?} chains {ch:?}", set.len()))
                    .or_insert(0usize) += 1;
            }
            if set.len() < mhi {
                let from = set.last().map_or(0, |&l| l + 1);
                for i in from..n {
                    let mut s = set.clone();
                    s.push(i);
                    stack.push(s);
                }
            }
        }
        for (key, c) in &counts {
            eprintln!("r5sat k {k} {key}: {c}");
        }
        eprintln!(
            "r5sat k {k} m {mlo}..{mhi} w {wmin} shard {shard}/{nsh} cases {} wrong {bad} units {units} most {most}",
            counts
                .iter()
                .filter(|(k, _)| !k.starts_with("mech"))
                .map(|(_, c)| c)
                .sum::<usize>()
        );
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
    let mut ds = vec![def("R5L", Expr::Union(vec![nil(), cons(int(), r(0))]))];
    ds.push(def("R5F1", cons(Expr::Type(lit(1)), r(0))));
    for k in 2..=6 {
        ds.push(def(
            &format!("R5F{k}"),
            cons(Expr::Type(&Type::int() - &lit(k as i64)), r(k - 1)),
        ));
    }
    let hs = [
        &lit(4) | &(&lit(5) | &lit(6)),
        if outside {
            &lit(4) | &lit(5)
        } else {
            Type::int()
        },
        if outside { lit(2) } else { Type::int() },
        lit(1),
        lit(1),
        lit(1),
    ];
    let mut p = r(0);
    for _ in 0..n {
        p = cons(int(), p);
    }
    for h in hs.iter().rev() {
        p = cons(Expr::Type(h.clone()), p);
    }
    ds.push(def("R5P", p));
    let g = r3_instance(ds);
    &g[7] - &(&g[4] | &(&g[5] | &g[6]))
}
fn r5_varying_width(w: usize) -> Type {
    let all = Type::tuple(vec![Type::bool(); w]);
    let mut defs = vec![def(
        "R5WidthL",
        Expr::Union(vec![nil(), cons(Expr::Type(all.clone()), r(0))]),
    )];
    for j in 0..w {
        let mut cs = vec![Type::bool(); w];
        cs[j] = Type::lit(&Value::Bool(true)).unwrap();
        defs.push(def(
            &format!("R5WidthF{j}"),
            cons(Expr::Type(Type::tuple(cs)), r(0)),
        ));
    }
    defs.push(def("R5WidthP", cons(Expr::Type(all), r(0))));
    let g = Group::new(defs).unwrap().instance(vec![]);
    let u = (1..=w).fold(Type::empty(), |u, j| &u | &g[j]);
    &g[w + 1] - &u
}
#[test]
fn rfxx_r5_matching_non_nested_slots() {
    let mut ds = vec![def("R5L", Expr::Union(vec![nil(), cons(int(), r(0))]))];
    ds.push(def("R5F1", cons(Expr::Type(lit(1)), r(0))));
    for k in 2..=6 {
        ds.push(def(
            &format!("R5F{k}"),
            cons(Expr::Type(&Type::int() - &lit(k as i64)), r(k - 1)),
        ));
    }
    let hs = [
        &lit(4) | &(&lit(5) | &lit(6)),
        &lit(4) | &lit(5),
        lit(2),
        lit(1),
        lit(1),
        lit(1),
    ];
    let mut p = r(0);
    for h in hs.iter().rev() {
        p = cons(Expr::Type(h.clone()), p);
    }
    ds.push(def("R5P", p));
    let g = r3_instance(ds);
    let t = &g[7] - &(&g[4] | &(&g[5] | &g[6]));
    let witness = [5, 5, 2, 1, 1, 1]
        .iter()
        .rev()
        .fold(Value::atom("nil"), |tail, &x| {
            Value::atom_with("cons", vec![Value::Int(x), tail])
        });
    assert!(t.contains(&witness));
    eprintln!(
        "matching nonnested sweep={:?} verdict={:?} witness_checked=true",
        t.sweep_verdict(),
        t.verdict()
    );
    assert_ne!(t.verdict(), Verdict::Empty);
    assert!(!t.is_empty());
}
#[test]
fn rfxx_r5_carrier_only_constrains_the_suffix() {
    let ds = vec![
        def("R5SuffixL", Expr::Union(vec![nil(), cons(int(), r(0))])),
        def("R5SuffixR", cons(int(), r(0))),
        def(
            "R5SuffixQ",
            Expr::Union(vec![
                nil(),
                cons(Expr::Type(&Type::int() | &Type::atom("a")), r(1)),
            ]),
        ),
        def("R5SuffixP", cons(Expr::Type(&Type::int() - &lit(1)), r(2))),
        def("R5SuffixN", cons(Expr::Type(&Type::int() - &lit(1)), r(0))),
    ];
    let g = Group::new(ds).unwrap().instance(vec![]);
    let t = &g[3] - &g[4];
    let w = [Value::Int(0), Value::atom("a"), Value::Int(0)]
        .into_iter()
        .rev()
        .fold(Value::atom("nil"), |tail, x| {
            Value::atom_with("cons", vec![x, tail])
        });
    assert!(t.contains(&w));
    assert_ne!(t.sweep_verdict(), Some(Verdict::Empty));
    assert_ne!(t.verdict(), Verdict::Empty);
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
    let mut cls: Vec<Vec<(usize, bool)>> = (1..=k)
        .map(|i| vec![(i, true), (i % k + 1, false)])
        .collect();
    cls.push(vec![(1, true), (2, true)]);
    let mut seen: BTreeSet<Vec<(usize, bool)>> = cls
        .iter()
        .map(|c| {
            let mut c = c.clone();
            c.sort();
            c
        })
        .collect();
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
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    defs.push(def(
        &format!("F1{tag}"),
        cons(Expr::Type(h[1].clone()), r(0)),
    ));
    defs.extend((2..=len).map(|d| {
        def(
            &format!("F{d}{tag}"),
            cons(Expr::Type(h[d].clone()), r(d - 1)),
        )
    }));
    let clause_place = |p: usize| p > k && (p - k).is_multiple_of(k + 1);
    let mut e = nil();
    for p in (1..=len).rev() {
        let head = if p <= k {
            &lit(0) | &lit(1)
        } else if clause_place(p) {
            lit(2)
        } else {
            filler.clone()
        };
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
    cases_scale_from(
        &[
            ("r6wide", Verdict::Inhabited),
            ("r6comb", Verdict::Inhabited),
        ],
        128,
    );
}

/// R7: the round-6 probe cases no other scaling test reads. `r6twowide` and `r6threeun` are
/// outside the chains' class and quadratic on the base search as well, so they are not here.
#[test]
fn r7_round6_probe_cases_are_decided_in_their_size() {
    r5_cases_scale(&[
        ("r6two", Verdict::Inhabited),
        ("r6twoun", Verdict::Empty),
        ("r6parity", Verdict::Inhabited),
        ("r6repeat3", Verdict::Inhabited),
        ("r6distinct2", Verdict::Inhabited),
        ("r6distinct3", Verdict::Inhabited),
    ]);
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
            let e = chain(&|p| {
                if p == u || p == v {
                    lit(c)
                } else {
                    Type::int()
                }
            });
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
    let blocks: Vec<(usize, usize, i64)> = edges
        .iter()
        .flat_map(|&(u, v)| (1..=3).map(move |c| (u, v, c)))
        .collect();
    let len = rc(blocks.len());
    let three = &(&lit(1) | &lit(2)) | &lit(3);
    let mut h = vec![Type::int(); len + 1];
    h[1] = lit(0);
    for (b, &(u, v, c)) in blocks.iter().enumerate() {
        let others = (1..=3)
            .filter(|&x| x != c)
            .fold(Type::empty(), |s, x| &s | &lit(x));
        for p in [u, v] {
            h[rc(b + 1) - p + 1] = &Type::int() - &others;
        }
    }
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    defs.push(def(
        &format!("F1{tag}"),
        cons(Expr::Type(h[1].clone()), r(0)),
    ));
    defs.extend((2..=len).map(|d| {
        def(
            &format!("F{d}{tag}"),
            cons(Expr::Type(h[d].clone()), r(d - 1)),
        )
    }));
    let mut e = nil();
    for p in (1..=len).rev() {
        let head = if p <= nv {
            three.clone()
        } else if (p - nv).is_multiple_of(nv + 1) {
            lit(0)
        } else {
            lit(7)
        };
        e = cons(Expr::Type(head), e);
    }
    defs.push(def(&format!("P{tag}"), e));
    let ts = u4_inst(defs);
    let u = (1..=len).fold(Type::empty(), |u, d| &u | &ts[d]);
    (&ts[len + 1] - &u, len)
}

fn r6_colour_list(xs: &[i64]) -> Value {
    xs.iter().rev().fold(Value::atom("nil"), |tl, &h| {
        Value::atom_with("cons", vec![Value::Int(h), tl])
    })
}

/// Every graph on `nv` vertices whose edge mask is `shard` mod `nsh`: the type is inhabited
/// exactly when brute force finds a proper colouring (each colouring is a list of `P`, tested by
/// membership), and no mechanism answers wrongly. With `comb`, also the comb form
/// ([`r6_colour_comb`]), which the escape solve reads and must decline (its atoms cross).
fn r6_colouring_check(nv: usize, shard: u32, nsh: u32, comb: bool) {
    big(move || {
        let mut counts = std::collections::BTreeMap::new();
        {
            let pairs: Vec<(usize, usize)> = (1..=nv)
                .flat_map(|u| (u + 1..=nv).map(move |v| (u, v)))
                .collect();
            for mask in 0u32..1 << pairs.len() {
                if mask % nsh != shard {
                    continue;
                }
                let edges: Vec<(usize, usize)> = pairs
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| mask >> i & 1 == 1)
                    .map(|(_, &e)| e)
                    .collect();
                if edges.is_empty() {
                    continue;
                }
                let t = r6_colour_type(nv, &edges, &format!("_r6col{nv}_{mask}"));
                let mut colourable = false;
                for code in 0..3u32.pow(nv as u32) {
                    let xs: Vec<i64> = (0..nv)
                        .map(|i| (code / 3u32.pow(i as u32) % 3) as i64 + 1)
                        .collect();
                    let proper = edges.iter().all(|&(u, v)| xs[u - 1] != xs[v - 1]);
                    assert_eq!(
                        t.contains(&r6_colour_list(&xs)),
                        proper,
                        "nv {nv} mask {mask} {xs:?}"
                    );
                    colourable |= proper;
                }
                Type::forget_emptiness();
                let ch = t.chain_verdict();
                Type::forget_emptiness();
                let v = t.verdict();
                let wrong = |x: &Verdict| {
                    matches!(
                        (x, colourable),
                        (Verdict::Empty, true) | (Verdict::Inhabited, false)
                    )
                };
                assert!(
                    !wrong(&v) && !ch.as_ref().is_some_and(wrong),
                    "nv {nv} mask {mask} colourable {colourable} {v:?} {ch:?}"
                );
                *counts
                    .entry(format!(
                        "nv {nv} colourable {colourable} {v:?} chains {ch:?}"
                    ))
                    .or_insert(0usize) += 1;
                if !comb {
                    continue;
                }
                // The comb form: the same colourings, padded with the block values.
                let (t, len) = r6_colour_comb(nv, &edges, &format!("_r6cc{nv}_{mask}"));
                for code in 0..3u32.pow(nv as u32) {
                    let mut xs: Vec<i64> = (0..nv)
                        .map(|i| (code / 3u32.pow(i as u32) % 3) as i64 + 1)
                        .collect();
                    let proper = edges.iter().all(|&(u, v)| xs[u - 1] != xs[v - 1]);
                    xs.extend((nv + 1..=len).map(|p| {
                        if (p - nv).is_multiple_of(nv + 1) {
                            0
                        } else {
                            7
                        }
                    }));
                    assert_eq!(
                        t.contains(&r6_colour_list(&xs)),
                        proper,
                        "comb nv {nv} mask {mask} {xs:?}"
                    );
                }
                Type::forget_emptiness();
                let ch = t.chain_verdict();
                Type::forget_emptiness();
                let v = t.verdict();
                assert!(
                    !wrong(&v) && !ch.as_ref().is_some_and(wrong),
                    "comb nv {nv} mask {mask} colourable {colourable} {v:?} {ch:?}"
                );
                *counts
                    .entry(format!(
                        "comb nv {nv} colourable {colourable} {v:?} chains {ch:?}"
                    ))
                    .or_insert(0usize) += 1;
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
        if x == 3 {
            self.cof
        } else {
            (self.mask >> x & 1 == 1) != self.cof
        }
    }
    fn ty(self) -> Type {
        let s = (0..3)
            .filter(|&i| self.mask >> i & 1 == 1)
            .fold(Type::empty(), |u, i| &u | &lit(i));
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
            1 | 2 => R6Head {
                cof: true,
                mask: 1 << g.below(3),
            },
            3 => R6Head {
                cof: true,
                mask: g.below(8) as u8,
            },
            _ => R6Head {
                cof: false,
                mask: 1 + g.below(7) as u8,
            },
        }
    };
    let carrier = (g.below(4) != 0).then(|| {
        if g.below(2) == 0 {
            R6Head { cof: true, mask: 0 }
        } else {
            head(g)
        }
    });
    let terminal = |g: &mut R6Rng| {
        if carrier.is_some() && g.below(3) != 0 {
            R6Tail::Car
        } else {
            R6Tail::End
        }
    };
    let np = 1 + g.below(np_max) as usize;
    let mut pool = Vec::new();
    for i in 0..np {
        let next = if i > 0 && g.below(3) != 0 {
            R6Tail::Node(g.below(i as u64) as usize)
        } else {
            terminal(g)
        };
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
    let tail = |g: &mut R6Rng| {
        if g.below(4) == 0 {
            terminal(g)
        } else {
            R6Tail::Node(g.below(np as u64) as usize)
        }
    };
    let mut taken = vec![(head(g), tail(g))];
    if g.below(2) == 0 {
        // A second taken row: on the carrier (inside the class), or another chain (outside).
        let t = if carrier.is_some() && g.below(4) != 0 {
            R6Tail::Car
        } else {
            tail(g)
        };
        // With the carrier's own head this is a top carrier row, which bounds every item.
        let top = alt_rows && t == R6Tail::Car && g.below(2) == 0;
        taken.push((if top { carrier.unwrap() } else { head(g) }, t));
    }
    let refused = (0..1 + g.below(nr_max))
        .map(|_| (head(g), tail(g)))
        .collect();
    R6Input {
        carrier,
        pool,
        taken,
        refused,
    }
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
        defs.push(def(
            &format!("L{tag}"),
            Expr::Union(vec![nil(), cons(Expr::Type(h.ty()), r(0))]),
        ));
    }
    for (i, &(stop, h, next, alt)) in x.pool.iter().enumerate() {
        let mut alts = vec![cons(Expr::Type(h.ty()), tail(next))];
        if let Some(a) = alt {
            alts.push(cons(Expr::Type(a.ty()), r(0)));
        }
        if stop {
            alts.insert(0, nil());
        }
        let body = if alts.len() == 1 {
            alts.pop().unwrap()
        } else {
            Expr::Union(alts)
        };
        defs.push(def(&format!("V{i}{tag}"), body));
    }
    for (i, &(h, t)) in x.taken.iter().chain(&x.refused).enumerate() {
        defs.push(def(
            &format!("R{i}{tag}"),
            cons(Expr::Type(h.ty()), tail(t)),
        ));
    }
    let ts = u4_inst(defs);
    let rows = &ts[base + x.pool.len()..];
    let p = rows[1..x.taken.len()]
        .iter()
        .fold(rows[0].clone(), |u, t| &u & t);
    let n = rows[x.taken.len()..]
        .iter()
        .fold(Type::empty(), |u, t| &u | t);
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
            if next[..nt].iter().all(|p| !p.is_empty())
                && go(x, rows, nt, &next, len + 1, max_len, accepts)
            {
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
            let wrong = |y: &Verdict| {
                matches!(
                    (y, truth),
                    (Verdict::Empty, true) | (Verdict::Inhabited, false)
                )
            };
            assert!(!wrong(&v), "verdict {v:?} truth {truth} on {x:?}");
            assert!(
                !ch.as_ref().is_some_and(wrong),
                "chains {ch:?} truth {truth} on {x:?}"
            );
            *counts
                .entry(format!("truth {truth} {v:?} chains {ch:?}"))
                .or_insert(0usize) += 1;
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
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for e in 1..=n {
        let h = &Type::int() - &lit((e % 2) as i64);
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if j == 1 {
            &lit(0) | &lit(7)
        } else {
            &lit((j % 2) as i64) | &lit(7)
        };
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
    let mut ds = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    ds.push(def(
        &format!("B1{tag}"),
        cons(Expr::Type(&Type::int() - &lit(1)), r(0)),
    ));
    ds.push(def(
        &format!("B2{tag}"),
        cons(Expr::Type(&Type::int() - &lit(0)), r(1)),
    ));
    let base = if three {
        ds.push(def(
            &format!("B3{tag}"),
            cons(Expr::Type(&Type::int() - &lit(0)), r(2)),
        ));
        3
    } else {
        2
    };
    for i in 1..n {
        ds.push(def(&format!("A{i}{tag}"), cons(int(), r(base + i - 1))));
    }
    let mut p = r(0);
    for _ in 0..n + base {
        p = cons(Expr::Type(&lit(0) | &lit(1)), p);
    }
    ds.push(def(&format!("P{tag}"), p));
    let ts = r3_instance(ds);
    let u = (base..base + n).fold(Type::empty(), |u, i| &u | &ts[i]);
    &ts[base + n] - &u
}

#[test]
fn r6_remout_short_witness_and_negative_controls() {
    big(|| {
        let word = |x| {
            [x, 1, 1].iter().rev().fold(Value::atom("nil"), |tail, &v| {
                Value::atom_with("cons", vec![Value::Int(v), tail])
            })
        };
        for n in [3, 16, 64, 256, 1024] {
            let t = r5_remainder_boundary(n, true, &format!("_r6remwit{n}"));
            assert!(t.contains(&word(5)), "short witness at {n}");
            assert!(
                !t.contains(&word(1)),
                "F1 captures the first negative control"
            );
            assert!(
                !t.contains(&word(4)),
                "F3 captures the second negative control"
            );
        }
    });
}

/// A period-three boundary for the height-congruence filter. All roots have heights
/// congruent to 2 modulo 3. Its first-place {2} atom survives; later places never separate.
/// Adding one root in a different residue makes the gcd 1 and invalidates that skip proof.
fn r7_congruence(n: usize, outside: bool, tag: &str) -> Type {
    let n = n.max(4);
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for e in 1..=n {
        let h = &Type::int() - &lit((e % 3) as i64);
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if j == 1 {
            &lit(2) | &lit(7)
        } else {
            &lit(((4 - j % 3) % 3) as i64) | &lit(7)
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let mut u = (2..=n).step_by(3).fold(Type::empty(), |u, d| &u | &ts[d]);
    if outside {
        u = &u | &ts[3];
    }
    &ts[n + 1] - &u
}

/// The escape reads no more empty cells on the parity family at 256 than at 16: the pair listing
/// never reads an empty cell, and method A counts each empty pair of a place class and a node
/// class once, a number fixed by the family (2 here), not by `n`.
#[test]
fn r7_height_congruence_skips_only_empty_cells() {
    big(|| {
        let mut first = None;
        for n in [16, 64, 256] {
            let t = r6_parity(n, &format!("_r7p{n}"));
            let e = t.escape_cell_counts().1;
            assert_eq!(*first.get_or_insert(e), e, "parity at {n}: {e} empty");
            assert_eq!(t.chain_verdict(), Some(Verdict::Inhabited));
            for outside in [false, true] {
                let t = r7_congruence(n, outside, &format!("_r7g{n}_{outside}"));
                let word = |first| {
                    (1..=n).rev().fold(Value::atom("nil"), |tail, j| {
                        let h = if j == 1 {
                            first
                        } else {
                            ((4 - j % 3) % 3) as i64
                        };
                        Value::atom_with("cons", vec![Value::Int(h), tail])
                    })
                };
                assert!(t.contains(&word(2)));
                assert!(!t.contains(&word(7)), "F2 must reject the bad witness");
                Type::forget_emptiness();
                assert_eq!(t.chain_verdict(), Some(Verdict::Inhabited));
                Type::forget_emptiness();
                assert_eq!(t.verdict(), Verdict::Inhabited);
            }
        }
    });
}

#[test]
fn r7_congruence_scales() {
    cases_scale_from(
        &[
            ("r6parity", Verdict::Inhabited),
            ("r7congruencein", Verdict::Inhabited),
            ("r7congruenceout", Verdict::Inhabited),
            ("r7bmmout", Verdict::Inhabited),
        ],
        128,
    );
}

#[test]
fn r7_peer_escape_families_scale() {
    cases_scale_from(
        &[
            ("r6repeat3", Verdict::Inhabited),
            ("r6distinct2", Verdict::Inhabited),
            ("r6distinct3", Verdict::Inhabited),
        ],
        128,
    );
}

/// Two sound Empty inputs at the guards' boundary. The first has a partial jump remainder
/// but an independent unconditional cover; the second has an optional spine choice followed
/// by contradictory positive heads. Their negative controls have the displayed finite words.
#[test]
fn r7_guard_admissions_are_sound() {
    big(|| {
        let chain = |heads: &[Type]| {
            heads
                .iter()
                .rev()
                .fold(r(0), |tail, h| cons(Expr::Type(h.clone()), tail))
        };
        let ts = u4_inst(vec![
            def("R7GuardCoverL", Expr::Union(vec![nil(), cons(int(), r(0))])),
            def(
                "R7GuardCoverP",
                chain(&[Type::int(), Type::int(), Type::int(), lit(1)]),
            ),
            def("R7GuardCoverA", chain(&[Type::int(), lit(3), lit(2)])),
            def(
                "R7GuardCoverN",
                chain(&[Type::int(), Type::int(), Type::int(), Type::int()]),
            ),
        ]);
        let t = &ts[1] - &(&ts[2] | &ts[3]);
        Type::forget_emptiness();
        let direct = t.chain_verdict();
        Type::forget_emptiness();
        let ordinary = t.verdict();
        eprintln!("r7 guard remainder cover direct {direct:?} full {ordinary:?}");
        assert_ne!(direct, Some(Verdict::Inhabited));
        assert_eq!(ordinary, Verdict::Empty); // P is a subset of N coordinate by coordinate.
        let control = &ts[1] - &ts[2];
        assert!(control.contains(&r6_colour_list(&[0, 0, 0, 1])));
        Type::forget_emptiness();
        assert_eq!(control.verdict(), Verdict::Inhabited);

        let ts = u4_inst(vec![
            def(
                "R7GuardOptionalL",
                Expr::Union(vec![nil(), cons(int(), r(0))]),
            ),
            def(
                "R7GuardOptionalP",
                chain(&[Type::int(), Type::int(), Type::int(), Type::int(), lit(1)]),
            ),
            def(
                "R7GuardOptionalQ",
                chain(&[Type::int(), Type::int(), Type::int(), Type::int(), lit(2)]),
            ),
            def("R7GuardOptionalF1", cons(Expr::Type(lit(1)), r(0))),
            def(
                "R7GuardOptionalF2",
                cons(Expr::Type(&Type::int() - &lit(2)), r(3)),
            ),
        ]);
        let t = &(&ts[1] & &ts[2]) - &ts[4];
        Type::forget_emptiness();
        let direct = t.chain_verdict();
        Type::forget_emptiness();
        let ordinary = t.verdict();
        eprintln!("r7 guard optional contradiction direct {direct:?} full {ordinary:?}");
        assert_ne!(direct, Some(Verdict::Inhabited));
        assert_eq!(ordinary, Verdict::Empty); // The fifth item cannot be both 1 and 2.
        let control = &ts[1] - &ts[4];
        assert!(control.contains(&r6_colour_list(&[0, 0, 0, 0, 1])));
        Type::forget_emptiness();
        assert_eq!(control.verdict(), Verdict::Inhabited);
    });
}

#[test]
fn r7_named_payload_is_not_a_list_pair() {
    big(|| {
        let l = list_named(Type::int(), "_r7struct");
        let n = cons_of(Type::int(), l.clone());
        let p = cons_of(Type::int(), n.clone());
        let named = Type::atom_with("cons", &Type::universe(zed_kernel::types::Universe::Struct));
        let t = &(&p | &named) - &n;
        let v = Value::atom_named("cons", vec![("field".into(), Value::Int(0))]).unwrap();
        assert!(t.contains(&v));
        Type::forget_emptiness();
        let direct = t.chain_verdict();
        Type::forget_emptiness();
        let ordinary = t.verdict();
        Type::forget_emptiness();
        let empty = t.is_empty();
        eprintln!("r7 named payload direct {direct:?} full {ordinary:?} is_empty {empty}");
        assert_ne!(direct, Some(Verdict::Empty));
        assert_eq!(ordinary, Verdict::Refused(Refusal::NoWitness));
        assert!(!empty);
    });
}

fn r7_reader_member(t: Type, v: Value, label: &str, expected: Verdict) {
    assert!(t.contains(&v), "the concrete member: {label}");
    Type::forget_emptiness();
    let direct = t.chain_verdict();
    Type::forget_emptiness();
    let ordinary = t.verdict();
    Type::forget_emptiness();
    let empty = t.is_empty();
    eprintln!("r7 reader {label} direct {direct:?} full {ordinary:?} is_empty {empty}");
    assert_ne!(direct, Some(Verdict::Empty), "{label}");
    assert_eq!(ordinary, expected, "{label}");
    assert!(!empty, "{label}");
}

#[test]
fn r7_named_payload_below_top_is_not_a_list_step() {
    big(|| {
        let l = list_named(Type::int(), "_r7structtail");
        let one = cons_of(Type::int(), l);
        let named = Type::atom_with("cons", &Type::universe(zed_kernel::types::Universe::Struct));
        let p = cons_of(Type::int(), &one | &named);
        let n = cons_of(Type::int(), one);
        let tail = Value::atom_named("cons", vec![("field".into(), Value::Int(0))]).unwrap();
        r7_reader_member(
            &p - &n,
            Value::atom_with("cons", vec![Value::Int(0), tail]),
            "named tail",
            Verdict::Refused(Refusal::NoWitness),
        );
    });
}

#[test]
fn r7_two_stop_names_are_not_one_stop() {
    big(|| {
        let l = list_named(Type::int(), "_r7stops");
        let p = cons_of(Type::int(), &l | &Type::atom("aaa_stop"));
        let n = cons_of(Type::int(), l);
        r7_reader_member(
            &p - &n,
            Value::atom_with("cons", vec![Value::Int(0), Value::atom("aaa_stop")]),
            "two stops",
            Verdict::Inhabited,
        );
    });
}

#[test]
fn r7_two_link_names_are_not_one_link() {
    big(|| {
        let l = list_named(Type::int(), "_r7links");
        let extra = Type::atom_with("aaa_link", &Type::tuple(vec![Type::int(), l.clone()]));
        let p = cons_of(Type::int(), &l | &extra);
        let n = cons_of(Type::int(), l);
        let tail = Value::atom_with("aaa_link", vec![Value::Int(0), Value::atom("nil")]);
        r7_reader_member(
            &p - &n,
            Value::atom_with("cons", vec![Value::Int(0), tail]),
            "two links",
            Verdict::Inhabited,
        );
    });
}

#[test]
fn r7_cycle_meet_does_not_drop_another_link_name() {
    big(|| {
        let l = list_named(Type::int(), "_r7rootlinks");
        let even = period_named(2, 0, "_r7rooteven");
        let p = cons_of(Type::int(), even);
        let n = cons_of(Type::int(), l.clone());
        let extra = Type::atom_with("aaa_link", &Type::tuple(vec![Type::int(), l]));
        r7_reader_member(
            &(&p | &extra) - &n,
            Value::atom_with("aaa_link", vec![Value::Int(0), Value::atom("nil")]),
            "cycle root names",
            Verdict::Inhabited,
        );
    });
}

/// R7 Q3 boundary (just inside `K <= 2`): Thue-Morse aperiodic comb over two bi-repeated channels
/// `{0, 1}`. `F_e = cons(int \ {tm(e)}, F_{e-1})` for `e = 1..=q` (`q = n / 3`) and `cons(int, F_{e-1})`
/// above `q`; `P` of length `n` has `{tm(j), 7}` on `j = 1..=q`, `{0, 7}` on `j = 2q + 1..=2q + 3`,
/// and `{7}` elsewhere; roots are `F_d` for `d = 2q + 3..=n`. Because no three consecutive integers
/// share `popcount` parity, every root has 1 or 2 separating cells (never 4, so never retired as
/// `wide`), `x_{2q+1..=2q+3} = 0` escapes all roots (`Inhabited`), a naive or fixed-period scan
/// visits `Theta(n^2)` empty `(root, place)` pairs, and the `K <= 2` NTT + Cauchy-Schwarz escape
/// solver reads 0 empty cells in `O(n log n)`.
fn r7_aperiodic(n: usize, tag: &str) -> Type {
    let n = n.max(12);
    let q = n / 3;
    let tm = |m: usize| (m.count_ones() % 2) as i64;
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for e in 1..=n {
        let h = if e <= q {
            &Type::int() - &lit(tm(e))
        } else {
            Type::int()
        };
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if j <= q {
            &lit(tm(j)) | &lit(7)
        } else if (2 * q + 1..=2 * q + 3).contains(&j) {
            &lit(0) | &lit(7)
        } else {
            lit(7)
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let u = (2 * q + 3..=n).fold(Type::empty(), |u, d| &u | &ts[d]);
    &ts[n + 1] - &u
}

/// R7 Q3 boundary (just outside `K <= 2`, at `K = 3`): mod-3 comb over three bi-repeated channels
/// `{0, 1, 2}` (`F_e = cons(int \ {e mod 3}, F_{e-1})`, `P` with `{0, 7}` at place 1 and
/// `{(2j) mod 3, 7}` at `j >= 2`, roots `F_{3m}`). Recognized in `O(n log n)` as `K = 3 > 2` and
/// declined by `escape::decide` to the general search without any empty-cell reads.
fn r7_bmm_out(n: usize, tag: &str) -> Type {
    let n = n.max(6);
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for e in 1..=n {
        let h = &Type::int() - &lit((e % 3) as i64);
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if j == 1 {
            &lit(0) | &lit(7)
        } else {
            &lit(((2 * j) % 3) as i64) | &lit(7)
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let u = (3..=n).step_by(3).fold(Type::empty(), |u, d| &u | &ts[d]);
    &ts[n + 1] - &u
}

/// `r7aperiodic` is not inhabited at every size. A root `F_d` (d from 2q+3 to n) is escaped only
/// by a 0 at a place i in 2q+1..=2q+3 with d-q+1 <= i <= d, where `F_d` excludes tm(d-i+1); so
/// the set is inhabited exactly when each such root has one of those places with tm(d-i+1) = 0.
/// At n 127 and 128 the root F_n has only places whose tm is 1, and the set is empty.
#[test]
fn r7_aperiodic_matches_its_closed_form() {
    big(|| {
        let tm = |m: usize| m.count_ones() % 2;
        let mut empties = 0;
        for n in 12..=160 {
            let q = n / 3;
            let inhabited = (2 * q + 3..=n).all(|d| {
                (2 * q + 1..=2 * q + 3).any(|i| i + q > d && i <= d && tm(d - i + 1) == 0)
            });
            let want = if inhabited {
                Verdict::Inhabited
            } else {
                Verdict::Empty
            };
            empties += usize::from(!inhabited);
            Type::forget_emptiness();
            let t = rfx_case("r7aperiodic", n, &format!("_r7ac{n}"));
            assert_eq!(t.verdict(), want, "r7aperiodic at {n}");
        }
        assert!(empties > 0, "the closed form must include empty sizes");
    });
}

/// X38: the suffix-height filter and the reachable-place lower bound must avoid
/// impossible alignments. The committed global-gcd enumerator fails these bounds.
#[test]
fn r8_escape_alignment_reads_scale_with_the_input() {
    big(|| {
        for name in ["r6parity", "r7congruenceout", "r7aperiodic", "r7bmmout"] {
            for n in [128, 1024] {
                Type::forget_emptiness();
                let t = rfx_case(name, n, &format!("_r8reads{name}{n}"));
                let counts = t.escape_cell_counts();
                eprintln!("r8 reads {name} {n} {counts:?}");
                assert!(counts.1 <= 4 * n, "{name} {n}: {counts:?}");
            }
        }
    });
}

#[test]
fn r8_escape_and_width_instruction_scaling() {
    cases_scale_from(
        &[
            ("r7congruenceout", Verdict::Inhabited),
            ("r7aperiodic", Verdict::Inhabited),
        ],
        32,
    );
    big(|| {
        // n counts the quadratic head representation. Width floor(sqrt(n))
        // gives inputs of about n and 8n, with all construction outside timing.
        let inputs = scaling::inputs(256, |n| {
            rfx_case(
                "r5varywidth",
                (n as f64).sqrt() as usize,
                &format!("_r8width{n}"),
            )
        });
        scaling::check("r5varywidth by head representation size", 256, |n| {
            Type::forget_emptiness();
            assert_eq!(inputs[&n].verdict(), Verdict::Inhabited);
        });
    });
}

/// X39: initialize the emptiness tables before the first type, and leave a deep
/// type in them until thread exit. No recursive group or escape solver is needed.
#[test]
fn r8_deep_type_cached_before_queue_initialization_drops_on_small_stack() {
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| {
            Type::forget_emptiness();
            let mut t = Type::int();
            for _ in 0..12000 {
                t = Type::tuple(vec![t]);
            }
            assert_eq!(t.verdict(), Verdict::Inhabited);
            let body = (0..12000).fold(int(), |tail, _| Expr::Tuple(vec![tail]));
            let group = Group::new(vec![def("R8DeepCachedGroup", body)]).unwrap();
            let member = group.instance(vec![]).remove(0);
            assert_eq!(member.verdict(), Verdict::Inhabited);
            eprintln!("r8 deep cached verdict complete");
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Preserve cb709f13 answers when list queries are nested in products and atom payloads.
/// The baseline refused the empty chain inside an atom payload, which this test recorded; since
/// R9 (X42) the payload gets the list's verdict there too.
#[test]
fn r8_roots_only_preserves_nested_list_answers() {
    big(|| {
        for name in [
            "chain",
            "chainfar",
            "r6parity",
            "r7congruenceout",
            "r7aperiodic",
        ] {
            for n in [16, 64, 128] {
                Type::forget_emptiness();
                let t = rfx_case(name, n, &format!("_r8nest{name}{n}"));
                let direct = t.verdict();
                let tuple = Type::tuple(vec![Type::int(), t.clone()]);
                let atom = Type::atom_with("r8box", &Type::tuple(vec![t.clone()]));
                Type::forget_emptiness();
                let tv = tuple.verdict();
                Type::forget_emptiness();
                let av = atom.verdict();
                eprintln!("r8nested {name} {n} direct {direct:?} tuple {tv:?} atom {av:?}");
                assert_eq!(tv, direct, "tuple {name} {n}");
                assert_eq!(av, direct, "payload {name} {n}: the list's verdict");
            }
        }
    });
}

/// X38 boundary: move the outlier from the shallow end to the tallest height.
fn r8_height_boundary(n: usize, outside: bool, tag: &str) -> Type {
    let n = n.max(4);
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for e in 1..=n {
        let h = &Type::int() - &lit((e % 3) as i64);
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if j == 1 {
            &lit(2) | &lit(7)
        } else {
            &lit(((4 - j % 3) % 3) as i64) | &lit(7)
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let mut u = (2..=n).step_by(3).fold(Type::empty(), |u, d| &u | &ts[d]);
    if outside {
        u = &u | &ts[3 * (n / 3)];
    }
    &ts[n + 1] - &u
}

#[test]
fn r8_height_boundary_keeps_the_checked_witness() {
    big(|| {
        for n in [16, 64, 256] {
            for outside in [false, true] {
                Type::forget_emptiness();
                let t = r8_height_boundary(n, outside, &format!("_r8hb{n}{outside}"));
                let good = (1..=n).rev().fold(Value::atom("nil"), |tail, j| {
                    let h = if j == 1 { 2 } else { ((4 - j % 3) % 3) as i64 };
                    Value::atom_with("cons", vec![Value::Int(h), tail])
                });
                let bad = (1..=n).rev().fold(Value::atom("nil"), |tail, _| {
                    Value::atom_with("cons", vec![Value::Int(7), tail])
                });
                assert!(t.contains(&good));
                assert!(!t.contains(&bad));
                Type::forget_emptiness();
                assert_eq!(t.verdict(), Verdict::Inhabited);
            }
        }
    });
}

/// Round 8 boundary of the escape's skips. `F_e = cons(int \ {0}, F_(e-1))` for `e` 0 or 1
/// modulo 4, `cons(int \ {2}, ..)` for 2, `cons(int, ..)` for 3; `P` with `{0, 2, 7}` first and
/// `{0, 7}` at places 0 and 1 modulo 4, `{7}` elsewhere; roots `F_d` for `d` 2 modulo 4. No place
/// after the first separates for a root: the cells land at `j + h` 3 modulo 4. Inside, the
/// root heights are one residue modulo 4 and the root-height skip reads no empty cell. `outside`
/// adds the root `F_5` (escaped at place 5 by 0): the root-height gcd is 1, and the places of 0
/// (residues 0 and 1 of 4) have difference gcd 1, so neither skip applies. Inhabited both ways.
fn r8_residues(n: usize, outside: bool, tag: &str) -> Type {
    let n = n.max(8);
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for e in 1..=n {
        let h = match e % 4 {
            0 | 1 => &Type::int() - &lit(0),
            2 => &Type::int() - &lit(2),
            _ => Type::int(),
        };
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if j == 1 {
            &(&lit(0) | &lit(2)) | &lit(7)
        } else if j % 4 <= 1 {
            &lit(0) | &lit(7)
        } else {
            lit(7)
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let mut u = (2..=n).step_by(4).fold(Type::empty(), |u, d| &u | &ts[d]);
    if outside {
        u = &u | &ts[5];
    }
    &ts[n + 1] - &u
}

/// Round 8 (X38): the escape's empty-cell reads stay linear on the stray-root congruence and
/// the aperiodic families, where the root-height skip does not apply, and on the two round-8
/// boundaries. On 91182428 the first two were 608 and 210 at `n` 64 and quadratic above it;
/// with the per-value residue filter alone, `r8residuesout` was 65,535 at 1024 (the suffix gcd
/// of the root heights lowers it to `n / 2`), and with both filters `r8heightout` was 174,249 at
/// 1024 (counting only the rows of a value's class not yet retired lowers it to 0).
/// `r8residues` is the inside of the boundary: as many empty reads at 512 as at 64 (method A
/// counts each empty pair of a place class and a node class once; the pair listing reads none).
#[test]
fn r8_escape_empty_reads_are_linear() {
    big(|| {
        let mut first = None;
        for n in [64, 512] {
            for case in [
                "r7congruenceout",
                "r7aperiodic",
                "r8heightout",
                "r8residuesout",
            ] {
                let t = rfx_case(case, n, &format!("_r8e_{case}_{n}"));
                let (reads, empty) = t.escape_cell_counts();
                assert!(empty <= n, "{case} at {n}: {empty} empty of {reads} reads");
                assert_eq!(t.verdict(), Verdict::Inhabited, "{case} at {n}");
            }
            let t = rfx_case("r8residues", n, &format!("_r8e_in_{n}"));
            let e = t.escape_cell_counts().1;
            assert_eq!(*first.get_or_insert(e), e, "r8residues at {n}: {e} empty");
            assert_eq!(t.verdict(), Verdict::Inhabited);
        }
    });
}

#[test]
fn r8_residue_boundary_scales() {
    cases_scale_from(
        &[
            ("r7aperiodic", Verdict::Inhabited),
            ("r8residues", Verdict::Inhabited),
            ("r8residuesout", Verdict::Inhabited),
        ],
        // 64 and 512: `r7aperiodic` is Empty at 128 (its closed form).
        64,
    );
}

/// A list type in a tuple or record field gets the verdict of the list alone, at near the list's
/// work (R8, Q5). The prefix chains and the escape solve ran on the query's own types only, so a
/// list in a field was left to the search, which refused `chain`, `r5remin` and `r6twoun` there,
/// at 12 to 530 times the work of the list alone.
#[test]
fn r8_a_list_in_a_field_is_decided_as_the_list_alone() {
    big(|| {
        let n = 64;
        let tag = format!("_r8field{n}");
        for case in ["chain", "r5remin", "r6twoun"] {
            for wrap in ["tup:", "rec:"] {
                Type::forget_emptiness();
                let bare = rfx_case(case, n, &tag);
                let mut v = None;
                let b = scaling::Meter::new().work(|| v = Some(bare.verdict()));
                Type::forget_emptiness();
                let t = rfx_case(&format!("{wrap}{case}"), n, &tag);
                let mut w = None;
                let f = scaling::Meter::new().work(|| w = Some(t.verdict()));
                assert_eq!(
                    w, v,
                    "{wrap}{case} at {n}: the field's verdict is the list's"
                );
                assert!(
                    f.units <= 2 * b.units,
                    "{wrap}{case} at {n}: {} units in a field, {} alone",
                    f.units,
                    b.units
                );
            }
        }
    });
}

/// A list of the front sweep's class in a tuple or record field gets the verdict of the list
/// alone at near the list's work (R9, X41). The front sweep ran on the query type alone, so the
/// search built the field's value itself: `rec:clstaggerholesout` cost 547 times the list alone
/// at 256, `tup:u4cofrontshared` 360 times, `tup:boundaryinside` 129 times. Sizes n and 8n, so a
/// cost that grows faster in a field than alone fails at the larger one.
#[test]
fn r9_a_front_sweep_list_in_a_field_is_decided_as_the_list_alone() {
    big(|| {
        for n in [16, 128] {
            let tag = format!("_r9field{n}");
            for case in [
                "clstaggerholesout",
                "u4holesout",
                "u4cofrontshared",
                "boundaryinside",
                "clcofrontsame",
            ] {
                for wrap in ["tup:", "rec:"] {
                    Type::forget_emptiness();
                    let bare = rfx_case(case, n, &tag);
                    let mut v = None;
                    let b = scaling::Meter::new().work(|| v = Some(bare.verdict()));
                    Type::forget_emptiness();
                    let t = rfx_case(&format!("{wrap}{case}"), n, &tag);
                    let mut w = None;
                    let f = scaling::Meter::new().work(|| w = Some(t.verdict()));
                    assert_eq!(
                        w, v,
                        "{wrap}{case} at {n}: the field's verdict is the list's"
                    );
                    assert!(
                        f.units <= 2 * b.units,
                        "{wrap}{case} at {n}: {} units in a field, {} alone",
                        f.units,
                        b.units
                    );
                }
            }
        }
    });
}

/// A list in a tagged atom's payload, `#wrap((l,))`, alone or in a tuple or record field, gets
/// the verdict of the list alone at near the list's work (R9, X42). The atom was taken for a
/// list outside the prefix chains, so the list in its payload was left to the general search:
/// `#wrap((l,))` with `l` of `r5remout` at 32 was Refused(Fork) at 34 times the list's work.
#[test]
fn r9_a_list_in_an_atom_payload_is_decided_as_the_list_alone() {
    big(|| {
        for n in [16, 128] {
            let tag = format!("_r9atom{n}");
            for case in [
                "r5remout",
                "chain",
                "r6twoun",
                "clstagger",
                "clstaggerholesout",
            ] {
                for wrap in ["atom:", "tup:atom:", "rec:atom:", "atom:tup:"] {
                    Type::forget_emptiness();
                    let bare = rfx_case(case, n, &tag);
                    let mut v = None;
                    let b = scaling::Meter::new().work(|| v = Some(bare.verdict()));
                    Type::forget_emptiness();
                    let t = rfx_case(&format!("{wrap}{case}"), n, &tag);
                    let mut w = None;
                    let f = scaling::Meter::new().work(|| w = Some(t.verdict()));
                    assert_eq!(
                        w, v,
                        "{wrap}{case} at {n}: the payload's verdict is the list's"
                    );
                    assert!(
                        f.units <= 2 * b.units,
                        "{wrap}{case} at {n}: {} units in a payload, {} alone",
                        f.units,
                        b.units
                    );
                }
            }
        }
    });
}

/// R8 Q2 boundary between Stage A (multi-residue congruence skip, `R_P <= ceil(log2(V + 2))`)
/// and Stage B (HLD + Abrahamson sparse/CRT-NTT moment cell finder, `R_P > ceil(log2(V + 2))`):
/// - `outside == false` (`r8stagein`): period `p = ilog2(n + 3)` positive tail with roots across
///   all `p` residue classes (`gcd = 1`, `R_P = p <= ceil(log2(V + 2))`), where `n / p` roots have
///   zero separating cells in `j >= 2` and escape at place 1 (`x_1 = 0`).
/// - `outside == true` (`r8stageout`): `K = 3` aperiodic Thue-Morse-mod-3 comb (`c(odd) = 1`,
///   `c(2k) = 2 * (popcount(k) mod 2)`) with `P_pl = Theta(n)` and `R_P = Theta(n)`, crossing out
///   of Stage A into Stage B. Every high root `d in 2q+3..=3q` (`q = n / 4`) has 2 atoms (even
///   `d - 2q`) or 1 atom (odd `d - 2q`) in `2q+1..=2q+3`, and one low root at `q` escapes at
///   place 1 with 0 cells in `2..=q`, so `t` is `Inhabited` at every `n >= 16` with 0 empty reads.
fn r8_stage_boundary(n: usize, outside: bool, tag: &str) -> Type {
    let n = n.max(16);
    if !outside {
        let p_mod = (n + 3).ilog2() as usize;
        let sentinel = (7 + p_mod) as i64;
        let mut defs = vec![def(
            &format!("L{tag}"),
            Expr::Union(vec![nil(), cons(int(), r(0))]),
        )];
        for e in 1..=n {
            let h = &Type::int() - &lit((e % p_mod) as i64);
            defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
        }
        for d in 1..=n {
            let h0 = &Type::int() - &lit(0);
            defs.push(def(&format!("G{d}{tag}"), cons(Expr::Type(h0), r(d - 1))));
        }
        let mut p = nil();
        for j in (1..=n).rev() {
            let h = if j == 1 {
                &lit(0) | &lit(sentinel)
            } else {
                &lit(((2 * p_mod + 2 - j % p_mod) % p_mod) as i64) | &lit(sentinel)
            };
            p = cons(Expr::Type(h), p);
        }
        defs.push(def(&format!("P{tag}"), p));
        let ts = u4_inst(defs);
        let u = (1..=n).fold(Type::empty(), |u, d| &u | &ts[n + d]);
        return &ts[2 * n + 1] - &u;
    }
    let q = n / 4;
    let c = |m: usize| -> i64 {
        if m % 2 == 1 {
            1
        } else {
            2 * ((m / 2).count_ones() % 2) as i64
        }
    };
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for e in 1..=n {
        let h = if e <= q {
            &Type::int() - &lit(c(e))
        } else {
            Type::int()
        };
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    defs.push(def(
        &format!("Glow{tag}"),
        cons(Expr::Type(&Type::int() - &lit(0)), r(q - 1)),
    ));
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if j == 1 {
            &lit(0) | &lit(7)
        } else if j <= q {
            &lit((c(q + 1 - j) + 1) % 3) | &lit(7)
        } else if j == 2 * q + 1 {
            &(&lit(0) | &lit(2)) | &lit(7)
        } else if j == 2 * q + 2 || j == 2 * q + 3 {
            &lit(1) | &lit(7)
        } else {
            lit(7)
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let u = (2 * q + 3..=3 * q).fold(ts[n + 1].clone(), |u, d| &u | &ts[d]);
    &ts[n + 2] - &u
}

/// Gemini R8: the closed-form witness of `r8stagein` and `r8stageout` and two negative controls
/// each, checked by `contains`, and the verdict, at every n from 16 to 64. These cases make the
/// committed escape read Θ(n²) empty cells (X38, open); the verdict and the work stay linear.
#[test]
fn r8_stage_boundary_keeps_the_checked_witness() {
    big(|| {
        for n in 16usize..=64 {
            let p_mod = (n + 3).ilog2() as usize;
            let sentinel = (7 + p_mod) as i64;
            let tin = r8_stage_boundary(n, false, &format!("_r8in_{n}"));
            let win_in = (1..=n).rev().fold(Value::atom("nil"), |tail, j| {
                let v = if j == 1 {
                    0
                } else {
                    ((2 * p_mod + 2 - j % p_mod) % p_mod) as i64
                };
                Value::atom_with("cons", vec![Value::Int(v), tail])
            });
            let bad_in = (1..=n).rev().fold(Value::atom("nil"), |tail, j| {
                let v = if j == 1 {
                    sentinel
                } else {
                    ((2 * p_mod + 2 - j % p_mod) % p_mod) as i64
                };
                Value::atom_with("cons", vec![Value::Int(v), tail])
            });
            assert!(tin.contains(&win_in), "r8stagein witness at {n}");
            assert!(!tin.contains(&bad_in), "r8stagein negative control at {n}");

            let q = n / 4;
            let c = |m: usize| -> i64 {
                if m % 2 == 1 {
                    1
                } else {
                    2 * ((m / 2).count_ones() % 2) as i64
                }
            };
            let tout = r8_stage_boundary(n, true, &format!("_r8out_{n}"));
            let make_out = |x1: i64, x_even: i64| {
                (1..=n).rev().fold(Value::atom("nil"), |tail, j| {
                    let v = if j == 1 {
                        x1
                    } else if j <= q {
                        (c(q + 1 - j) + 1) % 3
                    } else if j == 2 * q + 1 {
                        0
                    } else if j == 2 * q + 2 || j == 2 * q + 3 {
                        x_even
                    } else {
                        7
                    };
                    Value::atom_with("cons", vec![Value::Int(v), tail])
                })
            };
            assert!(tout.contains(&make_out(0, 1)), "r8stageout witness at {n}");
            assert!(
                !tout.contains(&make_out(7, 1)),
                "r8stageout low negative control at {n}"
            );
            assert!(
                !tout.contains(&make_out(0, 7)),
                "r8stageout high negative control at {n}"
            );
            Type::forget_emptiness();
            assert_eq!(tout.verdict(), Verdict::Inhabited, "r8stageout at {n}");
        }
    });
}

#[test]
fn r8_stage_boundary_scale() {
    cases_scale_from(
        &[
            ("r8stagein", Verdict::Inhabited),
            ("r8stageout", Verdict::Inhabited),
        ],
        128,
    );
}

#[test]
fn r8_varywidth_scales_within_input_size() {
    // Watch item `r5varywidth`: input has Theta(w^2) nodes (`w` boolean columns x `w` clauses),
    // so `w` to `4w` increases input size `N = w^2` by `16x` (`O(N log N)` bound <= `16 * 3 = 48x`).
    big(|| {
        Type::forget_emptiness();
        let small = r5_varying_width(16);
        let large = r5_varying_width(64);
        let mut m = scaling::Meter::new();
        let mut v1 = None;
        let mut v2 = None;
        let w1 = m.work(|| {
            Type::forget_emptiness();
            v1 = Some(small.verdict());
        });
        let w2 = m.work(|| {
            Type::forget_emptiness();
            v2 = Some(large.verdict());
        });
        assert_eq!(v1, Some(Verdict::Inhabited));
        assert_eq!(v2, Some(Verdict::Inhabited));
        assert!(
            w2.units <= w1.units.saturating_mul(48),
            "r5varywidth w=16 ({}) to w=64 ({}) exceeded O(w^2 log w) bound",
            w1.units,
            w2.units
        );
    });
}

#[test]
fn r8_x39_deep_type_drop_does_not_overflow_stack() {
    // Negative control on __COMMIT__ and main `f5ecad1d`: a 2 MiB thread that calls
    // `Type::forget_emptiness()` before building a deep nested `cons(int, ...)` chain (25,000
    // links = 50,000 nested `Node::Parts` / `BTreeMap<usize, Part<Row>>` levels, matching `P` in
    // `r6two` at `n = 4096`) initializes `VERDICTS` before `types::FREED`, and an external
    // thread-local initialized first outlives `types::FREED`; both overflow a 2 MiB stack
    // (`SIGSEGV`, `rc = 139`) at thread exit without `hold()` and `ENDING`.
    let run_forget_first = std::thread::Builder::new()
        .name("r8-x39-forget".into())
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            Type::forget_emptiness();
            let mut chain = Type::atom("nil");
            for _ in 0..25_000 {
                chain = cons_of(Type::int(), chain);
            }
            assert_eq!(chain.verdict(), Verdict::Inhabited);
        })
        .unwrap();
    run_forget_first.join().unwrap();

    let run_external_tls = std::thread::Builder::new()
        .name("r8-x39-ext-tls".into())
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            thread_local! {
                static EXT: std::cell::RefCell<Option<Type>> = const { std::cell::RefCell::new(None) };
            }
            EXT.with(|slot| *slot.borrow_mut() = None);
            let mut chain = Type::atom("nil");
            for _ in 0..25_000 {
                chain = cons_of(Type::int(), chain);
            }
            EXT.with(|slot| *slot.borrow_mut() = Some(chain));
        })
        .unwrap();
    run_external_tls.join().unwrap();
}

#[test]
fn r8_nested_prefix_chains_do_not_coarsen() {
    big(|| {
        let l_inhab = r5_remainder_boundary(32, true, "_r8_nest_in");
        let l_empty = r5_sat_type(2, &vec![vec![]; 16], "_r8_nest_em");
        let cases = [
            (
                "tuple_inhab",
                Type::tuple(vec![l_inhab.clone(), Type::int()]),
                Verdict::Inhabited,
                false,
            ),
            (
                "tuple_empty",
                Type::tuple(vec![l_empty.clone(), Type::int()]),
                Verdict::Empty,
                true,
            ),
            (
                "record_inhab",
                Type::exact(Type::atom("x"), l_inhab.clone()),
                Verdict::Inhabited,
                false,
            ),
            (
                "record_empty",
                Type::exact(Type::atom("x"), l_empty.clone()),
                Verdict::Empty,
                true,
            ),
            // Not asserted: `#wrap((l_inhab,))` is Refused(Fork) on this tree; Gemini R8 decides
            // it Inhabited and reports cb709f13 refused it too (X42, open).
            (
                "atom_empty",
                Type::atom_with("wrap", &Type::tuple(vec![l_empty])),
                Verdict::Empty,
                true,
            ),
        ];
        for (label, t, want_v, want_empty) in cases {
            Type::forget_emptiness();
            assert_eq!(t.verdict(), want_v, "nested verdict: {label}");
            Type::forget_emptiness();
            assert_eq!(t.is_empty(), want_empty, "nested is_empty: {label}");
        }
    });
}

#[test]
fn r8_batch_and_single_file_checking_agree() {
    big(|| {
        let make_types = |tag: &str| -> Vec<Type> {
            let l_in = r5_remainder_boundary(16, true, &format!("_r8b_in{tag}"));
            let l_em = r5_sat_type(2, &vec![vec![]; 8], &format!("_r8b_em{tag}"));
            vec![
                r8_stage_boundary(24, false, &format!("_r8b_sin{tag}")),
                r8_stage_boundary(24, true, &format!("_r8b_sout{tag}")),
                r7_congruence(24, true, &format!("_r8b_cout{tag}")),
                r7_aperiodic(127, &format!("_r8b_ap127{tag}")),
                r7_aperiodic(129, &format!("_r8b_ap129{tag}")),
                Type::tuple(vec![l_in.clone(), Type::int()]),
                Type::tuple(vec![l_em.clone(), Type::int()]),
                Type::exact(Type::atom("x"), l_in),
                Type::exact(Type::atom("x"), l_em),
            ]
        };
        let ts_batch = make_types("_batch");
        Type::forget_emptiness();
        let batch: Vec<(Verdict, bool)> = ts_batch
            .iter()
            .map(|t| {
                let empty = t.is_empty();
                (t.verdict(), empty)
            })
            .collect();
        Type::forget_emptiness();
        let mut rev: Vec<(Verdict, bool)> = ts_batch
            .iter()
            .rev()
            .map(|t| {
                let empty = t.is_empty();
                (t.verdict(), empty)
            })
            .collect();
        rev.reverse();
        let alone: Vec<(Verdict, bool)> = (0..batch.len())
            .map(|i| {
                std::thread::Builder::new()
                    .stack_size(16 * 1024 * 1024)
                    .spawn(move || {
                        let ts = make_types("_alone");
                        let v = ts[i].verdict();
                        Type::forget_emptiness();
                        let e = ts[i].is_empty();
                        (v, e)
                    })
                    .unwrap()
                    .join()
                    .unwrap()
            })
            .collect();
        assert_eq!(alone, batch, "alone vs forward batch");
        assert_eq!(alone, rev, "alone vs reversed batch");

        let units = [
            "f(x: #a .. #a | #b -> int) = 0;\nmain() = 0;\n",
            "f(x: (int, #a .. #a | #b -> int)) = 0;\nmain() = 0;\n",
            "f(x: #a | #b .. #a -> int) = 0;\nmain() = 0;\n",
            "f(x: (int -> #a | #b) .. ((int -> #a) | (int -> #b)) -> int) = 0;\nmain() = 0;\n",
        ];
        let u_alone: Vec<Option<String>> = units
            .iter()
            .map(|&s| {
                std::thread::spawn(move || zedc::run::load(s.as_bytes()).err())
                    .join()
                    .unwrap()
            })
            .collect();
        let u_batch: Vec<Option<String>> = units
            .iter()
            .map(|s| zedc::run::load(s.as_bytes()).err())
            .collect();
        let mut u_rev: Vec<Option<String>> = units
            .iter()
            .rev()
            .map(|s| zedc::run::load(s.as_bytes()).err())
            .collect();
        u_rev.reverse();
        assert_eq!(u_alone, u_batch, "zedc single-file vs forward batch");
        assert_eq!(u_alone, u_rev, "zedc single-file vs reversed batch");
        assert!(u_alone[0].is_none() && u_alone[1].is_none());
        assert!(u_alone[2].is_some() && u_alone[3].is_some());
    });
}

#[test]
fn r8_escape_laminar_boundary_declines_crossing_atoms() {
    big(|| {
        let l = list_named(Type::int(), "_r8_lam");
        let p = cons_of(
            &(&lit(0) | &lit(1)) | &lit(2),
            cons_of(lit(7), Type::atom("nil")),
        );
        let f01 = cons_of(&Type::int() - &(&lit(0) | &lit(1)), l.clone());
        let f12 = cons_of(&Type::int() - &(&lit(1) | &lit(2)), l.clone());
        let f02 = cons_of(&Type::int() - &(&lit(0) | &lit(2)), l.clone());
        let f1 = cons_of(&Type::int() - &lit(1), l);

        // Inside laminar boundary: `{1}` is nested inside `{0, 1}`.
        let laminar = &p - &(&f01 | &f1);
        Type::forget_emptiness();
        assert_eq!(laminar.chain_verdict(), Some(Verdict::Inhabited));
        assert_eq!(laminar.verdict(), Verdict::Inhabited);

        // Outside laminar boundary: `{0, 1}` and `{1, 2}` cross (`in_place_tree` declines to `None`),
        // and the base search still decides both inhabited (`[1, 7]`) and empty (`+ {0, 2}`).
        let cross_inhab = &p - &(&f01 | &f12);
        Type::forget_emptiness();
        assert_eq!(cross_inhab.chain_verdict(), None);
        assert_eq!(cross_inhab.verdict(), Verdict::Inhabited);

        let cross_empty = &p - &(&(&f01 | &f12) | &f02);
        Type::forget_emptiness();
        assert_eq!(cross_empty.chain_verdict(), None);
        assert_eq!(cross_empty.verdict(), Verdict::Empty);
    });
}

#[test]
fn r8_light_edges_and_wide_rows_agree_with_the_witness() {
    big(|| {
        // Aperiodic positive list `P` of length `l0 = 40` (`p_pl = 39`) with heavy spine `F_1..F_36`,
        // four interior light branches hanging off `F_4, F_9, F_14, F_19` (heights up to 24, giving
        // `R_P >= 12` residue classes so Stage B runs), and an optional `wide` root (`>= 5` atoms).
        let build_case = |spine6_separates: bool, include_wide: bool, tag: &str| -> Type {
            let l0 = 40usize;
            let ch_val = |j: usize| -> i64 { ((j.count_ones() as usize + j % 3) % 4) as i64 };
            let mut defs = vec![def(
                &format!("L{tag}"),
                Expr::Union(vec![nil(), cons(int(), r(0))]),
            )];
            // Heavy spine `F_1 .. F_36` (`defs` indices `1 ..= 36`, heights `1 ..= 36`).
            // `F_10 .. F_36` exclude `{0, 1, 2, 3}` (`27` cons nodes * `14` residue buckets >
            // `2 * (|cons| + l0 + |S|)`, forcing Stage B), while `F_1 .. F_9` (`e != 6`) are `int`
            // so light branch `B_9` (attached at `F_9`, tip height 12) can separate ONLY on spine
            // node `F_6` (`j = 12 - 6 + 2 = 8`) across the light edge `B_9 -> F_9`.
            for e in 1..=36usize {
                let h = if e == 6 && spine6_separates {
                    &Type::int() - &lit(5)
                } else if e >= 10 {
                    &Type::int() - &(&(&lit(0) | &lit(1)) | &(&lit(2) | &lit(3)))
                } else {
                    Type::int()
                };
                defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
            }
            // Light branches:
            // - `B_9`: 3 links (`ht = 10, 11, 12`) onto `F_9`, all heads `int` -> separates ONLY at `F_6`!
            let mut prev = 9usize;
            for k in 1..=3usize {
                let idx = defs.len();
                defs.push(def(&format!("B9_{k}{tag}"), cons(int(), r(prev))));
                prev = idx;
            }
            let b9_tip = prev; // ht = 12
            // - Three more light branches onto `F_12`, `F_15`, `F_18` of lengths 2, 3, 4 (distinct heights
            //   `14, 18, 22`, plus spine roots at `25..=34` giving 14 distinct residue classes!).
            let mut tips = vec![b9_tip];
            for (attach, len, bname) in [(12usize, 2usize, "B12"), (15, 3, "B15"), (18, 4, "B18")] {
                let mut cur = attach;
                for k in 1..=len {
                    let idx = defs.len();
                    let h = if k == len {
                        &Type::int() - &lit(5)
                    } else {
                        Type::int()
                    };
                    defs.push(def(
                        &format!("{bname}_{k}{tag}"),
                        cons(Expr::Type(h), r(cur)),
                    ));
                    cur = idx;
                }
                tips.push(cur);
            }
            // Optional wide branch onto `F_20` with 6 consecutive `int \ {5}` heads (`d >= 6` -> `Wide`).
            if include_wide {
                let mut cur = 20usize;
                for k in 1..=6usize {
                    let idx = defs.len();
                    defs.push(def(
                        &format!("BW_{k}{tag}"),
                        cons(Expr::Type(&Type::int() - &lit(5)), r(cur)),
                    ));
                    cur = idx;
                }
                tips.push(cur);
            }
            for ht_r in 25..=34usize {
                tips.push(ht_r);
            }
            let mut p = nil();
            for j in (1..=l0).rev() {
                let h = if j == 1 {
                    lit(9)
                } else {
                    &lit(ch_val(j)) | &lit(5)
                };
                p = cons(Expr::Type(h), p);
            }
            defs.push(def(&format!("P{tag}"), p));
            let p_idx = defs.len() - 1;
            let ts = u4_inst(defs);
            let neg = tips.into_iter().fold(Type::empty(), |u, idx| {
                &u | &cons_of(Type::int(), ts[idx].clone())
            });
            &ts[p_idx] - &neg
        };

        let t_inhab_wide = build_case(true, true, "_r8sb_iw");
        Type::forget_emptiness();
        let c_iw = t_inhab_wide.escape_cell_counts();
        assert!(c_iw.0 > 0, "inhab+wide cells: {c_iw:?}");
        Type::forget_emptiness();
        assert_eq!(t_inhab_wide.chain_verdict(), Some(Verdict::Inhabited));
        Type::forget_emptiness();
        assert_eq!(t_inhab_wide.verdict(), Verdict::Inhabited);

        let t_empty_light = build_case(false, false, "_r8sb_el");
        Type::forget_emptiness();
        let c_el = t_empty_light.escape_cell_counts();
        assert!(c_el.0 > 0, "empty+light cells: {c_el:?}");
        Type::forget_emptiness();
        assert_eq!(t_empty_light.chain_verdict(), Some(Verdict::Empty));
        Type::forget_emptiness();
        assert_eq!(t_empty_light.verdict(), Verdict::Empty);

        // Witness: the list of length 40 with 9 at place 1, 5 at places 2 and 8, and `ch_val(j)`
        // at every other place j is in `t_inhab_wide` and not in `t_empty_light`.
        let ch_val = |j: usize| -> i64 { ((j.count_ones() as usize + j % 3) % 4) as i64 };
        let w_bad_for_el = (1..=40usize).rev().fold(Value::atom("nil"), |tail, j| {
            let v = if j == 1 {
                9
            } else if j == 2 || j == 8 {
                5
            } else {
                ch_val(j)
            };
            Value::atom_with("cons", vec![Value::Int(v), tail])
        });
        assert!(t_inhab_wide.contains(&w_bad_for_el));
        assert!(!t_empty_light.contains(&w_bad_for_el));
    });
}

/// R9 X38: the shift encoding of Boolean matrix multiplication as an escape. For `m × m`
/// Boolean matrices `a` and `b`, the positive list (as long as the tallest row, so every row
/// holds its length) has one place per entry of `a` (place
/// `2 + i·m + q` holds `{100 + q, 7}` when `a[i][q]`, else `{7}`), the text nodes `F_e` exclude
/// `100 + q` at `e = E_k − q` when `b[q][k]` (`E_k = k(m + 1) + m`), and the refused row of the
/// pair `(i, k)` is `F_d` with `d = E_k + 1 + i·m`. Place `2 + i'·m + q'` of that row meets
/// `F_e` with `e = E_k − q' + (i − i')·m`, which excludes `100 + q'` only when it is
/// `E_{k'} − q'` with `b[q'][k']`, that is `(k − k')(m + 1) = (i' − i)·m`, so `k = k'` and
/// `i = i'` (`|k − k'| < m`). So the row of `(i, k)` has an atom exactly at the places
/// `2 + i·m + q` with `a[i][q] ∧ b[q][k]`, never a kill (7 is never excluded), and all atoms
/// at a place are the one value `100 + q`: the type is inhabited exactly when every entry of
/// the Boolean product `ab` is 1. Input size about `4m²`; reading each row's first cell is
/// computing `ab`.
fn r9_bmm(a: &[Vec<bool>], b: &[Vec<bool>], tag: &str) -> Type {
    let m = a.len();
    let ek = |k: usize| k * (m + 1) + m;
    let dmax = ek(m - 1) + 1 + (m - 1) * m;
    let mut excl = vec![None; dmax + 1];
    for k in 0..m {
        for q in 0..m {
            if b[q][k] {
                excl[ek(k) - q] = Some(100 + q as i64);
            }
        }
    }
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for (e, x) in excl.iter().enumerate().skip(1) {
        let h = match x {
            Some(c) => &Type::int() - &lit(*c),
            None => Type::int(),
        };
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    // The positive list is as long as the tallest row (a row `F_d` holds lengths `d` and up),
    // with `{7}` past the entries of `a`.
    let l0 = dmax;
    let mut p = nil();
    for j in (1..=l0).rev() {
        let h = if (2..2 + m * m).contains(&j) && a[(j - 2) / m][(j - 2) % m] {
            &lit(100 + ((j - 2) % m) as i64) | &lit(7)
        } else {
            lit(7)
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let mut u = Type::empty();
    for i in 0..m {
        for k in 0..m {
            u = &u | &ts[ek(k) + 1 + i * m];
        }
    }
    &ts[dmax + 1] - &u
}

/// A splitmix64 step, for the deterministic random matrices of the R9 tests and probe.
fn r9_mix(s: &mut u64) -> u64 {
    *s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *s;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// Two random `m × m` Boolean matrices with entries 1 at rate `num / 8`.
fn r9_matrices(m: usize, num: u64, seed: u64) -> (Vec<Vec<bool>>, Vec<Vec<bool>>) {
    let mut s = seed;
    let mut g = || {
        (0..m)
            .map(|_| (0..m).map(|_| r9_mix(&mut s) % 8 < num).collect())
            .collect::<Vec<Vec<bool>>>()
    };
    let a = g();
    let b = g();
    (a, b)
}

/// The sparse adversary of `r9_bmm`: side `m = s²` (s = isqrt of the requested side), index `q = (x, y)
/// = x·s + y`, `a[i][(x, y)] = [x = i mod s]` and `b[(x, y)][k] = [y = f(x, k)]` with `f` pseudo-random.
/// Every entry of the product is 1 through exactly one `q` among the `s` places `a[i]` holds, so
/// the type is inhabited and a method that reads row `(i, k)` place by place reads about `s / 2`
/// empty cells per row: about `m^2.5 / 2` in all, `I^1.25` in the input size `I ≈ 4m²`.
fn r9_one_matrices(side: usize) -> (Vec<Vec<bool>>, Vec<Vec<bool>>) {
    let s = side.isqrt();
    let m = s * s;
    let mut seed = 0x51ce_u64;
    let f: Vec<Vec<usize>> = (0..s)
        .map(|_| {
            (0..m)
                .map(|_| (r9_mix(&mut seed) % s as u64) as usize)
                .collect()
        })
        .collect();
    let a = (0..m)
        .map(|i| (0..m).map(|q| q / s == i % s).collect())
        .collect();
    let b = (0..m)
        .map(|q| (0..m).map(|k| q % s == f[q / s][k]).collect())
        .collect();
    (a, b)
}

/// An adversary of the committed cell finder for `r9_bmm`: `b` all ones, `a` all ones except row 0, which
/// holds only `q = m − 1`. Rows `(i ≥ 1, k)` reach three cells at the first three values of `q` and
/// retire, but row `(0, k)` keeps the class of column `k` live until its last value, so each of the
/// other `m − 4` values of column `k` still lists about `m` places (or reads the live rows): about
/// `m³` reads, `I^1.5` in the input size `I ≈ 4m²`. The product is all ones (inhabited).
fn r9_late_matrices(m: usize) -> (Vec<Vec<bool>>, Vec<Vec<bool>>) {
    let a = (0..m)
        .map(|i| (0..m).map(|q| i > 0 || q == m - 1).collect())
        .collect();
    (a, vec![vec![true; m]; m])
}

fn r9_product_all_ones(a: &[Vec<bool>], b: &[Vec<bool>]) -> bool {
    let m = a.len();
    (0..m).all(|i| (0..m).all(|k| (0..m).any(|q| a[i][q] && b[q][k])))
}

/// R9 X38: the shift encoding decides exactly as the Boolean product says, on random matrices
/// of side 2 to 5 at three densities (both verdicts occur), with the closed-form witness
/// checked by `contains` when inhabited. Negative control: the same matrices with the whole
/// row 0 of `a` cleared make the row of `(0, k)` atom-free, so the answer must be `Empty`.
#[test]
fn r9_bmm_encoding_decides_as_the_boolean_product() {
    big(|| {
        let mut seen = (0, 0);
        for m in 2usize..=5 {
            for num in [3u64, 4, 6] {
                for seed in 0..6u64 {
                    let (a, mut b) = r9_matrices(m, num, seed * 31 + m as u64);
                    if seed == 0 {
                        // One planted all-ones product per size: column 0 of `a` and row 0 of
                        // `b` all 1.
                        b[0] = vec![true; m];
                    }
                    let mut a = a;
                    if seed == 0 {
                        for row in a.iter_mut() {
                            row[0] = true;
                        }
                    }
                    let tag = format!("_r9bmm_{m}_{num}_{seed}");
                    Type::forget_emptiness();
                    let t = r9_bmm(&a, &b, &tag);
                    let want = if r9_product_all_ones(&a, &b) {
                        seen.0 += 1;
                        Verdict::Inhabited
                    } else {
                        seen.1 += 1;
                        Verdict::Empty
                    };
                    assert_eq!(t.verdict(), want, "r9bmm m {m} num {num} seed {seed}");
                    if want == Verdict::Inhabited {
                        let l0 = (m - 1) * (m + 1) + m + 1 + (m - 1) * m;
                        let w = (1..=l0).rev().fold(Value::atom("nil"), |tail, j| {
                            let v = if (2..2 + m * m).contains(&j) && a[(j - 2) / m][(j - 2) % m] {
                                100 + ((j - 2) % m) as i64
                            } else {
                                7
                            };
                            Value::atom_with("cons", vec![Value::Int(v), tail])
                        });
                        assert!(t.contains(&w), "r9bmm witness m {m} num {num} seed {seed}");
                        let mut a0 = a.clone();
                        a0[0] = vec![false; m];
                        Type::forget_emptiness();
                        let t0 = r9_bmm(&a0, &b, &format!("{tag}_z"));
                        assert_eq!(t0.verdict(), Verdict::Empty, "r9bmm control m {m}");
                    }
                }
            }
        }
        assert!(seen.0 >= 4 && seen.1 >= 4, "both verdicts occur: {seen:?}");
    });
}

/// R9 X38: the sparse adversary has an all-ones product with one witness per entry, and the
/// shift encoding decides it `Inhabited`. Negative control: clearing column 0 of `b` empties
/// the row of `(i, 0)`, so the answer must be `Empty`.
#[test]
fn r9_sparse_bmm_adversary_has_one_atom_per_row() {
    big(|| {
        for side in [4usize, 9, 16] {
            let (a, mut b) = r9_one_matrices(side);
            let m = a.len();
            for (i, ai) in a.iter().enumerate() {
                for k in 0..m {
                    let hits = ai.iter().zip(&b).filter(|&(&x, bq)| x && bq[k]).count();
                    assert_eq!(hits, 1, "one witness for ({i}, {k}) at side {m}");
                }
            }
            Type::forget_emptiness();
            let t = r9_bmm(&a, &b, &format!("_r9one_{m}"));
            assert_eq!(t.verdict(), Verdict::Inhabited, "r9bmmone side {m}");
            for row in b.iter_mut() {
                row[0] = false;
            }
            Type::forget_emptiness();
            let t0 = r9_bmm(&a, &b, &format!("_r9one_{m}_z"));
            assert_eq!(t0.verdict(), Verdict::Empty, "r9bmmone control side {m}");
        }
    });
}

fn r9_swapping_groups(n: usize, negative: bool, tag: &str) -> Type {
    // Two alternating runs exhaust and enter each other's group on the same step.
    let l = list_named(Type::int(), &format!("L{tag}"));
    let mut a = cons_of(lit(1), l.clone());
    let mut b = a.clone();
    let ha = &Type::int() - &lit(2);
    let hb = &Type::int() - &lit(3);
    for _ in 0..n {
        let na = cons_of(ha.clone(), b.clone());
        let nb = cons_of(hb.clone(), a);
        a = na;
        b = nb;
    }
    if negative {
        let mut p = l.clone();
        for _ in 0..n + 2 {
            p = cons_of(lit(0), p);
        }
        &(&p - &cons_of(Type::int(), a)) - &cons_of(Type::int(), b)
    } else {
        &(&cons_of(Type::int(), a) & &cons_of(Type::int(), b)) - &cons_of(lit(7), l)
    }
}

#[test]
fn r9_wrapped_witnesses_are_checked_and_empty_fields_remain_empty() {
    big(|| {
        for n in [4, 16, 32] {
            for case in [
                "chain",
                "chainfar",
                "r5remout",
                "u4holesout",
                "clstaggerholesout",
            ] {
                let t = rfx_case(case, n, "_r9nest");
                let want = t.verdict();
                for wrap in [
                    "tup", "rec", "atom", "atom2", "nested", "option", "map", "listhead",
                ] {
                    Type::forget_emptiness();
                    let w = rfx_case(&format!("{wrap}:{case}"), n, "_r9nest");
                    let got = w.verdict();
                    eprintln!("r9 nesting {wrap}:{case} n {n}: {got:?}, bare {want:?}");
                    assert_eq!(got, want, "{wrap}:{case} at {n}");
                    assert_eq!(w.is_empty(), want == Verdict::Empty);
                }
            }
        }
        let t = r5_remainder_boundary(16, true, "_r9member");
        let good = r6_colour_list(&[5, 1, 1]);
        let bad = r6_colour_list(&[1, 1, 1]);
        assert!(t.contains(&good));
        assert!(!t.contains(&bad)); // negative control for the concrete witness
        let w = Type::atom_with("wrap", &Type::tuple(vec![t]));
        assert!(w.contains(&Value::atom_with("wrap", vec![good])));
        assert!(!w.contains(&Value::atom_with("wrap", vec![bad])));
        assert_eq!(w.verdict(), Verdict::Inhabited);
    });
}

#[test]
fn r9_wrapped_witness_cost_scales() {
    big(|| {
        for case in [
            "clstaggerholesout",
            "u4holesout",
            "u4cofrontshared",
            "r5remout",
        ] {
            for wrap in [
                "tup", "rec", "atom", "atom2", "nested", "option", "map", "listhead",
            ] {
                let small = rfx_case(&format!("{wrap}:{case}"), 32, "_r9scale_small");
                let large = rfx_case(&format!("{wrap}:{case}"), 256, "_r9scale_large");
                scaling::check("a checked list witness inside a product", 32, |n| {
                    Type::forget_emptiness();
                    let t = if n == 32 { &small } else { &large };
                    assert_eq!(t.verdict(), Verdict::Inhabited);
                });
            }
        }
    });
}

#[test]
fn r9_active_groups_have_one_entry_across_simultaneous_reentry() {
    big(|| {
        let small = r9_swapping_groups(512, false, "_r9swap_small");
        let large = r9_swapping_groups(4096, false, "_r9swap_large");
        scaling::check(
            "two positive chains re-enter each other's exhausted groups",
            512,
            |n| {
                Type::forget_emptiness();
                assert_eq!(
                    (if n == 512 { &small } else { &large }).chain_verdict(),
                    Some(Verdict::Inhabited)
                );
            },
        );
        for n in 1..=6 {
            let t = r9_swapping_groups(n, false, "_r9swap_oracle");
            // The last positive item is 1, previous items 0, and the first is 0.
            let mut xs = vec![0; n + 1];
            xs.push(1);
            assert!(t.contains(&r6_colour_list(&xs)));
            assert!(!t.contains(&r6_colour_list(&vec![0; n + 2])));
            assert_eq!(t.chain_verdict(), Some(Verdict::Inhabited));
        }
    });
}

/// Growing-alphabet adversary: every requested tail height is even. The colours of a
/// positive place and an aligned negative hole occupy opposite parity blocks, so all
/// later cells are empty even though each of sqrt(n) channels has sqrt(n) incidences.
fn r9_balanced(n: usize, tag: &str) -> Type {
    let n = n.max(8);
    let q = n.isqrt() + 1;
    let colour = |j: usize, flip: bool| -> i64 {
        let mixed = j.wrapping_mul(1_103_515_245) ^ (j >> 2) ^ j.count_ones() as usize;
        2 + (((j % 2) ^ usize::from(flip)) * q + mixed % q) as i64
    };
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for e in 1..=n {
        let excluded = &lit(0) | &lit(colour(e, true));
        let h = &Type::int() - &excluded;
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if j == 1 {
            &lit(0) | &lit(-1)
        } else {
            lit(colour(j, false))
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let u = (3..=n).step_by(2).fold(Type::empty(), |u, d| &u | &ts[d]);
    &ts[n + 1] - &u
}

#[test]
fn r9_compressed_and_expanded_runs_agree_with_enumeration() {
    big(|| {
        let mut rng = R6Rng(0x91842aabbccd);
        for i in 0..2000 {
            let input = r6_random_input(&mut rng, 4, 4, true);
            let want = r6_oracle(&input);
            let t = r6_input_type(&input, &format!("_r9expand{i}"));
            for expanded in [false, true] {
                Type::forget_emptiness();
                let got = if expanded {
                    t.chain_verdict_expanded()
                } else {
                    t.chain_verdict()
                };
                if let Some(v) = got {
                    assert_eq!(
                        v == Verdict::Inhabited,
                        want,
                        "case {i} expanded {expanded}: {input:?} {v:?}"
                    );
                }
            }
        }
        for n in [2, 16, 64] {
            let t = r9_swapping_groups(n, false, "_r9expand_swap");
            assert_eq!(t.chain_verdict(), t.chain_verdict_expanded());
        }
        let yes = rfx_case("chainfar", 3, "_r9oracle_yes");
        let no = rfx_case("chain", 3, "_r9oracle_no");
        assert_eq!(yes.chain_verdict_expanded(), Some(Verdict::Inhabited));
        assert_eq!(no.chain_verdict_expanded(), Some(Verdict::Empty));
    });
}

#[test]
#[ignore]
fn r9_escape_probe() {
    let which = std::env::var("RFX").unwrap();
    let sizes: Vec<usize> = std::env::var("RFX_N")
        .unwrap()
        .split(',')
        .map(|s| s.parse().unwrap())
        .collect();
    big(move || {
        for n in sizes {
            let t = rfx_case(&which, n, "_r9finder");
            let mut meter = scaling::Meter::new();
            let mut counts = (0, 0);
            let work = meter.work(|| counts = t.escape_cell_counts());
            eprintln!(
                "rfx {which} n {n} finder units {} bytes {}",
                work.units, work.bytes
            );
            eprintln!("escape cells {which} n {n} {counts:?}");
        }
    });
}

#[test]
#[ignore]
fn r9_wide_literal_probe() {
    for text in [
        "9223372036854775807",
        "9223372036854775808",
        "-9223372036854775809",
        "18446744073709551616",
    ] {
        let v = Value::int(text.parse().unwrap());
        let ty = zedc::check::read::parse_type(text);
        match ty {
            Ok(t) => eprintln!(
                "r9 literal {text}: empty {} contains_literal {} contains_zero {}",
                t.is_empty(),
                t.contains(&v),
                t.contains(&Value::Int(0))
            ),
            Err(e) => eprintln!("r9 literal {text}: error {e}"),
        }
        for arg in [text, "0"] {
            let src = format!("f(x: {text}) = 0;\nmain() = f(x: {arg});\n");
            eprintln!(
                "r9 literal program {text} arg {arg}: {:?}",
                zedc::run::load(src.as_bytes()).err()
            );
        }
    }
}

/// X38 adversary with two positive and two negative residues mod 7. The tall
/// off-coset root keeps the height suffix gcd at 1; adjacent positive residues
/// keep the per-value gcd at 1. No aligned cell is nonempty, including the outlier's.
fn r9_cosets(n: usize, subtract: bool, tag: &str) -> Type {
    let n = n.max(16);
    let height = 7 * ((n - 2) / 7);
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for e in 1..=height + 1 {
        let h = if matches!(e % 7, 3 | 4) {
            &Type::int() - &lit(0)
        } else {
            Type::int()
        };
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if matches!(j % 7, 0 | 1) {
            &lit(0) | &lit(-1)
        } else {
            lit(-1)
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let p = ts[height + 2].clone();
    if !subtract {
        return p;
    }
    let u = (7..=height)
        .step_by(7)
        .map(|h| h + 1)
        .chain([height])
        .fold(Type::empty(), |u, d| &u | &ts[d]);
    &p - &u
}

#[test]
fn r9_wide_literals_are_preserved_and_compile_limits_are_reported() {
    big(|| {
        for text in [
            "9223372036854775807",
            "9223372036854775808",
            "-9223372036854775809",
            "18446744073709551616",
        ] {
            let v = Value::int(text.parse().unwrap());
            let t = zedc::check::read::parse_type(text).unwrap();
            assert!(!t.is_empty(), "{text}");
            assert!(t.contains(&v), "{text}");
            assert!(
                !t.contains(&Value::Int(0)),
                "negative membership control at {text}"
            );
            let src = format!(
                "f(x: {text}) = 0;
main() = f(x: {text});
"
            );
            let batch = zedc::run::load(src.as_bytes())
                .err()
                .expect("literal type compilation must be reported");
            assert!(batch.contains("does not compile it yet"), "{batch}");
            let alone = std::thread::spawn(move || zedc::run::load(src.as_bytes()).err())
                .join()
                .unwrap();
            assert_eq!(alone, Some(batch));
        }
    });
}

/// The escape's cell discovery stays within n log n from 1024 to 8192 on the families where the
/// sweep it replaced grew faster: `r9cosets` (place and head types both of period 7, every cell
/// empty by alignment; the sweep took 595.9M and 33,746M instructions at 8192 and 65,536, 57x for
/// 8x), and the Boolean-product chains `r9bmmlate` (11.9x) and `r10alternating` (10.7x, above the
/// 9.8x of n log n). The windows of block summaries and residue pair listing take 85.1M and 760.2M
/// on `r9cosets` (8.9x), 8.1x and 8.3x on the other two.
#[test]
fn escape_cells_scale_on_the_coset_and_product_chains() {
    big(|| {
        let base = 1024;
        for case in ["r9cosets", "r9bmmlate", "r10alternating"] {
            let (s_runs, l_runs) = scaling::Meter::new().runs();
            let small: Vec<Type> = (0..s_runs)
                .map(|i| rfx_case(case, base, &format!("_esc_{case}_{base}_{i}")))
                .collect();
            let large: Vec<Type> = (0..l_runs)
                .map(|i| rfx_case(case, 8 * base, &format!("_esc_{case}_{}_{i}", 8 * base)))
                .collect();
            let (si, li) = (AtomicUsize::new(0), AtomicUsize::new(0));
            scaling::check(&format!("escape cells of {case}"), base, |n| {
                let t = if n == base {
                    &small[si.fetch_add(1, Relaxed)]
                } else {
                    &large[li.fetch_add(1, Relaxed)]
                };
                std::hint::black_box(t.escape_cell_counts());
            });
        }
    });
}

#[test]
fn r9_coset_cover_agrees_with_enumeration() {
    big(|| {
        let t = r9_cosets(16, true, "_r9cosets");
        let p = r9_cosets(16, false, "_r9cosetscontrol");
        let variable: Vec<usize> = (1..=16).filter(|j| matches!(j % 7, 0 | 1)).collect();
        for mask in 0..1usize << variable.len() {
            let mut xs = vec![-1; 16];
            for (i, &j) in variable.iter().enumerate() {
                if mask >> i & 1 == 1 {
                    xs[j - 1] = 0;
                }
            }
            let value = r6_colour_list(&xs);
            assert!(p.contains(&value));
            assert!(!t.contains(&value), "mask {mask}");
        }
        assert_eq!(t.verdict(), Verdict::Empty);
        assert_eq!(p.verdict(), Verdict::Inhabited);
    });
}

#[test]
fn r9_nested_queries_agree_alone_forward_and_reverse() {
    fn make() -> Vec<Type> {
        ["tup", "rec", "atom", "nested", "option", "map", "listhead"]
            .iter()
            .flat_map(|w| {
                ["chain", "chainfar", "r5remout", "u4holesout"]
                    .iter()
                    .map(move |c| rfx_case(&format!("{w}:{c}"), 8, "_r9order"))
            })
            .collect()
    }
    big(|| {
        let ts = make();
        Type::forget_emptiness();
        let forward: Vec<_> = ts
            .iter()
            .map(|t| {
                let empty = t.is_empty();
                (t.verdict(), empty)
            })
            .collect();
        Type::forget_emptiness();
        let mut reverse: Vec<_> = ts
            .iter()
            .rev()
            .map(|t| {
                let empty = t.is_empty();
                (t.verdict(), empty)
            })
            .collect();
        reverse.reverse();
        assert_eq!(forward, reverse);
        for (i, want) in forward.iter().enumerate() {
            let got = std::thread::Builder::new()
                .stack_size(16 * 1024 * 1024)
                .spawn(move || {
                    let ts = make();
                    {
                        let empty = ts[i].is_empty();
                        (ts[i].verdict(), empty)
                    }
                })
                .unwrap()
                .join()
                .unwrap();
            assert_eq!(&got, want, "index {i}");
        }
    });
}

/// X43 (round 9; fixed in round 10): a list of the front-sweep class as the head of another list of
/// the same atom names (`listhead:`) was refused although the list alone is decided, and
/// `is_empty` of `listhead:chain` at 8 was true after the other wrappers were asked and false in
/// a fresh thread. The item is now a root (`fields`) and is swept inside the outer fallback.
#[test]
fn r9_x43_a_list_as_the_head_of_a_list_is_decided_as_the_list_alone() {
    big(|| {
        for case in ["chain", "chainfar", "r5remout", "u4holesout"] {
            let want = rfx_case(case, 8, "_r9x43").verdict();
            Type::forget_emptiness();
            let t = rfx_case(&format!("listhead:{case}"), 8, "_r9x43");
            assert_eq!(t.verdict(), want, "listhead:{case}");
            assert_eq!(t.is_empty(), want == Verdict::Empty, "listhead:{case}");
        }
    });
}

/// Diagnostic for the remaining same-constructor tail boundary (R9-C5).
#[test]
#[ignore]
fn r9_tail_admission_probe() {
    big(|| {
        for n in [3, 4, 8, 16] {
            let t = rfx_case("listtail:r5remout", n, "_r9tailmember");
            let good = Value::atom_with("cons", vec![Value::Int(0), r6_colour_list(&[5, 1, 1])]);
            let bad = Value::atom_with("cons", vec![Value::Int(0), r6_colour_list(&[1, 1, 1])]);
            assert!(t.contains(&good));
            assert!(!t.contains(&bad));
            eprintln!("r9 tail n {n}: {:?}, member [0,5,1,1] checked", t.verdict());
        }
        for n in 1..=6 {
            let t = rfx_case("listtail:chain", n, "_r9tailempty");
            // Integer heads distinguish only equality with 1. A chain test has
            // horizon n; one extra tail item covers the unbounded carrier case.
            for length in 0..=n + 1 {
                for mask in 0..1usize << length {
                    let xs: Vec<i64> = (0..length).map(|i| ((mask >> i) & 1) as i64).collect();
                    let v = Value::atom_with("cons", vec![Value::Int(0), r6_colour_list(&xs)]);
                    assert!(!t.contains(&v));
                }
            }
            eprintln!(
                "r9 empty tail n {n}: {:?}, enumeration found no member",
                t.verdict()
            );
        }
    });
}

/// `t(d) = (t(d-1), t(d-1))`, one type shared by both components at every level.
fn r9_shared_tuple_type(n: usize, leaf: Type) -> Type {
    let mut t = leaf;
    for _ in 0..n {
        t = Type::tuple(vec![t.clone(), t]);
    }
    t
}

/// R9-C7 (Codex R9): `decidable` walked a type shared by two components once per path, 2^d
/// visits at depth d. It visits each distinct type once, and still finds a bounded morphism
/// under tuples, atom payloads and recursive groups.
#[test]
fn r9_decidable_shared_dag_scales_and_rejects_bounded_leaves() {
    big(|| {
        let small = r9_shared_tuple_type(16, Type::bool());
        let large = r9_shared_tuple_type(128, Type::bool());
        scaling::check("decidability of a shared tuple DAG", 16, |n| {
            assert!((if n == 16 { &small } else { &large }).decidable());
        });
        let bounded = || Type::exact(lit(0), Type::int());
        for n in [0, 1, 16, 128, 1024] {
            assert!(r9_shared_tuple_type(n, Type::bool()).decidable());
            assert!(!r9_shared_tuple_type(n, bounded()).decidable());
        }
        assert!(list_named(Type::bool(), "_r9decidable_cycle").decidable());
        assert!(!list_named(bounded(), "_r9undecidable_cycle").decidable());
        let in_payload = |leaf: Type| {
            Type::atom_with("r9dec", &Type::tuple(vec![r9_shared_tuple_type(64, leaf)]))
                | Type::atom("r9other")
        };
        assert!(in_payload(Type::bool()).decidable());
        assert!(!in_payload(bounded()).decidable());
    });
}

/// X44 (R9-C5, fixed in round 10): a written Boolean list type as the tail of a list
/// (`cons(int, L - U)`) is decided as the tail alone: `fields` admits a tail whose own pair
/// part is not a union of literal rows (`boolean_tail`). Before, `listtail:chain` at n >= 3 and
/// `listtail:r5remout` were Refused(Fork).
#[test]
fn r10_a_boolean_list_tail_is_decided_as_the_tail() {
    big(|| {
        for n in [4, 16, 32] {
            for case in [
                "chain",
                "chainfar",
                "r5remout",
                "u4holesout",
                "clstaggerholesout",
            ] {
                Type::forget_emptiness();
                let want = rfx_case(case, n, "_r10tail").verdict();
                Type::forget_emptiness();
                let t = rfx_case(&format!("listtail:{case}"), n, "_r10tail");
                assert_eq!(t.verdict(), want, "listtail:{case} at {n}");
                assert_eq!(
                    t.is_empty(),
                    want == Verdict::Empty,
                    "listtail:{case} at {n}"
                );
            }
        }
    });
}

#[test]
fn r10_a_boolean_list_tail_scales() {
    big(|| {
        for case in ["clstaggerholesout", "r5remout", "chain"] {
            let small = rfx_case(&format!("listtail:{case}"), 32, "_r10tail_small");
            let large = rfx_case(&format!("listtail:{case}"), 256, "_r10tail_large");
            let want = rfx_case(case, 32, "_r10tail_want").verdict();
            scaling::check("a Boolean list type as a list's tail", 32, |n| {
                Type::forget_emptiness();
                let t = if n == 32 { &small } else { &large };
                assert_eq!(t.verdict(), want);
            });
        }
    });
}

/// X45 (Codex R9-C6, round 10): a map whose required keys lie strictly within its allowed ones is
/// built when the difference of the two key types is the empty type as written; its Empty-value
/// twins and a map whose required keys are not all allowed stay Empty.
#[test]
fn r10_required_keys_within_allowed_keys_are_built() {
    big(|| {
        let inhabited = [
            Type::morphism(lit(0), Type::int(), Type::int()),
            Type::morphism(lit(1), Type::int(), Type::int()),
            Type::morphism(&lit(0) | &lit(3), Type::int(), Type::int()),
            Type::morphism(lit(0), Type::int(), rfx_case("r5remout", 16, "_r10map")),
        ];
        for t in &inhabited {
            Type::forget_emptiness();
            assert_eq!(t.verdict(), Verdict::Inhabited, "{t:?}");
            assert!(!t.is_empty(), "{t:?}");
        }
        let empty = [
            Type::morphism(lit(0), Type::int(), Type::empty()),
            Type::morphism(lit(0), Type::int(), rfx_case("chain", 16, "_r10map")),
            Type::morphism(Type::int(), lit(0), Type::int()),
        ];
        for t in &empty {
            Type::forget_emptiness();
            assert_eq!(t.verdict(), Verdict::Empty, "{t:?}");
            assert!(t.is_empty(), "{t:?}");
        }
    });
}

/// The `Value::Big` gap (round 10): `r7congruenceout` with the first place's 7 replaced by
/// 2^63, a literal outside the 64-bit range, so `Ints::of` reads no 64-bit set for that place.
fn r10_big_congruence(n: usize, tag: &str) -> Type {
    let n = n.max(4);
    let big = Type::lit(&Value::int("9223372036854775808".parse().unwrap())).unwrap();
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for e in 1..=n {
        let h = &Type::int() - &lit((e % 3) as i64);
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if j == 1 {
            &lit(2) | &big
        } else {
            &lit(((4 - j % 3) % 3) as i64) | &lit(7)
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let u = (2..=n).step_by(3).fold(Type::empty(), |u, d| &u | &ts[d]);
    &ts[n + 1] - &(&u | &ts[3])
}

/// The `Value::Big` gap (round 10): one literal outside the 64-bit range in a head no longer
/// sends the list to the general search; the escape decides it, at the bare case's cost.
#[test]
fn r10_a_wide_head_literal_is_decided_by_the_escape() {
    big(|| {
        let big = Value::int("9223372036854775808".parse().unwrap());
        for n in [16, 64] {
            let t = r10_big_congruence(n, &format!("_r10big{n}"));
            let word = |first: Value| {
                (1..=n).rev().fold(Value::atom("nil"), |tail, j| {
                    let h = if j == 1 {
                        first.clone()
                    } else {
                        Value::Int(((4 - j % 3) % 3) as i64)
                    };
                    Value::atom_with("cons", vec![h, tail])
                })
            };
            assert!(t.contains(&word(Value::Int(2))));
            assert!(
                !t.contains(&word(big.clone())),
                "F2 must reject the wide head"
            );
            Type::forget_emptiness();
            assert_eq!(t.chain_verdict(), Some(Verdict::Inhabited), "escape at {n}");
            Type::forget_emptiness();
            assert_eq!(t.verdict(), Verdict::Inhabited);
        }
        let small = r10_big_congruence(32, "_r10big_small");
        let large = r10_big_congruence(256, "_r10big_large");
        scaling::check("a wide head literal", 32, |n| {
            Type::forget_emptiness();
            let t = if n == 32 { &small } else { &large };
            assert_eq!(t.verdict(), Verdict::Inhabited);
        });
    });
}

/// Codex R9's oracle test (archive/r9/R9_CODEX.diff), taken as BRIEF10 asks: a chain in an
/// atom payload agrees with enumeration of every 0/1 list up to length 4.
#[test]
fn r9_atom_chain_narrowing_agrees_with_finite_oracle() {
    big(|| {
        let empty = Type::atom_with(
            "r8box",
            &Type::tuple(vec![rfx_case("chain", 3, "_r9atomoracle")]),
        );
        let yes = Type::atom_with(
            "r8box",
            &Type::tuple(vec![rfx_case("chainfar", 3, "_r9atomoracle_far")]),
        );
        let mut found = false;
        for length in 0..=4 {
            for mask in 0..1usize << length {
                let xs: Vec<i64> = (0..length).map(|i| ((mask >> i) & 1) as i64).collect();
                let value = Value::atom_with("r8box", vec![r6_colour_list(&xs)]);
                assert!(!empty.contains(&value));
                found |= yes.contains(&value);
            }
        }
        assert!(found, "escaping twin is the oracle control");
        assert_eq!(empty.verdict(), Verdict::Empty);
        assert_eq!(yes.verdict(), Verdict::Inhabited);
        assert!(empty.is_empty());
        assert!(!yes.is_empty());
    });
}

fn r10_big_congruence_cx(n: usize, wide: bool, tag: &str) -> Type {
    let lit = |i: i64| {
        if wide && i == 2 {
            Type::lit(&Value::int("9223372036854775808".parse().unwrap())).unwrap()
        } else {
            lit(i)
        }
    };
    let outside = true;
    let n = n.max(4);
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for e in 1..=n {
        let h = &Type::int() - &lit((e % 3) as i64);
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if j == 1 {
            &lit(2) | &lit(7)
        } else {
            &lit(((4 - j % 3) % 3) as i64) | &lit(7)
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let mut u = (2..=n).step_by(3).fold(Type::empty(), |u, d| &u | &ts[d]);
    if outside {
        u = &u | &ts[3];
    }
    &ts[n + 1] - &u
}

#[test]
fn r10_scalar_required_keys_within_allowed_keys() {
    big(|| {
        for value in [Type::int(), rfx_case("r5remout", 16, "_r10map")] {
            let t = Type::morphism(lit(0), Type::int(), value.clone());
            let good = if value == Type::int() {
                Value::Int(0)
            } else {
                r6_colour_list(&[5, 1, 1])
            };
            // Runtime membership deliberately rejects bounded morphisms; check the
            // returned value and the scalar domain certificate independently.
            assert!(value.contains(&good));
            assert!(Type::int().contains(&Value::Int(0)));
            assert_eq!(t.verdict(), Verdict::Inhabited);
        }
        assert_eq!(
            Type::morphism(lit(0), Type::int(), Type::empty()).verdict(),
            Verdict::Empty
        );
        assert_eq!(
            Type::morphism(lit(0), lit(1), Type::int()).verdict(),
            Verdict::Empty
        );
        assert_eq!(
            Type::morphism(Type::bool(), Type::bool(), Type::int()).verdict(),
            Verdict::Inhabited
        );
    });
}

#[test]
fn r10_boolean_tail_is_decided_and_scales() {
    big(|| {
        for case in ["chain", "r5remout"] {
            let want = if case == "chain" {
                Verdict::Empty
            } else {
                Verdict::Inhabited
            };
            let a = rfx_case(&format!("listtail:{case}"), 32, "_r10tail32");
            let b = rfx_case(&format!("listtail:{case}"), 256, "_r10tail256");
            scaling::check("a written Boolean list tail", 32, |n| {
                Type::forget_emptiness();
                assert_eq!((if n == 32 { &a } else { &b }).verdict(), want);
            });
        }
    });
}

#[test]
fn r10_big_integer_escape_is_a_renaming_and_scales() {
    big(|| {
        let a = r10_big_congruence_cx(32, true, "_r10big32");
        let b = r10_big_congruence_cx(256, true, "_r10big256");
        scaling::check("a wide integer in escape heads", 32, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 32 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
        for n in [16, 64, 256, 1024] {
            let small = r10_big_congruence_cx(n, false, "_r10bigsmall");
            let wide = r10_big_congruence_cx(n, true, "_r10bigwide");
            assert_eq!(wide.escape_cell_counts(), small.escape_cell_counts());
            assert_eq!(wide.verdict(), small.verdict());
        }
    });
}
/// H has simultaneous landings at K and J, H2 lands only at K. Their union
/// covers K's incoming slice but must not be reused as coverage of J.
#[test]
fn r10_partial_multi_target_coverage_is_per_child() {
    big(|| {
        let l = list_named(Type::int(), "_r10targets");
        let all = small(7);
        for a in 1..=7 {
            for b in 1..=7 {
                for k in 1..=7 {
                    let tail = |h: Type, t: Type| cons_of(h, t);
                    let u = tail(small(a), tail(small(k), l.clone()));
                    let v = tail(small(a), tail(all.clone(), l.clone()));
                    let w = tail(small(b), tail(small(k), l.clone()));
                    let negatives =
                        &(&tail(Type::int(), u) | &tail(Type::int(), v)) | &tail(Type::int(), w);
                    let positive = tail(
                        lit(0),
                        tail(all.clone(), tail(all.clone(), Type::atom("nil"))),
                    );
                    let t = &positive - &negatives;
                    let mut inhabited = false;
                    for x in 1..=3 {
                        for y in 1..=3 {
                            inhabited |= t.contains(&r6_colour_list(&[0, x, y]));
                        }
                    }
                    let want = if inhabited {
                        Verdict::Inhabited
                    } else {
                        Verdict::Empty
                    };
                    for got in [
                        t.chain_verdict(),
                        t.chain_verdict_expanded(),
                        Some(t.verdict()),
                    ] {
                        if let Some(got @ (Verdict::Empty | Verdict::Inhabited)) = got {
                            assert_eq!(got, want, "heads {a} {b} {k}");
                        }
                    }
                }
            }
        }
        // Falsifiable pair: changing the final positive head changes the answer.
        for (last, want) in [(lit(2), Verdict::Inhabited), (lit(1), Verdict::Empty)] {
            let k = cons_of(lit(1), l.clone());
            let j = cons_of(all.clone(), l.clone());
            let n = &(&cons_of(Type::int(), cons_of(small(3), k.clone()))
                | &cons_of(Type::int(), cons_of(small(3), j)))
                | &cons_of(Type::int(), cons_of(small(6), k));
            let p = cons_of(
                lit(0),
                cons_of(all.clone(), cons_of(last, Type::atom("nil"))),
            );
            let t = &p - &n;
            assert_eq!(t.verdict(), want);
        }
    });
}

#[test]
fn r10_shared_product_list_is_swept_and_checked_once() {
    big(|| {
        let a = rfx_case("r10sharedfront", 16, "_r10shared16");
        let b = rfx_case("r10sharedfront", 128, "_r10shared128");
        scaling::check("one list type shared by every tuple component", 16, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 16 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
        let empty = rfx_case("chain", 3, "_r10sharedempty");
        assert_eq!(Type::tuple(vec![empty; 16]).verdict(), Verdict::Empty);
    });
}

#[test]
fn r10_is_empty_on_a_nested_list_is_independent_of_a_prior_verdict() {
    for case in ["chain", "chainfar", "r5remout", "u4holesout"] {
        for wrap in ["listhead", "listtail", "atom"] {
            let got = std::thread::Builder::new()
                .stack_size(16 * 1024 * 1024)
                .spawn(move || rfx_case(&format!("{wrap}:{case}"), 8, "_r10freshbool").is_empty())
                .unwrap()
                .join()
                .unwrap();
            assert_eq!(got, case == "chain", "fresh is_empty {wrap}:{case}");
        }
    }
}

/// The r7congruenceout language with n irrelevant excluded integers shared by all
/// three head predicates. The positive word uses only 0,1,2,7, so those exclusions
/// change no cell or verdict. Distinct written type/row DAG size is O(n).
fn r10_padded_congruence(n: usize, tag: &str) -> Type {
    let n = n.max(4);
    let padding = (0..n).fold(Type::empty(), |a, k| &a | &lit(10000 + k as i64));
    let heads: Vec<Type> = (0..3)
        .map(|k| &Type::int() - &(&padding | &lit(k)))
        .collect();
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for e in 1..=n {
        defs.push(def(
            &format!("F{e}{tag}"),
            cons(Expr::Type(heads[e % 3].clone()), r(e - 1)),
        ));
    }
    let mut p = nil();
    for j in (1..=n).rev() {
        let h = if j == 1 {
            &lit(2) | &lit(7)
        } else {
            &lit(((4 - j % 3) % 3) as i64) | &lit(7)
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let u = (2..=n).step_by(3).fold(ts[3].clone(), |u, d| &u | &ts[d]);
    &ts[n + 1] - &u
}

#[test]
fn r10_irrelevant_shared_holes_preserve_the_finite_language() {
    big(|| {
        for n in 4..=6usize {
            let a = r7_congruence(n, true, "_r10pad_a");
            let b = r10_padded_congruence(n, "_r10pad_b");
            let mut found = false;
            for word in 0..4usize.pow(n as u32) {
                let mut code = word;
                let xs: Vec<i64> = (0..n)
                    .map(|_| {
                        let v = [0, 1, 2, 7][code % 4];
                        code /= 4;
                        v
                    })
                    .collect();
                let v = r6_colour_list(&xs);
                let want = a.contains(&v);
                assert_eq!(b.contains(&v), want, "n={n} word={xs:?}");
                found |= want;
            }
            assert!(found);
            assert!(!b.contains(&r6_colour_list(&vec![7; n])));
            assert_eq!(b.verdict(), Verdict::Inhabited);
        }
    });
}

#[test]
fn r10_shared_irrelevant_holes_are_projected_once_and_scale() {
    big(|| {
        let a = r10_padded_congruence(32, "_r10pad32");
        let b = r10_padded_congruence(256, "_r10pad256");
        scaling::check("irrelevant shared holes in integer heads", 32, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 32 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
    });
}

#[test]
fn r10_projection_uses_every_positive_head_and_keeps_finite_and_cofinite_meanings() {
    big(|| {
        let l = list_named(&lit(1) | &lit(3), "_r10alphascope");
        let p = cons_of(lit(2), cons_of(lit(3), l.clone()));
        let w = r6_colour_list(&[2, 3]);
        for h in [
            &lit(1) | &lit(10000),
            &Type::int() - &(&lit(3) | &lit(10000)),
        ] {
            let t = &p - &cons_of(lit(2), cons_of(h, l.clone()));
            assert!(t.contains(&w));
            assert!(
                t.escape_cell_counts().0 > 0,
                "the direct escape parsed the global alphabet"
            );
            assert_eq!(t.verdict(), Verdict::Inhabited);
        }
        let empty = &p - &cons_of(lit(2), cons_of(&lit(3) | &lit(10000), l));
        assert!(!empty.contains(&w));
        assert_eq!(empty.verdict(), Verdict::Empty);
    });
}

#[test]
fn r10_scalar_domain_certificates_match_all_class_domains() {
    big(|| {
        let carriers = vec![
            (
                Type::int(),
                vec![Value::Int(-1), Value::Int(0), Value::Int(1)],
                true,
            ),
            (
                Type::rat(),
                (-1..=1)
                    .map(|i: i64| Value::rat(zed_kernel::Rat::int(i.into())))
                    .collect(),
                true,
            ),
            (
                Type::f64(),
                vec![Value::float(-1.0), Value::float(0.0), Value::float(1.0)],
                true,
            ),
            (
                Type::string(),
                vec![Value::str("a"), Value::str("b"), Value::str("c")],
                true,
            ),
            (
                Type::bool(),
                vec![Value::Bool(false), Value::Bool(true)],
                false,
            ),
        ];
        let mut checked = 0;
        let mut answers = [0usize; 2];
        for (carrier, pool, fresh) in carriers {
            let listed = 1usize << pool.len();
            let full = (1usize << (pool.len() + usize::from(fresh))) - 1;
            let make = |bits: usize, cof: bool| {
                let s = pool
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| bits >> i & 1 != 0)
                    .fold(Type::empty(), |s, (_, v)| &s | &Type::lit(v).unwrap());
                if cof { &carrier - &s } else { s }
            };
            for r in 0..listed {
                for u in 0..listed {
                    for rc in [false, true] {
                        for uc in [false, true] {
                            for empty_value in [false, true] {
                                // One exact class for each listed literal and one for all
                                // remaining values of an infinite carrier. Enumerate every
                                // possible domain in this quotient, independently of the kernel.
                                let required = if rc { full ^ r } else { r };
                                let allowed = if uc { full ^ u } else { u };
                                let exists = (0..=full).any(|d| {
                                    required & !d == 0
                                        && d & !allowed == 0
                                        && (d == 0 || !empty_value)
                                });
                                let t = Type::morphism(
                                    make(r, rc),
                                    make(u, uc),
                                    if empty_value {
                                        Type::empty()
                                    } else {
                                        Type::int()
                                    },
                                );
                                Type::forget_emptiness();
                                assert_eq!(
                                    t.verdict(),
                                    if exists {
                                        Verdict::Inhabited
                                    } else {
                                        Verdict::Empty
                                    },
                                    "carrier {carrier}, masks {r}/{u}, complements {rc}/{uc}, empty value {empty_value}"
                                );
                                checked += 1;
                                answers[usize::from(exists)] += 1;
                            }
                        }
                    }
                }
            }
        }
        assert!(answers[0] > 0 && answers[1] > 0);
        eprintln!(
            "R10 scalar domains: {checked} cases, Empty {}, Inhabited {}",
            answers[0], answers[1]
        );
    });
}

/// Two selector positions encode an orthogonal red/blue pair using d negative
/// rectangles. This specializes X32; it does not give a lower bound for the
/// laminar escape-cell finder, since the selector atoms can cross.
fn r10_ov_selector_type(a: &[Vec<bool>], b: &[Vec<bool>]) -> Type {
    let n = a.len();
    let d = a[0].len();
    let m = b[0].len();
    let dom = |size: usize| (0..size).fold(Type::empty(), |s, i| &s | &lit(i as i64));
    let p = cons_of(dom(n), cons_of(dom(m), Type::atom("nil")));
    let mut neg = Type::empty();
    for (q, bq) in b.iter().enumerate().take(d) {
        let ah = a
            .iter()
            .enumerate()
            .filter(|(_, ai)| ai[q])
            .fold(Type::empty(), |s, (i, _)| &s | &lit(i as i64));
        let bh = bq
            .iter()
            .enumerate()
            .filter(|(_, bit)| **bit)
            .fold(Type::empty(), |s, (j, _)| &s | &lit(j as i64));
        neg = &neg | &cons_of(ah, cons_of(bh, Type::atom("nil")));
    }
    &p - &neg
}

#[test]
fn r10_ov_selector_reduction_matches_every_small_matrix_and_pair() {
    big(|| {
        let (n, d) = (3usize, 2usize);
        let mut words = 0;
        for am in 0..1usize << (n * d) {
            for bm in 0..1usize << (n * d) {
                let a: Vec<Vec<bool>> = (0..n)
                    .map(|i| (0..d).map(|q| am >> (i * d + q) & 1 != 0).collect())
                    .collect();
                let b: Vec<Vec<bool>> = (0..d)
                    .map(|q| (0..n).map(|j| bm >> (q * n + j) & 1 != 0).collect())
                    .collect();
                let t = r10_ov_selector_type(&a, &b);
                for (i, ai) in a.iter().enumerate() {
                    for (j, _) in b[0].iter().enumerate() {
                        let orthogonal = !(0..d).any(|q| ai[q] && b[q][j]);
                        assert_eq!(
                            t.contains(&r6_colour_list(&[i as i64, j as i64])),
                            orthogonal,
                            "A mask {am}, B mask {bm}, pair {i}/{j}"
                        );
                        words += 1;
                    }
                }
            }
        }
        let a = vec![vec![true; d]; n];
        assert_eq!(
            r10_ov_selector_type(&a, &vec![vec![true; n]; d]).verdict(),
            Verdict::Empty
        );
        assert_eq!(
            r10_ov_selector_type(&a, &vec![vec![false; n]; d]).verdict(),
            Verdict::Inhabited
        );
        eprintln!("R10 OV: 4096 matrix pairs, {words} exact selector-word checks");
    });
}

/// The naive compact rectangular version of the r9 shift encoding. Root heights
/// collide when the vector count exceeds the dimension; it is used only to test
/// that proposed reduction, never as a kernel algorithm.
fn r10_rectangular_shift(a: &[Vec<bool>], b: &[Vec<bool>], tag: &str) -> Type {
    let nr = a.len();
    let dim = a[0].len();
    let nc = b[0].len();
    let ek = |k: usize| k * (dim + 1) + dim;
    let top = ek(nc - 1) + 1 + (nr - 1) * dim;
    let mut holes = vec![None; top + 1];
    for k in 0..nc {
        for (q, bq) in b.iter().enumerate() {
            if bq[k] {
                holes[ek(k) - q] = Some(100 + q as i64);
            }
        }
    }
    let mut defs = vec![def(
        &format!("L{tag}"),
        Expr::Union(vec![nil(), cons(int(), r(0))]),
    )];
    for (e, hole) in holes.iter().enumerate().skip(1) {
        let h = match hole {
            Some(v) => &Type::int() - &lit(*v),
            None => Type::int(),
        };
        defs.push(def(&format!("F{e}{tag}"), cons(Expr::Type(h), r(e - 1))));
    }
    let mut p = nil();
    for j in (1..=top).rev() {
        let h = if (2..2 + nr * dim).contains(&j) && a[(j - 2) / dim][(j - 2) % dim] {
            &lit(7) | &lit(100 + ((j - 2) % dim) as i64)
        } else {
            lit(7)
        };
        p = cons(Expr::Type(h), p);
    }
    defs.push(def(&format!("P{tag}"), p));
    let ts = u4_inst(defs);
    let mut neg = Type::empty();
    for i in 0..nr {
        for k in 0..nc {
            neg = &neg | &ts[ek(k) + 1 + i * dim];
        }
    }
    &ts[top + 1] - &neg
}

#[test]
fn r10_low_dimension_shift_collisions_mask_an_orthogonal_pair() {
    big(|| {
        let a = vec![
            vec![true, false],
            vec![true, true],
            vec![true, true],
            vec![false, true],
        ];
        let b = vec![vec![true, true, false, true], vec![true, true, true, true]];
        let zeroes: Vec<_> = a
            .iter()
            .enumerate()
            .flat_map(|(i, ai)| {
                (0..4)
                    .filter(|&k| !(0..2).any(|q| ai[q] && b[q][k]))
                    .map(move |k| (i, k))
                    .collect::<Vec<_>>()
            })
            .collect();
        assert_eq!(zeroes, vec![(0, 2)]);
        let height = |i: usize, k: usize| k * 3 + 3 + i * 2;
        assert_eq!(height(0, 2), height(3, 0));
        let t = r10_rectangular_shift(&a, &b, "_r10collision");
        let mut xs = vec![7; 18];
        for (i, ai) in a.iter().enumerate() {
            for (q, &bit) in ai.iter().enumerate() {
                if bit {
                    xs[1 + i * 2 + q] = 100 + q as i64;
                }
            }
        }
        assert!(t.contains(&r6_colour_list(&xs)));
        assert_eq!(t.verdict(), Verdict::Inhabited); // AB is nevertheless not all ones.
        let none = r10_rectangular_shift(&a, &vec![vec![false; 4]; 2], "_r10collision_no");
        assert!(!none.contains(&r6_colour_list(&xs)));
        assert_eq!(none.verdict(), Verdict::Empty);
    });
}

/// R10-C3: a nine-node list whose answer changed since 19bc4e25; cause still open.
fn r10_precision_case(tag: &str, reverse: bool) -> Type {
    let raw = [
        (true, 63, 0),
        (false, 2, 0),
        (false, 59, 1),
        (false, 40, 2),
        (true, 61, 0),
        (true, 61, 4),
        (true, 25, 5),
        (true, 61, 6),
        (false, 47, 3),
    ];
    let ns: Vec<_> = raw
        .iter()
        .map(|&(stop, mask, next)| R3Node { stop, mask, next })
        .collect();
    assert!(r3_oracle(&ns, &[1, 2, 3, 7, 8], 63));
    r3_build(&ns, &[1, 2, 3, 7, 8], 63, reverse, tag, 0)
}

#[test]
#[ignore = "R10-C3: Inhabited on 19bc4e25; Fork on 27a5b72b4"]
fn r10_answer_preservation_nine_node_list_regression() {
    big(|| {
        for reverse in [false, true] {
            Type::forget_emptiness();
            let t = r10_precision_case("r10precision", reverse);
            assert_eq!(t.verdict(), Verdict::Inhabited);
            assert!(t.contains(&r6_colour_list(&[0, 2])));
            assert!(!t.contains(&r6_colour_list(&[])));
            assert!(!t.contains(&r6_colour_list(&[0])));
        }
        let inner = r10_precision_case("r10precisionwidth", false);
        let a = Type::tuple(vec![inner.clone(); 8]);
        let b = Type::tuple(vec![inner; 64]);
        scaling::check(
            "preserving a prefix witness in shared list fields",
            8,
            |n| {
                Type::forget_emptiness();
                assert_eq!((if n == 8 { &a } else { &b }).verdict(), Verdict::Inhabited);
            },
        );
    });
}

/// R10-C4: many tags share one positive union of diagonal scalar tuples.
fn r10_shared_payloads(n: usize, tag: &str) -> Type {
    let payload = (0..n).fold(Type::empty(), |p, i| {
        let h = lit(i as i64);
        &p | &Type::tuple(vec![h.clone(), h])
    });
    (0..n).fold(Type::empty(), |t, i| {
        &t | &Type::atom_with(&format!("r10tag{i}{tag}"), &payload)
    })
}

#[test]
#[ignore]
fn r10_shared_payload_probe() {
    let sizes = std::env::var("RFX_N").unwrap_or("16,64,256,1024".into());
    big(move || {
        for n in sizes.split(',').map(|s| s.parse::<usize>().unwrap()) {
            Type::forget_emptiness();
            let tag = format!("_shared{n}");
            let t = r10_shared_payloads(n, &tag);
            let mut v = None;
            let mut meter = scaling::Meter::new();
            let w = meter.work(|| v = Some(t.verdict()));
            assert_eq!(v, Some(Verdict::Inhabited));
            assert!(t.contains(&Value::atom_with(
                format!("r10tag0{tag}"),
                vec![Value::Int(0), Value::Int(0)]
            )));
            assert!(!t.contains(&Value::atom_with(
                format!("r10tag0{tag}"),
                vec![Value::Int(0), Value::Int(1)]
            )));
            eprintln!("R10PAYLOAD n {n} {v:?} units {} bytes {}", w.units, w.bytes);
        }
    });
}

#[test]
fn r10_shared_payload_rows_must_scale() {
    big(|| {
        let a = r10_shared_payloads(32, "_payload32");
        let b = r10_shared_payloads(256, "_payload256");
        scaling::check("tags sharing one tuple payload diagram", 32, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 32 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
    });
}

/// R11-C1 (kind 3): the group-dependency walk must not read all bare names of
/// each prefix of a persistent union. The written name-map DAG is shared.
fn r11_failure_prefixes(n: usize) -> Type {
    let mut a = Type::empty();
    let fields = (0..n)
        .map(|i| {
            a = &a | &Type::atom(&format!("r11_failure_{i}"));
            a.clone()
        })
        .collect();
    Type::tuple(fields)
}

#[test]
fn r11_group_reads_skip_bare_atom_names_and_scale() {
    big(|| {
        let a = r11_failure_prefixes(128);
        let b = r11_failure_prefixes(1024);
        scaling::check(
            "group dependencies of shared failure-atom prefixes",
            128,
            |n| {
                Type::forget_emptiness();
                assert_eq!(
                    (if n == 128 { &a } else { &b }).verdict(),
                    Verdict::Inhabited
                );
            },
        );
    });
}

#[test]
#[ignore]
fn r11_failure_prefix_probe() {
    big(|| {
        for n in [16, 64, 256, 1024] {
            let t = r11_failure_prefixes(n);
            Type::forget_emptiness();
            let mut m = scaling::Meter::new();
            let w = m.work(|| assert_eq!(t.verdict(), Verdict::Inhabited));
            eprintln!("R11FAIL n {n} units {} bytes {}", w.units, w.bytes);
        }
    });
}

/// A tagged version of C4: every row component has atoms, all under a name
/// different from the many outer tags. It is still one shared payload diagram.
fn r11_tagged_payloads(n: usize) -> Type {
    let payload = (0..n).fold(Type::empty(), |p, i| {
        let h = Type::atom_with("inner", &Type::tuple(vec![lit(i as i64)]));
        &p | &Type::tuple(vec![h.clone(), h])
    });
    (0..n).fold(Type::empty(), |t, i| {
        &t | &Type::atom_with(&format!("r11outer{i}"), &payload)
    })
}

#[test]
#[ignore]
fn r11_tagged_payload_probe() {
    big(|| {
        for n in [16, 64, 256, 1024] {
            let t = r11_tagged_payloads(n);
            Type::forget_emptiness();
            let mut m = scaling::Meter::new();
            let w = m.work(|| assert_eq!(t.verdict(), Verdict::Inhabited));
            eprintln!("R11TAG n {n} units {} bytes {}", w.units, w.bytes);
        }
    });
}

#[test]
fn r11_front_end_keeps_wide_integer_literals() {
    use zed_tests::step_helpers::l01_26_type_resolution::info;
    for digits in [
        "9223372036854775807",
        "9223372036854775808",
        "18446744073709551616",
    ] {
        let text = format!("x = {digits};\ny = (x, x);\n");
        let (i, _) = info(&text);
        assert!(i.errors.is_empty(), "{digits}: {:?}", i.errors);
        let got = i.tops["x"].to_string();
        eprintln!("front literal {digits}: {got}");
        assert_ne!(got, "Never");
        let read = zedc::check::read::parse_type(digits).unwrap();
        assert_eq!(read.to_string(), digits);
        // A nearby value must remain a different printed singleton.
        assert_ne!(read.to_string(), "0");
    }
}

#[test]
fn r11_boolean_tail_two_links_down() {
    big(|| {
        for depth in [2, 3, 8] {
            for (case, want) in [("chain", Verdict::Empty), ("r5remout", Verdict::Inhabited)] {
                let mut t = rfx_case(case, 8, "_r11tail");
                for _ in 0..depth {
                    t = cons_of(Type::int(), t);
                }
                Type::forget_emptiness();
                assert_eq!(t.verdict(), want, "{case}, depth {depth}");
            }
        }
    });
}

#[test]
fn r11_boolean_tail_behind_literal_prefix_scales() {
    big(|| {
        let make = |n| {
            let mut t = rfx_case("r5remout", 8, "_r11deepscale");
            for _ in 0..n {
                t = cons_of(Type::int(), t);
            }
            t
        };
        let a = make(32);
        let b = make(256);
        scaling::check("Boolean list boundary behind a literal prefix", 32, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 32 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
    });
}

#[test]
#[ignore]
fn r11_literal_prefix_probe() {
    big(|| {
        for n in [16, 64, 256, 1024] {
            let mut t = rfx_case("r5remout", 8, "_r11prefixprobe");
            for _ in 0..n {
                t = cons_of(Type::int(), t);
            }
            Type::forget_emptiness();
            let mut m = scaling::Meter::new();
            let w = m.work(|| assert_eq!(t.verdict(), Verdict::Inhabited));
            let mut word = vec![0; n];
            word.extend([5, 1, 1]);
            assert!(t.contains(&r6_colour_list(&word)));
            eprintln!("R11PREFIX n {n} units {} bytes {}", w.units, w.bytes);
        }
    });
}

#[test]
fn r11_wide_literals_agree_in_a_batch_and_separate_files() {
    use zed_tests::step_helpers::l01_26_type_resolution::info;
    let literals = ["9223372036854775808", "18446744073709551616"];
    let text = literals
        .iter()
        .enumerate()
        .map(|(i, n)| format!("x{i} = {n};\n"))
        .collect::<String>();
    let (batch, _) = info(&text);
    assert!(batch.errors.is_empty(), "{:?}", batch.errors);
    for (i, n) in literals.iter().enumerate() {
        let (single, _) = info(&format!("x{i} = {n};\n"));
        assert!(single.errors.is_empty(), "{:?}", single.errors);
        let name = format!("x{i}");
        assert_eq!(
            batch.tops[&name].to_string(),
            single.tops[&name].to_string()
        );
        assert_eq!(single.tops[&name].to_string(), *n);
    }
}

/// R11-C3: payload-bearing name prefixes share their persistent maps too.
fn r11_payload_name_prefixes(n: usize) -> Type {
    let payload = Type::tuple(vec![lit(0)]);
    let mut a = Type::empty();
    let fields = (0..n)
        .map(|i| {
            a = &a | &Type::atom_with(&format!("r11_named_{i}"), &payload);
            a.clone()
        })
        .collect();
    Type::tuple(fields)
}

#[test]
#[ignore]
fn r11_payload_name_prefix_probe() {
    big(|| {
        for n in [16, 64, 256, 1024] {
            let t = r11_payload_name_prefixes(n);
            Type::forget_emptiness();
            let mut m = scaling::Meter::new();
            let w = m.work(|| assert_eq!(t.verdict(), Verdict::Inhabited));
            eprintln!("R11NAMES n {n} units {} bytes {}", w.units, w.bytes);
        }
    });
}

#[test]
#[ignore = "R11-C3: payload-bearing prefixes still reread a shared persistent name map"]
fn r11_payload_name_prefixes_must_scale() {
    big(|| {
        let a = r11_payload_name_prefixes(128);
        let b = r11_payload_name_prefixes(1024);
        scaling::check("shared payload-bearing name prefixes", 128, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 128 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
    });
}

/// A ternary-density alignment family: one row class has only the final two
/// coordinates, two classes have every coordinate. Every product entry is 1.
#[test]
#[ignore]
fn r11_ternary_alignment_probe() {
    big(|| {
        for n in [16usize, 64, 256, 1024, 4096] {
            let m = n.isqrt().max(4);
            let a: Vec<Vec<bool>> = (0..m)
                .map(|i| (0..m).map(|q| i % 3 != 0 || q >= m - 2).collect())
                .collect();
            let b = vec![vec![true; m]; m];
            assert!(r9_product_all_ones(&a, &b));
            let t = r9_bmm(&a, &b, &format!("_r11ternary{n}"));
            Type::forget_emptiness();
            let mut meter = scaling::Meter::new();
            let work = meter.work(|| assert_eq!(t.verdict(), Verdict::Inhabited));
            let l0 = (m - 1) * (m + 1) + m + 1 + (m - 1) * m;
            let word: Vec<i64> = (1..=l0)
                .map(|j| {
                    if (2..2 + m * m).contains(&j) && a[(j - 2) / m][(j - 2) % m] {
                        100 + ((j - 2) % m) as i64
                    } else {
                        7
                    }
                })
                .collect();
            assert!(t.contains(&r6_colour_list(&word)));
            eprintln!(
                "R11TERN n {n} units {} cells {:?}",
                work.units,
                t.escape_cell_counts()
            );
        }
    });
}

#[test]
fn r11_fields_within_a_list_item_are_admitted_as_written_fields() {
    big(|| {
        for n in [3, 4, 8, 16] {
            let inner = rfx_case("r5remout", n, "_r11mapitem");
            assert!(inner.contains(&r6_colour_list(&[5, 1, 1])));
            let map = Type::morphism(lit(0), Type::int(), inner);
            assert_eq!(&lit(0) - &Type::int(), Type::empty());
            Type::forget_emptiness();
            assert_eq!(map.verdict(), Verdict::Inhabited);
            let t = cons_of(map, list_named(Type::top(), "_r11outermapitem"));
            Type::forget_emptiness();
            assert_eq!(t.verdict(), Verdict::Inhabited, "map item at {n}");
        }
    });
}

#[test]
fn r11_tuple_fields_within_list_items_scale() {
    big(|| {
        let a = rfx_case("listhead:pairfar", 32, "_r11pairitem32");
        let b = rfx_case("listhead:pairfar", 256, "_r11pairitem256");
        scaling::check("tuple fields within a list item", 32, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 32 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
    });
}

#[test]
fn r11_item_field_scopes_agree_alone_forward_and_reverse() {
    fn make() -> Vec<Type> {
        ["listhead:pairfar", "listhead:r10mapvalue"]
            .iter()
            .map(|c| rfx_case(c, 8, "_r11scopeorder"))
            .collect()
    }
    big(|| {
        let types = make();
        Type::forget_emptiness();
        let batch: Vec<_> = types.iter().map(|t| (t.is_empty(), t.verdict())).collect();
        Type::forget_emptiness();
        let mut reverse: Vec<_> = types
            .iter()
            .rev()
            .map(|t| (t.is_empty(), t.verdict()))
            .collect();
        reverse.reverse();
        let alone: Vec<_> = (0..types.len())
            .map(|i| {
                std::thread::Builder::new()
                    .stack_size(16 * 1024 * 1024)
                    .spawn(move || {
                        let t = make().swap_remove(i);
                        (t.is_empty(), t.verdict())
                    })
                    .unwrap()
                    .join()
                    .unwrap()
            })
            .collect();
        assert_eq!(batch, vec![(false, Verdict::Inhabited); types.len()]);
        assert_eq!(reverse, batch);
        assert_eq!(alone, batch);
    });
}

/// R11 probe for the name loop of `decide_groups_read`'s walk: n distinct types `E | i`, each
/// holding the same n atom names, as the components of n tuples. Each type is walked once, and
/// the walk reads all n names of each, so the walk alone does n^2 steps if no other part of the
/// decider already does.
fn r11_names_family(n: usize, tag: &str) -> Type {
    let e = (0..n).fold(Type::empty(), |t, i| {
        &t | &Type::atom(&format!("r11e{i}{tag}"))
    });
    (0..n).fold(Type::empty(), |t, i| {
        let c = &e | &lit(i as i64);
        &t | &Type::tuple(vec![c.clone(), c])
    })
}

#[test]
#[ignore]
fn r11_many_names_probe() {
    let sizes = std::env::var("RFX_N").unwrap_or("16,64,256,1024".into());
    big(move || {
        for n in sizes.split(',').map(|s| s.parse::<usize>().unwrap()) {
            Type::forget_emptiness();
            let t = r11_names_family(n, &format!("_n{n}"));
            let mut v = None;
            let mut meter = scaling::Meter::new();
            let w = meter.work(|| v = Some(t.verdict()));
            assert_eq!(v, Some(Verdict::Inhabited));
            eprintln!("R11NAMES n {n} {v:?} units {} bytes {}", w.units, w.bytes);
        }
    });
}

#[test]
fn r11_many_names_must_scale() {
    big(|| {
        let a = r11_names_family(32, "_s32");
        let b = r11_names_family(256, "_s256");
        scaling::check("types sharing many atom names", 32, |n| {
            Type::forget_emptiness();
            assert_eq!(
                (if n == 32 { &a } else { &b }).verdict(),
                Verdict::Inhabited
            );
        });
    });
}

/// R11 probe for what the R10-C4 memo leaves: n tags sharing one payload diagram whose n rows
/// each hold a component with an atom name, which every tag still reads.
#[test]
#[ignore]
fn r11_named_payload_probe() {
    let sizes = std::env::var("RFX_N").unwrap_or("16,64,256,1024".into());
    big(move || {
        for n in sizes.split(',').map(|s| s.parse::<usize>().unwrap()) {
            Type::forget_emptiness();
            let payload = (0..n).fold(Type::empty(), |p, i| {
                &p | &Type::tuple(vec![Type::atom(&format!("r11q{i}_{n}")), lit(i as i64)])
            });
            let t = (0..n).fold(Type::empty(), |t, i| {
                &t | &Type::atom_with(&format!("r11tag{i}_{n}"), &payload)
            });
            let mut v = None;
            let mut meter = scaling::Meter::new();
            let w = meter.work(|| v = Some(t.verdict()));
            assert_eq!(v, Some(Verdict::Inhabited));
            eprintln!("R11NAMED n {n} {v:?} units {} bytes {}", w.units, w.bytes);
        }
    });
}

/// `fork_empty` with the lists of `2i + 1` and `2i + 2` in place of those of 1 and 2: a type for
/// each `i`, each refused for its fork.
fn fork_empty_at(i: i64) -> Type {
    let l = list(Type::int());
    let pair = |a: Type, b: Type| Type::tuple(vec![a, b]);
    let (ones, twos) = (list(lit(2 * i + 1)), list(lit(2 * i + 2)));
    [
        pair(ones.clone(), period(2, 0)),
        pair(twos.clone(), period(2, 1)),
        pair(&l - &ones, period(2, 0)),
        pair(&l - &twos, period(2, 1)),
    ]
    .iter()
    .fold(pair(l.clone(), l.clone()), |t, x| &t - x)
}

/// The meet `(int, int) & (bool, int)`: empty, as its first component is no value.
fn pair_meet_empty() -> Type {
    &Type::tuple(vec![Type::int(), Type::int()]) & &Type::tuple(vec![Type::bool(), Type::int()])
}

#[test]
fn a_tuple_with_an_empty_component_is_empty_in_either_order() {
    // A tuple is empty when one of its components is. The search of a verdict ends at the
    // first fork it meets, so with the forked `fork_empty` first and an empty component after
    // it the tuple was refused (Fork), and in the other order empty. A search that sets the
    // fork aside and tries the later components proves it empty in both orders. Measured on
    // r5-base e82e6cff: `(F, E)` Refused(Fork), `(E, F)` Empty.
    let (fork, empty) = (fork_empty(), pair_meet_empty());
    for t in [
        Type::tuple(vec![fork.clone(), empty.clone()]),
        Type::tuple(vec![empty.clone(), fork.clone()]),
        Type::tuple(vec![fork.clone(), fork.clone(), empty.clone()]),
    ] {
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Empty, "{t}");
        Type::forget_emptiness();
        assert!(t.is_empty(), "{t}");
    }
    // With no empty component the fork still refuses the tuple.
    Type::forget_emptiness();
    let t = Type::tuple(vec![fork.clone(), Type::int()]);
    assert_eq!(t.verdict(), Verdict::Refused(Refusal::Fork), "{t}");
    // n forked components before the empty one: the second search sets each fork aside once.
    big(|| {
        scaling::check("Empty, n forked components and an empty one", 8, |n| {
            Type::forget_emptiness();
            let mut parts: Vec<Type> = (0..n as i64).map(fork_empty_at).collect();
            parts.push(pair_meet_empty());
            let t = Type::tuple(parts);
            assert_eq!(t.verdict(), Verdict::Empty, "at {n}");
        });
    });
}

/// The second blame search must walk n distinct forked components before the
/// empty component. Both presentations and both public routes are measured;
/// constructing the groups and tuples is outside the counters.
#[test]
fn a_chain_of_forks_before_an_empty_component_scales() {
    let n = 8;
    let inputs = scaling::inputs(n, |k| {
        let mut parts: Vec<Type> = (0..k as i64).map(fork_empty_at).collect();
        parts.push(pair_meet_empty());
        let last = Type::tuple(parts.clone());
        parts.reverse();
        [last, Type::tuple(parts)]
    });
    scaling::check_order(
        "second blame search over distinct forked components",
        n,
        1,
        |k| {
            for t in &inputs[&k] {
                Type::forget_emptiness();
                assert_eq!(t.verdict(), Verdict::Empty);
                Type::forget_emptiness();
                assert!(t.is_empty());
            }
        },
    );
}

/// Independent finite-set checks with a mathematically empty fork as one
/// leaf. No closure or recursive-list approximation is used by this model.
#[test]
fn standalone_empty_proofs_agree_with_finite_sets_beside_forks() {
    use std::collections::BTreeSet;
    let inputs: Vec<(Type, BTreeSet<Value>)> = vec![
        (fork_empty(), BTreeSet::new()),
        (pair_meet_empty(), BTreeSet::new()),
        (Type::empty(), BTreeSet::new()),
        (lit(0), BTreeSet::from([Value::Int(0)])),
        (lit(1), BTreeSet::from([Value::Int(1)])),
        (
            &lit(0) | &lit(1),
            BTreeSet::from([Value::Int(0), Value::Int(1)]),
        ),
    ];
    let mut checked = 0;
    for (a, av) in &inputs {
        for (b, bv) in &inputs {
            let pairs: BTreeSet<Value> = av
                .iter()
                .flat_map(|x| {
                    bv.iter()
                        .map(move |y| Value::tuple(vec![x.clone(), y.clone()]))
                })
                .collect();
            for (t, values) in [
                (a | b, av.union(bv).cloned().collect()),
                (a & b, av.intersection(bv).cloned().collect()),
                (a - b, av.difference(bv).cloned().collect()),
                (Type::tuple(vec![a.clone(), b.clone()]), pairs),
            ] {
                Type::forget_emptiness();
                let v = t.verdict();
                Type::forget_emptiness();
                let e = t.is_empty();
                assert!(
                    (v != Verdict::Empty && !e) || values.is_empty(),
                    "{t}: {v:?}"
                );
                for value in &values {
                    assert!(t.contains(value));
                }
                checked += 1;
            }
        }
    }
    eprintln!("STANDALONE finite-set checks {checked}");
}

/// `(F0, (F1, ... (F(n-1), E)))`: `n` forked components `fork_empty_at(i)`, each met before the
/// nested tuple that holds the empty component `pair_meet_empty()`.
fn forks_nested_before_empty(n: usize) -> Type {
    (0..n as i64).rev().fold(pair_meet_empty(), |t, i| {
        Type::tuple(vec![fork_empty_at(i), t])
    })
}

#[test]
fn a_chain_of_forks_nested_before_an_empty_component_is_empty_in_its_size() {
    // The search of a verdict ends at the first fork; the second search (`empty_past_forks`)
    // sets the fork in each of the n nested tuples aside once and reaches the empty component.
    big(|| {
        let inputs = scaling::inputs(8, forks_nested_before_empty);
        scaling::check_order(
            "Empty, n forks nested before an empty component",
            8,
            1,
            |n| {
                Type::forget_emptiness();
                assert_eq!(inputs[&n].verdict(), Verdict::Empty, "at {n}");
            },
        );
    });
}

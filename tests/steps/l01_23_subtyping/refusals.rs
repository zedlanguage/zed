//! Refusals: a check the strict search does not decide, and for which no value is found, is
//! refused with its cause, and claims nothing about the type. A value is sought before any
//! refusal, so an inhabited type is never refused when a value is in reach. Each cause has its
//! own message, and the checker adds it to a message that a type is not within another, so a
//! refusal never reads as a counterexample. Equal plain definitions of different groups are
//! one type.

use std::collections::BTreeSet;

use zed_kernel::Value;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Refusal, Type, Verdict};
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
        Refusal::MorphismSplit,
        Refusal::NoWitness,
    ];
    let messages: BTreeSet<&str> = all.iter().map(|r| r.message()).collect();
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
        format!(" (not decided: {})", Refusal::Residues.message())
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
            "2:52: `g` does not take ({triple}) (not decided: {})",
            Refusal::TupleSplit.message()
        )
    );
    // A decided failure names no cause.
    assert_eq!(
        rejected(&box_program(6)),
        format!("2:52: `g` does not take ({triple})")
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
        "2:28: `g` does not take ((#a | #b | #c, #c))"
    );
}

#[test]
fn a_morphism_type_whose_bound_check_was_refused_says_why() {
    // A function into `#a | #b` that gives both is in neither union member, but the kernel
    // shows no family against a morphism type before L2, and splits no function part. The
    // `is` is an error of its own: the bound check no longer stops elaboration of the type.
    let src = "f(x) = x is ((int -> #a | #b) .. ((int -> #a) | (int -> #b)) -> int);";
    assert_eq!(
        crate::l01_16_elaboration::errors(src),
        [
            "`is` cannot test a value against a function type at run time \
             [((int -> #a | #b) .. ((int -> #a) | (int -> #b)) -> int)]"
                .to_string(),
            format!(
                "the guarantee (left of `..`) of this morphism type is not within its permission \
             (right of `..`) (not decided: {}) [((int -> #a | #b) .. ((int -> #a) | (int -> #b)) -> int)]",
                Refusal::MorphismSplit.message()
            )
        ]
    );
}

/// The errors of the operator `op` applied to `args`, through the checker's `apply`.
fn operator_errors(op: &str, args: &[Ty]) -> Vec<String> {
    zedc::check::operator(op, args).1
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
                    let tail = format!(" (not decided: {})", r.message());
                    assert!(first.ends_with(&tail), "{op} on {t}: {first}");
                }
                None => assert!(!first.contains("not decided"), "{op} on {t}: {first}"),
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
        "2:10: `g` does not take (1)"
    );
    // What a use of an argument gives against what the use needs: decided here. The
    // checker's own types hold no difference of tuples (a written `\` of tuples is dropped
    // from them), so no refused check reaches this path from a program.
    assert_eq!(
        rejected("f(x) = x[1] + 1;\nmain() = f(x: (1, \"s\"));\n"),
        "2:10: `f` gives \"s\" here, which is not int"
    );
}

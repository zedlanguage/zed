//! A member of a recursive group that the group's decider refuses (DESIGN.md L1.23, item
//! GROUP-refusal): a component mixing cycles through tuples and through function results, with
//! two or more independent cycles and a tuple with two undecided components, is refused with a
//! message naming the definition, the definitions taking part, the cycles, the tuple and a
//! repair that a re-check confirms, when the search for a value, which every member the decider
//! leaves open goes to, does not decide it either. The rest of the group stays on the decider:
//! a part the decider does not take is a leaf, decided with it empty and with it inhabited.

use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Refusal, Type, Verdict};
use zed_tests::scaling;

fn r(i: usize) -> Expr {
    Expr::Ref(i, vec![])
}

fn int() -> Expr {
    Expr::Type(Type::int())
}

/// `(int) -> x`.
fn f(x: Expr) -> Expr {
    Expr::exact(int(), x)
}

fn pair(a: Expr, b: Expr) -> Expr {
    Expr::Tuple(vec![a, b])
}

fn or(xs: Vec<Expr>) -> Expr {
    Expr::Union(xs)
}

fn atom(name: &str, items: Vec<Expr>) -> Expr {
    Expr::Atom(name.into(), items)
}

/// The group of `defs`, instantiated with no arguments.
fn group(defs: Vec<(String, Expr)>) -> Vec<Type> {
    let defs = (defs.into_iter())
        .map(|(name, body)| Def {
            name,
            params: vec![],
            body,
        })
        .collect();
    Group::new(defs)
        .map(|g| g.instance(vec![]))
        .unwrap_or_else(|e| panic!("{}", e.message))
}

/// The three definitions
///
/// ```text
/// type A = (#k, C & A) | (B & (_, _), (int) -> C)
/// type B = ((int) -> C & (_, _)) | (B & ((int) -> C), B) | (A & (_, _),)
/// type C = (B & (_, _), B) | ((int) -> A)
/// ```
///
/// with the names suffixed by `tag` and definition k at `at[k]`. Each has a value, which the
/// search for values does not build: with `b = λ_. (p, b)` and `p = (b, b)`, `b` is a value of
/// `B`, `(p, b)` of `C`, and `(p, λ_. (p, b))` of `A` (a function may return a value that holds
/// it). The search does not build a value of the meet of a tuple type with `(_, _)`
/// (GROUP-search-meet-values), so the decider refuses them all, in each order of the
/// definitions. Seed 219 of `group_oracle`'s meets family. Until GROUP-closure-order this
/// fixture was a group of four of the X14 shape, without meets; the search now builds a value of
/// each member of it, and of every group of four, five and six definitions of that shape tried
/// (see [`the_former_fixtures_are_inhabited`]).
fn refused(tag: &str, at: [usize; SIZE]) -> [(String, Expr); SIZE] {
    let [a, b, c] = at.map(r);
    let k = || Expr::Type(Type::atom("k"));
    let and = |x: Expr, y: Expr| Expr::And(vec![x, y]);
    let two = || Expr::Type(Type::tuple(vec![Type::top(), Type::top()]));
    [
        (
            format!("A{tag}"),
            or(vec![
                pair(k(), and(c.clone(), a.clone())),
                pair(and(b.clone(), two()), f(c.clone())),
            ]),
        ),
        (
            format!("B{tag}"),
            or(vec![
                f(and(c.clone(), two())),
                pair(and(b.clone(), f(c.clone())), b.clone()),
                Expr::Tuple(vec![and(a.clone(), two())]),
            ]),
        ),
        (
            format!("C{tag}"),
            or(vec![pair(and(b.clone(), two()), b), f(a)]),
        ),
    ]
}

/// The number of definitions of [`refused`].
const SIZE: usize = 3;

/// The places of the definitions of copy `c` of [`refused`], one copy after another.
fn copy(c: usize) -> [usize; SIZE] {
    std::array::from_fn(|i| SIZE * c + i)
}

/// The definitions of [`refused`] in the order of `at`.
fn placed(at: [usize; SIZE]) -> Vec<(String, Expr)> {
    let mut defs: Vec<Option<(String, Expr)>> = vec![None; SIZE];
    for (k, def) in refused("", at).into_iter().enumerate() {
        defs[at[k]] = Some(def);
    }
    defs.into_iter().map(Option::unwrap).collect()
}

const IN_ORDER: [usize; SIZE] = [0, 1, 2];
const ROTATED: [usize; SIZE] = [2, 0, 1];

/// The refusal of `t`'s verdict, with its message.
fn message(t: &Type) -> String {
    assert_eq!(t.verdict(), Verdict::Refused(Refusal::Group));
    let site = t.refusal_site(Refusal::Group).expect("a refused member");
    site.detail.expect("the decider's reason")
}

/// The members go to the search, which decides none of them; before this item the search's own
/// cause was given, so the first assertion fails there.
#[test]
fn a_mixed_component_is_refused_with_its_own_message() {
    Type::forget_emptiness();
    let types = group(placed(IN_ORDER));
    for t in &types {
        assert_eq!(t.verdict(), Verdict::Refused(Refusal::Group));
        assert_eq!(t.decided_by_group(), None);
        assert!(!t.is_empty(), "a refused member counts as inhabited");
    }
    let m = message(&types[0]);
    let site = types[0].refusal_site(Refusal::Group).unwrap();
    assert_eq!(site.head, "A");
    assert_eq!(
        site.defs,
        [
            "type A = (#k, C & A) | (B & (_, _), (int) -> C);",
            // MSG-derive-type-size: a tuple with no part of its own is written in full wherever
            // it stands, as `A` and `C` write it. Before, `B`, which writes `(_, _)` twice,
            // named it `T1`, declared after the definitions (PRINT-fmt-audit,
            // PRINT-group-site-defs): `type B = ((int) -> C & T1) | (B & ((int) -> C), B) |
            // (A & T1,);` and `type T1 = (_, _);`.
            "type B = ((int) -> C & (_, _)) | (B & ((int) -> C), B) | (A & (_, _),);",
            "type C = (B & (_, _), B) | ((int) -> A);",
        ]
    );
    // The lines read as declarations at the top level of a file.
    let unit = site.defs.join("\n");
    let tokens = zedc::lex::lex_fence(&unit).unwrap_or_else(|e| panic!("{unit}: {e:?}"));
    zedc::parse::parse(&unit, &tokens, "Unit", zedc::parse::TOP)
        .unwrap_or_else(|e| panic!("{unit}: {e:?}"));
    assert_eq!(
        m,
        "deciding whether `A` has a value needs the definitions `A`, `B` and `C` together; `A` \
         refers to `B`, `C` and itself; `B` refers to `A`, `C` and itself; `C` refers to `A` and \
         `B`; these references make 6 independent cycles; some of these cycles pass through a \
         tuple, which no value can go around forever since a value is finite, and some through \
         the result of a function type, which a value can, since a function can return without \
         calling itself; the tuple `(B & (_, _), (int) -> C)` in `A` needs a value of both \
         `B & (_, _)` and `(int) -> C`, and whether they have one is still open; the known ways \
         to settle such a group take time that grows with the square of its size, while the \
         checker decides each group in time linear in it, so it does not settle this one; a \
         search for a value of `A` then neither finds one nor shows that there is none, so the \
         checker counts `A` as possibly having a value; adding the case `| #end` to `A`, as in \
         `type A = (#k, C & A) | (B & (_, _), (int) -> C) | #end`, removes this obstacle, and \
         whether `A` has a value is then left to the search for one"
    );
    for (t, head) in types.iter().zip(["A", "B", "C"]) {
        assert_eq!(t.refusal_site(Refusal::Group).unwrap().head, head);
    }
}

#[test]
fn a_members_message_is_the_same_when_the_definitions_are_listed_in_another_order() {
    Type::forget_emptiness();
    let a = group(placed(IN_ORDER));
    let b = group(placed(ROTATED));
    for k in 0..SIZE {
        let (x, y) = (&a[k], &b[ROTATED[k]]);
        assert_eq!(message(x), message(y), "definition {k}");
        assert_eq!(
            x.refusal_site(Refusal::Group),
            y.refusal_site(Refusal::Group)
        );
    }
}

/// The repair the message offers is applied, and the group so written is no longer refused by
/// the decider: only a repair a re-check confirms is offered. Each member reads `A & (_, _)` or
/// `B & (_, _)`, so the decider's "inhabited" does not decide it (GROUP-setop) and the message
/// says the member is then left to the search; the search builds a value of `A` and of `C`, and
/// for `B` stops at a fork, though `B` has a value (see [`refused`], GROUP-search-meet-values).
/// No fixture now gives the other ending of the message, "lets the checker decide it".
#[test]
fn the_repair_offered_removes_the_group_refusal() {
    Type::forget_emptiness();
    let defs = placed(IN_ORDER);
    let types = group(defs.clone());
    for (k, t) in types.iter().enumerate() {
        let m = message(t);
        let (_, after) = (m.split_once("adding the case `| #end` to "))
            .unwrap_or_else(|| panic!("no repair offered: {m}"));
        // "`A`, as in `...`, removes ..." or "each of `A` and `B` removes ...".
        let named = after.split(", as in").next().unwrap();
        let named = named.split(" removes").next().unwrap();
        assert_eq!(named, "`A`", "{m}");
        let fixed: Vec<(String, Expr)> = (defs.iter())
            .map(|(name, body)| {
                let body = if named.contains(&format!("`{name}`")) {
                    or(vec![body.clone(), atom("end", vec![])])
                } else {
                    body.clone()
                };
                (name.clone(), body)
            })
            .collect();
        assert_ne!(fixed, defs, "{m}");
        Type::forget_emptiness();
        let fixed = group(fixed);
        let verdicts: Vec<_> = (fixed.iter())
            .map(|t| (t.decided_by_group(), t.verdict()))
            .collect();
        assert_eq!(
            verdicts,
            [
                (None, Verdict::Inhabited),
                (None, Verdict::Refused(Refusal::Fork)),
                (None, Verdict::Inhabited),
            ],
            "{} repaired",
            defs[k].0
        );
    }
}

/// A member decided by neither the decider nor the search for emptiness, whose value the search
/// for values builds, is inhabited: the refusal does not withhold a verdict that a value shows,
/// as it is not withheld from a type outside the group that reads the member. Seed 268 of the
/// X14 family sweep (`group_oracle`).
#[test]
fn a_refused_member_with_a_value_built_is_inhabited() {
    Type::forget_emptiness();
    let types = group(
        [
            or(vec![f(r(2)), pair(r(1), r(0))]),
            pair(r(4), r(0)),
            f(r(5)),
            or(vec![pair(r(2), r(4)), f(r(4))]),
            or(vec![f(r(5)), pair(r(3), r(5)), f(r(2))]),
            pair(r(2), r(3)),
        ]
        .into_iter()
        .enumerate()
        .map(|(i, body)| (format!("R{i}"), body))
        .collect(),
    );
    for t in &types {
        assert_eq!(t.decided_by_group(), None);
        assert_eq!(t.verdict(), Verdict::Inhabited);
    }
}

/// A refused member read through a meet: its message names the tuple, not the meet, and the
/// repair it offers leaves it to the search, since the decider's "inhabited" does not decide a
/// member read through a meet (GROUP-setop); applied, the repair removes the group refusal and
/// leaves every member to the search, as the message says. The search builds values of `A` and
/// `C`, and stops at a fork for `B` and for `Both`, which read `A & (_, _)`: it does not build a
/// value of the meet of a tuple type with `(_, _)` (GROUP-search-meet-values), though `A` has
/// one (see [`refused`]). With the former fixture the search built a value of `Both` here, which
/// exercised GROUP-refusal-meet-witness; this test no longer does.
#[test]
fn a_refused_member_read_through_a_meet_is_left_to_the_search_by_its_repair() {
    Type::forget_emptiness();
    let mut defs = placed(IN_ORDER);
    defs.push((
        "Both".into(),
        atom(
            "both",
            vec![
                r(0),
                Expr::And(vec![
                    r(0),
                    Expr::Type(Type::tuple(vec![Type::top(), Type::top()])),
                ]),
            ],
        ),
    ));
    let types = group(defs.clone());
    let m = message(&types[SIZE]);
    assert!(
        m.contains(
            "the tuple `(B & (_, _), (int) -> C)` in `A` needs a value of both `B & (_, _)` and \
             `(int) -> C`"
        ),
        "{m}"
    );
    assert!(
        m.ends_with(
            "adding the case `| #end` to `A`, as in `type A = (#k, C & A) | (B & (_, _), \
             (int) -> C) | #end`, removes this obstacle, and whether `Both` has a value is then \
             left to the search for one"
        ),
        "{m}"
    );
    defs[0].1 = or(vec![defs[0].1.clone(), atom("end", vec![])]);
    Type::forget_emptiness();
    let types = group(defs);
    let verdicts: Vec<_> = (types.iter())
        .map(|t| (t.decided_by_group(), t.verdict()))
        .collect();
    assert_eq!(
        verdicts,
        [
            (None, Verdict::Inhabited),
            (None, Verdict::Refused(Refusal::Fork)),
            (None, Verdict::Inhabited),
            (None, Verdict::Refused(Refusal::Fork)),
        ]
    );
}

/// A member that reads a refused component is refused with it, and a type outside the group
/// that reads a refused member points at that member; a member apart from the component stays
/// on the decider.
#[test]
fn a_reader_of_a_refused_member_points_at_it() {
    Type::forget_emptiness();
    let mut defs = placed(IN_ORDER);
    defs.push(("Box".into(), pair(int(), r(0))));
    defs.push((
        "List".into(),
        or(vec![
            atom("nil", vec![]),
            atom("cons", vec![int(), r(SIZE + 1)]),
        ]),
    ));
    let types = group(defs);
    assert_eq!(types[SIZE].verdict(), Verdict::Refused(Refusal::Group));
    let site = types[SIZE].refusal_site(Refusal::Group).unwrap();
    assert_eq!(site.head, "Box");
    assert!(site.detail.unwrap().contains("`Box` refers to `A`"));
    assert_eq!(types[SIZE + 1].decided_by_group(), Some(false));
    assert_eq!(types[SIZE + 1].verdict(), Verdict::Inhabited);
    let outside = Type::tuple(vec![Type::int(), types[1].clone()]);
    assert_eq!(outside.verdict(), Verdict::Refused(Refusal::Group));
    assert_eq!(
        outside.refusal_site(Refusal::Group).map(|s| s.head),
        Some("B".into())
    );
}

/// A function type permitting its own group's keys and returning into it is a leaf of the decider, decided
/// empty and inhabited in turn, so the members whose answer does not rest on it stay decided;
/// before this item every member of such a group went to the search, and none was decided by
/// the group.
#[test]
fn a_part_the_decider_does_not_take_leaves_the_rest_of_the_group_decided() {
    Type::forget_emptiness();
    let leaf = || {
        Expr::Morphism(
            Box::new(Expr::Type(Type::empty())),
            Box::new(r(0)),
            Box::new(r(0)),
        )
    };
    let types = group(vec![
        // A = #nil | #s(A) -> A with nothing promised: inhabited whatever the leaf.
        (
            "A".into(),
            or(vec![atom("nil", vec![]), atom("s", vec![leaf()])]),
        ),
        // E = (int, E) | #e((A) -> empty, E): empty whatever the leaf.
        (
            "E".into(),
            or(vec![pair(int(), r(1)), atom("e", vec![leaf(), r(1)])]),
        ),
    ]);
    assert_eq!(types[0].decided_by_group(), Some(false));
    assert_eq!(types[1].decided_by_group(), Some(true));
    assert_eq!(types[1].verdict(), Verdict::Empty);
}

/// A recursive occurrence under `&` is read as GROUP-setop reads it (DESIGN.md L1.23): the meet
/// as a tuple of its operands, a member shown empty is empty, and a member shown inhabited
/// through the meet goes to the search, here `A`, though its case `#nil` has a value. The
/// members that do not read the meet stay decided.
#[test]
fn a_member_read_through_a_meet_goes_to_the_search_and_the_rest_stays_decided() {
    Type::forget_emptiness();
    let types = group(vec![
        // A = #nil | #s(A & L): inhabited, through `#nil`.
        (
            "A".into(),
            or(vec![
                atom("nil", vec![]),
                atom("s", vec![Expr::And(vec![r(0), r(2)])]),
            ]),
        ),
        // E = (int, E) | #e(A & L, E): empty, as each case reads `E`.
        (
            "E".into(),
            or(vec![
                pair(int(), r(1)),
                atom("e", vec![Expr::And(vec![r(0), r(2)]), r(1)]),
            ]),
        ),
        // L = #nil | #cons(int, L).
        (
            "L".into(),
            or(vec![atom("nil", vec![]), atom("cons", vec![int(), r(2)])]),
        ),
    ]);
    assert_eq!(types[0].decided_by_group(), None);
    assert_eq!(types[0].verdict(), Verdict::Inhabited);
    assert_eq!(types[1].decided_by_group(), Some(true));
    assert_eq!(types[2].decided_by_group(), Some(false));
    assert_eq!(types[1].verdict(), Verdict::Empty);
}

/// M0 = (empty) -> M0 with M0 as both bounds is accepted (`admission::the_named_groups`), and
/// decided: inhabited, by the function with no keys.
#[test]
fn m0_stays_accepted_and_decided() {
    Type::forget_emptiness();
    let m0 = group(vec![(
        "M0".into(),
        Expr::Morphism(
            Box::new(Expr::Type(Type::empty())),
            Box::new(r(0)),
            Box::new(r(0)),
        ),
    )]);
    assert_eq!(m0[0].verdict(), Verdict::Inhabited);
}

/// A census group written as in the X14 oracle's files: `(U a b ..)` a union, `(T #name a ..)`
/// an atom with a payload, `(T a ..)` a tuple, `(M g p v)` a morphism type, `#name` an atom,
/// `int`, `empty`, `Rk` definition k.
fn census(text: &str) -> Vec<Type> {
    fn parse(tokens: &mut std::iter::Peekable<std::vec::IntoIter<String>>) -> Expr {
        let t = tokens.next().expect("a token");
        if t != "(" {
            return match t.as_str() {
                "int" => int(),
                "empty" => Expr::Type(Type::empty()),
                _ if t.starts_with('#') => Expr::Atom(t[1..].into(), vec![]),
                _ => r(t[1..].parse().expect("Rk")),
            };
        }
        let head = tokens.next().expect("a head");
        let mut items = Vec::new();
        let mut atom = None;
        if head == "T" && tokens.peek().is_some_and(|t| t.starts_with('#')) {
            atom = tokens.next().map(|t| t[1..].to_owned());
        }
        while tokens.peek().is_some_and(|t| t != ")") {
            items.push(parse(tokens));
        }
        tokens.next();
        match (head.as_str(), atom) {
            ("U", _) => Expr::Union(items),
            ("T", Some(a)) => Expr::Atom(a, items),
            ("T", None) => Expr::Tuple(items),
            ("M", _) => {
                let [g, p, v] = <[Expr; 3]>::try_from(items).expect("three parts");
                Expr::Morphism(Box::new(g), Box::new(p), Box::new(v))
            }
            _ => panic!("head {head}"),
        }
    }
    let defs = (text.split(';').enumerate())
        .map(|(i, body)| {
            let spaced = body.replace('(', " ( ").replace(')', " ) ");
            let tokens: Vec<String> = spaced.split_whitespace().map(String::from).collect();
            let mut tokens = tokens.into_iter().peekable();
            (format!("R{i}"), parse(&mut tokens))
        })
        .collect();
    group(defs)
}

/// The nine natural types and the two JSON groups of the X14 census
/// (wt/xs2/claude/r2/oracle natural.txt and json.txt) are decided, none refused.
#[test]
fn the_census_groups_are_decided() {
    let groups = [
        (
            "expr_31",
            "(U (T #num int) (T #bool int) (T #var int) (T #add R0 R0) (T #eq R0 R0) \
             (T #cond R0 R0 R0) #bad)",
        ),
        (
            "re_10",
            "(U #void #eps (T #lit int) (T #range int int) (T #seq R0 R0) (T #alt R0 R0) \
             (T #star R0))",
        ),
        (
            "proof_design",
            "(U #eval #domain (T #rewrite int int int) (T #chain (U (M empty empty R0) \
             (M int int R0)) int) (T #cases int (M int int R0)) (T #induction int R0 R0) \
             (T #use int int) (T #implies int R0) (T #reflect int) (T #assume int))",
        ),
        (
            "lazy_stream",
            "(U (T #cons int R0) (T #defer (M int int R0)))",
        ),
        ("lazy_tree", "(U (T #node R0 R0) (T #lazy (M int int R0)))"),
        (
            "lazy_rose",
            "(U (T #node R0 R1) (T #later (M int int R0))) ; \
             (U (T #cons R0 R1) (T #later (M int int R1)))",
        ),
        ("node_thunk", "(T #node R1 (U R1 R0)) ; (M int int R0)"),
        (
            "ui_list",
            "(T #panel R1 (M int int R0)) ; (U #nil (T #cons R0 R1))",
        ),
        (
            "widget_lazy_children",
            "(T #widget R1 (M int int R0)) ; (U (T #cons R0 R1) (M int int R1))",
        ),
        (
            "json_fence",
            "(U R1 (T #arr int) int int #true #false #null) ; (T R2) ; (T int R0)",
        ),
        (
            "json_corpus",
            "(U R1 R3 int int int) ; (T R5) ; (T int R0) ; (T R4) ; \
             (U #nil (T #cons R0 R4)) ; (U #nil (T #cons R2 R5))",
        ),
    ];
    let mut refused = 0;
    for (name, text) in groups {
        Type::forget_emptiness();
        for (i, t) in census(text).iter().enumerate() {
            match t.verdict() {
                Verdict::Refused(r) => {
                    refused += 1;
                    eprintln!("{name} R{i}: {r:?}");
                }
                Verdict::Empty | Verdict::Inhabited => {}
            }
        }
    }
    assert_eq!(refused, 0);
}

/// `n` copies of the refused component of [`refused`] and `n` lists apart from it, in one group.
fn copies(n: usize) -> Vec<(String, Expr)> {
    let mut defs: Vec<(String, Expr)> = (0..n)
        .flat_map(|c| refused(&c.to_string(), copy(c)))
        .collect();
    let lists = defs.len();
    for c in 0..n {
        defs.push((
            format!("L{c}"),
            or(vec![
                atom("nil", vec![]),
                atom("cons", vec![int(), r(lists + c)]),
            ]),
        ));
    }
    defs
}

/// A group of n copies of the component and n lists apart: the verdict of every member and the
/// message of every refused one, at n and 8n, within the limit of the scaling test; the lists
/// stay decided by the decider.
#[test]
fn a_group_of_refused_components_scales() {
    let n = 64;
    Type::forget_emptiness();
    let types = group(copies(n));
    assert!(
        types[SIZE * n..]
            .iter()
            .all(|t| t.decided_by_group() == Some(false))
    );
    assert!((types[..SIZE * n].iter()).all(|t| t.verdict() == Verdict::Refused(Refusal::Group)));
    scaling::check_order("refused components and lists, n copies", n, 1, |n| {
        Type::forget_emptiness();
        let types = group(copies(n));
        for t in &types {
            std::hint::black_box(t.verdict());
        }
        for t in &types[..SIZE * n] {
            std::hint::black_box(t.refusal_site(Refusal::Group));
        }
    });
}

/// The refused component of [`refused`], a ring of `n` lists `Ints{k} = #nil | #cons(int,
/// Ints{k+1})` that the decider decides, and `m` members `Box{k} = (A, Ints0)`, each refused
/// since it reads `A`, and each reading the whole ring.
fn boxes(m: usize, n: usize) -> Vec<(String, Expr)> {
    let mut defs: Vec<(String, Expr)> = refused("", IN_ORDER).into();
    for k in 0..n {
        defs.push((
            format!("Ints{k}"),
            or(vec![
                atom("nil", vec![]),
                atom("cons", vec![int(), r(SIZE + (k + 1) % n)]),
            ]),
        ));
    }
    for k in 0..m {
        defs.push((format!("Box{k}"), pair(r(0), r(SIZE))));
    }
    defs
}

/// m refused members that share one decided part of n definitions: their messages together
/// cost O(m + n), not O(m n), at (m, n) and (8m, 8n), since the re-check of the repair does not
/// walk the decided part again for each member (COMPLEXITY.md K85).
#[test]
fn refused_members_sharing_a_decided_part_scale() {
    let n = 128;
    Type::forget_emptiness();
    let types = group(boxes(n, n));
    assert!((types[SIZE..SIZE + n].iter()).all(|t| t.decided_by_group() == Some(false)));
    for t in &types[SIZE + n..] {
        assert_eq!(t.verdict(), Verdict::Refused(Refusal::Group));
        let site = t.refusal_site(Refusal::Group).expect("a refused member");
        assert!(site.head.starts_with("Box"), "{site:?}");
        // The definitions alone: `B` writes its `(_, _)` in full (MSG-derive-type-size).
        assert_eq!(site.defs.len(), SIZE + 1, "{site:?}");
    }
    scaling::check_order("m refused members sharing a decided part of n", n, 1, |n| {
        Type::forget_emptiness();
        let types = group(boxes(n, n));
        for t in &types[SIZE + n..] {
            std::hint::black_box(t.refusal_site(Refusal::Group));
        }
    });
}

/// The group, found by a random search over groups of four definitions (seed 138 of
/// `group_oracle`'s generator, with the names shortened),
///
/// ```text
/// type P = (P,) | (P & S,)
/// type Q = ((int) -> P) | ((int) -> R) | (S,)
/// type R = (S & R,) | (S & Q,) | ((int) -> S)
/// type S = (Q & R,) | (S,)
/// ```
///
/// with the repair `| #end` added to `R` when `repaired`. Its tuples have one component each,
/// so the obstacle the message names is a meet: GROUP-setop reads a meet as a conjunction of its
/// operands.
fn meets(repaired: bool) -> Vec<(String, Expr)> {
    let and = |a: Expr, b: Expr| Expr::And(vec![a, b]);
    let one = |a: Expr| Expr::Tuple(vec![a]);
    let mut r_body = vec![one(and(r(3), r(2))), one(and(r(3), r(1))), f(r(3))];
    if repaired {
        r_body.push(atom("end", vec![]));
    }
    vec![
        ("P".into(), or(vec![one(r(0)), one(and(r(0), r(3)))])),
        ("Q".into(), or(vec![f(r(0)), f(r(2)), one(r(3))])),
        ("R".into(), or(r_body)),
        ("S".into(), or(vec![one(and(r(1), r(2))), one(r(3))])),
    ]
}

/// A refused member whose undecided part is a meet: the message names the meet, the definition
/// it is written in and its operands, and offers the repair the re-check confirms, which leaves
/// the member to the search for a value since it reads meets (GROUP-refusal-meet-wording). The
/// one-tuple in the repair prints as `(x,)`; before this item it printed as `(x)`, which reads
/// as `x` in parentheses.
#[test]
fn a_refused_member_read_through_a_meet_names_the_meet() {
    Type::forget_emptiness();
    let types = group(meets(false));
    assert_eq!(types[0].decided_by_group(), Some(true));
    assert_eq!(types[0].verdict(), Verdict::Empty);
    let tail = |member: &str| {
        format!(
            "these references make 6 independent cycles; some of these cycles pass through a \
             tuple, which no value can go around forever since a value is finite, and some \
             through the result of a function type, which a value can, since a function can \
             return without calling itself; the meet `S & Q` in `R` needs a value in each of \
             `S` and `Q`, and whether they have one is still open; the known ways to settle \
             such a group take time that grows with the square of its size, while the checker \
             decides each group in time linear in it, so it does not settle this one; a search \
             for a value of `{member}` then neither finds one nor shows that there is none, so \
             the checker counts `{member}` as possibly having a value; adding the case `| #end` \
             to `R`, as in `type R = (S & R,) | (S & Q,) | ((int) -> S) | #end`, removes \
             this obstacle, and whether `{member}` has a value is then left to the search for \
             one"
        )
    };
    assert_eq!(
        message(&types[1]),
        "deciding whether `Q` has a value needs the definitions `Q`, `R` and `S` together; `Q` \
         refers to `R` and `S`; `R` refers to `Q`, `S` and itself; `S` refers to `Q`, `R` and \
         itself; "
            .to_owned()
            + &tail("Q")
    );
    assert_eq!(
        message(&types[2]),
        "deciding whether `R` has a value needs the definitions `R`, `Q` and `S` together; `R` \
         refers to `Q`, `S` and itself; `Q` refers to `R` and `S`; `S` refers to `Q`, `R` and \
         itself; "
            .to_owned()
            + &tail("R")
    );
    assert_eq!(
        message(&types[3]),
        "deciding whether `S` has a value needs the definitions `S`, `Q` and `R` together; `S` \
         refers to `Q`, `R` and itself; `Q` refers to `R` and `S`; `R` refers to `Q`, `S` and \
         itself; "
            .to_owned()
            + &tail("S")
    );
    Type::forget_emptiness();
    let types = group(meets(true));
    let verdicts: Vec<_> = types
        .iter()
        .map(|t| (t.decided_by_group(), t.verdict()))
        .collect();
    // After the repair the decider leaves `Q`, `R` and `S` to the search, as the message says:
    // it builds values of `Q` and `R`, and refuses `S`, which reads the meet `Q & R`, with
    // `Refusal::Fork` (COMPLEXITY.md K35); so the group refusal is gone, and the search's own
    // refusal of `S` is what remains.
    assert_eq!(
        verdicts,
        vec![
            (Some(true), Verdict::Empty),
            (None, Verdict::Inhabited),
            (None, Verdict::Inhabited),
            (None, Verdict::Refused(Refusal::Fork)),
        ]
    );
}

/// `n` copies of the refused component of [`refused`]; a ring of `n` definitions `Opt{k} = #none |
/// #some(A{k}, Opt{k+1})`, each inhabited by its case `#none` though it reads the refused copy
/// `k`; and `m` members `Box{j} = (A0, Opt0)`, each refused since it reads `A0`, and each
/// reaching every `Opt{k}` and through it every refused copy. Each `Opt{k}` reaches the meets of
/// copy `k`, so the decider's "inhabited" does not decide it (GROUP-setop), and the search
/// builds its value; with the former fixture, which had no meets, the decider decided it.
fn reach(m: usize, n: usize) -> Vec<(String, Expr)> {
    let mut defs: Vec<(String, Expr)> = (0..n)
        .flat_map(|c| refused(&c.to_string(), copy(c)))
        .collect();
    let opt = defs.len();
    for k in 0..n {
        defs.push((
            format!("Opt{k}"),
            or(vec![
                atom("none", vec![]),
                atom("some", vec![r(SIZE * k), r(opt + (k + 1) % n)]),
            ]),
        ));
    }
    for j in 0..m {
        defs.push((format!("Box{j}"), pair(r(0), r(opt))));
    }
    defs
}

/// m refused members, each reaching n nodes that each reach another refused component:
/// their messages together cost O(m + n) at (m, n) and (8m, 8n) (GROUP-refusal-reach). The
/// message of each names only the definitions its refusal rests on, those of `A0`'s copy.
#[test]
fn refused_members_reaching_many_refused_components_scale() {
    let n = 64;
    Type::forget_emptiness();
    let types = group(reach(n, n));
    let opt = SIZE * n;
    assert!((types[..opt].iter()).all(|t| t.verdict() == Verdict::Refused(Refusal::Group)));
    assert!(
        (types[opt..opt + n].iter())
            .all(|t| (t.decided_by_group(), t.verdict()) == (None, Verdict::Inhabited))
    );
    for t in &types[opt + n..] {
        assert_eq!(t.verdict(), Verdict::Refused(Refusal::Group));
        let site = t.refusal_site(Refusal::Group).expect("a refused member");
        assert!(site.head.starts_with("Box"), "{site:?}");
        // The definitions alone: `B` writes its `(_, _)` in full (MSG-derive-type-size).
        assert_eq!(site.defs.len(), SIZE + 1, "{site:?}");
    }
    scaling::check_order(
        "m refused members reaching n refused components",
        n,
        1,
        |n| {
            Type::forget_emptiness();
            let types = group(reach(n, n));
            for t in &types[SIZE * n + n..] {
                std::hint::black_box(t.refusal_site(Refusal::Group));
            }
        },
    );
}

/// Each refused member's message is the same when it is the first asked for in its group and
/// when the messages of the members before it were asked for first, which re-checked repairs
/// that the later ones read part of (GROUP-refusal-reach): the answers a re-check keeps and
/// reads again are the ones a re-check of its own finds.
#[test]
fn a_message_is_the_same_asked_for_first_or_after_the_others() {
    let mut both = placed(IN_ORDER);
    both.push((
        "Both".into(),
        atom(
            "both",
            vec![
                r(0),
                Expr::And(vec![
                    r(0),
                    Expr::Type(Type::tuple(vec![Type::top(), Type::top()])),
                ]),
            ],
        ),
    ));
    // Two refused copies and members reading both, so that the repair of one copy that a
    // message re-checks leaves the other refused, and the next message's walk meets it kept.
    let mut crossed: Vec<(String, Expr)> = (0..2)
        .flat_map(|c| refused(&c.to_string(), copy(c)))
        .collect();
    for j in 0..3 {
        crossed.push((format!("Box{j}"), or(vec![pair(r(0), int()), r(SIZE)])));
    }
    for defs in [
        both,
        meets(false),
        copies(3),
        boxes(3, 3),
        reach(3, 3),
        crossed,
    ] {
        Type::forget_emptiness();
        let types = group(defs.clone());
        let refused: Vec<usize> = (0..types.len())
            .filter(|&j| types[j].verdict() == Verdict::Refused(Refusal::Group))
            .collect();
        assert!(!refused.is_empty());
        let in_turn: Vec<_> = (refused.iter())
            .map(|&j| types[j].refusal_site(Refusal::Group))
            .collect();
        for (&j, site) in refused.iter().zip(&in_turn).rev() {
            Type::forget_emptiness();
            let types = group(defs.clone());
            assert_eq!(&types[j].refusal_site(Refusal::Group), site);
        }
    }
}

/// The fixtures [`refused`] had until GROUP-closure-order, each in four orders of its
/// definitions: each member is inhabited, as the group oracle finds.
///
/// ```text
/// type Pair = (Thunk, Node)
/// type Tree = (Pair, Thunk) | (Pair, Node)
/// type Thunk = (int) -> Tree
/// type Node = ((int) -> Pair) | (Tree, Thunk)
/// ```
///
/// has `p = (t, n)`, with `t = λ_. (p, t)`, whose result is a value of `Tree`, and `n = λ_. p`;
/// the search builds `Pair` again once the function type `Thunk`, taken while `Pair` was being
/// built, holds a value of it. Its replacement, seed 9014 of the X14 family of four,
///
/// ```text
/// type Pair = (Tree, Node)
/// type Tree = (Thunk, Thunk) | (Pair, Node)
/// type Thunk = (int) -> Pair
/// type Node = ((int) -> Tree) | (Tree, Thunk)
/// ```
///
/// has `p = (u, n)`, with `t = λ_. p`, `u = (t, t)` and `n = λ_. u`, which the search builds
/// once a failure kept while `Thunk` was taken to have a value is sought again.
#[test]
fn the_former_fixtures_are_inhabited() {
    let former = |[pair_, tree, thunk, node]: [Expr; 4]| {
        [
            ("Pair", pair(thunk.clone(), node.clone())),
            (
                "Tree",
                or(vec![
                    pair(pair_.clone(), thunk.clone()),
                    pair(pair_.clone(), node),
                ]),
            ),
            ("Thunk", f(tree.clone())),
            ("Node", or(vec![f(pair_), pair(tree, thunk)])),
        ]
    };
    let x9014 = |[pair_, tree, thunk, node]: [Expr; 4]| {
        [
            ("Pair", pair(tree.clone(), node.clone())),
            (
                "Tree",
                or(vec![
                    pair(thunk.clone(), thunk.clone()),
                    pair(pair_.clone(), node),
                ]),
            ),
            ("Thunk", f(pair_)),
            ("Node", or(vec![f(tree.clone()), pair(tree, thunk)])),
        ]
    };
    for fixture in [former, x9014] {
        for at in [[0, 1, 2, 3], [2, 3, 1, 0], [3, 2, 1, 0], [1, 0, 3, 2]] {
            let mut defs: Vec<Option<(String, Expr)>> = vec![None, None, None, None];
            for (k, (name, body)) in fixture(at.map(r)).into_iter().enumerate() {
                defs[at[k]] = Some((name.into(), body));
            }
            Type::forget_emptiness();
            let types = group(defs.into_iter().map(Option::unwrap).collect());
            for t in &types {
                assert_eq!(t.verdict(), Verdict::Inhabited, "{at:?}");
            }
        }
    }
}

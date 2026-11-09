//! A member of a recursive group that the group's decider refuses (DESIGN.md L1.23, item
//! GROUP-refusal): a component mixing cycles through tuples and through function results, with
//! two or more independent cycles and a tuple with two undecided components, is refused with a
//! message naming the definition, the definitions taking part, the cycles, the tuple and a
//! repair that a re-check confirms; it is not searched for emptiness. The rest of the group
//! stays on the decider: a part the decider does not take is a leaf, decided with it empty and
//! with it inhabited.

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

/// The four definitions
///
/// ```text
/// type Pair = (Thunk, Node)
/// type Tree = (Pair, Thunk) | (Pair, Node)
/// type Thunk = (int) -> Tree
/// type Node = ((int) -> Pair) | (Tree, Thunk)
/// ```
///
/// with the names suffixed by `tag` and definition k at `at[k]`. Each has a value (a function
/// may return a value that holds it), which the search for values does not build, since it
/// builds a function only once its value type has a value; the decider refuses them all. No
/// smaller group of the X14 shape (tuples of two, `(int) -> x`, `#stop`, no arm written twice)
/// is refused: none of 200000 random groups of two or three definitions was.
fn pairs(tag: &str, at: [usize; 4]) -> [(String, Expr); 4] {
    let [pair_, tree, thunk, node] = at.map(r);
    [
        (format!("Pair{tag}"), pair(thunk.clone(), node.clone())),
        (
            format!("Tree{tag}"),
            or(vec![
                pair(pair_.clone(), thunk.clone()),
                pair(pair_.clone(), node),
            ]),
        ),
        (format!("Thunk{tag}"), f(tree.clone())),
        (format!("Node{tag}"), or(vec![f(pair_), pair(tree, thunk)])),
    ]
}

/// The definitions of `pairs` in the order of `at`.
fn placed(at: [usize; 4]) -> Vec<(String, Expr)> {
    let mut defs: Vec<Option<(String, Expr)>> = vec![None, None, None, None];
    for (k, def) in pairs("", at).into_iter().enumerate() {
        defs[at[k]] = Some(def);
    }
    defs.into_iter().map(Option::unwrap).collect()
}

const IN_ORDER: [usize; 4] = [0, 1, 2, 3];
const ROTATED: [usize; 4] = [2, 3, 1, 0];

/// The refusal of `t`'s verdict, with its message.
fn message(t: &Type) -> String {
    assert_eq!(t.verdict(), Verdict::Refused(Refusal::Group));
    let site = t.refusal_site(Refusal::Group).expect("a refused member");
    site.detail.expect("the decider's reason")
}

/// Before this item the members went to the search, which refused them for another cause, so
/// the first assertion fails there.
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
    assert_eq!(site.head, "Pair");
    assert_eq!(
        site.defs,
        [
            "type Pair = (Thunk, Node)",
            "type Node = ((int) -> Pair) | (Tree, Thunk)",
            "type Thunk = (int) -> Tree",
            "type Tree = (Pair, Thunk) | (Pair, Node)",
        ]
    );
    assert_eq!(
        m,
        "deciding whether `Pair` has a value needs the definitions `Pair`, `Node`, `Thunk` and \
         `Tree` together; `Pair` refers to `Node` and `Thunk`; `Node` refers to `Pair`, `Thunk` \
         and `Tree`; `Thunk` refers to `Tree`; `Tree` refers to `Node`, `Pair` and `Thunk`; \
         these references make 6 independent cycles; some of these cycles pass through a tuple, which no \
         value can go around forever since a value is finite, and some through the result of a \
         function type, which a value can, since a function can return without calling itself; \
         the tuple `(Tree, Thunk)` in `Node` needs a value of both `Tree` and `Thunk`, and \
         whether they have one is still open; the known ways to settle such a group take time \
         that grows with the square of its size, while the checker decides each group in time \
         linear in it, so it stops here and counts `Pair` as possibly having a value; adding the \
         case `| #end` to `Node`, as in `type Node = ((int) -> Pair) | (Tree, Thunk) | #end`, \
         lets the checker decide it"
    );
}

#[test]
fn a_members_message_is_the_same_when_the_definitions_are_listed_in_another_order() {
    Type::forget_emptiness();
    let a = group(placed(IN_ORDER));
    let b = group(placed(ROTATED));
    for k in 0..4 {
        let (x, y) = (&a[k], &b[ROTATED[k]]);
        assert_eq!(message(x), message(y), "definition {k}");
        assert_eq!(
            x.refusal_site(Refusal::Group),
            y.refusal_site(Refusal::Group)
        );
    }
}

/// The repair the message offers is applied, and the group so written is decided for the
/// member by the decider alone: only a repair a re-check confirms is offered.
#[test]
fn the_repair_offered_decides_the_member() {
    Type::forget_emptiness();
    let defs = placed(IN_ORDER);
    let types = group(defs.clone());
    for (k, t) in types.iter().enumerate() {
        let m = message(t);
        let (_, after) = (m.split_once("adding the case `| #end` to "))
            .unwrap_or_else(|| panic!("no repair offered: {m}"));
        // "`Tree`, as in `...`, lets ..." or "each of `Tree` and `Node` lets ...".
        let named = after.split(", as in").next().unwrap();
        let named = named.split(" lets").next().unwrap();
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
        let t = &group(fixed)[k];
        assert!(t.decided_by_group().is_some(), "{} with {named}", defs[k].0);
        assert_eq!(t.verdict(), Verdict::Inhabited);
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
        or(vec![atom("nil", vec![]), atom("cons", vec![int(), r(5)])]),
    ));
    let types = group(defs);
    assert_eq!(types[4].verdict(), Verdict::Refused(Refusal::Group));
    let site = types[4].refusal_site(Refusal::Group).unwrap();
    assert_eq!(site.head, "Box");
    assert!(site.detail.unwrap().contains("`Box` refers to `Pair`"));
    assert_eq!(types[5].decided_by_group(), Some(false));
    assert_eq!(types[5].verdict(), Verdict::Inhabited);
    let outside = Type::tuple(vec![Type::int(), types[3].clone()]);
    assert_eq!(outside.verdict(), Verdict::Refused(Refusal::Group));
    assert_eq!(
        outside.refusal_site(Refusal::Group).map(|s| s.head),
        Some("Node".into())
    );
}

/// A recursive occurrence under `&` is a leaf of the decider, decided empty and inhabited in
/// turn, so the members whose answer does not rest on it stay decided; before this item every
/// member of such a group went to the search, and none was decided by the group.
#[test]
fn a_part_the_decider_does_not_take_leaves_the_rest_of_the_group_decided() {
    Type::forget_emptiness();
    let types = group(vec![
        // A = #nil | #s(A & L): inhabited whatever the leaf.
        (
            "A".into(),
            or(vec![
                atom("nil", vec![]),
                atom("s", vec![Expr::And(vec![r(0), r(2)])]),
            ]),
        ),
        // E = (int, E) | #e(A & L, E): empty whatever the leaf.
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
    assert_eq!(types[0].decided_by_group(), Some(false));
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

/// `n` copies of the refused component of [`pairs`] and `n` lists apart from it, in one group.
fn copies(n: usize) -> Vec<(String, Expr)> {
    let mut defs: Vec<(String, Expr)> = (0..n)
        .flat_map(|c| pairs(&c.to_string(), [4 * c, 4 * c + 1, 4 * c + 2, 4 * c + 3]))
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
        types[4 * n..]
            .iter()
            .all(|t| t.decided_by_group() == Some(false))
    );
    assert!((types[..4 * n].iter()).all(|t| t.verdict() == Verdict::Refused(Refusal::Group)));
    scaling::check_order("refused components and lists, n copies", n, 1, |n| {
        Type::forget_emptiness();
        let types = group(copies(n));
        for t in &types {
            std::hint::black_box(t.verdict());
        }
        for t in &types[..4 * n] {
            std::hint::black_box(t.refusal_site(Refusal::Group));
        }
    });
}

/// The refused component of [`pairs`], a ring of `n` lists `Ints{k} = #nil | #cons(int,
/// Ints{k+1})` that the decider decides, and `m` members `Box{k} = (Pair, Ints0)`, each refused
/// since it reads `Pair`, and each reading the whole ring.
fn boxes(m: usize, n: usize) -> Vec<(String, Expr)> {
    let mut defs: Vec<(String, Expr)> = pairs("", [0, 1, 2, 3]).into();
    for k in 0..n {
        defs.push((
            format!("Ints{k}"),
            or(vec![
                atom("nil", vec![]),
                atom("cons", vec![int(), r(4 + (k + 1) % n)]),
            ]),
        ));
    }
    for k in 0..m {
        defs.push((format!("Box{k}"), pair(r(0), r(4))));
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
    assert!((types[4..4 + n].iter()).all(|t| t.decided_by_group() == Some(false)));
    for t in &types[4 + n..] {
        assert_eq!(t.verdict(), Verdict::Refused(Refusal::Group));
        let site = t.refusal_site(Refusal::Group).expect("a refused member");
        assert!(site.head.starts_with("Box"), "{site:?}");
        assert_eq!(site.defs.len(), 5, "{site:?}");
    }
    scaling::check_order("m refused members sharing a decided part of n", n, 1, |n| {
        Type::forget_emptiness();
        let types = group(boxes(n, n));
        for t in &types[4 + n..] {
            std::hint::black_box(t.refusal_site(Refusal::Group));
        }
    });
}

//! The tests of the names of parts kept unevaluated (item PERF-part-name-nested), in a file of
//! their own so that `unfold.rs` does not import the group builder they use (S.1f).

use std::collections::HashSet;

use super::*;
use crate::types::TextPlace;
use crate::types::rec::{Expr, Group};

/// `k` parts kept unevaluated, each inside the one before, the innermost holding the member:
/// at depth `i` by `i % 4`, a tuple `(#ai, #ai | …)`, an atom `#w(#ai | …)`, a permission
/// `((#ai, …)) ->? #ai` and a permission `((#ai) -> …) ->? #ai`, each parenthesized where it
/// stands. The atoms and the member are named after `tag`, so their texts are made by the
/// first naming and a try finds them missing.
fn nest(tag: &str, k: usize) -> Type {
    let mut body = Expr::Ref(0, vec![]);
    for i in (0..k).rev() {
        let a = || Expr::Type(Type::atom(&format!("{tag}{i}")));
        body = match i % 4 {
            0 => Expr::Tuple(vec![a(), Expr::Union(vec![a(), body])]),
            1 => Expr::Atom("w".into(), vec![Expr::Union(vec![a(), body])]),
            2 => Expr::Morphism(
                Box::new(Expr::Type(Type::empty())),
                Box::new(Expr::Tuple(vec![a(), body])),
                Box::new(a()),
            ),
            _ => Expr::Morphism(
                Box::new(Expr::Type(Type::empty())),
                Box::new(Expr::exact(a(), body)),
                Box::new(a()),
            ),
        };
    }
    let def = Def {
        name: format!("{tag}R"),
        params: vec![],
        body,
    };
    Group::new(vec![def])
        .expect("accepted")
        .instance(vec![])
        .remove(0)
}

/// The instance of the member `t`.
fn env_of(t: &Type) -> Arc<Env> {
    match &*t.0 {
        crate::types::Node::Rec(r) => r.key.env.clone(),
        _ => panic!("a recursive member"),
    }
}

/// The parts kept unevaluated in the instance's bodies, each once, outer before inner.
fn parts(env: &Env) -> Vec<&Arc<Node>> {
    let (mut seen, mut out) = (HashSet::new(), Vec::new());
    let mut todo: Vec<&Arc<Node>> = env.group().0.bodies.iter().collect();
    while let Some(e) = todo.pop() {
        for c in e.e.kids() {
            if !seen.insert(c.at) {
                continue;
            }
            if kept_as_part(&e.e, c) {
                out.push(c);
            }
            todo.push(c);
        }
    }
    out
}

/// The text of `e` at the instance's arguments, spelled out in full.
fn spelled(e: &Node, env: &Env) -> String {
    let show = Show {
        defs: &env.group().0.defs,
        params: &[],
        args: Some(&env.args),
        e,
        surface: false,
    };
    let text: String = show.rope().strs().collect();
    // Written by `Display` outside the surface syntax: the same text.
    assert_eq!(show.to_string(), text);
    text
}

#[test]
fn a_part_s_name_is_unchanged_when_the_names_inside_it_are_shared() {
    // Item PERF-part-name-nested: a name holds the names of the parts inside it, kept once
    // per instance; the text is the one spelled out, byte for byte, in any order of naming.
    for k in 1..=9 {
        for order in ["outer first", "inner first", "alternate"] {
            let tag = format!("pn{k}{}", &order[..1]);
            let t = nest(&tag, k);
            let env = env_of(&t);
            let mut ps = parts(&env);
            assert!(ps.len() >= k, "{tag}: {} parts", ps.len());
            match order {
                "inner first" => ps.reverse(),
                "alternate" => ps.sort_by_key(|p| (p.at % 2, p.at)),
                _ => {}
            }
            for p in &ps {
                let name: String = component(p, &env).rope().strs().collect();
                assert_eq!(name, spelled(p, &env), "{tag}, {order}");
            }
            // Those named inside another's walk are kept too, and only whole texts.
            let kept = env.part_names.lock().expect("no panic under the lock");
            assert_eq!(kept.len(), ps.len(), "{tag}, {order}");
            for p in &ps {
                let text: String = kept[&p.at].strs().collect();
                assert_eq!(text, spelled(p, &env), "{tag}, {order}");
            }
        }
    }
}

#[test]
fn a_nest_of_parts_prints_as_it_did_before_names_were_shared() {
    // The printer ranks the recursive types it defines by their names (`Tok::Rec`), so a
    // change of a name's text could change the order of the definitions; the texts below
    // were printed before item PERF-part-name-nested.
    let expected = [
        (
            4,
            "(#q40, #q40 | #w((((#q42, (#q43 -> q4R) ->? #q43)) ->? #q42) | #q41))",
            "type Part1 = #q43 -> Part6;\ntype Part2 = Part1 ->? #q43;\ntype Part3 = (#q42, Part2);\n\
             type Part4 = (Part3 ->? #q42) | #q41;\ntype Part5 = #q40 | #w(Part4);\n\
             type Part6 = (#q40, Part5);\nPart6",
        ),
        (
            6,
            "type Part1 = Part9 | #q65;\ntype Part2 = #q64 | #w(Part1);\ntype Part3 = (#q64, Part2);\n\
             type Part4 = #q63 -> Part3;\ntype Part5 = Part4 ->? #q63;\ntype Part6 = (#q62, Part5);\n\
             type Part7 = (Part6 ->? #q62) | #q61;\ntype Part8 = #q60 | #w(Part7);\n\
             type Part9 = (#q60, Part8);\nPart9",
            "type Part1 = Part9 | #q65;\ntype Part2 = #q64 | #w(Part1);\ntype Part3 = (#q64, Part2);\n\
             type Part4 = #q63 -> Part3;\ntype Part5 = Part4 ->? #q63;\ntype Part6 = (#q62, Part5);\n\
             type Part7 = (Part6 ->? #q62) | #q61;\ntype Part8 = #q60 | #w(Part7);\n\
             type Part9 = (#q60, Part8);\nPart9",
        ),
    ];
    for (k, expected_by_name, expected_plain) in expected {
        // `S = R \ Never`: printed, `S` unfolds once, and so do the parts of `R`, which then
        // get definitions ranked by their names.
        let body = Expr::Diff(
            Box::new(Expr::Type(nest(&format!("q{k}"), k))),
            Box::new(Expr::Type(Type::empty())),
        );
        let def = Def {
            name: format!("q{k}S"),
            params: vec![],
            body,
        };
        let t = Group::new(vec![def])
            .expect("accepted")
            .instance(vec![])
            .remove(0);
        let by_name = t.surface_by_name(TextPlace::Any).to_string();
        let plain = t.surface().to_string();
        assert_eq!(by_name, expected_by_name, "k = {k}, by name");
        assert_eq!(plain, expected_plain, "k = {k}, plain");
    }
}

//! The order a scope's statements are bound in, where names are overloaded: each use of an
//! overload set waits on every arrow of the set, through one join per set.

use std::collections::HashMap;

use zedc::elab::{top_order, topo, topo_joined};
use zedc::resolve::Ref;

use super::errors;

/// The top-level statements of `text` in the order they are bound, each by its text up to
/// ` =`; else those of each cycle.
fn order(text: &str) -> Result<Vec<String>, Vec<Vec<String>>> {
    let tokens = zedc::lex::lex_fence(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(text, &tokens, &tree).unwrap();
    let res = zedc::resolve::resolve(&stmts).unwrap();
    let name = |i: usize| {
        let s = &text[stmts[i].span.start..stmts[i].span.end];
        s[..s.find(" =").unwrap_or(s.len())].to_string()
    };
    let names = |is: Vec<usize>| is.into_iter().map(name).collect::<Vec<_>>();
    top_order(&stmts, &res)
        .map(names)
        .map_err(|cs| cs.into_iter().map(names).collect())
}

#[test]
fn a_use_of_one_function_waits_on_it() {
    let src = "total = double(3) + 1;\ndouble(positional x) = 2 * x;\n";
    assert_eq!(
        order(src),
        Ok(vec!["double(positional x)".into(), "total".into()])
    );
}

#[test]
fn a_use_of_an_overloaded_name_waits_on_every_overload() {
    let src = "area = size(2) + size(true);\nsize(x: int) = x;\nlabel = \"box\";\n\
               size(x: bool) = 1;\n";
    let want = ["size(x: int)", "label", "size(x: bool)", "area"];
    assert_eq!(order(src), Ok(want.map(String::from).to_vec()));
}

#[test]
fn a_user_comes_right_after_the_last_overload_it_waits_on() {
    // The join of the overloads is passed at once, so `twice` is placed before the later
    // `unrelated`, as when it waits on each overload directly.
    let src = "size(x: int) = x;\nsize(x: bool) = 1;\ntwice = size(1) + size(false);\n\
               unrelated = 4;\n";
    let want = ["size(x: int)", "size(x: bool)", "twice", "unrelated"];
    assert_eq!(order(src), Ok(want.map(String::from).to_vec()));
}

#[test]
fn a_use_of_a_prelude_word_waits_on_nothing() {
    let src = "shown = label;\nlabel = String(7);\nsize(x: int) = x;\nsize(x: bool) = 1;\n";
    let want = ["label", "shown", "size(x: int)", "size(x: bool)"];
    assert_eq!(order(src), Ok(want.map(String::from).to_vec()));
}

#[test]
fn a_cycle_through_an_overload_set() {
    let src = "f(x: int) = g;\nf(x: bool) = 0;\ng = f(1);\n";
    assert_eq!(order(src), Err(vec![vec!["f(x: int)".into(), "g".into()]]));
    assert_eq!(
        errors(src),
        [
            "`f`, `g` are defined in terms of each other: recursion arrives at layer L6 \
          [f(x: int) = g;]"
        ]
    );
}

#[test]
fn an_inner_scope_overloading_a_name_makes_its_own_set() {
    // Each scope binds all of its names before reading any use, and an inner scope's
    // overloads hide the outer ones, so no binder is in two different lists of uses: the
    // lists of an overloaded name are disjoint, whatever the nesting.
    let src = "f(x: int) = x;\nf(x: bool) = 0;\n\
               inner = { f(x: String) = 1; f(x: rat) = 2; f(\"a\") + f(1) };\n\
               outer = f(1) + f(true);\n";
    let tokens = zedc::lex::lex_fence(src).unwrap();
    let tree = zedc::parse::parse(src, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(src, &tokens, &tree).unwrap();
    let res = zedc::resolve::resolve(&stmts).unwrap();
    let mut list_of: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut lists = 0;
    for r in res.uses.values() {
        let Ref::Bound(ids) = r else { continue };
        let ids: Vec<usize> = ids.iter().copied().collect();
        lists += usize::from(ids.len() == 2);
        for &b in &ids {
            assert_eq!(list_of.entry(b).or_insert_with(|| ids.clone()), &ids);
        }
    }
    assert_eq!(lists, 4);
    let want = ["f(x: int)", "f(x: bool)", "inner", "outer"];
    assert_eq!(order(src), Ok(want.map(String::from).to_vec()));
}

#[test]
fn joins_order_as_their_items_written_out() {
    // Random graphs of items and joins: the order is that of `topo` on the graph with each
    // join's items written into each sorted list that names it, and the cycles are its
    // components found by reachability.
    let mut x: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = |m: usize| {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        (x % m as u64) as usize
    };
    let (mut orders, mut cycles) = (0, 0);
    for _ in 0..4000 {
        let items = 1 + next(10);
        let joins = next(4);
        let mut deps: Vec<Vec<usize>> = (0..items)
            .map(|_| (0..next(3)).map(|_| next(items + joins)).collect())
            .collect();
        deps.extend((0..joins).map(|_| (0..1 + next(3)).map(|_| next(items)).collect()));
        for d in &mut deps {
            d.sort_unstable();
            d.dedup();
        }
        let written: Vec<Vec<usize>> = deps[..items]
            .iter()
            .map(|d| {
                let mut w: Vec<usize> = (d.iter())
                    .flat_map(|&e| match e < items {
                        true => vec![e],
                        false => deps[e].clone(),
                    })
                    .collect();
                w.sort_unstable();
                w.dedup();
                w
            })
            .collect();
        let got = topo_joined(&deps, items);
        match topo(&written) {
            Ok(order) => {
                orders += 1;
                assert_eq!(got, Ok(order), "{deps:?}");
            }
            Err(_) => {
                cycles += 1;
                assert_eq!(got, Err(cycles_by_reach(&written)), "{deps:?}");
            }
        }
    }
    assert!(
        orders > 400 && cycles > 400,
        "{orders} orders, {cycles} cycles"
    );
}

/// The cycles of `deps` found by reachability: each set of items that reach each other and
/// themselves, in increasing order, the sets by their least item.
fn cycles_by_reach(deps: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = deps.len();
    let reach: Vec<Vec<bool>> = (0..n)
        .map(|i| {
            let mut seen = vec![false; n];
            let mut stack = deps[i].clone();
            while let Some(j) = stack.pop() {
                if !seen[j] {
                    seen[j] = true;
                    stack.extend(&deps[j]);
                }
            }
            seen
        })
        .collect();
    let mut placed = vec![false; n];
    let mut out = Vec::new();
    for i in 0..n {
        if placed[i] || !reach[i][i] {
            continue;
        }
        let c: Vec<usize> = (i..n).filter(|&j| reach[i][j] && reach[j][i]).collect();
        for &j in &c {
            placed[j] = true;
        }
        out.push(c);
    }
    out
}

#[test]
fn every_cycle_is_reported_each_by_name() {
    // Two separate cycles, and an item that waits on one of them without being in it: each
    // cycle is reported, its names sorted, at the item of its first name.
    let src = "odd(positional n) = if n == 0 { false } else { even(n - 1) };\n\
               uses = odd(3);\n\
               even(positional n) = if n == 0 { true } else { odd(n - 1) };\n\
               b = a + 1;\na = b + 1;\nfine = 2;\n";
    let cycle = |names: &[&str]| names.iter().map(|&n| String::from(n)).collect::<Vec<_>>();
    assert_eq!(
        order(src),
        Err(vec![
            cycle(&["odd(positional n)", "even(positional n)"]),
            cycle(&["b", "a"]),
        ])
    );
    assert_eq!(
        errors(src),
        [
            "`even`, `odd` are defined in terms of each other: recursion arrives at layer L6 \
             [even(positional n) = if n == 0 { true } else { odd(n - 1) };]",
            "`a`, `b` are defined in terms of each other: recursion arrives at layer L6 \
             [a = b + 1;]",
        ]
    );
}

//! Name resolution at the rule of low complexity (DESIGN.md Part G).

use zedc::resolve::Ref;

use super::{at, errors, run};

/// Blocks nested `n` deep, each binding a name, the innermost reading the top-level `c` `n`
/// times.
fn nested(n: usize) -> String {
    let mut src = "c = 1;\nmain = ".to_string();
    for i in 0..n {
        src += &format!("{{\ny{i} = c;\n");
    }
    src += &format!("{}\n", vec!["c"; n].join(" + "));
    src += &"}\n".repeat(n);
    src + ";\n"
}

/// `k` overloads of `f`, at most 8^5: five parameters, each with no written type or one of
/// the seven types of L1, so no two have the same parameter types.
pub(crate) fn overloads(k: usize) -> String {
    const TYPES: [&str; 8] = [
        "", ": int", ": rat", ": f64", ": bool", ": String", ": Lines", ": Files",
    ];
    let mut src = String::new();
    for i in 0..k {
        let ps: Vec<String> = (0..5)
            .map(|j| format!("p{j}{}", TYPES[i >> (3 * j) & 7]))
            .collect();
        src += &format!("f({}) = 0;\n", ps.join(", "));
    }
    src
}

#[test]
fn names_read_inside_deeply_nested_blocks_scale() {
    // A name was looked for in each open scope in turn, innermost first.
    std::thread::Builder::new()
        .stack_size(1 << 32)
        .spawn(|| {
            zed_tests::scaling::check("names read in blocks nested n deep", 800, |n| {
                assert!(run(&nested(n)).is_ok());
            });
            assert_eq!(at(&nested(3), "c", 2), ["binding c = 1;"]);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn declaring_many_overloads_scales() {
    // Each overload's parameter types were compared with those of every one before it.
    zed_tests::scaling::check("k overloads of one function", 1000, |k| {
        assert_eq!(run(&overloads(k)).unwrap().binders.len(), 6 * k);
    });
    assert_eq!(
        errors("f(x: int) = x;\nf(y: int) = 1;\ng = 1;\ng(x) = x;\n"),
        [
            "`f` is already declared in this scope with these parameter types \
             [f(y: int) = 1;]; the first `f` with these parameter types [f(x: int) = x;]",
            "`g` is already bound in this scope [g(x) = x;]; the first binding of `g` [g = 1;]",
        ]
    );
}

#[test]
fn using_many_overloads_scales() {
    // Each use of `f` copied the list of all `k` overloads, so `k` uses cost `k²`.
    let src = |k: usize| {
        // One tuple of `k` uses, so that little but the lookup is done for each.
        overloads(k) + "g = (" + &vec!["f"; k].join(", ") + ");\n"
    };
    // The statements are built before the timing, so only resolution is measured.
    let built = |k: usize| {
        let text = src(k);
        let tokens = zedc::lex::lex_fence(&text).unwrap();
        let tree = zedc::parse::parse(&text, &tokens, "Unit", zedc::parse::TOP).unwrap();
        zedc::ast::unit(&text, &tokens, &tree).unwrap()
    };
    let n = 1000;
    let (small, large) = (built(n), built(zed_tests::scaling::FACTOR * n));
    zed_tests::scaling::check_order("k overloads of one function used k times", n, 1, |k| {
        let stmts = if k == n { &small } else { &large };
        let r = zedc::resolve::resolve(stmts).unwrap();
        let sets = r
            .uses
            .values()
            .filter(|f| matches!(f, Ref::Bound(ids) if ids.len() == k));
        assert_eq!(sets.count(), k);
    });
    // The timing alone does not tell a shared list from `k` copies at these sizes, so check
    // the sharing itself: every use holds the one list of overloads, not a copy of it.
    // (A list of three is stored inline and copied, which costs no more than a pointer.)
    let r = zedc::resolve::resolve(&small).unwrap();
    let lists: Vec<_> = r
        .uses
        .values()
        .filter_map(|f| match f {
            Ref::Bound(ids) if ids.len() == n => Some(ids),
            _ => None,
        })
        .collect();
    assert_eq!(lists.len(), n);
    assert!(lists.iter().all(|ids| ids.ptr_eq(lists[0])));
    // Each use of the overloaded name is bound to every overload, in declaration order; the
    // types in the parameters are the prelude's.
    let r = zedc::resolve::resolve(&built(3)).unwrap();
    let sets: Vec<Vec<usize>> = r
        .uses
        .values()
        .filter_map(|f| match f {
            Ref::Bound(ids) => Some(ids.iter().copied().collect()),
            Ref::Prelude(_) => None,
        })
        .collect();
    assert_eq!(sets.len(), 3);
    assert!(
        sets.iter()
            .all(|v| v.len() == 3 && v.is_sorted() && *v == sets[0])
    );
}

/// Resolves each program of `shapes` on a 2 MiB stack, 100,000 deep and 12,500 deep, and checks
/// the time is linear. Resolution recursed once per level of nesting, and overflowed this stack
/// near 10,000.
fn resolves_deep(shapes: &[&str]) {
    use zed_tests::deep::{on_small_stack, program, statements};
    let n = 12_500;
    let deep = 8 * n;
    on_small_stack(|| {
        for &shape in shapes {
            let small = statements(&program(shape, n).text);
            let large = statements(&program(shape, deep).text);
            zed_tests::scaling::check_order(&format!("resolving {shape}"), n, 1, |k| {
                let stmts = if k == n { &small } else { &large };
                assert!(!zedc::resolve::resolve(stmts).unwrap().binders.is_empty());
            });
            let r = zedc::resolve::resolve(&large).unwrap();
            match shape {
                // The `c` inside every block is the top level's.
                "nested blocks" => {
                    let c = r.binders.iter().position(|b| b.name == "c").unwrap();
                    let reads_c = r.uses.values().filter(|u| **u == Ref::Bound([c].into()));
                    assert_eq!(reads_c.count(), 1);
                }
                // Nested lambdas bind their parameters in written order, after `main`, its
                // port and `t`.
                "nested lambdas" => {
                    let names = r.binders[3..].iter().map(|b| b.name.as_str());
                    assert!(names.enumerate().all(|(i, x)| x == format!("x{i}")));
                    assert_eq!(r.binders.len(), 3 + deep);
                }
                // Each call names the one `f`.
                "nested calls" => {
                    let f = r.binders.iter().position(|b| b.name == "f").unwrap();
                    let calls = r.uses.values().filter(|u| **u == Ref::Bound([f].into()));
                    assert_eq!(calls.count(), deep);
                }
                _ => {}
            }
        }
    });
}

#[test]
fn sums_negations_lambdas_and_long_bodies_100000_deep_resolve_on_a_2_mib_stack() {
    resolves_deep(&[
        "a left-nested sum",
        "nested negations",
        "nested lambdas",
        "a long sum in a function's body",
    ]);
}

#[test]
fn blocks_nested_100000_deep_resolve_on_a_2_mib_stack() {
    resolves_deep(&["nested blocks"]);
}

#[test]
fn else_if_chains_and_parenthesized_sums_100000_deep_resolve_on_a_2_mib_stack() {
    resolves_deep(&["an `else if` chain", "a sum nested in parentheses"]);
}

#[test]
fn calls_and_tuples_nested_100000_deep_resolve_on_a_2_mib_stack() {
    resolves_deep(&["nested calls", "nested tuples"]);
}

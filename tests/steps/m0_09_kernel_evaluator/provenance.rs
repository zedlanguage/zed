//! The evaluator's provenance walks (item T14-provenance): the origins of a failure, found in
//! one backward pass over the run graph, and terms whose subterms are shared, as a term built
//! by cloning is.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::term::build::{if_, let_, lit, prim, var};
use zed_kernel::{Evaluator, Family, Prim, Provenance, Term, Value, World};
use zed_tests::kernel::*;
use zed_tests::scaling;

/// The value of `t` and the provenance of its run.
fn trace(t: &Term) -> (Value, Provenance) {
    let mut ev = Evaluator::new(World::new()).with_provenance(vec![Value::Int(0)]);
    let v = ev.run(t).unwrap();
    (v, ev.provenance().unwrap())
}

/// The printed terms of the origins of the result's failure, sorted.
fn origin_terms(p: &Provenance) -> Vec<String> {
    let terms = p.fact_terms();
    let mut out: Vec<String> = p
        .origins(p.result())
        .into_iter()
        .map(|j| terms[j].to_string())
        .collect();
    out.sort();
    out
}

/// Asserts that no two facts of `p` share an address.
fn unique(p: &Provenance) {
    let r: Vec<String> = p.repeated().iter().map(|a| a.to_string()).collect();
    assert!(r.is_empty(), "repeated fact addresses: {r:?}");
}

/// `a * b * …` over `xs`, as a balanced tree of products.
fn product(xs: &[Term]) -> Term {
    match xs {
        [x] => x.clone(),
        _ => {
            let (l, r) = xs.split_at(xs.len() / 2);
            mul(product(l), product(r))
        }
    }
}

/// `let row = (#missing0, …, #missing{n-1}) in row.0 * row.1 * … * row.{n-1}`: a row of `n`
/// sensor readings, each missing with an atom of its own, and the product of the row. The
/// tuple's fact reads `n` literals, and each reading's search for its origin passes through it.
fn missing_row(n: usize) -> Term {
    let row = prim(
        Prim::Tuple,
        (0..n)
            .map(|i| lit(Value::atom(&format!("missing{i}"))))
            .collect(),
    );
    let reads: Vec<Term> = (0..n).map(|i| nth(var("row"), i as i64)).collect();
    let_("row", row, product(&reads))
}

#[test]
fn each_missing_reading_of_a_row_is_traced_to_its_literal() {
    let (v, p) = trace(&missing_row(3));
    assert_eq!(v.errs().map(|e| e.len()), Some(3), "{v}");
    assert_eq!(
        origin_terms(&p),
        ["#missing0", "#missing1", "#missing2"],
        "each member first appears at its literal, not at the tuple that holds all three"
    );
}

#[test]
fn a_value_that_is_not_a_failure_has_no_origins() {
    let (v, p) = trace(&add(lit(2), lit(3)));
    assert_eq!(v, Value::Int(5));
    assert!(p.origins(p.result()).is_empty());
    // A tuple holding a failure is data, not a failure.
    let (_, p) = trace(&prim(Prim::Tuple, vec![lit(Value::atom("late")), lit(1)]));
    assert!(p.origins(p.result()).is_empty());
}

#[test]
fn one_failure_from_two_sources_has_both_origins() {
    // let a = #late; let b = #late in a + b: one atom, which each operand holds.
    let t = let_(
        "a",
        lit(Value::atom("late")),
        let_("b", lit(Value::atom("late")), add(var("a"), var("b"))),
    );
    let (v, p) = trace(&t);
    assert_eq!(v, Value::atom("late"));
    let o = p.origins(p.result());
    assert_eq!(o.len(), 2, "{o:?}");
    assert_eq!(origin_terms(&p), ["#late", "#late"]);
}

#[test]
fn a_failure_read_through_a_variable_many_times_has_one_origin() {
    // let x = #late in x + x + x + x
    let t = let_(
        "x",
        lit(Value::atom("late")),
        product(&[var("x"), var("x"), var("x"), var("x")]),
    );
    let (v, p) = trace(&t);
    assert_eq!(v, Value::atom("late"));
    assert_eq!(origin_terms(&p), ["#late"]);
}

#[test]
fn a_failure_taken_out_of_a_tuple_starts_at_its_literal() {
    // (1, #late).1 * #early: the tuple holds `#late` without being a failure, and passes it on.
    let pair = prim(Prim::Tuple, vec![lit(1), lit(Value::atom("late"))]);
    let t = mul(nth(pair, 1), lit(Value::atom("early")));
    let (v, p) = trace(&t);
    assert_eq!(v.errs().map(|e| e.len()), Some(2), "{v}");
    assert_eq!(origin_terms(&p), ["#early", "#late"]);
}

/// `if true then D else D`, `depth` levels deep, each level's two branches one shared term, as
/// cloning a branch into both arms builds: the term has `depth` distinct nodes and `2^depth`
/// positions, and the run takes one branch per level.
fn shared_branches(depth: usize) -> Term {
    let mut d = Arc::new(lit(1));
    for _ in 0..depth {
        d = Arc::new(Term::If(Arc::new(lit(true)), d.clone(), d));
    }
    Arc::unwrap_or_clone(d)
}

#[test]
fn a_term_shared_by_both_branches_of_each_level_runs_with_provenance() {
    let (v, p) = trace(&shared_branches(10));
    assert_eq!(v, Value::Int(1));
    unique(&p);
    // Per level the `if` and its condition, and the literal at the bottom.
    assert_eq!(p.facts().len(), 2 * 10 + 1);
}

#[test]
fn two_uses_of_a_cloned_term_in_one_scope_are_two_facts() {
    // let a = (if true then 2 else 3) in (if true then 2 else 3) * a, where the second `if`
    // is a clone of the first: the two share their condition and branches, which the run
    // evaluates twice in one scope, so each needs an address of its own.
    let pick = if_(lit(true), lit(2), lit(3));
    let t = let_("a", pick.clone(), mul(pick, var("a")));
    let (v, p) = trace(&t);
    assert_eq!(v, Value::Int(4));
    unique(&p);
    let twos = p
        .fact_terms()
        .iter()
        .filter(|t| t.to_string() == "2")
        .count();
    assert_eq!(twos, 2);
}

#[test]
fn the_origins_of_a_failure_read_through_a_wide_tuple_scale() {
    // The runs are recorded before the timing, which covers the walk alone. A search per
    // member tested each of the tuple's `n` inputs once per member: `O(n²)`. The pass reads
    // every value of the run graph once, each node with a search of the members, `O(W log n)`;
    // here the products' `#errs` sets make `W` itself `n log n`, so the work is `n log² n`:
    // 500, 4000, 32000 readings took 12.5 and then 11.5 times the work (COMPLEXITY.md K25).
    let n = 500;
    let runs: Vec<(usize, Provenance)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, trace(&missing_row(m)).1))
        .collect();
    scaling::check_order(
        "the origins of a row of n missing readings, by n",
        n,
        1,
        |m| {
            let (_, p) = runs.iter().find(|(size, _)| *size == m).expect("recorded");
            assert_eq!(p.origins(p.result()).len(), m);
        },
    );
}

#[test]
fn a_term_shared_by_both_branches_of_each_level_scales() {
    // The run takes `depth` branches, and a fact's position is its parent's and one child
    // index, so recording its provenance is `O(depth)`. Copying the term to one node per
    // position took `2^depth` steps (COMPLEXITY.md K25).
    let n = 3;
    let terms: Vec<(usize, Term)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, shared_branches(m)))
        .collect();
    scaling::check_order(
        "a run with provenance of shared branches, by depth",
        n,
        1,
        |m| {
            let (_, t) = terms.iter().find(|(size, _)| *size == m).expect("built");
            assert_eq!(trace(t).0, Value::Int(1));
        },
    );
}

/// `let row = (#missing0, …) in ((row.0 * row.1) * row.2) * …`: the readings multiplied one
/// at a time, as a fold over a list does. The `k`-th product holds `k` members.
fn missing_chain(n: usize) -> Term {
    let row = prim(
        Prim::Tuple,
        (0..n)
            .map(|i| lit(Value::atom(&format!("missing{i}"))))
            .collect(),
    );
    let product = (1..n).fold(nth(var("row"), 0), |acc, i| {
        mul(acc, nth(var("row"), i as i64))
    });
    let_("row", row, product)
}

#[test]
fn each_missing_reading_of_a_chain_is_traced_to_its_literal() {
    let (v, p) = trace(&missing_chain(4));
    assert_eq!(v.errs().map(|e| e.len()), Some(4), "{v}");
    assert_eq!(
        origin_terms(&p),
        ["#missing0", "#missing1", "#missing2", "#missing3"]
    );
}

#[test]
fn the_origins_of_a_failure_built_one_reading_at_a_time_scale() {
    // The `k`-th product's `#errs` set is made from the one before it by adding one member, so
    // the failures it holds are found from that set's by their difference, and the common
    // members of two sets likewise: `O(n log n)`. Reading every member of each set took
    // `O(n² log n)` (COMPLEXITY.md K25). The runs are recorded before timing.
    let n = 200;
    let runs: Vec<(usize, Provenance)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, trace(&missing_chain(m)).1))
        .collect();
    scaling::check_order(
        "the origins of a chain of n missing readings, by n",
        n,
        1,
        |m| {
            let (_, p) = runs.iter().find(|(size, _)| *size == m).expect("recorded");
            assert_eq!(p.origins(p.result()).len(), m);
        },
    );
}

#[test]
fn the_check_for_repeated_addresses_on_a_chain_of_products_scales() {
    // A chain of n products is n deep, and two positions far apart in it are compared by a
    // walk up to their common ancestor; a set ordered by position made the check `O(n²)`
    // (54.7x at 250 vs 2000). Addresses are found by their hashes. The runs are recorded
    // before timing.
    let n = 250;
    let runs: Vec<(usize, Provenance)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, trace(&missing_chain(m)).1))
        .collect();
    scaling::check_order(
        "the check for repeated addresses on a chain of n products, by n",
        n,
        1,
        |m| {
            let (_, p) = runs.iter().find(|(size, _)| *size == m).expect("recorded");
            assert!(p.repeated().is_empty());
        },
    );
}

/// `let f0 = #late in let f1 = fam({0, 1}, k -> f0) in … f{depth}[0]…[0]`: a table of
/// `depth` levels whose two entries at each level are one shared value, read down to its
/// bottom. The run takes `depth` steps; the value `f{depth}`, read as a tree, has `2^depth`
/// leaves.
fn shared_levels(depth: usize) -> Term {
    let keys = lit(Family::set([0, 1].map(Value::Int)));
    let mut read = var(&format!("f{depth}"));
    for _ in 0..depth {
        read = get(read, lit(0));
    }
    let body = (1..=depth).rev().fold(read, |body, i| {
        let_(
            &format!("f{i}"),
            fam(keys.clone(), "k", var(&format!("f{}", i - 1))),
            body,
        )
    });
    let_("f0", lit(Value::atom("late")), body)
}

#[test]
fn a_failure_read_out_of_a_table_of_shared_levels_starts_at_its_literal() {
    let (v, p) = trace(&shared_levels(6));
    assert_eq!(v, Value::atom("late"));
    unique(&p);
    assert_eq!(origin_terms(&p), ["#late"]);
}

#[test]
fn the_origins_of_a_failure_read_out_of_shared_levels_scale() {
    // The run takes `depth` steps, and the failures each value holds are found once per
    // distinct tuple and family, keyed by its id: `O(depth)`. Walking each value as a tree took
    // `2^depth` steps (COMPLEXITY.md K25). The runs are recorded before the timing.
    shared_levels_scale(2);
}

#[test]
fn the_origins_of_a_failure_read_out_of_deep_shared_levels_scale() {
    // Each level's family holds the level below it, so comparing two levels' maps compares
    // them whole: finding one level's set from another's by their difference made this
    // `O(depth²)`. A family's set is found that way only from a family it was made from.
    shared_levels_scale(128);
}

fn shared_levels_scale(n: usize) {
    let runs: Vec<(usize, Provenance)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, trace(&shared_levels(m)).1))
        .collect();
    scaling::check_order(
        "the origins of a failure read out of shared levels, by depth",
        n,
        1,
        |m| {
            let (_, p) = runs.iter().find(|(size, _)| *size == m).expect("recorded");
            assert_eq!(p.origins(p.result()).len(), 1);
        },
    );
}

/// Whether `v` is `m` or holds it, read as a tree.
fn holds(v: &Value, m: &Value) -> bool {
    let mut todo = vec![v];
    while let Some(v) = todo.pop() {
        if v == m {
            return true;
        }
        match v {
            Value::Atom(a) => todo.extend(&a.args),
            Value::Tuple(xs) | Value::Path(xs) => todo.extend(xs.iter()),
            Value::Family(f) => todo.extend(f.iter().map(|(_, x)| x)),
            _ => {}
        }
    }
    false
}

/// The origins of fact `i`'s failure by a search per member over every input, each value read
/// as a tree: the definition, at a cost only small runs afford.
fn origins_by_search(p: &Provenance, i: usize) -> BTreeSet<usize> {
    let Some(v @ Value::Atom(_)) = &p.facts()[i].value else {
        return BTreeSet::new();
    };
    let members: Vec<Value> = match v.errs() {
        Some(set) => set.iter().map(|(k, _)| k.clone()).collect(),
        None => vec![v.clone()],
    };
    let mut out = BTreeSet::new();
    for m in &members {
        let mut seen = BTreeSet::from([i]);
        let mut todo = vec![i];
        while let Some(j) = todo.pop() {
            let mut held = false;
            for &k in &p.facts()[j].inputs {
                if p.facts()[k].value.as_ref().is_some_and(|v| holds(v, m)) {
                    held = true;
                    if seen.insert(k) {
                        todo.push(k);
                    }
                }
            }
            if !held {
                out.insert(j);
            }
        }
    }
    out
}

/// Asserts that the origins of every fact of `t`'s run are those the search per member finds.
fn agrees_with_search(t: &Term) {
    let (_, p) = trace(t);
    unique(&p);
    for i in 0..p.facts().len() {
        assert_eq!(p.origins(i), origins_by_search(&p, i), "fact {i} of {t}");
    }
}

/// `shared_branches` with `#late` at the bottom, each level's branches one shared term when
/// `shared`, or two copies built apart.
fn late_branches(depth: usize, shared: bool) -> Arc<Term> {
    match depth {
        0 => Arc::new(lit(Value::atom("late"))),
        _ if shared => {
            let d = late_branches(depth - 1, true);
            Arc::new(Term::If(Arc::new(lit(true)), d.clone(), d))
        }
        _ => Arc::new(Term::If(
            Arc::new(lit(true)),
            late_branches(depth - 1, false),
            late_branches(depth - 1, false),
        )),
    }
}

#[test]
fn the_origins_agree_with_a_search_per_member() {
    let late = || lit(Value::atom("late"));
    let both = let_("a", late(), let_("b", late(), add(var("a"), var("b"))));
    let picked = mul(
        nth(prim(Prim::Tuple, vec![lit(1), late()]), 1),
        lit(Value::atom("early")),
    );
    for t in [
        missing_row(5),
        missing_chain(6),
        shared_levels(5),
        Arc::unwrap_or_clone(late_branches(4, true)),
        both,
        picked,
    ] {
        agrees_with_search(&t);
    }
}

#[test]
fn a_shared_term_and_its_copy_built_apart_have_the_same_provenance() {
    let (v, p) = trace(&late_branches(5, true));
    let (w, q) = trace(&late_branches(5, false));
    assert_eq!(v, w);
    let show = |p: &Provenance| -> Vec<String> {
        p.facts()
            .iter()
            .map(|f| format!("{} {:?} {:?}", f.address, f.value, f.inputs))
            .collect()
    };
    assert_eq!(show(&p), show(&q));
    assert_eq!(p.origins(p.result()), q.origins(q.result()));
    assert_eq!(origin_terms(&p), ["#late"]);
}

#[test]
fn an_empty_failure_has_no_origins() {
    let empty = Value::atom_with("errs", vec![Value::Family(Family::new())]);
    let (v, p) = trace(&lit(empty.clone()));
    assert_eq!(v, empty);
    assert!(p.origins(p.result()).is_empty());
    assert_eq!(origins_by_search(&p, p.result()), BTreeSet::new());
}

#[test]
fn a_failure_read_by_itself_is_its_own_origin() {
    let (_, p) = trace(&lit(Value::atom("late")));
    assert_eq!(p.origins(p.result()), BTreeSet::from([p.result()]));
}

#[test]
fn a_term_shared_by_both_parts_of_the_root_runs_once_at_each_position() {
    // `let x = #late * #early in #late * #early`, the bound term and the body one shared
    // term: the run evaluates it at two positions, and the `let` reads both, so each
    // literal is an origin at each position.
    let both = Arc::new(mul(lit(Value::atom("late")), lit(Value::atom("early"))));
    let t = Term::Let("x".into(), both.clone(), both);
    let (v, p) = trace(&t);
    assert_eq!(v.errs().map(|e| e.len()), Some(2), "{v}");
    unique(&p);
    let o = p.origins(p.result());
    let at: Vec<String> = o
        .iter()
        .map(|&j| p.facts()[j].address.to_string())
        .collect();
    assert_eq!(at, [".0.0@(0)", ".0.1@(0)", ".1.0@(0)", ".1.1@(0)"]);
    agrees_with_search(&t);
}

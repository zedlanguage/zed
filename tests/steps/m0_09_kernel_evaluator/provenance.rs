//! The evaluator's provenance walks (item T14-provenance): the origins of a failure, found in
//! one backward pass over the run graph, and terms whose subterms are shared, as a term built
//! by cloning is.

use std::sync::Arc;

use zed_kernel::term::build::{if_, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Provenance, Term, Value, World};
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
    let terms = p.terms();
    let mut out: Vec<String> = p
        .origins(p.result())
        .into_iter()
        .map(|j| terms[p.facts()[j].address.node.position() as usize].to_string())
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
    let terms = p.terms();
    let twos = p
        .facts()
        .iter()
        .filter(|f| terms[f.address.node.position() as usize].to_string() == "2")
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
#[ignore = "open: unshare copies the term to one node per position, 2^depth here; see COMPLEXITY.md"]
fn a_term_shared_by_both_branches_of_each_level_scales() {
    // The run takes `depth` branches; recording its provenance copies the whole term, each
    // shared branch once per position: `2^depth` nodes.
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
#[ignore = "open: origins reads each product's #errs set whole, n²/2 members on a chain; see COMPLEXITY.md K25"]
fn the_origins_of_a_failure_built_one_reading_at_a_time_scale() {
    // The `k`-th product's `#errs` set shares all but one member with the one before it, and
    // the pass tests every member of each: `O(n² log n)`. The runs are recorded before timing.
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

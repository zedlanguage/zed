//! Remaps as the kernel terms they elaborate to (DESIGN.md sec:remap_law, sec:grouping,
//! sec:push_pull, sec:level_names, the bounds table of sec:type_language), run by the M0.9
//! reference evaluator. `into (q)` is `reindex` with a key map built from `q`, a `fold` for
//! each level collapsed by `><`, and `discard` for a truncation (sec:grammar, kernel
//! desugaring of `ReduceTail`; the row `m into (… -> _)` of the kernel table).
//!
//! Each test writes out the value the spec's rule or example gives. The evaluator checks the
//! collision rule on every run (T-Reindex), so a pattern the catalog rejects is shown here as
//! the collision its data would cause; the compile-time rejection and its menu are tested on
//! the source spelling in the other files of this group.

use zed_kernel::term::build::{if_, lit, prim};
use zed_kernel::{Family, KernelError, Prim, Term, Value, eval};
use zed_tests::kernel::*;

/// A family from its leaves, each a keypath and a value.
fn leaves(ls: Vec<(Vec<Value>, Value)>) -> Term {
    lit(Value::Family(Family::from_leaves(ls).unwrap()))
}

fn i(n: i64) -> Value {
    Value::Int(n)
}

/// `[x0, x1, …]`: a list, keyed by position.
fn list(xs: &[i64]) -> Term {
    lit(Value::Family(Family::of(
        xs.iter().enumerate().map(|(k, &x)| (k as i64, x)),
    )))
}

fn show(t: &Term) -> String {
    match eval(t) {
        Ok(v) => v.to_string(),
        Err(e) => format!("error: {e:?}"),
    }
}

/// `sales` of sec:level_names, `region -> day -> sku -> quantitySold`:
/// `{ "east" -> [{ "B7" -> 5 }], "west" -> [{ "A12" -> 3, "B7" -> 1 }, { "A12" -> 2 }] }`.
fn sales() -> Term {
    leaves(vec![
        (vec![s("east"), i(0), s("B7")], i(5)),
        (vec![s("west"), i(0), s("A12")], i(3)),
        (vec![s("west"), i(0), s("B7")], i(1)),
        (vec![s("west"), i(1), s("A12")], i(2)),
    ])
}

/// The output keypath built from the source keypath's keys at `order`.
fn permute(f: Term, order: &[i64]) -> Term {
    let order = order.to_vec();
    reindex(
        f,
        func(|[p, _]| path(order.iter().map(|&j| key(p.clone(), j)).collect())),
        func(|[_, v]| v),
    )
}

/// `{ "a" -> {1 -> 10, 2 -> 20}, "b" -> {1 -> 30} }`, two levels.
fn two() -> Term {
    leaves(vec![
        (vec![s("a"), i(1)], i(10)),
        (vec![s("a"), i(2)], i(20)),
        (vec![s("b"), i(1)], i(30)),
    ])
}

fn tuple(items: Vec<Term>) -> Term {
    prim(Prim::Tuple, items)
}

// ---- Repack (sec:remap_law, "The legal moves", 1) ----

#[test]
fn transpose_levels() {
    // sec:remap_law: `as (k1 -> k2 -> v) into (k2 -> k1 -> v)  // transpose levels`.
    assert_eq!(
        show(&permute(two(), &[1, 0])),
        r#"{1 -> {"a" -> 10, "b" -> 30}, 2 -> {"a" -> 20}}"#
    );
}

#[test]
fn permute_three_levels_and_back() {
    // sec:level_names, transfer table: `sales into (sku -> region -> day -> quantitySold)`.
    let moved = permute(sales(), &[2, 0, 1]);
    assert_eq!(
        show(&moved),
        r#"{"A12" -> {"west" -> {0 -> 3, 1 -> 2}}, "B7" -> {"east" -> {0 -> 5}, "west" -> {0 -> 1}}}"#
    );
    // A permutation is a bijection: the inverse permutation gives `sales` back.
    assert_eq!(
        eval(&permute(moved, &[1, 2, 0])).unwrap(),
        eval(&sales()).unwrap()
    );
}

#[test]
fn as_alone_is_the_identity() {
    // sec:remap_law: "`as` alone (`m as (r -> c -> v)`) is the identity remap and only names
    // levels".
    assert_eq!(
        eval(&permute(sales(), &[0, 1, 2])).unwrap(),
        eval(&sales()).unwrap()
    );
}

#[test]
fn flatten_to_a_tuple_key_and_back() {
    // sec:remap_law: `as (k1 -> k2 -> v) into ((k1, k2) -> v)  // flatten to a tuple key`.
    let flat = reindex(
        two(),
        func(|[p, _]| path(vec![tuple(vec![key(p.clone(), 0), key(p, 1)])])),
        func(|[_, v]| v),
    );
    assert_eq!(
        show(&flat),
        r#"{("a", 1) -> 10, ("a", 2) -> 20, ("b", 1) -> 30}"#
    );
    // Untupling, `as (t -> v) into (t.0 -> t.1 -> v)`, is its inverse.
    let back = reindex(
        flat,
        func(|[p, _]| path(vec![nth(key(p.clone(), 0), 0), nth(key(p, 0), 1)])),
        func(|[_, v]| v),
    );
    assert_eq!(eval(&back).unwrap(), eval(&two()).unwrap());
}

#[test]
fn bijective_key_transform() {
    // sec:remap_law: `as (k -> v) into (k + 1 -> v)  // bijective key transform`.
    let shifted = reindex(
        list(&[10, 20, 30]),
        func(|[p, _]| path(vec![add(key(p, 0), lit(1))])),
        func(|[_, v]| v),
    );
    assert_eq!(show(&shifted), "{1 -> 10, 2 -> 20, 3 -> 30}");
}

// ---- Widen (sec:remap_law, "The legal moves", 2) ----

#[test]
fn widen_a_key_with_the_value() {
    // sec:remap_law: `as (k1 -> k2 -> v) into (k1 -> (k2, v) -> v)  // key widened with the
    // value: still injective`.
    let w = reindex(
        two(),
        func(|[p, v]| path(vec![key(p.clone(), 0), tuple(vec![key(p, 1), v])])),
        func(|[_, v]| v),
    );
    assert_eq!(
        show(&w),
        r#"{"a" -> {(1, 10) -> 10, (2, 20) -> 20}, "b" -> {(1, 30) -> 30}}"#
    );
}

#[test]
fn widen_a_key_with_derived_data() {
    // sec:remap_law: `as (k -> v) into ((k, f(k)) -> v)  // key widened with derived data`,
    // here `f(k) = k * k`.
    let w = reindex(
        list(&[10, 20, 30]),
        func(|[p, _]| {
            let k = key(p, 0);
            path(vec![tuple(vec![k.clone(), mul(k.clone(), k)])])
        }),
        func(|[_, v]| v),
    );
    assert_eq!(show(&w), "{(0, 0) -> 10, (1, 1) -> 20, (2, 4) -> 30}");
}

#[test]
fn widen_by_a_key_function_gives_ten_groups_of_ten() {
    // Bounds table, row `m as (k -> v) into (w(k) -> k -> v)`: "a 100-entry array widened by
    // `i div 10` has ten guaranteed groups of ten guaranteed entries".
    let xs: Vec<i64> = (0..100).collect();
    let w = reindex(
        list(&xs),
        func(|[p, _]| path(vec![idiv(key(p.clone(), 0), lit(10)), key(p, 0)])),
        func(|[_, v]| v),
    );
    let sizes = counts(w);
    assert_eq!(
        show(&sizes),
        "{0 -> 10, 1 -> 10, 2 -> 10, 3 -> 10, 4 -> 10, 5 -> 10, 6 -> 10, 7 -> 10, 8 -> 10, 9 -> 10}"
    );
}

// ---- Truncate (sec:remap_law, "The legal moves", 3) ----

/// `discard` keeping the first `depth` levels, the last of them as set leaves.
fn truncate(f: Term, depth: i64) -> Term {
    discard_with(f, move |p, _| {
        if_(
            eq(prim(Prim::PathLen, vec![p]), lit(depth)),
            atom("boundary"),
            lit(true),
        )
    })
}

#[test]
fn truncate_drops_the_values_and_keeps_the_keys() {
    // sec:remap_law: `as (k1 -> k2 -> v) into (k1 -> k2 -> _)  // keep the key structure,
    // discard values: result type K1 -> (K2 -> K2) (set-leaf)`.
    assert_eq!(show(&truncate(two(), 2)), r#"{"a" -> {1, 2}, "b" -> {1}}"#);
}

#[test]
fn truncate_to_the_outer_level() {
    // sec:remap_law: "Truncate — drop a suffix of levels, discarding everything beneath a
    // kept prefix ... the last kept level's keys become the leaves (a set at that level)":
    // `sales into (region -> _)`.
    assert_eq!(show(&truncate(sales(), 1)), r#"{"east", "west"}"#);
    // `sales into (region -> day -> sku -> _)`, the first repair of the worked collision.
    assert_eq!(
        show(&truncate(sales(), 3)),
        r#"{"east" -> {0 -> {"B7"}}, "west" -> {0 -> {"A12", "B7"}, 1 -> {"A12"}}}"#
    );
}

// ---- The illegal move (sec:remap_law) ----

#[test]
fn dropping_a_discriminator_above_surviving_values_collides() {
    // sec:remap_law: `as (region -> day -> sku -> r) into (region -> day -> r)  // ✗
    // Collision`: west's day 0 holds two skus, so two values land on ("west", 0).
    let t = permute(sales(), &[0, 1]);
    assert!(
        matches!(eval(&t), Err(KernelError::Collision { .. })),
        "{}",
        show(&t)
    );
}

// ---- Reductions at each level (sec:reduction; sec:level_names, "Derived names") ----

#[test]
fn reduce_the_innermost_level() {
    // sec:level_names: `totals = sales into (region -> day -> sku >< (+) -> quantitySold);`
    // "totals is { "east" -> [5], "west" -> [4, 2] }".
    let totals = fold_at(sales(), 3, Term::PrimFn(Prim::Add), None);
    assert_eq!(
        show(&totals),
        r#"{"east" -> {0 -> 5}, "west" -> {0 -> 4, 1 -> 2}}"#
    );
}

#[test]
fn reduce_two_levels_from_the_inside_out() {
    // sec:level_names: "Two reductions in one pattern derive from the inside out: `sales into
    // (region -> day >< (+) -> sku >< (+) -> quantitySold)`".
    let per_day = fold_at(sales(), 3, Term::PrimFn(Prim::Add), None);
    let per_region = fold_at(per_day, 2, Term::PrimFn(Prim::Add), None);
    assert_eq!(show(&per_region), r#"{"east" -> 5, "west" -> 6}"#);
}

#[test]
fn reduce_a_middle_level() {
    // sec:alternatives, row "A reduction over a level by its name": `sales into (region -> sku ->
    // day >< (+) -> quantitySold)`: the day level moves innermost and is folded.
    let moved = permute(sales(), &[0, 2, 1]);
    let t = fold_at(moved, 3, Term::PrimFn(Prim::Add), None);
    assert_eq!(
        show(&t),
        r#"{"east" -> {"B7" -> 5}, "west" -> {"A12" -> 5, "B7" -> 1}}"#
    );
}

#[test]
fn reduce_the_outermost_level() {
    // sec:reduction: "`m into (… -> k >< op -> …)` collapses key level `k` by folding `op` over
    // that level's entries": `sales into (day -> sku -> region >< (+) -> quantitySold)` sums
    // over regions under each (day, sku).
    let moved = permute(sales(), &[1, 2, 0]);
    let t = fold_at(moved, 3, Term::PrimFn(Prim::Add), None);
    assert_eq!(
        show(&t),
        r#"{0 -> {"A12" -> 3, "B7" -> 6}, 1 -> {"A12" -> 2}}"#
    );
}

#[test]
fn reduce_every_level() {
    // `sales into (region >< (+) -> day >< (+) -> sku >< (+) -> quantitySold)`: 5 + 3 + 1 + 2.
    let a = fold_at(sales(), 3, Term::PrimFn(Prim::Add), None);
    let b = fold_at(a, 2, Term::PrimFn(Prim::Add), None);
    assert_eq!(show(&fold(b, Term::PrimFn(Prim::Add), None)), "11");
}

#[test]
fn reduce_with_concatenation_in_key_order() {
    // sec:level_names: `joined = labels into (sku -> pos >< (++) -> label);` "joined is
    // { "A12" -> "redsmall" }": `++` is associative, not commutative, so it folds in the
    // level's order (sec:remap_law, "Ranking").
    let labels = leaves(vec![
        (vec![s("A12"), i(0)], s("red")),
        (vec![s("A12"), i(1)], s("small")),
    ]);
    let t = fold_at(labels, 2, Term::PrimFn(Prim::Concat), None);
    assert_eq!(show(&t), r#"{"A12" -> "redsmall"}"#);
}

#[test]
fn reduce_with_max_and_with_product() {
    // sec:level_names, transfer table: `sales into (region -> day -> sku >< max ->
    // quantitySold)`; Derived names table: `(*)` is `product`.
    let mx = fold_at(sales(), 3, Term::PrimFn(Prim::Max), None);
    assert_eq!(
        show(&mx),
        r#"{"east" -> {0 -> 5}, "west" -> {0 -> 3, 1 -> 2}}"#
    );
    // On `sales` the product equals the max (3 * 1 = 3), so the product is shown on `two()`,
    // where it differs: 10 * 20 = 200.
    let pr = fold_at(two(), 2, Term::PrimFn(Prim::Mul), None);
    assert_eq!(show(&pr), r#"{"a" -> 200, "b" -> 30}"#);
}

#[test]
fn reduce_with_a_lambda() {
    // sec:level_names: `g = sales into (region -> day -> sku >< ((a, b) -> a + b) ->
    // quantitySold);` folds as `(+)` does.
    let op = func(|[a, b]| add(a, b));
    let t = fold_at(sales(), 3, op, None);
    assert_eq!(
        show(&t),
        r#"{"east" -> {0 -> 5}, "west" -> {0 -> 4, 1 -> 2}}"#
    );
}

#[test]
fn reduce_an_empty_level_with_and_without_an_identity() {
    // sec:reduction, Boom table, "possibly empty | above ∧ identity element — or `>< op else
    // init`, or result type gains `| #empty`"; bounds table row `m >< op`: `V | #empty` only
    // when no identity, no nonempty guarantee and no `else init`.
    let m = leaves(vec![
        (vec![s("a"), i(0)], i(2)),
        (vec![s("b")], Value::Family(Family::new())),
    ]);
    assert_eq!(
        show(&fold_at(m.clone(), 2, Term::PrimFn(Prim::Max), None)),
        r#"{"a" -> 2, "b" -> #empty}"#
    );
    assert_eq!(
        show(&fold_at(m, 2, Term::PrimFn(Prim::Add), Some(lit(0)))),
        r#"{"a" -> 2, "b" -> 0}"#
    );
}

// ---- Grouping by a written residue (sec:grouping) ----

#[test]
fn group_by_a_derived_key_with_the_residue_written() {
    // sec:grouping: `byLower = words into (w.lower -> i -> w);  // words : i -> w; residue `i`
    // written — injective, one level deeper`.
    let words = lit(Value::Family(Family::of([
        (0i64, s("The")),
        (1, s("cat")),
        (2, s("the")),
    ])));
    let by_lower = reindex(
        words,
        func(|[p, w]| path(vec![prim(Prim::Lower, vec![w]), key(p, 0)])),
        func(|[_, w]| w),
    );
    assert_eq!(
        show(&by_lower),
        r#"{"cat" -> {1 -> "cat"}, "the" -> {0 -> "The", 2 -> "the"}}"#
    );
}

#[test]
fn word_count_groups_then_folds() {
    // sec:tour_collections:
    // `counts = text.split(" ") as (i -> w) into (w.lower -> i -> 1) >< (+);`.
    let words = lit(Value::Family(Family::of(
        ["the", "Cat", "the", "cat", "sat"]
            .iter()
            .enumerate()
            .map(|(k, w)| (k as i64, s(w))),
    )));
    let ones = reindex(
        words,
        func(|[p, w]| path(vec![prim(Prim::Lower, vec![w]), key(p, 0)])),
        func(|[_, _]| lit(1)),
    );
    let counts = fold_at(ones, 2, Term::PrimFn(Prim::Add), None);
    assert_eq!(show(&counts), r#"{"cat" -> 2, "sat" -> 1, "the" -> 2}"#);
}

#[test]
fn a_scatter_and_a_gather_are_one_grouping_remap() {
    // sec:push_pull: "A scatter `hist[s.len] <- 1` and a gather ... elaborate to the identical
    // kernel term — the grouping remap `as (i -> s) into (s.len -> i -> _)` (residue `i`
    // written) with a count reduction."
    let strs = lit(Value::Family(Family::of(
        ["a", "bb", "cc", "d", "eee"]
            .iter()
            .enumerate()
            .map(|(k, w)| (k as i64, s(w))),
    )));
    let grouped = reindex(
        strs,
        func(|[p, w]| path(vec![prim(Prim::Len, vec![w]), key(p, 0)])),
        func(|[_, w]| w),
    );
    let hist = counts(truncate(grouped, 2));
    assert_eq!(show(&hist), "{1 -> 2, 2 -> 2, 3 -> 1}");
}

#[test]
fn invert_a_relation_into_a_set_per_key() {
    // sec:power: `whoTeaches = teacherOf as (teacher -> course) into (course -> teacher -> _);
    // // teacherOf : Teacher -> Course; result Course ->? {Teacher}`.
    let teacher_of = lit(Value::Family(Family::of([
        ("ann", s("math")),
        ("bob", s("art")),
        ("cy", s("math")),
    ])));
    let inverted = reindex(
        teacher_of,
        func(|[p, c]| path(vec![c, key(p, 0)])),
        func(|[_, c]| c),
    );
    assert_eq!(
        show(&truncate(inverted, 2)),
        r#"{"art" -> {"bob"}, "math" -> {"ann", "cy"}}"#
    );
}

// ---- Rank insertion (sec:remap_law, "Ranking: order is a key you add") ----

#[test]
fn desc_inserts_a_rank_with_ties_grouped_beneath() {
    // sec:remap_law: `byScore = scores into (desc score -> name -> score);` rank insertion is
    // the widen `k ↦ (rank(k), k)`; "tied entries remain a group beneath their shared rank,
    // distinguished by the surviving original keys".
    let scores = lit(Value::Family(Family::of([
        ("ann", 3i64),
        ("bob", 5),
        ("cy", 3),
    ])));
    let gt = |a, b| bin(Prim::Gt, a, b);
    let by_score = rank_widen(scores.clone(), &|v| v, &gt);
    assert_eq!(
        show(&by_score),
        r#"{0 -> {"bob" -> 5}, 1 -> {"ann" -> 3, "cy" -> 3}}"#
    );
    // `asc score`: the ranks run the other way.
    let by_asc = rank_widen(scores, &|v| v, &lt);
    assert_eq!(
        show(&by_asc),
        r#"{0 -> {"ann" -> 3, "cy" -> 3}, 1 -> {"bob" -> 5}}"#
    );
}

#[test]
fn a_filtered_list_ranks_under_its_kept_positions() {
    // sec:remap_law: "`[3, 1, 4].where(x -> x > 2).sort(desc x -> x)` is `{0 -> {2 -> 4},
    // 1 -> {0 -> 3}}`, each value under its position in the source".
    let kept = discard_with(list(&[3, 1, 4]), |_, v| bin(Prim::Gt, v, lit(2)));
    let gt = |a, b| bin(Prim::Gt, a, b);
    assert_eq!(
        show(&rank_widen(kept, &|v| v, &gt)),
        "{0 -> {2 -> 4}, 1 -> {0 -> 3}}"
    );
}

// ---- The witness catalog (sec:grouping) ----

fn range(lo: i64, hi: i64) -> Term {
    lit(Value::Family(Family::of((lo..hi).map(|k| (k, k * 10)))))
}

/// `m as (k -> v) into (g(k) -> v)`.
fn rekey(f: Term, g: impl FnOnce(Term) -> Term) -> Term {
    reindex(f, func(|[p, _]| path(vec![g(key(p, 0))])), func(|[_, v]| v))
}

fn collides(t: &Term) -> bool {
    matches!(eval(t), Err(KernelError::Collision { .. }))
}

#[test]
fn witness_strictly_monotone_arithmetic() {
    // sec:grouping: "strictly monotone arithmetic on refined integer ranges (`k+1`, `2*k`)".
    assert_eq!(
        show(&rekey(range(0, 3), |k| mul(lit(2), k))),
        "{0 -> 0, 2 -> 10, 4 -> 20}"
    );
}

#[test]
fn witness_modulo_over_a_range_no_wider_than_the_modulus() {
    // sec:grouping: "`k mod p` where the domain is at most `p` contiguous integers ... one
    // integer wider it fails".
    assert_eq!(
        show(&rekey(range(5, 10), |k| modulo(k, lit(5)))),
        "{0 -> 50, 1 -> 60, 2 -> 70, 3 -> 80, 4 -> 90}"
    );
    assert!(collides(&rekey(range(5, 11), |k| modulo(k, lit(5)))));
}

/// `{(k1, k2) -> 10 * k1 + k2}` over `k1 in 0..<rows`, `k2 in 0..<cols`, as a tuple key.
fn grid(rows: i64, cols: i64) -> Term {
    lit(Value::Family(Family::of((0..rows).flat_map(|a| {
        (0..cols).map(move |b| (Value::tuple(vec![i(a), i(b)]), 10 * a + b))
    }))))
}

#[test]
fn witness_affine_packing_and_its_stride_condition() {
    // sec:grouping: "affine packing ... `(k1, k2) ↦ k1·s + k2` on `k2 : int[0..<s]` ... Each
    // stride must dominate the span of the keys beneath it ... one integer short and the
    // packing collides".
    let pack = |stride: i64| {
        rekey(grid(2, 3), move |t| {
            add(mul(nth(t.clone(), 0), lit(stride)), nth(t, 1))
        })
    };
    assert_eq!(
        show(&pack(3)),
        "{0 -> 0, 1 -> 1, 2 -> 2, 3 -> 10, 4 -> 11, 5 -> 12}"
    );
    assert!(collides(&pack(2)));
}

#[test]
fn witness_unpacking_is_the_inverse_under_euclidean_division() {
    // sec:grouping: "the quotient/remainder pair `k ↦ (k div s, k mod s)` as its two-sided
    // inverse — under the Euclidean `div`/`mod`", negative keys included.
    let unpack = rekey(range(-3, 3), |k| {
        tuple(vec![idiv(k.clone(), lit(3)), modulo(k, lit(3))])
    });
    assert_eq!(
        show(&unpack),
        "{(-1, 0) -> -30, (-1, 1) -> -20, (-1, 2) -> -10, (0, 0) -> 0, (0, 1) -> 10, (0, 2) -> 20}"
    );
    let repack = rekey(unpack, |t| add(mul(nth(t.clone(), 0), lit(3)), nth(t, 1)));
    assert_eq!(eval(&repack).unwrap(), eval(&range(-3, 3)).unwrap());
}

#[test]
fn witness_unimodular_skew_and_its_inverse() {
    // sec:grouping: "a square `A` of determinant ±1 is a bijection whose inverse is again an
    // integer affine map, as the skew `(i, j) ↦ (i, i + j)` of a wavefront schedule is, with
    // inverse `(a, c) ↦ (a, c - a)`".
    let skew = rekey(grid(2, 2), |t| {
        tuple(vec![nth(t.clone(), 0), add(nth(t.clone(), 0), nth(t, 1))])
    });
    assert_eq!(
        show(&skew),
        "{(0, 0) -> 0, (0, 1) -> 1, (1, 1) -> 10, (1, 2) -> 11}"
    );
    let back = rekey(skew, |t| {
        tuple(vec![nth(t.clone(), 0), sub(nth(t.clone(), 1), nth(t, 0))])
    });
    assert_eq!(eval(&back).unwrap(), eval(&grid(2, 2)).unwrap());
}

#[test]
fn witness_full_column_rank_that_is_not_square() {
    // sec:grouping: "integer affine maps of full column rank — `k ↦ A·k + b` ... columns
    // linearly independent ... injective on all of ℤⁿ with no range condition":
    // `(i, j) ↦ (i + j, i - j, 7)`, columns (1, 1, 0) and (1, -1, 0).
    let t = rekey(grid(2, 2), |t| {
        tuple(vec![
            add(nth(t.clone(), 0), nth(t.clone(), 1)),
            sub(nth(t.clone(), 0), nth(t, 1)),
            lit(7),
        ])
    });
    assert_eq!(
        show(&t),
        "{(0, 0, 7) -> 0, (1, -1, 7) -> 1, (1, 1, 7) -> 10, (2, 0, 7) -> 11}"
    );
    // Rank one, `(i, j) ↦ i + j`, is outside the entry, and the grid shows why.
    assert!(collides(&rekey(grid(2, 2), |t| add(
        nth(t.clone(), 0),
        nth(t, 1)
    ))));
}

#[test]
fn witness_componentwise_maps_on_a_tuple_key() {
    // sec:grouping: "componentwise application of witnessed maps to a tuple key (the key map
    // `(k1, k2) ↦ (f(k1), g(k2))` — a product of injections is an injection)".
    let t = rekey(grid(2, 2), |t| {
        tuple(vec![add(nth(t.clone(), 0), lit(1)), mul(lit(2), nth(t, 1))])
    });
    assert_eq!(
        show(&t),
        "{(1, 0) -> 0, (1, 2) -> 1, (2, 0) -> 10, (2, 2) -> 11}"
    );
}

// ---- Miss atoms (sec:level_names "Named slicing"; sec:push_pull) ----

#[test]
fn a_slice_below_the_top_misses_with_not_found() {
    // sec:level_names: `a12 = sales[sku: "A12"];` "a12 is { "east" -> [#notFound], "west" ->
    // [3, 2] }": `sales.map(days -> days.map(skus -> skus["A12"]))`.
    let read = reindex(
        truncate(sales(), 2),
        func(|[p, _]| p),
        func(|[p, _]| {
            get(
                get(get(sales(), key(p.clone(), 0)), key(p.clone(), 1)),
                lit(s("A12")),
            )
        }),
    );
    assert_eq!(
        show(&read),
        r#"{"east" -> {0 -> #notFound}, "west" -> {0 -> 3, 1 -> 2}}"#
    );
}

#[test]
fn an_injective_rekey_reads_back_with_not_found_off_its_image() {
    // sec:push_pull, conversion table, row "injective with an `inverse(g)` witness": "partial
    // inverse: `y[j] = f(x[g⁻¹(j)])` where defined, else `#notFound`".
    let y = rekey(list(&[10, 20, 30]), |k| mul(lit(2), k));
    let pulled = fam_with(lit(Value::Family(Family::set(0i64..6))), |j| get(y, j));
    assert_eq!(
        show(&pulled),
        "{0 -> 10, 1 -> #notFound, 2 -> 20, 3 -> #notFound, 4 -> 30, 5 -> #notFound}"
    );
}

// ---- Empty levels (sec:remap_law, repack; author decision Q4) ----

#[test]
fn an_empty_inner_level_keeps_its_key_where_the_output_can_place_it() {
    // sec:remap_law: "`{"a" -> {}} as (k -> j -> v) into (k.upper -> j -> v)` is
    // `{"A" -> {}}` ... `{"a" -> {}}` transposed is `{}`".
    let a = || lit(Value::Family(Family::of([("a", Family::new())])));
    let upper = reindex(
        a(),
        func(|[p, _]| path(vec![prim(Prim::Upper, vec![key(p.clone(), 0)]), key(p, 1)])),
        func(|[_, v]| v),
    );
    assert_eq!(show(&upper), r#"{"A" -> {}}"#);
    assert_eq!(show(&permute(a(), &[1, 0])), "{}");
}

// ---- Two sources (sec:joins) ----

#[test]
fn matrix_product_folds_the_shared_level() {
    // sec:joins: `(a, b) into (r -> k -> c >< (+) -> a[r][c] * b[c][k])`, on integers.
    let m = |rows: &[[i64; 2]; 2]| {
        lit(Value::Family(Family::of(rows.iter().enumerate().map(
            |(r, row)| {
                (
                    r as i64,
                    Value::Family(Family::of(
                        row.iter().enumerate().map(|(c, &x)| (c as i64, x)),
                    )),
                )
            },
        ))))
    };
    let a = m(&[[1, 2], [3, 4]]);
    let b = m(&[[5, 6], [7, 8]]);
    let dom = || lit(Value::Family(Family::set(0i64..2)));
    let prod = fam(
        dom(),
        "r",
        fam(
            dom(),
            "k",
            fold(
                fam(
                    dom(),
                    "c",
                    mul(
                        get(get(a, var_("r")), var_("c")),
                        get(get(b, var_("c")), var_("k")),
                    ),
                ),
                Term::PrimFn(Prim::Add),
                None,
            ),
        ),
    );
    assert_eq!(
        show(&prod),
        "{0 -> {0 -> 19, 1 -> 22}, 1 -> {0 -> 43, 1 -> 50}}"
    );
}

fn var_(n: &str) -> Term {
    zed_kernel::term::build::var(n)
}

/// `F.map(inner -> inner.count)` over the top level of `F`: the size of each group. (`map`
/// of the helpers maps the leaves, which here are below the level counted.)
fn counts(f: Term) -> Term {
    shared(f, |f| fam_with(f.clone(), |k| count(get(f, k))))
}

#[test]
fn a_finitely_invertible_key_map_needs_its_residue() {
    // sec:push_pull, conversion table: "finitely invertible (`i div 2`)" is not injective, so
    // `as (k -> v) into (k div 2 -> v)` collides, and writing the residue `k` beneath makes
    // it legal (sec:grouping, "Writing the residue").
    assert!(collides(&rekey(list(&[10, 20, 30]), |k| idiv(k, lit(2)))));
    let grouped = reindex(
        list(&[10, 20, 30]),
        func(|[p, _]| path(vec![idiv(key(p.clone(), 0), lit(2)), key(p, 0)])),
        func(|[_, v]| v),
    );
    assert_eq!(show(&grouped), "{0 -> {0 -> 10, 1 -> 20}, 1 -> {2 -> 30}}");
}

#[test]
fn a_read_past_a_short_list_level() {
    // sec:level_names: "`sales[day: 1]` is `{ "east" -> #outOfBounds, "west" -> { "A12" -> 2 } }`".
    let t = fam_with(lit(Value::Family(Family::set(["east", "west"]))), |r| {
        // The day level's keys are one integer interval, so the elaboration reads it with `At`.
        prim(Prim::At, vec![get(sales(), r), lit(1)])
    });
    assert_eq!(
        show(&t),
        r#"{"east" -> #outOfBounds, "west" -> {"A12" -> 2}}"#
    );
}

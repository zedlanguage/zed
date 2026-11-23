//! The benchmarks of `preimage::tests`, run by `tools/run_tests.sh --bench` and left out of
//! its default run (TEST-bench-move-crates). The correctness tests that keep a small instance
//! of what each checks besides the ratio are `two_large_classes_stay_apart`,
//! `chains_are_read_exactly_at_small_lengths`, `a_staged_chain_is_read_exactly` and
//! `copies_of_an_if_are_one_variable_in_the_linear_stage`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.4 to 0.7 s and a piece stays under
//! 20 s, except the two chains held below the sizes where reading them stops being near
//! linear (see each).

use super::*;

/// The n of [`refused_joins_between_two_large_classes_scale`].
const REFUSED_N: usize = 350_000;

/// The p of [`a_summary_under_a_sloped_tag_is_inverted_and_clamped_in_time_linear_in_its_pieces`].
const SLOPED_P: usize = 100_000;

/// A staircase of `p` constant pieces, piece `i` over `2i..=2i + 1` with value `2i`, under the
/// tag `v - x` of slope -1, so each piece's values are 0 and -1, while each subtree's bounds
/// ([`Tag::vals`]) widen to about its staircase's span and hold 5 for every subtree of more than
/// three pieces. An inversion at `z = {5}` and a clamp `min(_, 5)` then meet no value and change
/// none, yet visit every node (PERF-preimage-treap-hulls): the worst case of the bound proved at
/// [`invert_treap`] and [`clamp_treap`], each node at most once, so O(p) nodes for the inversion
/// and O(p) joins of O(log p) expected for the clamp. The treaps are built outside the measured
/// runs, so the ratio is that of the two calls alone: about 8 (every node) for the inversion and
/// about 8 log(8p) / log p for the clamp's joins, where kept hulls would give O(log p) for this
/// input. Why hulls are not kept: see [`invert_treap`].
#[test]
fn a_summary_under_a_sloped_tag_is_inverted_and_clamped_in_time_linear_in_its_pieces() {
    fn staircase(p: usize) -> Tree {
        let mut root = None;
        for i in 0..p as i64 {
            let node = make_node(
                End::of(2 * i),
                End::of(2 * i + 1),
                Int::ZERO,
                (2 * i).into(),
                None,
                None,
            );
            root = join_treap(root, Some(node));
        }
        let down = Tag {
            mul: Int::ONE,
            slope: Int::from(-1),
            add: Int::ZERO,
        };
        root.map(|n| apply_tag(&n, &down))
    }
    let run = |root: &Tree, p: usize| {
        let mut out = Vec::new();
        invert_treap(root, &Tag::ID, &IntervalSet::of(5, 5), &mut out);
        assert!(out.is_empty(), "no value is 5");
        let clamped = clamp_treap(root, true, &Int::from(5)).expect("ends well inside i128");
        assert_eq!(clamped.as_ref().map_or(0, |n| n.len), p);
        std::hint::black_box(clamped);
    };
    let (small, large) = (staircase(SLOPED_P), staircase(8 * SLOPED_P));
    crate::scaling::compare(
        "inverting and clamping a staircase of p pieces under a tag of slope -1, p and 8p",
        1,
        || run(&small, SLOPED_P),
        || run(&large, 8 * SLOPED_P),
    );
}

/// The k of [`copies_of_an_if_are_read_in_time_near_their_count`].
const COPIES_N: usize = 8000;

/// Eight pairs of classes of n/8 functions each, each pair sharing one function `s(x, y)`
/// (`x` in the first class, `y` in the second), and n/8 functions
/// `t{j}(x) = ra(x: x) && rb(y: x)` a pair, each joining its parameter to the first class
/// and then refused against the second for `s`, which is neither its caller nor its callee.
/// Looking through the smaller class at each refusal is O(n²) (eight pairs, so the place of
/// `s` in each class's order varies less between runs). Each join now costs two finds and one
/// comparison of the lengths of the two classes' sets; no class here holds two functions of
/// two or more parameters, so each refusal compares two inline functions (`s` on both sides)
/// and no set is looked through: 8.00 times the instructions (DynamoRIO's zed_icount, hm2,
/// 2026-11-22, 469,905,587 and 3,759,031,805).
#[test]
fn refused_joins_between_two_large_classes_scale() {
    let (small, large) = (
        two_large_classes(REFUSED_N),
        two_large_classes(8 * REFUSED_N),
    );
    crate::scaling::compare(
        "refused joins between two classes of n/8 functions, eight pairs, n and 8n",
        1,
        || {
            std::hint::black_box(unite(&small.first, &small.joins));
        },
        || {
            std::hint::black_box(unite(&large.first, &large.joins));
        },
    );
}

/// The joins of item LOAD-join-disjoint: `k` chains of `k` one-parameter functions (classes
/// `C_i`), `h` of `k` parameters joined one to each chain's head, and `k` functions `q_i`
/// joining their parameter to chain `i`'s head and then to every other chain's head. Each
/// join of `q_i` to chain `j ≠ i` is refused (`C_i` and `C_j` share `h`, neither caller nor
/// callee): k(k − 1) refusals, two per unordered pair of chains.
fn shared_function_joins(k: usize) -> (Vec<usize>, Vec<(usize, usize)>) {
    let mut first = vec![0];
    let add = |first: &mut Vec<usize>, p: usize| {
        let at = *first.last().expect("starts with 0");
        first.push(at + p);
        at
    };
    let mut joins = Vec::new();
    let mut heads = Vec::new();
    for _ in 0..k {
        let mut prev = add(&mut first, 1);
        heads.push(prev);
        for _ in 1..k {
            let c = add(&mut first, 1);
            joins.push((prev, c));
            prev = c;
        }
    }
    let h = add(&mut first, k);
    joins.extend(heads.iter().enumerate().map(|(i, &c)| (h + i, c)));
    for i in 0..k {
        let q = add(&mut first, 1);
        joins.push((q, heads[i]));
        joins.extend((0..k).filter(|&j| j != i).map(|j| (q, heads[j])));
    }
    (first, joins)
}

/// The joins of [`shared_function_joins`] at `k` = 160 and 452, 25,920 and 205,208
/// parameters (7.92 times). Each of the `k(k − 1)` refusals (two per unordered pair of
/// chains) was decided by looking through the smaller class of `k` functions, `n^1.5` in the
/// `n` parameters: 17.37 times the instructions (item LOAD-join-disjoint, 2026-11-22). The
/// sets now hold only functions of two or more parameters, here `h` alone, kept inline, so
/// each refusal compares two inline functions, `O(1)`: 7.95 times the instructions
/// (DynamoRIO's zed_icount, hm2, 2026-11-22, 15,896,771 and 126,373,868; COMPLEXITY.md row
/// LOAD-join-disjoint).
#[test]
fn joins_refused_for_a_function_shared_by_merged_classes_scale() {
    let (small, large) = (shared_function_joins(160), shared_function_joins(452));
    crate::scaling::compare(
        "joins refused for a function shared by k classes of k functions, k = 160 and 452",
        1,
        || {
            std::hint::black_box(unite(&small.0, &small.1));
        },
        || {
            std::hint::black_box(unite(&large.0, &large.1));
        },
    );
}

/// One function of 50,000 and of 400,000 parameters and no join (from the XR-algos review,
/// Codex, round 1; sizes from cross-review XR-join-disjoint round 2, since at 256 and 2048 the
/// fixed cost of a run hid the growth): a count per pair of class roots of the functions with
/// parameters in both, the candidate of COMPLEXITY.md row LOAD-affine-join, would start at
/// `k(k - 1)/2` pairs here before any join; `unite` costs `O(k)`: 7.98 times the instructions
/// (DynamoRIO's zed_icount, hm2, 2026-11-22, 8,544,673 and 68,221,301).
#[test]
fn one_high_arity_owner_with_no_attempts_does_not_expand_pairs() {
    let small = [0, 50_000];
    let large = [0, 400_000];
    let (roots, joined) = unite(&small, &[]);
    assert!(roots.into_iter().eq(0..small[1]));
    assert_eq!(joined, vec![false; small[1]]);
    crate::scaling::compare(
        "one function with 50,000 and 400,000 parameters, no join",
        1,
        || {
            std::hint::black_box(unite(&small, &[]));
        },
        || {
            std::hint::black_box(unite(&large, &[]));
        },
    );
}

/// One function of 50,000 and of 400,000 parameters, and a join between each two adjacent
/// parameters, every one refused since both classes hold the function (from the XR-algos
/// review, Gemini, round 1, adversary 2B): each refusal compares two inline functions, the
/// same one on each side: 7.99 times the instructions (DynamoRIO's zed_icount, hm2,
/// 2026-11-22, 17,894,520 and 143,021,148, the same in two runs).
#[test]
fn joins_refused_between_the_parameters_of_one_wide_function_scale() {
    let build = |n: usize| ([0, n], (1..n).map(|i| (i - 1, i)).collect::<Vec<_>>());
    let (small, large) = (build(50_000), build(400_000));
    let (roots, joined) = unite(&small.0, &small.1);
    assert!(roots.into_iter().eq(0..small.0[1]));
    assert_eq!(joined, vec![false; small.0[1]]);
    // The steps of `unite` (`unite_steps`), held without a timer: 7n - 4 here (two finds a
    // join in each pass, a find a parameter in the marks and in `hot`, a find a node at the
    // end, no set look-up since each refusal sees the function inline), 8.00 times at 8n
    // (cross-review XR-join-disjoint round 2, where processor time spread from 6.3 to 20.0).
    let steps = |(first, joins): &([usize; 2], Vec<(usize, usize)>)| {
        unite_steps::take();
        std::hint::black_box(unite(first, joins));
        unite_steps::take()
    };
    let (at_n, at_8n) = (steps(&small), steps(&large));
    assert_eq!((at_n, at_8n), (7 * 50_000 - 4, 7 * 400_000 - 4));
    crate::scaling::hold_linear(
        "one function of n parameters, n - 1 refused joins, n = 50,000 and 400,000",
        "steps of unite",
        at_n,
        at_8n,
    );
    crate::scaling::compare(
        "one function of n parameters, n - 1 refused joins, n = 50,000 and 400,000",
        1,
        || {
            std::hint::black_box(unite(&small.0, &small.1));
        },
        || {
            std::hint::black_box(unite(&large.0, &large.1));
        },
    );
}

/// The joins of [`opposed_multi_owner_classes`] at `k` = 64 and 181, about `2k²` parameters
/// (8.0 times). The exact rule looked through a class of `k + 1` functions at each of the `k²`
/// cross refusals, `n^1.5` (Codex, XR-algos round 1: 16.5 times); [`unite`]'s rule refuses each
/// in O(1), since both classes hold two or more functions of two or more parameters: 8.62
/// times the instructions (DynamoRIO's zed_icount, hm2, 2026-11-22, 8,531,964 and
/// 73,546,161).
#[test]
fn many_multi_owner_functions_can_refuse_the_same_cross_pairs_scale() {
    let (small, large) = (
        opposed_multi_owner_classes(64),
        opposed_multi_owner_classes(181),
    );
    crate::scaling::compare(
        "multi-owner classes, k = 64 and 181",
        1,
        || {
            std::hint::black_box(unite(&small.0, &small.1));
        },
        || {
            std::hint::black_box(unite(&large.0, &large.1));
        },
    );
}

/// The joins of [`chains_of_two_parameter_functions`] at `k` = 120 and 340, about `2k²`
/// parameters (8.0 times). The exact rule took 15.2 times the instructions (Gemini, XR-algos
/// round 1, adversary 2A, on b65fc8f5f, 2026-11-22): each of the `k(k - 1)/2` joins of two
/// heads looked through a class of `k + 1` functions. Now each is refused in O(1), both classes
/// holding two or more functions: 8.41 times the instructions (DynamoRIO's zed_icount, hm2,
/// 2026-11-22, 23,634,602 and 198,774,560).
#[test]
fn joins_refused_for_a_shared_function_over_chains_of_two_parameter_functions_scale() {
    let (small, large) = (
        chains_of_two_parameter_functions(120),
        chains_of_two_parameter_functions(340),
    );
    crate::scaling::compare(
        "k chains of k two-parameter functions sharing one function, k = 120 and 340",
        1,
        || {
            std::hint::black_box(unite(&small.0, &small.1));
        },
        || {
            std::hint::black_box(unite(&large.0, &large.1));
        },
    );
}

/// `n/2` functions of two parameters `2i` and `2i + 1`, the joins `(0, 2i)` for `0 < i < n/2`,
/// which merge the even parameters into one class whose set grows to all `n/2` functions, then
/// the joins `(0, 2i + 1)` for `0 <= i < n/2`, each refused by a look-up in that set that finds
/// the function of `2i + 1` (Gemini, cross-review XR-join-disjoint round 3; no other bench here
/// finds a function in a set, nor grows one past `Θ(√n)`). The `n/2 - 1` merges insert into the
/// set and the `n/2` refusals look it up, `O(n log n)` in all: 8.83 times the instructions
/// (DynamoRIO's zed_icount, hm4, 2026-11-22, 54,761,361 and 483,472,420, the same in two runs).
#[test]
fn joins_refused_by_a_look_up_in_a_set_of_n_over_2_functions_scale() {
    let build = |n: usize| {
        let m = n / 2;
        let first: Vec<usize> = (0..=m).map(|i| 2 * i).collect();
        let joins: Vec<(usize, usize)> = (1..m)
            .map(|i| (0, 2 * i))
            .chain((0..m).map(|i| (0, 2 * i + 1)))
            .collect();
        (first, joins)
    };
    let (small, large) = (build(50_000), build(400_000));
    let (roots, joined) = unite(&small.0, &small.1);
    let r = roots[0];
    assert!((0..50_000).step_by(2).all(|v| roots[v] == r));
    assert!((1..50_000).step_by(2).all(|v| roots[v] == v && !joined[v]));
    assert!(joined[r]);
    // The steps of `unite` (`unite_steps`): two finds a join in each pass, 4(n - 1); a find a
    // parameter in the marks, in `hot` and at the end, 3n; a look-up and an insertion a merge,
    // 2(n/2 - 1); a look-up a refusal, n/2. In all 8.5n - 6, 424,994 and 3,399,994, the counts
    // of Gemini's copy of `unite` in round 3.
    let steps = |(first, joins): &(Vec<usize>, Vec<(usize, usize)>)| {
        unite_steps::take();
        std::hint::black_box(unite(first, joins));
        unite_steps::take()
    };
    let (at_n, at_8n) = (steps(&small), steps(&large));
    assert_eq!((at_n, at_8n), (424_994, 3_399_994));
    crate::scaling::compare(
        "n/2 refused joins, each a look-up that finds the function in a set of n/2, n = 50,000 \
         and 400,000",
        1,
        || {
            std::hint::black_box(unite(&small.0, &small.1));
        },
        || {
            std::hint::black_box(unite(&large.0, &large.1));
        },
    );
}

/// [`Gen::chain`] makes a chain of `n` `if`s in work of order `n`: each level reads the
/// one term below it, shared, so neither the work nor the term doubles at a level.
#[test]
fn a_chain_is_made_in_work_of_order_its_length() {
    crate::scaling::check_order("a chain of n ifs over one input made", 200_000, 1, |n| {
        let mut g = Gen::new(0x5851_f42d_4c95_7f2d, true);
        g.chains = true;
        std::hint::black_box(g.chain(n, true));
    });
}

/// A chain of guards on `x mod 3` whose arms move, reflect, negate, scale and clamp the
/// term below, with `min` and `max` across their constant and `0 * u` (COMPLEXITY.md row
/// S22-order-chain: 6.7 ms, 209 ms, 3.37 s and 30.2 s at k = 20, 40, 80 and 160). Each
/// level is one summary over the classes ([`ByClass`]), so the shared term is read once.
/// Until item PREIMAGE-chain-cliff it was held at k = 40: past k = 320 the bound of the
/// summaries by class ([`ByClass::clamp`]) kept the multipliers of the doublings that the
/// clamps had undone, passed `i64`, and each level was read by its guard and arms, 3.5 s at
/// k = 400 and over 60 s at 500. Now 20 ms at k = 400, 87 ms at 2000, 1.06 s at 32,000 and
/// 2.3 s at 64,000 (debug build, measured 2026-11-14, load 25 to 38).
#[test]
fn a_chain_is_read_in_time_near_its_length() {
    crate::scaling::check_order("the preimage of a chain of k ifs", 16_000, 1, |k| {
        chain_preimage(0x5851_f42d_4c95_7f2d, k)
    });
}

/// A chain on `y` whose guards compare `y` with constants or take `y mod 2`, with `min`
/// arms across their constant, and `if`s on a comparison whose arms read the remainder in
/// different ways ([`Walk::by_class_if`], [`ByClass::clamp`]). Until item PREIMAGE-chain-cliff
/// it was held at k = 250: past k = 2000 the bound of [`ByClass::clamp`] passed `i64` as in
/// [`a_chain_is_read_in_time_near_its_length`], 4.4 s at k = 2250 and 17.5 s at 2300, and at
/// 4000 the recursion of `Terms::form` overflowed the 2 MiB test thread stack. Now 51 ms at
/// k = 2250, 0.1 s at 4000, 0.95 s at 32,000 and 3.5 s at 64,000 (debug build, measured
/// 2026-11-14, load 25 to 38).
#[test]
fn a_chain_with_clamps_is_read_in_time_near_its_length() {
    crate::scaling::check_order(
        "the preimage of a chain of k ifs, mixed guards",
        16_000,
        1,
        |k| chain_preimage(0xa, k),
    );
}

/// A chain whose guards compare `x` with constants, with `min` and `max` arms across their
/// constant: one summary of each level ([`Pa::clamp`]).
#[test]
fn a_chain_of_comparisons_is_read_in_time_near_its_length() {
    crate::scaling::check_order(
        "the preimage of a chain of k ifs, comparisons",
        6000,
        1,
        |k| chain_preimage(1, k),
    );
}

/// A chain of guards on `x mod 2` over `[-6, 6]`, which the first split finds wide
/// ([`Split::Wide`]) and the split over the box it found reads exactly ([`preimage_in`]).
/// Row PRE-class-int found it exponential past k = 360 (359G instructions at k = 640) when
/// the bound of [`ByClass`] passed `i64` and each class was read by its own run; item
/// PREIMAGE-chain-cliff fixed the bound after a clamp. The deferred test ran sizes 10 and 80
/// and failed on main cdf07ac4f at 16.1 times the bytes; on main at 7b58d316e it passes, at
/// 8.2 times the work and 8.6 times the bytes, and at k = 2000 and 16,000, past the cliff, at
/// 6.8 and 6.2 (b22-misc, 2026-11-22, load near 50). So this test passed before b22-misc
/// changed any code: it is the deferred test put back, with a size past the cliff added.
#[test]
fn a_chain_split_by_two_classes_is_read_in_time_near_its_length() {
    for n in [10, 2000] {
        crate::scaling::check_order("the preimage of a chain of k ifs, x mod 2", n, 1, |k| {
            chain_preimage(2, k)
        });
    }
}

/// `if x mod 2 == 0 { 2 * s } else { 2 * s + 1 }` nested `k` times over `x` in `[-6, 6]`, then
/// `<= 2`: the values double at every level, so from k near 60 the bound of [`ByClass`]
/// passes `i64` ([`Bound::holds`]) and the summary by class is given up for the run of each
/// class ([`Walk::by_class`]), the fallback row PRE-class-int called exponential. Measured
/// on main at 7b58d316e (b22-misc, 2026-11-22): 29, 101, 175, 392 and 808 ms at k = 100,
/// 200, 400, 800 and 1600, near linear, every answer exact; this test, k = 200 and 1600, 9.3
/// times the instructions and 9.2 times the bytes, under the limit, over the preferred 9. Not
/// proved for every term: a family on which that fallback costs more than `O(n log n)` is
/// not excluded by an argument, only by this test and its siblings above.
#[test]
fn a_doubling_chain_past_the_bound_is_read_in_time_near_its_length() {
    let lit = |n: i64| Term::Lit(Value::Int(n));
    let x = Term::Var("x".into());
    let even = Term::Prim(
        Prim::Eq,
        vec![Term::Prim(Prim::Mod, vec![x.clone(), lit(2)]), lit(0)],
    );
    crate::scaling::check_order("the preimage of k doublings by class", 200, 1, |k| {
        let mut t = x.clone();
        for _ in 0..k {
            let twice = Term::Prim(Prim::Mul, vec![lit(2), t]);
            let odd = Term::Prim(Prim::Add, vec![twice.clone(), lit(1)]);
            t = Term::If(
                Shared::new(even.clone()),
                Shared::new(twice),
                Shared::new(odd),
            );
        }
        let t = Term::Prim(Prim::Le, vec![t, lit(2)]);
        let p = preimage(&t, &domains(), &Demand::Bool(true));
        assert!(p.exact, "k = {k}: {p:?}");
    });
}

/// The preimage of [`staged_chain`] under `false`, whose hulls are tightened by questions
/// to the solver over the whole formula (`presburger::project_each`). Before item
/// PREIMAGE-slow-rounds each question probed every disjunct again; now the points found
/// are kept across the questions and a disjunct is searched from both ends of the chain.
/// What was left was the probe of the formula itself, whose `learn` settled a bound at
/// stage `i` in about `i` rounds of the whole formula (COMPLEXITY.md
/// PREIMAGE-slow-rounds); at 3000 to 24,000 stages it reads 8.03 times the instructions
/// (2026-11-22, PRES-settle-chain-rounds).
#[test]
fn a_staged_chain_under_false_is_read_in_time_near_its_length() {
    crate::scaling::check_order(
        "the preimage under false of a chain of k stages",
        3000,
        1,
        |k| {
            let p = preimage(&staged_chain(k), &domains(), &Demand::Bool(false));
            assert!(p.exact, "k = {k}: {p:?}");
        },
    );
}

/// The linear stage ([`linear`]: the relation, then its projections) of `c + c + ... + c != 1`,
/// a sum of k copies of `c = if y > -5 then 2 * y else min(y, 3)`, each copy made afresh (so
/// each has its own term id, as the shallow copies of seed 7776978274844439420 of
/// `summaries_read_again_give_what_reading_the_term_again_gives` had), added in a balanced tree
/// so the term is of depth log k. Until PREIMAGE-summaries-slow-seed each copy was an
/// auxiliary variable of its own, defined by the same disjunction of its arms, which the solver
/// splits on; the four copies of that seed's round 1 took 13.5 s for one projection. Now
/// `Tr::choices` keys each `if` by its translated guard and arms, so the copies are one
/// variable (`copies_of_an_if_are_one_variable_in_the_linear_stage`). This holds that cost in
/// instructions, in place of the 20 s wall-time limit the seed's test held, which passed or
/// failed with the machine's load (FAIL-preimage-slow-seed-wall-time). Measured 2026-11-15
/// (load 33 to 37): k = 8000 and 64,000, 0.53 s and 7.95 times the instructions; with the
/// lookup in `Tr::choices` turned off, 9.26 times at k = 8 and 64, 26.0 times (21.8 times
/// the bytes) at k = 64 and 512, and the run at k = 8000 passes the piece's time limit.
#[test]
fn copies_of_an_if_are_read_in_time_near_their_count() {
    fn sum(k: usize) -> Term {
        if k == 1 {
            let v = |s: &str| Term::Var(s.into());
            let i = |k: i64| Term::Lit(Value::Int(k));
            return Term::If(
                Shared::new(Term::Prim(Prim::Gt, vec![v("y"), i(-5)])),
                Shared::new(Term::Prim(Prim::Mul, vec![i(2), v("y")])),
                Shared::new(Term::Prim(Prim::Min, vec![v("y"), i(3)])),
            );
        }
        Term::Prim(Prim::Add, vec![sum(k / 2), sum(k - k / 2)])
    }
    let terms = crate::scaling::inputs(COPIES_N, |k| {
        Term::Prim(Prim::Ne, vec![sum(k), Term::Lit(Value::Int(1))])
    });
    crate::scaling::check_order(
        "the linear stage of a sum of k copies of an if",
        COPIES_N,
        1,
        |k| {
            let mut tx = Tx::new();
            let root = tx.terms.add(&terms[&k]);
            let (rel, found) =
                linear(&mut tx, root, &domains(), &Demand::Bool(true)).expect("linear");
            assert!(found.is_ok(), "k = {k}: {found:?}");
            std::hint::black_box(rel);
        },
    );
}

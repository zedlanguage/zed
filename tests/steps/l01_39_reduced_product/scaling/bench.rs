//! Benchmarks of `scaling`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`). What each family computes is checked
//! at small sizes in `scaling.rs`.

use super::*;

/// Runs `f` on a thread with a stack deep enough for the nests of `scaling.rs` (item T2-mid).
fn on_big_stack<R: Send>(f: impl FnOnce() -> R + Send) -> R {
    std::thread::scope(|s| {
        let thread = std::thread::Builder::new().stack_size(1 << 28);
        thread.spawn_scoped(s, f).unwrap().join().unwrap()
    })
}

#[test]
fn narrowing_by_a_conjunction_of_disjunctions_scales() {
    let s = ints(&["x".into(), "y".into()]);
    scaling::check("a conjunction of disjunctions of linear tests", 128, |k| {
        s.assume(&clauses(k), true, &Premises::new());
    });
}

#[test]
fn a_chain_of_lets_and_a_nest_of_ifs_scale() {
    let x0 = ints(&["x0".into()]);
    scaling::check("a chain of `let`s", 400, |k| {
        super::super::arms(&lets(k), &x0);
    });
    // Each level's test implies the one before, so the relation keeps one constraint.
    scaling::check("`if`s nested on one name", 512, |k| {
        super::super::arms(&ifs(k), &x0);
    });
}

#[test]
fn a_join_keeps_the_equalities_of_its_sides_and_scales() {
    // The two sides, built before the timing; the join of the two, reduced, is timed.
    let built = scaling::inputs(32, zero_and_one_sides);
    scaling::check("the join of two sides that fix k names, reduced", 32, |k| {
        let (l, r) = &built[&k];
        l.join(r).reduce();
    });
}

#[test]
fn tests_read_through_the_functions_they_call_scale() {
    let x = ints(&["x".into()]);
    // The terms, built before the timing; walking their arms is timed. Each test closes over
    // the functions it reaches, each once however many paths reach it, so both are linear.
    let chains = scaling::inputs(512, helper_chain);
    scaling::check_order(
        "an `else if` chain of k tests, each calling a function",
        512,
        1,
        |k| {
            super::super::arms(&chains[&k], &x);
        },
    );
    // The preimage still recurses on the depth of the term (item T2-mid), about 4 KB a level
    // here, so the nest runs on a stack of its own: at 256 levels it needs about as much as a
    // test thread holds (2 MiB).
    let nests = scaling::inputs(256, nested_helpers);
    on_big_stack(|| {
        scaling::check_order(
            "one test through k functions, each calling the two before it",
            256,
            1,
            |k| {
                super::super::arms(&nests[&k], &x);
            },
        )
    });
}

#[test]
fn tests_on_names_apart_narrow_in_time_near_their_number() {
    // A test projects the names it is linked to, not the whole relation: the scope, the
    // conjunction and the list of tests are built before the timing.
    let n = 50;
    for or in [false, true] {
        let built = scaling::inputs(n, |k| apart_conjunction(k, or));
        let what = if or {
            "a conjunction of k disjunctions on names apart"
        } else {
            "a conjunction of k tests on names apart"
        };
        scaling::check(what, n, |k| {
            let (s, t) = &built[&k];
            s.assume(t, true, &Premises::new());
        });
    }
    let one_by_one = scaling::inputs(n, |k| {
        let (names, tests) = apart(k, true);
        (ints(&names), tests)
    });
    scaling::check(
        "k disjunctions on names apart, assumed one by one",
        n,
        |k| {
            let (s, tests) = &one_by_one[&k];
            let p = Premises::new();
            tests.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
        },
    );
}

#[test]
fn a_chain_of_shadowing_lets_scales() {
    // `arms` recurses on the depth of the term (T2-mid), so the chain runs on a thread whose
    // stack holds it: 1,600 `let`s at the larger size. Kept at 100: in TEST-bench-move the work
    // grew 9.6 times from 100 and 10.1 from 800.
    let t = std::thread::Builder::new().stack_size(1 << 28).spawn(|| {
        let x0 = ints(&["x0".into()]);
        let terms = scaling::inputs(100, shadows);
        scaling::check("a chain of shadowing `let`s", 100, |k| {
            super::super::arms(&terms[&k], &x0);
        });
    });
    t.expect("a thread").join().expect("the chain scales");
}

#[test]
fn many_reductions_under_exact_scale() {
    // An `@exact` scope reduced after each of k written constraints: a reduction searches only
    // the constraints written since the last one and those on names that changed, and a point
    // kept from an earlier search that the new constraint extends is not searched again, so
    // the k reductions cost about k, for constraints on names apart and for one group linked
    // in a chain. The scopes and constraints are built before the timing.
    for (what, family) in EXACT_FAMILIES {
        let built = scaling::inputs(256, |k| (exact_within(k + 1), family(k)));
        scaling::check(what, 256, |k| {
            let (s, cs) = &built[&k];
            assert!(!reduced_one_by_one(s, cs).bottom);
        });
    }
}

/// `x0 >= 0`, `x1 >= 1`, … `x{k-1} >= k - 1` holding one after another, and at each the test
/// `xi < i` that fails there: what a checker reading a nest of `k` tests on `k` names meets
/// when one case of each test is unreachable.
#[test]
fn a_failing_case_costs_its_test_and_not_the_names_in_scope() {
    let built = scaling::inputs(1200, failing_cases);
    // Emptying each name of a failing case costs the names in scope: O(k²) for the nest.
    scaling::check(
        "a nest of k tests on k names, each failing in one case",
        1200,
        |k| {
            let (s, tests) = &built[&k];
            nest_of_failing_cases(s, tests);
        },
    );
}

#[test]
fn tests_among_the_hubs_of_many_stars_narrow_an_eager_scope_in_linear_time() {
    // `k` tests `n - m <= k`, …, `n - m <= 1` under the `k` stars: each replaces the one
    // before as the tighter (`Conjuncts::tight`), so each removes a conjunct among the hubs
    // and adds one, and neither moves a leaf, since `n = m = -1` meets them all. Each
    // projected every star again: `k` projections per test, 57.4 times the bytes for 8 times
    // the size (item NARROW-eager-scope). The stars of one class, the same conjuncts but for
    // the leaf, are now projected again only when the class's bound on its leaf changes
    // (`Scope::leaf_bound_stays`).
    let built = scaling::inputs(128, stars_of_two_hubs);
    scaling::check(
        "k tests among the hubs of k stars of two hubs, in an eager scope",
        128,
        |k| {
            narrow_hubs(&built[&k], k);
        },
    );
}

#[test]
fn tests_on_the_hubs_of_many_stars_in_an_eager_scope_scale() {
    // `k` tests on the hub `n` of `k` stars, one after another and as a nest of `if`s, in an
    // eager scope. No test moves a leaf, since every leaf lies above every value the tests
    // give `n`, but each projected every star at `n` again, or brought it up to date to find
    // nothing due: O(k) per test and O(k²) in all (item EAGER-if-nest-quadratic). The
    // family's bound on its leaf is now found once per move, and only the leaves it cuts are
    // projected (`Scope::moved_blocks`) or refreshed by a join (`Scope::join`); the search by
    // shortest paths reads a hub's conjuncts in the forest alone, not those of the stars
    // apart from it (`Blocks::in_forest`). COMPLEXITY.md row C49.
    let inputs = scaling::inputs(128, |k| {
        (
            stars_above_the_hubs(k, false),
            stars_above_the_hubs(k, true),
        )
    });
    scaling::check(
        "k tests on a hub of k stars of two hubs and of one, in turn and nested, eager",
        128,
        |k| {
            let (two, one) = &inputs[&k];
            tests_on_a_hub(two, k);
            tests_on_a_hub(one, k);
        },
    );
}

#[test]
fn a_lazy_scope_settles_the_hubs_of_a_class_of_stars_in_linear_time() {
    // `k` stars on the hubs `n` and `m`, a disjunction on both, then `k` tests among the hubs.
    // Each star is a class of its own, its constant differing, and each test changes the
    // conjuncts among the hubs of all `k` classes. The lazy scope projects no star for them:
    // a star moves no hub that the hubs' own block does not, so the leaves stay stale until
    // read (item NARROW-lazy-settle). Projecting one star of each class, `k` projections per
    // test, took 73.3 times the bytes for 8 times the size (negative control, not committed).
    let inputs = scaling::inputs(128, |k| {
        let (start, tests) = a_class_of_stars(k);
        (start.lazy(), tests)
    });
    scaling::check(
        "k tests among the hubs of a class of k stars, lazy",
        128,
        |k| {
            let (start, tests) = &inputs[&k];
            let p = Premises::new();
            tests
                .iter()
                .fold(start.clone(), |s, t| s.assume(t, true, &p));
        },
    );
}

#[test]
fn a_lazy_scope_with_many_disjunctions_among_the_hubs_of_a_star_scales() {
    // A lazy scope projects the star for none of them: each test costs its own part in the
    // hubs' block (item NARROW-lazy-settle). Projecting one star of each set of hubs for each
    // test took 25.4 times the instructions (negative control, not committed).
    disjunctions_scale("k disjunctions among the hubs of a star, lazy", true);
}

#[test]
fn an_eager_scope_with_many_disjunctions_among_the_hubs_of_a_star_scales() {
    // Each test `x + y >= j || x - y >= j` implies the ones before it, which the relation
    // drops (`Conjuncts::pair`), so the star's block holds one disjunction at each test and
    // its pass over its parts costs O(1). Before item ST-B4 every disjunction stayed, and
    // that pass, `Block::of`, the due check and the snapshot of every part, ran over all `k`
    // parts at each test: 25.0 to 26.4 times the instructions for 8 times the size
    // (COMPLEXITY.md C26; META4 O6).
    disjunctions_scale("k disjunctions among the hubs of a star, eager", false);
}

#[test]
fn an_eager_scope_settles_the_hubs_of_a_class_of_stars_in_linear_time() {
    // The tests of the lazy case above, in an eager scope: `k` stars `ai >= n + m - i`, each a
    // class of its own, then `k` tests among their hubs, none of which moves a leaf. Each test
    // projected every star again, the disjunction among the hubs keeping each class's bound
    // from being shown to stay: `k` projections per test, O(k²) (item
    // NARROW-eager-star-redo).
    let inputs = scaling::inputs(96, a_class_of_stars);
    let p = Premises::new();
    scaling::check(
        "k tests among the hubs of a class of k stars, eager",
        96,
        |k| {
            let (start, tests) = &inputs[&k];
            tests
                .iter()
                .fold(start.clone(), |s, t| s.assume(t, true, &p));
        },
    );
}

#[test]
fn an_eager_scope_with_many_distinct_disjunctions_among_the_hubs_of_a_star_scales() {
    // Every disjunction stays in the relation, so the star's block and the hubs' block each
    // hold `k` of them. Each test made both blocks again from all their conjuncts, and
    // checked and recorded every part of each: O(k) per test though one part is new, O(k²)
    // in all (item NARROW-eager-star-redo).
    let inputs = scaling::inputs(80, distinct_disjunctions_among_the_hubs_of_a_star);
    let p = Premises::new();
    scaling::check(
        "k distinct disjunctions among the hubs of a star, eager",
        80,
        |k| {
            let (start, tests) = &inputs[&k];
            tests
                .iter()
                .fold(start.clone(), |s, t| s.assume(t, true, &p));
        },
    );
}

#[test]
fn changes_of_one_block_hold_bounded_memory() {
    // A part's last projection is kept by the part, with what it was projected with beside
    // it (`PartKey`, `PartWith`): each tightening changes the constraints the block's own part
    // is projected with, and each equality those of the disjunction's part, and the scope
    // keeps one entry for each part. Keyed by what they were projected with, the entries grew
    // by one with each change while the conjuncts stayed three: 42 then 322 entries, holding
    // 103536 then 813712 bytes, at k = 40 then 320 (negative control, not committed; item
    // ST-projected-stale). The bytes the whole scope leaves allocated still grow, by the
    // nodes of the union-find of `Blocks`, one for each change (item ST-blocks-stale).
    let n = 160;
    let inputs = scaling::inputs(n, changes_of_one_block);
    let (mut entries, mut held) = (Vec::new(), Vec::new());
    for k in [n, scaling::FACTOR * n] {
        let (s, tests) = &inputs[&k];
        let mut end = change_one_block(s, tests);
        assert!(!end.bottom, "k = {k}: the scope became empty");
        entries.push(end.projected.len());
        let map = std::mem::take(&mut end.projected);
        let ((), freed) = zed_alloc_count::live(|| drop(map));
        held.push(-freed.net);
    }
    eprintln!(
        "entries {entries:?} holding {held:?} bytes at k = {n} and {}",
        scaling::FACTOR * n
    );
    assert_eq!(
        entries[0], entries[1],
        "the parts' entries grew with the changes: {entries:?}"
    );
    assert!(
        held[1] <= held[0].max(0) + 1024,
        "the parts' entries held {} bytes after {} changes, {} after {n}",
        held[1],
        scaling::FACTOR * n,
        held[0]
    );
    scaling::check("k changes of the constraints of one block", n, |k| {
        let (s, tests) = &inputs[&k];
        change_one_block(s, tests);
    });
}

/// `k` disjunctions `v_i - w >= 5 || w - v_(i+1) >= 5`, a chain through the shared name `w`,
/// and `v0 - z >= 5 || z - v0 >= 5`, which makes the chain and `w + z` one block; each `v_i`
/// in 0..=10 and `w`, `z` in -10^6..=10^6; then `k` tests `w + z <= c` that move no
/// interval. The group of `w + z <= c` holds `w` and `z` and each disjunction one of them,
/// so no part is due by the group (item LAZY-hub-coarse), found by reading the one part of
/// `z` and not the k parts of `w` (`Block::reframe` in `product.rs`). The scope is the one
/// made again from no projection. At 12 and 96 it takes 10.6 times the work, with main's rule
/// as with the fix; at 40 and 320 main already takes 18.0 times the work, in
/// `Scope::project_part` under `Scope::project_block` at each test (gdb samples), so the
/// family cannot show the cost of reading the parts: reading the parts of `w` and `z` both
/// gave the same counts at 40 and 320 (negative control, run once, not committed). Kept at 12:
/// in TEST-bench-move the work grew 9.1 times from 12, 10.8 from 24 and 13.9 from 48.
/// COMPLEXITY.md C52.
#[test]
fn tightenings_beside_a_chain_of_disjunctions_scale() {
    let n = 12;
    let inputs = scaling::inputs(n, tightenings_beside_a_chain);
    scaling::check("k tightenings beside a chain of k disjunctions", n, |k| {
        let (s, tests) = &inputs[&k];
        change_one_block(s, tests);
    });
}

/// `v_i - n >= 5 || n - v_i >= 5` for each even `i` and the same on `m` for each odd `i`,
/// then `k` tests `n + m <= c` that move no interval. The group of `n + m <= c` holds `n` and
/// `m`, each of k/2 parts, and no part holds both, so no part is due by the group (item
/// LAZY-hub-coarse); the parts of one of the two are read to find that out
/// (`Block::reframe` in `product.rs`), O(k) reads per test, O(k^2 log k) in all, beside the
/// projections each test costs. COMPLEXITY.md C52. Sized at 64 (8.9 times the work at 8n,
/// 0.02 and 0.2 s), not at 256 (8.8 times, 0.06 and 0.54 s), because building the scopes
/// before the timing grows near `k^2`: the run takes 5.2, 18.9 and 68 s at 64, 128 and 256,
/// over the 20 s piece limit from 128 (plan row SCOPE-assume-disjunctions-setup).
#[test]
fn tightenings_of_a_sum_beside_disjunctions_on_each_name_scale() {
    let n = 64;
    let inputs = scaling::inputs(n, tightenings_of_a_sum);
    scaling::check(
        "k tightenings of n + m beside k disjunctions each on n or m",
        n,
        |k| {
            let (s, tests) = &inputs[&k];
            change_one_block(s, tests);
        },
    );
}

/// A binding over several inputs narrows each of them (item PA-walk-multi), and a test of it
/// reads, from the last read of the summary, only the inputs narrowed since: the leaves set in
/// the trees of what summaries read grow linearly in the number of tests, where reading
/// every input each time grows with its square.
#[test]
fn a_binding_over_many_inputs_narrows_each_and_is_read_in_linear_time() {
    let built: BTreeMap<usize, (Scope, Term)> = [40, 320]
        .into_iter()
        .map(|k| {
            let (names, t) = sums_read_as_inputs_narrow(k);
            (k, (ints(&names), t))
        })
        .collect();
    let counted = |k: usize| {
        let (s, t) = &built[&k];
        scaling::on_a_thread(1 << 26, || {
            let before = zedc::store::preimage::counts::image_sets();
            let a = super::super::arms(t, s);
            // Every `xi >= 0`, so `z >= 0` and `wk >= k`: only the false arm of `wk >= 0` is unreachable.
            // The arms in order: each `xi >= 0` true, `wk >= 0` true and false, each `xi >= 0` false.
            let unreachable: Vec<usize> = (0..a.len()).filter(|&i| !a[i].reachable()).collect();
            assert_eq!(unreachable, [k + 1], "{k} tests");
            zedc::store::preimage::counts::image_sets() - before
        })
    };
    scaling::hold(
        "tests of a binding over many inputs: 40 and 320 tests",
        "image sets made",
        counted(40),
        counted(320),
        1,
    );
    scaling::check("tests of a binding over many inputs", 40, |k| {
        let (s, t) = &built[&k];
        super::super::arms(t, s);
    });
}

#[test]
fn tests_of_a_name_over_many_inputs_take_the_bounds_of_the_inputs_they_narrow() {
    let built: BTreeMap<usize, (Scope, Term)> = [40, 320]
        .into_iter()
        .map(|k| {
            let (names, t) = tests_of_one_sum(k);
            (k, (ints(&names), t))
        })
        .collect();
    let counted = |k: usize| {
        let (s, t) = &built[&k];
        scaling::on_a_thread(1 << 26, || {
            let before = zedc::store::preimage::counts::term_bounds();
            let a = super::super::arms(t, s);
            assert!(a.iter().all(|a| a.reachable()), "{k} tests");
            zedc::store::preimage::counts::term_bounds() - before
        })
    };
    scaling::hold(
        "tests over many inputs, their term bounds: 40 and 320 tests",
        "term bounds taken",
        counted(40),
        counted(320),
        1,
    );
}

/// `let z = x1 + … + xk in if x1 >= 2 { if z >= 1 { if z == 2 { … } } } else { 0 }` in the
/// scope where each `xi` is in `0..=1`: `k` tests of `z`, by `>=` and `==` in turn, in a scope
/// no state reaches. No test reads it, since what narrows and what excludes stop there, and the
/// arms shown below it share its names, emptied once (item PA-letpre-linear).
#[test]
fn tests_in_a_scope_no_state_reaches_read_nothing() {
    let built = scaling::inputs(3200, tests_in_a_dead_scope);
    scaling::check(
        "k tests of a sum over k inputs in a scope no state reaches",
        3200,
        |k| {
            let (s, t) = &built[&k];
            let a = super::super::arms(t, s);
            assert!(a.iter().any(|a| !a.reachable()), "{k} tests");
        },
    );
}

/// `if x1 >= 0 { if x1 <= 1 { … let z1 = x1 + 1 in … let zk = xk + k in if z1 >= 2 { …
/// if zk >= k + 1 { 0 } else { k } … } else { 1 } … } } }`: `k` tests, each of a summary over
/// one input, which reads that input as an input (item PA-letpre-linear).
#[test]
fn tests_of_summaries_over_one_input_read_that_input() {
    let built = scaling::inputs(40, summaries_over_one_input);
    scaling::check("k tests, each of a summary over one input", 40, |k| {
        let (s, t) = &built[&k];
        let a = super::super::arms(t, s);
        assert!(a.iter().all(|a| a.reachable()), "{k} tests");
    });
    // The time of a test is mostly its binding's and its arms', so the inputs are counted too.
    let given = |k: usize| {
        let (s, t) = &built[&k];
        scaling::on_a_thread(1 << 26, || {
            let before = zedc::store::preimage::counts::inputs();
            super::super::arms(t, s);
            zedc::store::preimage::counts::inputs() - before
        })
    };
    scaling::hold(
        "tests over many inputs, their inputs: 40 and 320 tests",
        "inputs given",
        given(40),
        given(320),
        1,
    );
}

/// `z = x1 + … + xk` over each `xi` in `0..=1`, read through the tree of its terms' bounds, and
/// `k` tests `z >= 1`, the `i`-th given `xi` in `1..=1`, another domain than the scope's: each
/// reads that input over its own domain and the rest through the tree (item PA-letpre-linear).
#[test]
fn tests_that_give_an_input_another_domain_read_it_through_the_tree() {
    let built = scaling::inputs(6400, each_input_given_its_own_domain);
    scaling::check(
        "k tests of a sum over k inputs, each giving one input its own domain",
        6400,
        |k| built[&k](),
    );
}

#[test]
fn a_test_beside_a_wide_part_costs_its_own_part() {
    // Each scope's record of its parts' projections ([`Scope::projected`]) is a persistent
    // map that the next test shares and copies along the path to the entry it changes. The
    // conjunct `z0 + … + z(k-1) >= 0`, which mentions `k` inputs, is the greatest key, so the
    // entry of each new test lands in its leaf, and each copy of that leaf copied the key's
    // formula and the intervals of its `k` names while they were held by value (item
    // PERF-partkey-arc). Negative control, the cloning version at d5714627, not committed:
    // 317M and 2.98G instructions (9.4 times), 64.4M and 667M bytes (10.4 times). Shared:
    // 306M and 2.69G instructions (8.8 times), 59.9M and 518M bytes (8.7 times). The control
    // passes the limit of 13.2 too: each test costs about 1M bytes besides the copies, and a
    // wider part takes too long to build (its projection costs the square of its names), so
    // at sizes a test can afford this one bounds the order and does not tell the two apart.
    let n = 256;
    let inputs = scaling::inputs(n, parts_beside_a_wide_part);
    let p = Premises::new();
    scaling::check("k tests beside a part of k names", n, |k| {
        let (s, tests) = &inputs[&k];
        tests.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
    });
}

#[test]
fn a_sum_over_many_names_is_assumed_in_time_near_linear() {
    // Each name's values are read from the row and the others' bounds, not asked of the solver
    // one name at a time (item PERF-wide-sum-project, COMPLEXITY.md F154).
    let p = Premises::new();
    // The scopes and tests, built before the timing.
    let built = scaling::inputs(1024, |k| {
        let (names, sum, bounded) = wide_sum(k);
        (ints(&names), prim(Prim::Ge, sum, int(0)), bounded)
    });
    scaling::check("z0 + … + z(k-1) >= 0 assumed on k names", 1024, |k| {
        let (s, t, _) = &built[&k];
        s.assume(t, true, &p);
    });
    scaling::check(
        "0 <= zj <= 3 for each of k names and their sum at least 3·k - 1",
        1024,
        |k| {
            let (s, _, t) = &built[&k];
            s.assume(t, true, &p);
        },
    );
}

#[test]
fn a_disjunction_beside_a_wide_one_in_its_block_costs_its_own_part() {
    // A kept block indexes its parts by the terms their conjuncts compare, in a persistent map
    // that the next projection shares and copies along the path to the entry it changes. The
    // terms of each test, `a_i + h` and `a_i + g`, sort just before those of the first
    // disjunction, `g` and `h + z0 + … + z(k-1)`, so each new entry lands in the leaf that holds
    // the term of `k + 1` names; held by value, that term was copied with each such path copy
    // (item PERF-block-terms-key). The blocks themselves, kept in a persistent map of the scope,
    // are shared as well (item PERF-seen-blocks-arc). COMPLEXITY.md C44.
    let n = 128;
    let inputs = scaling::inputs(n, disjunctions_beside_a_wide_disjunction);
    let p = Premises::new();
    scaling::check(
        "k disjunctions beside one on k names in one block",
        n,
        |k| {
            let (s, tests) = &inputs[&k];
            tests.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
        },
    );
}

#[test]
fn an_eager_join_projects_again_the_stars_it_settles_and_scales() {
    // The arms of `if n - m <= 5` test a term the disjunction does not compare, and the eager
    // join projects each of the `k` stars again (`Scope::refresh`): its lone part that is not
    // a constraint, the disjunction with the star, once per star, O(k) in all (COMPLEXITY
    // C45). The naive version, every part of each star projected again, costs the same here,
    // where each star has one such part; with k parts per star it fails
    // `an_eager_scope_with_many_distinct_disjunctions_among_the_hubs_of_a_star_scales`.
    let p = Premises::new();
    let test = hubs_within(5);
    let inputs = scaling::inputs(64, |k| stars_under_a_disjunction(k, false));
    scaling::check(
        "the join of an if among the hubs of k stars, eager",
        64,
        |k| {
            let s = &inputs[&k];
            s.assume(&test, true, &p).join(&s.assume(&test, false, &p));
        },
    );
}

//! Benchmarks of `scaling`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn narrowing_by_a_conjunction_of_disjunctions_scales() {
    let s = ints(&["x".into(), "y".into()]);
    scaling::check("a conjunction of disjunctions of linear tests", 8, |k| {
        s.assume(&clauses(k), true, &Premises::new());
    });
}

#[test]
fn a_chain_of_lets_and_a_nest_of_ifs_scale() {
    let x0 = ints(&["x0".into()]);
    scaling::check("a chain of `let`s", 50, |k| {
        super::super::arms(&lets(k), &x0);
    });
    // Each level's test implies the one before, so the relation keeps one constraint.
    scaling::check("`if`s nested on one name", 64, |k| {
        super::super::arms(&ifs(k), &x0);
    });
}

#[test]
fn a_join_keeps_the_equalities_of_its_sides_and_scales() {
    let names = |k: usize| -> Vec<std::sync::Arc<str>> {
        (1..=k).map(|i| format!("x{i}").into()).collect()
    };
    for k in [2, 5, 10, 20] {
        let r = ints(&names(k)).assume(&all_zero_or_all_one(k), true, &Premises::new());
        let differ = prim(Prim::Ne, var("x1"), var(&format!("x{k}")));
        assert!(
            r.assume(&differ, true, &Premises::new()).bottom,
            "k = {k}: {}",
            r.relation
        );
        let x1 = prim(Prim::Eq, var("x1"), int(1));
        assert!(!r.assume(&x1, true, &Premises::new()).bottom, "k = {k}");
    }
    // The two sides, built before the timing; the join of the two, reduced, is timed.
    let sides = |k: usize| {
        let s = ints(&names(k));
        let Term::Prim(_, a) = &all_zero_or_all_one(k) else {
            unreachable!("a disjunction")
        };
        let p = Premises::new();
        (s.assume(&a[0], true, &p), s.assume(&a[1], true, &p))
    };
    let built: BTreeMap<usize, (Scope, Scope)> =
        [32, 256].into_iter().map(|k| (k, sides(k))).collect();
    scaling::check("the join of two sides that fix k names, reduced", 32, |k| {
        let (l, r) = &built[&k];
        l.join(r).reduce();
    });
}

#[test]
fn tests_read_through_the_functions_they_call_scale() {
    let x = ints(&["x".into()]);
    // `h(x) >= 4` and below it `h(x) < 4`, `h(x) >= 3`: the test of 3 is reached where
    // `2x + 1` is 3, that of 2 never, since `2x + 1` is odd.
    let a = super::super::arms(&helper_chain(4), &x);
    let reach: Vec<bool> = a.iter().map(|a| a.reachable()).collect();
    assert_eq!(
        reach,
        [true, true, true, true, false, true, true, true],
        "{a:#?}"
    );
    // `h5(x)` is `8x + 13`, so the true arm holds `x >= -1`.
    let a = super::super::arms(&nested_helpers(5), &x);
    assert_eq!(a[0].scope.get("x").ints().to_string(), "[-1..]");
    assert_eq!(a[1].scope.get("x").ints().to_string(), "[..=-2]");
    // The terms, built before the timing; walking their arms is timed. Each test closes over
    // the functions it reaches, each once however many paths reach it, so both are linear.
    let chains: BTreeMap<usize, Term> = [64, 512]
        .into_iter()
        .map(|k| (k, helper_chain(k)))
        .collect();
    scaling::check_order(
        "an `else if` chain of k tests, each calling a function",
        64,
        1,
        |k| {
            super::super::arms(&chains[&k], &x);
        },
    );
    // The preimage still recurses on the depth of the term (item T2-mid), about 4 KB a level
    // here, so the nest runs on a stack of its own: at 256 levels it needs about as much as a
    // test thread holds (2 MiB).
    let nests: BTreeMap<usize, Term> = [32, 256]
        .into_iter()
        .map(|k| (k, nested_helpers(k)))
        .collect();
    on_big_stack(|| {
        scaling::check_order(
            "one test through k functions, each calling the two before it",
            32,
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
    let conjunction = |k: usize, or: bool| {
        let (names, tests) = apart(k, or);
        let all = tests
            .into_iter()
            .reduce(|a, t| prim(Prim::And, a, t))
            .expect("k > 0");
        (ints(&names), all)
    };
    let sizes = [50, 400];
    for or in [false, true] {
        let built: BTreeMap<usize, (Scope, Term)> =
            sizes.into_iter().map(|k| (k, conjunction(k, or))).collect();
        let what = if or {
            "a conjunction of k disjunctions on names apart"
        } else {
            "a conjunction of k tests on names apart"
        };
        scaling::check(what, 50, |k| {
            let (s, t) = &built[&k];
            s.assume(t, true, &Premises::new());
        });
    }
    let one_by_one: BTreeMap<usize, (Scope, Vec<Term>)> = sizes
        .into_iter()
        .map(|k| {
            let (names, tests) = apart(k, true);
            (k, (ints(&names), tests))
        })
        .collect();
    scaling::check(
        "k disjunctions on names apart, assumed one by one",
        50,
        |k| {
            let (s, tests) = &one_by_one[&k];
            let p = Premises::new();
            tests.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
        },
    );
    // What each kind keeps: every test of the conjunction, and each point that meets them.
    let (s, t) = conjunction(3, true);
    let r = s.assume(&t, true, &Premises::new());
    assert_eq!(r.relation.cons().len(), 6, "{}", r.relation);
    let at = |v: [i64; 6]| -> BTreeMap<std::sync::Arc<str>, Value> {
        ["x0", "y0", "x1", "y1", "x2", "y2"]
            .into_iter()
            .zip(v)
            .map(|(n, v)| (n.into(), Value::Int(v)))
            .collect()
    };
    assert!(r.contains(&at([1, 0, 0, 1, 5, -5])));
    let (s, tests) = &one_by_one[&50];
    let p = Premises::new();
    let r = tests.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
    assert!(!r.bottom);
    let (s, t) = conjunction(3, false);
    let r = s.assume(&t, true, &Premises::new());
    assert!(r.contains(&at([1, 0, 1, 0, 9, 8])));
    assert!(!r.contains(&at([0, 0, 1, 0, 9, 8])));
}

#[test]
fn a_chain_of_shadowing_lets_scales() {
    // `arms` recurses on the depth of the term (T2-mid), so the chain runs on a thread whose
    // stack holds it: 1,600 `let`s at the larger size.
    let t = std::thread::Builder::new().stack_size(1 << 28).spawn(|| {
        let x0 = ints(&["x0".into()]);
        let terms: BTreeMap<usize, Term> = [100, scaling::FACTOR * 100]
            .into_iter()
            .map(|k| (k, shadows(k)))
            .collect();
        let a = super::super::arms(&terms[&100], &x0);
        assert_eq!(a.len(), 2, "both arms of the last test are reached");
        assert!(a.iter().all(|a| !a.scope.bottom));
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
    let families: [Family; 2] = [
        (
            "k reductions under @exact, each after a constraint on names apart",
            squares_apart,
        ),
        (
            "k reductions under @exact, each after a constraint of one chain",
            products_in_a_chain,
        ),
    ];
    for (what, family) in families {
        let built = scaling::inputs(32, |k| (exact_within(k + 1), family(k)));
        scaling::check(what, 32, |k| {
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
    let ge = |i: usize| prim(Prim::Ge, var(&format!("x{i}")), int(i as i64));
    let lt = |i: usize| prim(Prim::Lt, var(&format!("x{i}")), int(i as i64));
    let names =
        |k: usize| -> Vec<std::sync::Arc<str>> { (0..k).map(|i| format!("x{i}").into()).collect() };
    let built: BTreeMap<usize, (Scope, Vec<(Term, Term)>)> = [300, 2400]
        .into_iter()
        .map(|k| {
            (
                k,
                (ints(&names(k)), (0..k).map(|i| (ge(i), lt(i))).collect()),
            )
        })
        .collect();
    let p = Premises::new();
    let nest = |s: &Scope, tests: &[(Term, Term)]| {
        let mut failed = Vec::with_capacity(tests.len());
        let s = tests.iter().fold(s.clone(), |s, (holds, fails)| {
            failed.push(
                s.assume_case(holds, false, &p)
                    .assume_case(fails, false, &p),
            );
            s.assume_case(holds, true, &p)
        });
        (s, failed)
    };
    // Each failing case is unreachable, and every name reads as empty there, its own and the
    // others, though the case kept them as they were.
    let (s, tests) = &built[&300];
    let (last, failed) = nest(s, tests);
    assert!(!last.bottom);
    assert_eq!(last.get("x7").ints().to_string(), "[7..]");
    for (i, f) in failed.iter().enumerate() {
        assert!(f.bottom, "case {i}");
        assert!(f.get(&format!("x{i}")).is_empty(), "x{i} in case {i}");
        assert!(f.get("x0").is_empty() && f.get("y").is_empty(), "case {i}");
    }
    // Emptying each name of a failing case costs the names in scope: O(k²) for the nest.
    scaling::check(
        "a nest of k tests on k names, each failing in one case",
        300,
        |k| {
            let (s, tests) = &built[&k];
            nest(s, tests);
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
    let p = Premises::new();
    let built: BTreeMap<usize, Scope> = [16, 128]
        .into_iter()
        .map(|k| (k, stars_of_two_hubs(k)))
        .collect();
    let narrow = |k: usize| {
        (1..=k as i64).rev().fold(built[&k].clone(), |s, c| {
            s.assume(&hubs_within(c), true, &p)
        })
    };
    let s = narrow(16);
    for i in 0..16 {
        assert_eq!(s.get(&format!("a{i}")).ints().to_string(), "[-1..]", "a{i}");
    }
    // A test that moves every leaf still reaches each: `n + m >= 4` with `n - m <= 1` puts
    // the least `max(n, m)` at 2.
    let up = prim(Prim::Ge, prim(Prim::Add, var("n"), var("m")), int(4));
    let s = s.assume(&up, true, &p);
    for i in 0..16 {
        assert_eq!(s.get(&format!("a{i}")).ints().to_string(), "[2..]", "a{i}");
    }
    scaling::check(
        "k tests among the hubs of k stars of two hubs, in an eager scope",
        16,
        |k| {
            narrow(k);
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
    let inputs = scaling::inputs(16, |k| {
        (
            stars_above_the_hubs(k, false),
            stars_above_the_hubs(k, true),
        )
    });
    for one in [false, true] {
        let start = stars_above_the_hubs(16, one);
        let (after, nest) = tests_on_a_hub(&start, 16);
        assert_eq!(after.get("n").ints().to_string(), "[-1..=1001]");
        assert_eq!(nest.get("n").ints().to_string(), "[-1..]");
        for s in [&after, &nest] {
            for i in 0..16 {
                assert_eq!(s.get(&format!("a{i}")).ints().to_string(), "[5000..]");
            }
        }
        // A test that moves the hub past the leaves still reaches each.
        let up = prim(Prim::Ge, var("n"), int(6000));
        let s = start.assume(&up, true, &Premises::new());
        for i in 0..16 {
            assert_eq!(
                s.get(&format!("a{i}")).ints().to_string(),
                "[6000..]",
                "a{i}"
            );
        }
    }
    scaling::check(
        "k tests on a hub of k stars of two hubs and of one, in turn and nested, eager",
        16,
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
    let inputs = scaling::inputs(16, |k| {
        let (start, tests) = a_class_of_stars(k);
        (start.lazy(), tests)
    });
    scaling::check(
        "k tests among the hubs of a class of k stars, lazy",
        16,
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
    let inputs = scaling::inputs(16, a_class_of_stars);
    let p = Premises::new();
    let (start, tests) = &inputs[&16];
    let s = tests
        .iter()
        .fold(start.clone(), |s, t| s.assume(t, true, &p));
    for i in 0..16 {
        assert_eq!(s.get(&format!("a{i}")).ints().to_string(), "[..]", "a{i}");
    }
    scaling::check(
        "k tests among the hubs of a class of k stars, eager",
        16,
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
    let inputs = scaling::inputs(16, distinct_disjunctions_among_the_hubs_of_a_star);
    let p = Premises::new();
    let (start, tests) = &inputs[&16];
    let s = tests
        .iter()
        .fold(start.clone(), |s, t| s.assume(t, true, &p));
    assert_eq!(s.relation.set().len(), 17);
    scaling::check(
        "k distinct disjunctions among the hubs of a star, eager",
        16,
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
    let n = 40;
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
/// gave the same counts at 40 and 320 (negative control, run once, not committed).
/// COMPLEXITY.md C52.
#[test]
fn tightenings_beside_a_chain_of_disjunctions_scale() {
    const W: i64 = 1_000_000;
    let n = 12;
    let family = |k: usize| {
        let p = Premises::new();
        let vs: Vec<String> = (0..=k).map(|i| format!("v{i}")).collect();
        let mut all: Vec<Arc<str>> = vs.iter().map(|v| Arc::from(v.as_str())).collect();
        all.extend([Arc::from("w"), Arc::from("z")]);
        let within = |s: Scope, x: &str, lo: i64, hi: i64| {
            s.assume(&prim(Prim::Ge, var(x), int(lo)), true, &p).assume(
                &prim(Prim::Le, var(x), int(hi)),
                true,
                &p,
            )
        };
        let mut s = within(within(ints(&all), "w", -W, W), "z", -W, W);
        for v in &vs {
            s = within(s, v, 0, 10);
        }
        let apart = |a: &str, b: &str, c: &str, d: &str| {
            or(
                prim(Prim::Ge, prim(Prim::Sub, var(a), var(b)), int(5)),
                prim(Prim::Ge, prim(Prim::Sub, var(c), var(d)), int(5)),
            )
        };
        for i in 0..k {
            s = s.assume(&apart(&vs[i], "w", "w", &vs[i + 1]), true, &p);
        }
        s = s.assume(&apart("v0", "z", "z", "v0"), true, &p);
        let tests: Vec<(Term, bool)> = (1..=k as i64)
            .map(|j| {
                let sum = prim(Prim::Add, var("w"), var("z"));
                (prim(Prim::Le, sum, int(W - 10 - j)), false)
            })
            .collect();
        (s, tests)
    };
    let inputs = scaling::inputs(n, family);
    for k in [n, scaling::FACTOR * n] {
        let (s, tests) = &inputs[&k];
        let end = change_one_block(s, tests);
        assert!(!end.bottom, "k = {k}: the scope became empty");
        let mut again = end.clone();
        again.forget_projections();
        again.reduce();
        for h in ["w", "z", "v0"] {
            assert_eq!(end.get(h), again.get(h), "k = {k}: {h}");
        }
    }
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
/// projections each test costs. COMPLEXITY.md C52.
#[test]
fn tightenings_of_a_sum_beside_disjunctions_on_each_name_scale() {
    let n = 12;
    let family = |k| {
        tightenings_beside_disjunctions(
            k,
            |v| {
                let i: usize = v[1..].parse().unwrap();
                let x = if i.is_multiple_of(2) { "n" } else { "m" };
                or(
                    prim(Prim::Ge, prim(Prim::Sub, var(v), var(x)), int(5)),
                    prim(Prim::Ge, prim(Prim::Sub, var(x), var(v)), int(5)),
                )
            },
            |c| prim(Prim::Le, prim(Prim::Add, var("n"), var("m")), int(c)),
        )
    };
    let inputs = scaling::inputs(n, family);
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
    // `let z = x + y in if y <= 0 { if z >= 5 { 1 } else { 2 } } else { 3 }`: in arm 1, x >= 5.
    let body = Term::Let(
        "z".into(),
        arc(prim(Prim::Add, var("x"), var("y"))),
        arc(Term::If(
            arc(prim(Prim::Le, var("y"), int(0))),
            arc(Term::If(
                arc(prim(Prim::Ge, var("z"), int(5))),
                arc(int(1)),
                arc(int(2)),
            )),
            arc(int(3)),
        )),
    );
    let a = super::super::arms(&body, &ints(&["x".into(), "y".into()]));
    assert_eq!(
        a[1].scope.get("x").ints().to_string(),
        "[5..]",
        "{:#?}",
        a[1]
    );
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
    let built = scaling::inputs(40, |k| {
        let (names, _) = tests_of_one_sum(k);
        let bits = (1..=k)
            .flat_map(|i| {
                let x = format!("x{i}");
                [
                    prim(Prim::Ge, var(&x), int(0)),
                    prim(Prim::Le, var(&x), int(1)),
                ]
            })
            .reduce(|a, b| prim(Prim::And, a, b))
            .expect("k is not 0");
        let s = ints(&names).assume(&bits, true, &Premises::new());
        let test = |i: usize| {
            let p = if i.is_multiple_of(2) {
                Prim::Eq
            } else {
                Prim::Ge
            };
            prim(p, var("z"), int(i as i64))
        };
        let dead = Term::If(
            arc(prim(Prim::Ge, var("x1"), int(2))),
            arc(nested(k, test)),
            arc(int(0)),
        );
        (s, Term::Let("z".into(), arc(sum_of(k)), arc(dead)))
    });
    scaling::check(
        "k tests of a sum over k inputs in a scope no state reaches",
        40,
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
    let built = scaling::inputs(40, |k| {
        let names: Vec<Arc<str>> = (1..=k).map(|i| format!("x{i}").into()).collect();
        let z = |i: usize| format!("z{i}");
        let tests = nested(k, |i| prim(Prim::Ge, var(&z(i)), int(i as i64 + 1)));
        let t = (1..=k).rev().fold(tests, |t, i| {
            let v = prim(Prim::Add, var(&format!("x{i}")), int(i as i64));
            Term::Let(z(i).into(), arc(v), arc(t))
        });
        (ints(&names), in_bits(k, t))
    });
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
    let built = scaling::inputs(40, |k| {
        let xs: Vec<Arc<str>> = (1..=k).map(|i| format!("x{i}").into()).collect();
        let names: images::Names<IntervalSet> = (xs.iter())
            .map(|x| (x.clone(), IntervalSet::range(End::of(0), End::of(1))))
            .collect();
        let doms: Domains = names.iter().map(|(x, d)| (x.clone(), d.clone())).collect();
        let s = let_summary(&sum_of(k), &doms, Lets::new()).expect("a sum of inputs");
        let leaf = |v: &Arc<str>, d: &IntervalSet| s.term_bounds(v, d);
        let tree = images::fresh(s.vars(), &names, leaf);
        let read = Arc::new(TermRead {
            names,
            vars: s.vars().clone(),
            tree,
            ints: |d| d,
        });
        (xs, s, read)
    });
    scaling::check(
        "k tests of a sum over k inputs, each giving one input its own domain",
        40,
        |k| {
            let (xs, s, read) = &built[&k];
            let test = prim(Prim::Ge, var("z"), int(1));
            for x in xs {
                let lets: Lets = [(
                    "z".into(),
                    LetIn {
                        summary: s.clone(),
                        ints: IntervalSet::top(),
                        read: Some(read.clone() as _),
                    },
                )]
                .into_iter()
                .collect();
                let over: Domains = [(x.clone(), IntervalSet::single(1))].into_iter().collect();
                let got = let_narrowing(&test, &over, lets, &Demand::Bool(true));
                assert!(got.is_some(), "{x}");
            }
        },
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
    let n = 64;
    let inputs = scaling::inputs(n, parts_beside_a_wide_part);
    let p = Premises::new();
    for k in [n, scaling::FACTOR * n] {
        let (s, tests) = &inputs[&k];
        assert_eq!(
            s.projected.len(),
            1,
            "k = {k}: the wide part alone at the start"
        );
        let end = tests.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
        assert!(!end.bottom, "k = {k}: the scope became empty");
        assert_eq!(
            end.projected.len(),
            k + 1,
            "k = {k}: one part for each test"
        );
    }
    scaling::check("k tests beside a part of k names", n, |k| {
        let (s, tests) = &inputs[&k];
        tests.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
    });
}

#[test]
fn a_sum_over_many_names_is_assumed_in_time_near_linear() {
    // Each name's values are read from the row and the others' bounds, not asked of the solver
    // one name at a time (item PERF-wide-sum-project, COMPLEXITY.md F154): with `0 <= zj <= 3`
    // and the sum at least `3·k - 1`, the others give at most `3·(k - 1)`, so each `zj >= 2`.
    let p = Premises::new();
    let (names, sum, bounded) = wide_sum(5);
    let r = ints(&names).assume(&bounded, true, &p);
    for x in &names {
        assert_eq!(r.get(x).ints().to_string(), "[2..=3]", "{x}");
    }
    let r = ints(&names).assume(&prim(Prim::Ge, sum, int(0)), true, &p);
    assert!(!r.bottom);
    assert_eq!(r.get("z0").ints().to_string(), "[..]");
    // The scopes and tests, built before the timing.
    let built = scaling::inputs(128, |k| {
        let (names, sum, bounded) = wide_sum(k);
        (ints(&names), prim(Prim::Ge, sum, int(0)), bounded)
    });
    scaling::check("z0 + … + z(k-1) >= 0 assumed on k names", 128, |k| {
        let (s, t, _) = &built[&k];
        s.assume(t, true, &p);
    });
    scaling::check(
        "0 <= zj <= 3 for each of k names and their sum at least 3·k - 1",
        128,
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
    let n = 64;
    let inputs = scaling::inputs(n, disjunctions_beside_a_wide_disjunction);
    let p = Premises::new();
    for k in [n, scaling::FACTOR * n] {
        let (s, tests) = &inputs[&k];
        let end = tests.iter().fold(s.clone(), |s, t| s.assume(t, true, &p));
        assert!(!end.bottom, "k = {k}: the scope became empty");
        assert_eq!(
            end.relation.set().len(),
            k + 1,
            "k = {k}: each disjunction kept"
        );
        assert_eq!(
            end.relation.blocks().all().count(),
            1,
            "k = {k}: the disjunctions are one block"
        );
        assert!(end.relation.stars().is_empty(), "k = {k}: no star");
    }
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
    let inputs = scaling::inputs(16, |k| stars_under_a_disjunction(k, false));
    let eager = &inputs[&16];
    let joined = eager
        .assume(&test, true, &p)
        .join(&eager.assume(&test, false, &p));
    let lazy = stars_under_a_disjunction(16, true);
    let lazy = lazy
        .assume(&test, true, &p)
        .join(&lazy.assume(&test, false, &p));
    for i in 0..16 {
        let a: Arc<str> = format!("a{i}").into();
        assert_eq!(joined.get(&a), lazy.settled(&a), "a{i}");
        assert_eq!(joined.get(&a).ints().to_string(), "[-1..]", "a{i}");
    }
    scaling::check(
        "the join of an if among the hubs of k stars, eager",
        16,
        |k| {
            let s = &inputs[&k];
            s.assume(&test, true, &p).join(&s.assume(&test, false, &p));
        },
    );
}

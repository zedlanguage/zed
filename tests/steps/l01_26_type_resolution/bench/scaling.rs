//! The time of the checker at the rule of low complexity (DESIGN.md Part G), on the programs and
//! types of `scaling`, where a small instance of each is checked.

use std::collections::BTreeMap;

use zed_tests::scaling;
use zedc::check::ty::Ty;

use super::super::Resolved;
use super::super::info;
use super::super::scaling::{
    a_chain_of_tests, bounded_at_many_parameters, call_chain, chain, constants_and_functions,
    covering_overload, curried, curried_sums, curried_tested, disjoint_rows, else_patterns, fan,
    functions_holding_one, generic_applied_to_many, many_destructurings, meeting_on_different_sets,
    met_and_within, nested_overload, never_arguments, overlapping_rows, overloads, payloads,
    resolved, results_holding_a_variable, results_met_alone, shared_overloads, shared_rows, sum,
    sums_of_a_line_or_a_count, tuple, variables, wide_arrows, wide_destructuring, wider_overloads,
    with_a_function_arrow,
};

/// Runs `want` on the unit `text(m)` at `n` and `8 * n`, both read and resolved before either
/// is run.
fn scales(what: &str, n: usize, text: impl Fn(usize) -> String, want: impl Fn(&Resolved) + Sync) {
    let units = resolved(n, text);
    scaling::check(what, n, |m| want(&units[&m]));
}

/// The variables named `{prefix}0` to `{prefix}(m-1)`, for `m` of `n` and `FACTOR * n`, made
/// before the timing.
fn variables_at(prefix: &str, n: usize) -> BTreeMap<usize, Vec<Ty>> {
    [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, variables(prefix, m)))
        .collect()
}

/// The statements of `text(m)` and their resolution, at `n` and `FACTOR * n`, made before the
/// timing.
fn built(
    n: usize,
    text: impl Fn(usize) -> String,
) -> BTreeMap<usize, (Vec<zedc::ast::Stmt>, zedc::resolve::Resolution)> {
    [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let stmts = zed_tests::deep::statements(&text(m));
            let res = zedc::resolve::resolve(&stmts).unwrap();
            (m, (stmts, res))
        })
        .collect()
}

#[test]
fn searching_the_signatures_of_many_functions_scales() {
    // Twenty constants for each function, each adopting its literal with no search, so that
    // what the unit has found is large beside the searches.
    let units = resolved(125, constants_and_functions);
    scaling::check(
        "the signatures of n functions beside 20n constants",
        125,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
            assert_eq!(info.sigs.len(), n);
            assert_eq!(info.adopt.len(), 20 * n);
        },
    );
}

#[test]
fn a_function_of_many_untyped_parameters_scales() {
    // The search tried the product of the carriers of the parameters, 3^n, until its budget
    // of 256 combinations gave `_`. The parameters now merge into one class, once each.
    // The body is a chain of `n` additions, nested `n` deep, on a 2 MiB stack.
    zed_tests::deep::on_small_stack(|| {
        scaling::check("a function of n untyped parameters", 6400, |n| {
            let (info, _) = info(&sum(n));
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        });
    });
}

#[test]
fn a_chain_of_functions_with_untyped_parameters_scales() {
    // Each takes the bound of the one it calls, by its signature, with no search.
    let units = resolved(2000, chain);
    scaling::check("a chain of n functions", 2000, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(info.sigs.len(), n);
    });
}

#[test]
fn many_else_patterns_scale() {
    // Each `else` with a pattern read every binder of the unit to find its own.
    let units = resolved(5000, else_patterns);
    scaling::check("n bindings each with an else pattern", 5000, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn a_signature_of_many_type_variables_scales() {
    // Naming the variables looked for each among those named before (COMPLEXITY.md F28).
    let units = resolved(10_000, tuple);
    scaling::check("a signature of n type variables", 10_000, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn needs_replayed_through_a_fan_of_calls_scale() {
    // Each of the two calls met the needs of the one before anew, so they doubled at each
    // function; a use met twice now gives what it gave the first time.
    let units = resolved(1250, fan);
    scaling::check(
        "needs replayed through n functions, each calling the one before twice",
        1250,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn the_union_of_many_atoms_with_payloads_scales() {
    let sides: BTreeMap<usize, (Vec<_>, Vec<_>)> = [8192, scaling::FACTOR * 8192]
        .into_iter()
        .map(|n| (n, (payloads(n, false), payloads(n, true))))
        .collect();
    scaling::check("the union of n atoms with payloads", 8192, |n| {
        let (names, shapes) = &sides[&n];
        let u = Ty::union_all(names);
        assert_eq!(u.payloads.len(), n);
        assert!(u.payloads.values().all(Option::is_some));
        let u = Ty::union_all(shapes);
        assert_eq!(u.payloads["e"].as_ref().map(Vec::len), Some(n));
    });
}

/// Besides its ratio: no type error. Small instance, with the signature:
/// `scaling::curried_lambdas_name_their_parameters_and_take_their_carriers`.
#[test]
fn curried_lambdas_using_every_parameter_check_in_linear_time() {
    // Each lambda names its parameter's class when it is closed. The name is kept on the
    // class, and the class variable stays in the signatures inside, which are not rewritten:
    // only `finish` writes the names, once per signature it shows. Before CHK-curried the
    // name replaced the class in every lambda inside, n - k signatures at the k-th, so the
    // time was quadratic. The facts of a signature are persistent sets shared with the
    // signatures inside (`VarFacts::held`), so merging them costs O(log n) per variable.
    let n = 3200;
    let built = built(n, curried);
    scaling::check_order("n curried lambdas using every parameter", n, 1, |m| {
        let (stmts, res) = &built[&m];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// Besides its ratio: no type error. Small instance, with the signature:
/// `scaling::curried_lambdas_name_their_parameters_and_take_their_carriers`.
#[test]
fn curried_lambdas_whose_parameters_take_a_carrier_check_in_linear_time() {
    // Each lambda's parameter takes int when the lambda ends. `generalize` replaced the class
    // by int in each of the n - k lambdas inside the k-th, which hold it: n^2, 38.2 times the
    // bytes for 8 times n at ab0d3a84. Now a class solved to a type with no variable is
    // replaced outside the lambdas only, and read through the union-find inside them by the
    // comparisons and messages that read them; `finish` settles each signature once
    // (CHK-carrier, COMPLEXITY.md F77). Per node at n = 100 and 800: 274103 and 274564
    // instructions, 49621 and 49236 bytes; replaced at every depth, 798369 and 4944027
    // instructions, 101619 and 481807 bytes.
    let n = 1600;
    let built = built(n, curried_sums);
    scaling::check_order(
        "n curried lambdas whose parameters take a carrier",
        n,
        1,
        |m| {
            let (stmts, res) = &built[&m];
            let info = zedc::check::walk::check(stmts, res);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn an_is_test_of_curried_lambdas_whose_parameters_take_a_carrier_scales() {
    // `is` compares the lambdas of `t` with the written ones, reading the classes solved
    // inside them through the union-find (`Ty::diff_with`), so the `else` branch, where `t`
    // is not of the type, narrows to nothing, and a tuple may hold a function (L1.17), so the
    // program has no error. The comparison of function types recursed once per lambda, about 8
    // frames a level, and overflowed a 2 MiB stack at 800; it now keeps its frames on the
    // heap (`Comparing`, TY-sub-stack).
    let n = 1000;
    zed_tests::deep::on_small_stack(|| {
        let built = built(n, curried_tested);
        scaling::check_order("an is test of n curried lambdas", n, 1, |m| {
            let (stmts, res) = &built[&m];
            let info = zedc::check::walk::check(stmts, res);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        });
    });
}

#[test]
fn a_chain_of_calls_on_one_value_checks_in_linear_time() {
    // Each call's result is a function that holds the rest of the chain. A set of functions
    // hashed each whole (`Ty::union`), and `hold` walked each result whole, so each call cost
    // the depth left: n^2. A signature's hash is now made once from those of the functions it
    // holds (`Sig::digest`), and `hold` reads their facts (CHK-carrier, COMPLEXITY.md F77).
    // Per node at n = 100 and 800: 413888 and 413130 instructions, 70057 and 69516 bytes;
    // before, 1076078 and 5444818 instructions, 82672 and 166976 bytes.
    let n = 1600;
    let built = built(n, call_chain);
    scaling::check_order("a chain of n calls on one value", n, 1, |m| {
        let (stmts, res) = &built[&m];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// Besides its ratio: no type error, two signatures. Small instance:
/// `scaling::overloads_passed_to_slots_of_arrows_check`.
#[test]
fn passing_an_overload_of_many_arrows_scales() {
    scales(
        "an overload of n arrows passed to a slot of n arrows",
        6400,
        overloads,
        |unit| {
            let info = unit.check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
            assert_eq!(info.sigs.len(), 2);
        },
    );
}

/// An overload of n arrows passed to a slot of n other arrows: each arrow of the slot is
/// looked up by its parameter's atom in an index of the function's arrows, which gives the one
/// arrow that takes it (COMPLEXITY.md F82). Before the index each was compared with every
/// arrow of the function: 57.1 times the bytes at n = 100 and 800.
///
/// Besides its ratio: no type error. Small instance:
/// `scaling::overloads_passed_to_slots_of_arrows_check`.
#[test]
fn passing_an_overload_to_a_slot_of_other_arrows_scales() {
    scales(
        "an overload of n arrows passed to a slot of n other arrows",
        3200,
        wider_overloads,
        |unit| {
            let info = unit.check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

/// The arrows share the piece of the parameter the slot's arrows need, so the index of arrows
/// by parameter leaves every arrow; the index by result leaves one (COMPLEXITY.md F82; the
/// parameter index alone cost n^2/2 comparisons, 57.6x at n and 8n).
///
/// Besides its ratio: no type error. Small instance:
/// `scaling::overloads_passed_to_slots_of_arrows_check`.
#[test]
fn passing_an_overload_whose_arrows_share_a_parameter_piece_scales() {
    scales(
        "an overload of n arrows sharing a parameter piece passed to a slot of n arrows",
        3200,
        shared_overloads,
        |unit| {
            let info = unit.check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn a_slot_written_as_an_overload_nested_in_parentheses_scales() {
    // Resolution and the checker are timed, on statements parsed before the timing.
    let n = 3200;
    let units: BTreeMap<usize, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, zed_tests::deep::statements(&nested_overload(m))))
        .collect();
    scaling::check("a slot of n arrows nested n deep in parentheses", n, |m| {
        let stmts = &units[&m];
        let res = zedc::resolve::resolve(stmts).unwrap();
        let info = zedc::check::walk::check(stmts, &res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(info.sigs.len(), 1);
    });
}

#[test]
fn an_overload_of_many_arrows_that_cover_a_slot_together_scales() {
    scales(
        "an overload of n arrows covering a slot together",
        3200,
        covering_overload,
        |unit| assert_eq!(unit.type_errors(), Vec::<String>::new()),
    );
}

#[test]
fn a_function_of_many_parameters_that_misses_one_scales() {
    scales(
        "an arrow of w parameters that misses the slot's last",
        3200,
        wide_arrows,
        |unit| {
            let errors = unit.type_errors();
            assert_eq!(errors.len(), 1, "{errors:?}");
        },
    );
}

#[test]
fn many_arrows_whose_results_intersect_within_the_slots_scale() {
    scales("n arrows met and n within", 3200, met_and_within, |unit| {
        assert_eq!(unit.type_errors(), Vec::<String>::new());
    });
}

/// Besides its ratio: one error, that the work grows with the product of their number. Small
/// instance: `scaling::results_of_arrows_meet_within_the_slots_or_are_refused`.
#[test]
fn many_arrows_whose_results_meet_only_on_different_sets_are_refused_in_linear_time() {
    scales(
        "n arrows whose results meet on different sets",
        1600,
        meeting_on_different_sets,
        |unit| {
            let errors = unit.type_errors();
            assert_eq!(errors.len(), 1, "{errors:?}");
            assert!(
                errors[0].contains("grows with the product of their number"),
                "{errors:?}"
            );
        },
    );
}

/// Besides its ratio: no type error. Small instance:
/// `scaling::results_of_arrows_meet_within_the_slots_or_are_refused`.
#[test]
fn an_overload_with_a_function_arrow_covering_a_slot_scales() {
    scales(
        "n arrows and a function arrow covering",
        3200,
        with_a_function_arrow,
        |unit| {
            assert_eq!(unit.type_errors(), Vec::<String>::new());
        },
    );
}

/// Besides its ratio: one error, naming the places the arguments give. Small instance:
/// `scaling::results_of_arrows_meet_within_the_slots_or_are_refused`.
#[test]
fn a_bounded_variable_at_many_parameters_is_refused_in_linear_time() {
    scales(
        "a bounded variable at w parameters",
        3200,
        bounded_at_many_parameters,
        |unit| {
            let errors = unit.type_errors();
            assert_eq!(errors.len(), 1, "{errors:?}");
            assert!(
                errors[0].contains("places the arguments give"),
                "{errors:?}"
            );
        },
    );
}

/// Besides its ratio: no type error. Small instance:
/// `scaling::results_of_arrows_meet_within_the_slots_or_are_refused`.
#[test]
fn many_results_that_hold_a_variable_or_a_function_meet_in_linear_time() {
    scales(
        "n results holding a variable met",
        3200,
        results_holding_a_variable,
        |unit| {
            assert_eq!(unit.type_errors(), Vec::<String>::new());
        },
    );
}

/// The intersection of [`many_results_that_hold_a_variable_or_a_function_meet_in_linear_time`]
/// timed alone, on results built before the timing: `n` results `U | String | #bi`, `U`
/// bounded by `int | f64`, met within `U | String`. There the check around the intersection
/// costs about 160,000 instructions a result, so a quadratic in the results that allocates
/// nothing, such as reading the carriers of every other result for each result, passes it
/// even at 3,200 results; here it fails at 1,000, and the more at the larger size used now,
/// since the quadratic part's share grows with n (COMPLEXITY.md F82).
#[test]
fn many_results_that_hold_a_variable_meet_in_linear_time_alone() {
    let n = 32_000;
    let meets: BTreeMap<usize, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, results_met_alone(m)))
        .collect();
    scaling::check("n results holding a variable met alone", n, |m| {
        assert!(meets[&m].within());
    });
}

#[test]
fn needs_that_name_a_variable_the_call_leaves_unbound_check_in_linear_time() {
    // At n = 200 the scan of every bound variable at each signature (`Ty::replace_in`) gave
    // 19.2 times the instructions, inside the limit; at n = 400 it gave 26.5 times.
    scales(
        "a generic function applied to n parameters",
        3000,
        generic_applied_to_many,
        |unit| {
            assert_eq!(unit.type_errors(), Vec::<String>::new());
        },
    );
}

#[test]
fn a_parameter_destructured_into_many_names_checks_in_linear_time() {
    scales(
        "a parameter destructured into n names",
        6400,
        wide_destructuring,
        |unit| {
            assert_eq!(unit.type_errors(), Vec::<String>::new());
        },
    );
}

#[test]
fn many_parameters_each_destructured_check_in_linear_time() {
    scales(
        "n parameters each destructured into two names",
        1000,
        many_destructurings,
        |unit| {
            assert_eq!(unit.type_errors(), Vec::<String>::new());
        },
    );
}

/// `n` rows `t(k) = (t(k-1), (t(k-1), Vk))`: each row merges the variables of its two
/// components, `k` and `k + 1` of them, the second set made from the first by adding `Vk`
/// (ROW-made-cost). Inserting each variable of the smaller set cost `O(k log k)` a row, and
/// took 70.6 times the instructions at 2,000 against 250; stepping over the nodes the two sets
/// share took 10.0 times. A row now keeps no set, only the bits of its variables and the range
/// of its classes, `O(1)` a row, and the variables of the last row are listed by one walk that
/// enters each row once (CK-data-memo, COMPLEXITY.md F93).
///
/// Besides its ratio: the last row holds every variable. Small instance:
/// `scaling::rows_of_overlapping_or_disjoint_variable_sets_list_their_variables`.
#[test]
fn rows_made_from_overlapping_variable_sets_scale() {
    let n = 8000;
    let vars = variables_at("V", n);
    scaling::check_order("n rows of overlapping variable sets", n, 1, |m| {
        let t = overlapping_rows(&vars[&m]);
        assert_eq!(t.var_facts().names.len(), m);
    });
}

/// `n` rows `z(k) = (x(k), y(k))`, with `x(k) = (x(k-1), Ak)` and `y(k) = (y(k-1), Bk)`: each
/// `z(k)` holds a set of `2k` variables no other row holds, made from two sets that share no
/// node. When each row kept its set, `Row::made` cost `O(n^2 log n)` here (71.2 times the
/// instructions and 39.4 times the bytes at 2,000 against 250), since those sets are the
/// transitive closure of a DAG. A row now keeps flags, the bits of its variables and the
/// range of its classes, `O(1)` a row, and the variables of the last row are listed by one
/// walk (author's answer A8 as amended by A20; CK-data-memo, COMPLEXITY.md F93).
///
/// Besides its ratio: the last row holds every variable of both sets. Small instance:
/// `scaling::rows_of_overlapping_or_disjoint_variable_sets_list_their_variables`.
#[test]
fn rows_made_from_disjoint_variable_sets_scale() {
    let n = 8000;
    let (xs, ys) = (variables_at("A", n), variables_at("B", n));
    scaling::check_order("n rows of disjoint variable sets", n, 1, |m| {
        let zs = disjoint_rows(&xs[&m], &ys[&m]);
        assert_eq!(zs.last().map(|z| z.var_facts().names.len()), Some(2 * m));
    });
}

/// `n` rows `t(k) = (t(k-1), (t(k-1), Vk))`, `2^n` paths, with each `Vk` replaced by `Wk`:
/// `Ty::replace`, `Ty::subst` and `Ty::settle` each make a row once, however many paths reach
/// it (REPLACE-shared-rows, COMPLEXITY.md F97). Each walked every path before: 2^n.
fn replacing_in_rows_shared_on_many_paths(
    what: &str,
    replace: fn(&Ty, &zedc::check::ty::Binds) -> Ty,
) {
    let n = 3200;
    let (vs, ws) = (variables_at("V", n), variables_at("W", n));
    let binds = |m: usize| -> zedc::check::ty::Binds {
        let pairs = vs[&m].iter().zip(&ws[&m]);
        (pairs.map(|(v, w)| (v.vars.first().cloned().unwrap(), w.clone()))).collect()
    };
    let binds: BTreeMap<_, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, binds(m)))
        .collect();
    // Built before timing, so the runs time the walks alone.
    let shared: BTreeMap<_, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, overlapping_rows(&vs[&m])))
        .collect();
    scaling::check(what, n, |m| {
        let f = replace(&shared[&m], &binds[&m]).var_facts();
        assert_eq!(f.names.len() + f.classes.len(), m);
        assert!(f.names.iter().chain(&f.classes).all(|v| v.starts_with('W')));
    });
}

/// Besides its ratio: every variable is replaced. Small instance, by each of the three:
/// `scaling::replacing_in_rows_shared_on_many_paths_replaces_each_variable`.
#[test]
fn replacing_in_rows_shared_on_many_paths_scales_by_replace() {
    replacing_in_rows_shared_on_many_paths("Ty::replace in n shared rows", |t, b| t.replace(b));
}

/// Besides its ratio: every variable is replaced. Small instance, by each of the three:
/// `scaling::replacing_in_rows_shared_on_many_paths_replaces_each_variable`.
#[test]
fn replacing_in_rows_shared_on_many_paths_scales_by_subst() {
    replacing_in_rows_shared_on_many_paths("Ty::subst in n shared rows", |t, b| t.subst(b));
}

/// Besides its ratio: every variable is replaced. Small instance, by each of the three:
/// `scaling::replacing_in_rows_shared_on_many_paths_replaces_each_variable`.
#[test]
fn replacing_in_rows_shared_on_many_paths_scales_by_settle() {
    replacing_in_rows_shared_on_many_paths("Ty::settle in n shared rows", |t, b| {
        t.settle(&|v: &str| b.get(v).cloned())
    });
}

/// `n` functions `(Oi) -> (Oi, Hi)`, each holding the one variable `Hi` and owning `Oi`, with
/// all `2n` variables bound: each function keeps its own `Oi` and replaces `Hi`, looked up for
/// the variables it holds, not by a copy of the `2n` binds less its own (O(n^2) in all;
/// REPLACE-shared-rows, COMPLEXITY.md F97).
#[test]
fn replacing_in_many_functions_that_each_hold_one_bound_variable_scales() {
    let n = 8000;
    let (os, hs, ws) = (
        variables_at("O", n),
        variables_at("H", n),
        variables_at("W", n),
    );
    let made: BTreeMap<_, _> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, functions_holding_one(&os[&m], &hs[&m], &ws[&m])))
        .collect();
    scaling::check(
        "n functions each holding one of 2n bound variables",
        n,
        |m| {
            let (t, binds) = &made[&m];
            let out = t.replace(binds);
            for (s, (o, w)) in out.fns.iter().zip(os[&m].iter().zip(&ws[&m])) {
                assert_eq!(s.arrows[0].result, Ty::tuple(vec![o.clone(), w.clone()]));
            }
        },
    );
}

/// The program family checks with no walk that follows each of its `2^n` paths, and in time
/// linear in `n`: each call `p(s, v)` replays its data need on `s`, a type of `k` rows at the
/// `k`th call, and `Ck::data` enters only the one row the call before made, since it keeps the
/// rows it entered. `Ck::bound` likewise skips the rows it found to hold only classes that
/// outlast the call (`Ck::clean`), and a replacement reads the index its binding keeps
/// (`Binds`) rather than building one from all the binds (CK-data-memo, COMPLEXITY.md F97; it
/// was of order `n^2`).
fn rows_shared_on_many_paths(what: &str, call: bool) {
    let units = resolved(3200, |n| shared_rows(n, call));
    scaling::check_order(what, 3200, 1, |m| {
        assert_eq!(units[&m].type_errors(), Vec::<String>::new());
    });
}

/// Besides its ratio: no type error. Small instance, in a function and its call:
/// `scaling::rows_shared_on_many_paths_check_in_a_function_and_its_call`.
#[test]
fn rows_shared_on_many_paths_scale_in_a_function() {
    rows_shared_on_many_paths("a function of n shared rows", false);
}

/// Besides its ratio: no type error. Small instance, in a function and its call:
/// `scaling::rows_shared_on_many_paths_check_in_a_function_and_its_call`.
#[test]
fn rows_shared_on_many_paths_scale_in_its_call() {
    rows_shared_on_many_paths("its call", true);
}

#[test]
fn sums_of_a_line_or_a_count_check_in_linear_time() {
    let units = resolved(5000, sums_of_a_line_or_a_count);
    scaling::check_order("n sums of a line or a count", 5000, 1, |m| {
        assert_eq!(units[&m].type_errors(), Vec::<String>::new());
    });
}

#[test]
fn a_chain_of_tests_is_linear_in_its_length() {
    let units = resolved(1024, a_chain_of_tests);
    scaling::check("a chain of n tests on one int", 1024, |m| {
        let info = units[&m].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn never_arguments_check_in_linear_time() {
    let units = resolved(8000, never_arguments);
    scaling::check_order(
        "n arguments of type Never to a generic function",
        8000,
        1,
        |m| {
            assert_eq!(units[&m].type_errors(), Vec::<String>::new());
        },
    );
}

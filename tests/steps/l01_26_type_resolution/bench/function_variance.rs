use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::elab;

/// n functions, each with a parameter declared with a range and each passed to a partial slot
/// whose domain is wider (FAIL-fn-range-domain-partial-slot), and n with exact parameters of
/// a narrower type (FAIL-partial-slot-call-outside-domain): each passing builds one domain
/// test, O(arrows · parameters), so checking and elaborating the whole is linear. Besides its
/// ratio: the program elaborates at each size. Small instances:
/// `function_variance::a_partial_slot_takes_a_function_on_a_narrower_range` and
/// `function_variance::a_call_through_a_partial_slot_outside_the_domain_misses`.
#[test]
fn many_functions_passed_to_partial_slots_scale() {
    let what = "n functions, each passed to a partial slot through a domain test";
    let make = |n: usize| {
        let mut src = String::from(
            "opt(f: (x: int) ->? int) = f(x: 50) else #notFound -> 0;\napply(f: (x: int | f64) ->? int) = f(x: 2.5) else #notFound -> 0;\n",
        );
        for i in 0..n {
            src.push_str(&format!(
                "r{i}(x: int[0..<10]) = x;\na{i} = opt(f: r{i});\ns{i}(x: int) = x + {i};\nb{i} = apply(f: s{i});\n"
            ));
        }
        src
    };
    let n = 400;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        assert!(u.get(&format!("b{}", m - 1)).is_some(), "{what} at {m}");
    });
}

/// n functions, each passed to a partial slot inside a one-tuple and as the result of a call,
/// and one function inside n nested one-tuples passed to a partial slot of the same nesting
/// (FAIL-partial-slot-nested-guard): each value is rebuilt once, by a walk of its type and the
/// slot's type that visits each place a value stands once (`Ck::coercion`), and the rebuilt
/// term has one node per place, so checking and elaborating the whole is linear. Besides its
/// ratio: the program elaborates at each size. Small instance:
/// `function_variance::a_function_inside_a_value_misses_outside_its_domain`.
#[test]
fn many_and_deep_functions_inside_values_at_partial_slots_scale() {
    let what = "n functions inside values, and one n deep, each rebuilt at a partial slot";
    let make = |n: usize| {
        let slot = "(x: int | f64) ->? int";
        let (mut deep_t, mut deep_v, mut deep_get) =
            (slot.to_string(), "s0".to_string(), "b".to_string());
        for _ in 0..n {
            deep_t = format!("({deep_t},)");
            deep_v = format!("({deep_v},)");
            deep_get.push_str("[0]");
        }
        let mut src = format!(
            "useWide(b: ({slot},)) = b[0](x: 2.5) else #notFound -> 0;\napply(f: {slot}) = f(x: 2.5) else #notFound -> 0;\n\
             useDeep(b: {deep_t}) = {deep_get}(x: 2.5) else #notFound -> 0;\n"
        );
        for i in 0..n {
            src.push_str(&format!(
                "s{i}(x: int) = x + {i};\nb{i} = useWide(b: (s{i},));\n\
                 g{i}() = s{i};\nc{i} = apply(f: g{i}());\n"
            ));
        }
        src.push_str(&format!("d = useDeep(b: {deep_v});\n"));
        src
    };
    let n = 200;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        assert!(u.get("d").is_some(), "{what} at {m}");
    });
}

/// n functions, each passed through its own generic parameter to a partial slot; one function
/// passed down a chain of n generic functions to the slot; and one function n tuples deep in a
/// generic argument, taken out by n indexings (FAIL-partial-slot-generic-pass): each need that
/// passes a function through a type variable into the slot finds the argument it came from by
/// one hash lookup and rebuilds it along the component path, O(depth), once per call, so
/// checking and elaborating the whole is linear. Besides its ratio: the program elaborates at
/// each size. Small instances:
/// `function_variance::a_function_passed_through_a_generic_parameter_misses_outside_its_domain`
/// and
/// `function_variance::a_function_in_a_component_of_a_generic_argument_misses_outside_its_domain`.
#[test]
fn functions_passed_through_generic_parameters_to_partial_slots_scale() {
    let what = "n functions passed through generic parameters, a chain of n, and one n deep";
    let make = |n: usize| {
        let mut src = String::from(
            "apply(f: (x: int | f64) ->? int) = f(x: 2.5) else #notFound -> 0;\npass(x) = apply(f: x);\nq0(x) = apply(f: x);\n",
        );
        let (mut deep_v, mut deep_get) = ("s0".to_string(), "p".to_string());
        for _ in 0..n {
            deep_v = format!("({deep_v}, 1)");
            deep_get.push_str("[0]");
        }
        for i in 0..n {
            src.push_str(&format!(
                "s{i}(x: int) = x + {i};\nb{i} = pass(x: s{i});\nq{}(x) = q{i}(x: x);\n",
                i + 1
            ));
        }
        src.push_str(&format!(
            "c = q{n}(x: s0);\ndeep(p) = apply(f: {deep_get});\nd = deep(p: {deep_v});\n"
        ));
        src
    };
    let n = 200;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        assert!(
            u.get("d").is_some() && u.get("c").is_some(),
            "{what} at {m}"
        );
    });
}

/// n functions, each passed to one generic function that calls its parameter by name; one
/// function passed down a chain of n generic functions to such a call; and one function passed
/// to a body of n calls of it by name (FAIL-elab-named-call-generic-param): each call need
/// carries its call's place in the body, and each meeting of it at a call of the generic
/// function records the signature there, by a hash lookup and O(parameters + arguments), and
/// the recordings are compared once at the end (row TEST-call-site-need-key), O(k log k), so
/// checking and elaborating the whole is n log n at most. Besides its
/// ratio: the program elaborates at each size. Small instance:
/// `function_variance::a_named_call_of_a_generic_parameter_runs`.
#[test]
fn named_calls_of_generic_parameters_scale() {
    let what = "n functions called by name through a generic parameter, a chain of n, and a body of n calls";
    let make = |n: usize| {
        let mut src = String::from("call(g) = g(x: 3);\nq0(g) = g(x: 1);\n");
        let mut many = String::from("many(g) = 0");
        for i in 0..n {
            src.push_str(&format!(
                "s{i}(x: int) = x + {i};\nb{i} = call(g: s{i});\nq{}(g) = q{i}(g: g);\n",
                i + 1
            ));
            many.push_str(&format!(" + g(x: {i})"));
        }
        src.push_str(&format!("c = q{n}(g: s0);\n{many};\nd = many(g: s0);\n"));
        src
    };
    let n = 200;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        assert!(
            u.get("d").is_some() && u.get("c").is_some(),
            "{what} at {m}"
        );
    });
}

/// n functions passed to a partial slot through a generic body by each route of
/// FAIL-partial-slot-generic-needless-refusals: a default that reads another parameter, `x else
/// x`, a generic function passed as a value with the function as the other argument, and a
/// generic function passed as a value called on a function its caller's body writes. Each call
/// replays the callee's needs once; a default is recorded once per default, a written call use
/// once per use (`Ck::call_written`), and a named call through a parameter records its
/// signature once per call (`Ck::record_call`), so checking and elaborating the whole is linear.
/// Besides its ratio: the program elaborates at each size. Small instances:
/// `function_variance::values_a_generic_body_passes_on_from_its_arguments_miss_outside_the_domain`.
#[test]
fn functions_passed_by_defaults_else_and_generic_values_to_partial_slots_scale() {
    let what =
        "n functions passed by a default, `x else #notFound -> x`, and generic functions as values";
    let make = |n: usize| {
        let mut src = String::from(
            "apply(f: (x: int | f64) ->? int) = f(x: 2.5) else #notFound -> 0;\npass(x) = apply(f: x);\n\
             pd(x, y = x) = apply(f: y);\npe(x) = apply(f: x else #notFound -> x);\nrun(g, v) = g(x: v);\n",
        );
        for i in 0..n {
            src.push_str(&format!(
                "s{i}(x: int) = x + {i};\nd{i} = pd(x: s{i});\ne{i} = pe(x: s{i});\n\
                 r{i} = run(g: pass, v: s{i});\nt{i}(g) = g(x: s{i});\nw{i} = t{i}(g: pass);\n"
            ));
        }
        src
    };
    let n = 200;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        let last = m - 1;
        assert!(
            ["d", "e", "r", "w"]
                .iter()
                .all(|k| u.get(&format!("{k}{last}")).is_some()),
            "{what} at {m}"
        );
    });
}

/// n functions passed to a partial slot as entries of a family that lies in an argument
/// (FAIL-partial-slot-generic-family-entry, FAIL-partial-slot-generic-lambda-map): read by key
/// in a generic body, passed on by a lambda of `map` on a written list, and by a lambda of
/// `map` in a generic body; and one generic body of n such lambdas on one receiver, called
/// once. Each read or `map` tests the family's arrows once (`entries_alike`, O(arrows)), each
/// call replays the callee's needs once after one pass over them
/// (`Ck::lambda_entries_placed`, O(needs)), and each place rebuilt is one coercion at one
/// span, so checking and elaborating the whole is linear. Besides its ratio: the program
/// elaborates at each size. Small instances:
/// `function_variance::a_function_taken_from_a_family_argument_misses_outside_its_domain` and
/// `function_variance::a_generic_function_called_from_a_map_lambda_misses_outside_the_domain`.
#[test]
fn functions_passed_as_family_entries_to_partial_slots_scale() {
    let what =
        "n functions passed as family entries by key, by `map` written and in a generic body";
    let make = |n: usize| {
        let mut src = String::from(
            "apply(f: (x: int | f64) ->? int) = f(x: 2.5) else #notFound -> 0;\npass(x) = apply(f: x);\n\
             key(m) = apply(f: m[0]);\nh(m) = m.map(g -> pass(x: g))[0];\nmany(m) = 0",
        );
        for _ in 0..n {
            src.push_str(" + m.map(g -> pass(x: g))[0]");
        }
        src.push_str(";\n");
        for i in 0..n {
            src.push_str(&format!(
                "s{i}(x: int) = x + {i};\nk{i} = key(m: [s{i}]);\n\
                 w{i} = [s{i}].map(g -> pass(x: g))[0];\ng{i} = h(m: [s{i}]);\n"
            ));
        }
        src.push_str("c = many(m: [s0]);\n");
        src
    };
    let n = 200;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        let last = m - 1;
        assert!(
            u.get("c").is_some()
                && ["k", "w", "g"]
                    .iter()
                    .all(|k| u.get(&format!("{k}{last}")).is_some()),
            "{what} at {m}"
        );
    });
}

/// One generic body with n named calls of its parameter, all with arguments of one type, called
/// at n places, each with a function of its own of one type (row TEST-call-site-need-key):
/// each call of the body meets the body's needs for its function, and n calls in the body with
/// arguments of one type are one need (`Class::known` keys a call need without its call), so
/// the whole is linear; keyed with it, as at commit 69526a75a, they were n needs at each of
/// the n calls, n·n in all (ratio 44 at 8n). Besides its ratio: the program elaborates at each
/// size. Small instances: `function_variance::named_calls_with_arguments_alike_run` and
/// `function_variance::a_generic_curried_call_runs_in_any_order_of_the_text`.
#[test]
fn many_calls_of_a_body_with_many_named_calls_scale() {
    let what = "one generic body with n named calls of its parameter, called at n places";
    let make = |n: usize| {
        let mut src = String::from("many(g, v: int) = 0");
        for _ in 0..n {
            src.push_str(" + g(x: v)");
        }
        src.push_str(";\n");
        for i in 0..n {
            src.push_str(&format!(
                "s{i}(x: int) = x + {i};\nc{i}(y: int) = many(g: s{i}, v: y);\n"
            ));
        }
        src
    };
    let n = 200;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        assert!(u.get(&format!("c{}", m - 1)).is_some(), "{what} at {m}");
    });
}

/// One generic body indexing its parameter n times, `many(t) = 0 + t[0] + ... + t[0]`, called
/// at n places, each with a tuple of its own (row FAIL-component-need-site-product): the n
/// brackets alike are one need on the parameter's class, recorded at the first bracket, met
/// once at each call, and each later bracket takes the first's meaning once when the check
/// ends (`Ck::share_alike`, row TEST-component-site-need-key), so the whole is linear; with
/// the bracket's site in the need's key, as at commit 4b9fda6f9, they were n needs met at each
/// of the n calls, n·n in all (ratio 42.24 at 8n). Besides its ratio: the program elaborates
/// at each size. Small instances: `function_variance::uses_alike_in_one_body_run` and
/// `function_variance::brackets_alike_give_the_errors_of_one_bracket_in_any_order`.
#[test]
fn one_body_indexing_its_parameter_n_times_called_n_times_scales() {
    let what = "one generic body with n indexings of its parameter, called at n places";
    let make = |n: usize| {
        let mut src = String::from("many(t) = 0");
        for _ in 0..n {
            src.push_str(" + t[0]");
        }
        src.push_str(";\n");
        for i in 0..n {
            src.push_str(&format!("c{i}(y: int) = many(t: (y, {i}));\n"));
        }
        src
    };
    let n = 200;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        assert!(u.get(&format!("c{}", m - 1)).is_some(), "{what} at {m}");
    });
}

/// n functions, each with a parameter declared with a range and each passed to an exact slot
/// whose parameter type is wider (MSG-fn-domain-wider-repair, part 2): each is refused once,
/// with the narrower-domain message, after one trial of the fit without its range needs, so
/// checking the whole is linear. Besides its ratio: n errors at each size, each in that form.
/// Small instance: `function_variance::a_narrower_range_domain_says_so_in_the_carrier_form`.
#[test]
fn many_narrower_range_domains_at_exact_slots_scale() {
    use super::super::type_errors;
    let what = "n functions on a range, each refused at an exact slot";
    let make = |n: usize| {
        let mut src = String::from("apply(f: (x: int) -> int) = f(x: 100);\n");
        for i in 0..n {
            src.push_str(&format!(
                "r{i}(x: int[0..<10]) = x;\na{i} = apply(f: r{i});\n"
            ));
        }
        src
    };
    let n = 400;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let errors = type_errors(&inputs[&m]);
        assert_eq!(errors.len(), m, "{what} at {m}");
        assert!(
            errors.iter().all(|e| e.contains("its domain is narrower")),
            "{what} at {m}"
        );
    });
}

/// One generic body with n uses `u` alike of its parameter, `many(t) = 0 + u + ... + u`, called
/// at n places, each with a list of `int` of its own (row TEST-component-site-need-key): the
/// uses alike are one need on the parameter's class, recorded at the first written, met once
/// at each call, and each later use takes what the first's need decided once when the check
/// ends (`Ck::alike_fold`, `Ck::share_alike`), so the whole is linear; with a need for each
/// use, as at commit 4b9fda6f9, they were n needs met at each of the n calls, n·n in all
/// (ratios 44 to 48 at 8n). Besides its ratio: the program elaborates at each size.
fn many_uses_alike_scale(u: &str) {
    let what = format!("one generic body with n uses `{u}` of its parameter, called at n places");
    let u = u.to_string();
    let make = move |n: usize| {
        let mut src = String::from("many(t) = 0");
        for _ in 0..n {
            src.push_str(&format!(" + {u}"));
        }
        src.push_str(";\n");
        for i in 0..n {
            src.push_str(&format!("c{i}(y: int) = many(t: [y, {i}]);\n"));
        }
        src
    };
    let n = 100;
    let inputs = scaling::inputs(n, make);
    scaling::check(&what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        assert!(u.get(&format!("c{}", m - 1)).is_some(), "{what} at {m}");
    });
}

/// A level word, `.count` (`NeedKind::Level`), at [`many_uses_alike_scale`]. Small instance:
/// `function_variance::uses_alike_in_one_body_run`.
#[test]
fn one_body_counting_its_parameter_n_times_called_n_times_scales() {
    many_uses_alike_scale("t.count");
}

/// A scan, `.scan((+))` (`NeedKind::Level`, whose key holds the receiver as written), at
/// [`many_uses_alike_scale`]. Small instance: `function_variance::uses_alike_in_one_body_run`.
#[test]
fn one_body_scanning_its_parameter_n_times_called_n_times_scales() {
    many_uses_alike_scale("t.scan((+)).count");
}

/// A fold `><` (`NeedKind::Reduce`) at [`many_uses_alike_scale`]. Small instances:
/// `function_variance::uses_alike_in_one_body_run` and
/// `function_variance::a_fold_alike_to_one_split_by_its_calls_is_split_too`.
#[test]
fn one_body_folding_its_parameter_n_times_called_n_times_scales() {
    many_uses_alike_scale("(t >< (+))");
}

/// `.sum` (`NeedKind::SumMethod`) at [`many_uses_alike_scale`]. Small instance:
/// `function_variance::uses_alike_in_one_body_run`.
#[test]
fn one_body_summing_its_parameter_n_times_called_n_times_scales() {
    many_uses_alike_scale("t.sum");
}

/// A remap (`NeedKind::Remap`) at [`many_uses_alike_scale`] (FAIL-remap-need-site-product,
/// 54.40 times the instructions at 8n before).
#[test]
fn one_body_remapping_its_parameter_n_times_called_n_times_scales() {
    many_uses_alike_scale("(t as (k -> v) into (v -> k)).count");
}

/// A remap whose new key computes (FAIL-remap-computed-key-need-site-product) at
/// [`many_uses_alike_scale`].
#[test]
fn one_body_remapping_its_parameter_to_a_computed_key_n_times_called_n_times_scales() {
    many_uses_alike_scale("(t as (k -> v) into (k + 1 -> v)).count");
}

/// A remap whose new keys compute and whose last level folds by `><`
/// (FAIL-remap-computed-key-need-site-product) at [`many_uses_alike_scale`].
#[test]
fn one_body_remapping_its_parameter_to_a_folded_computed_key_n_times_called_n_times_scales() {
    many_uses_alike_scale("(t as (k -> v) into (k mod 2 -> k * 2 >< (+) -> v)).count");
}

/// One generic body with n brackets `t[0]` alike whose results resolve differently, called at
/// n places (row TEST-component-site-need-key). The brackets cycle through four forms: passed
/// to `drop`, which takes any value (a type variable with no bound), passed to a parameter of
/// type `int` (resolved to `int`), passed to one of type `int | f64` (resolved to that type),
/// and added to `1` and passed to `drop` (a type variable bounded to the numbers).
/// `Ck::share_alike` groups the brackets by what their results are, so each form keeps one
/// need of its own, four in all, met at each call, and the whole stays linear. The body is a
/// sum so that its result type keeps one size: a tuple of the n brackets would give each call
/// a result type of n components, n·n in all whatever the needs do (ratio 43.5 with the tuple
/// of n plain brackets). Besides its ratio: the program elaborates at each size.
#[test]
fn one_body_indexing_its_parameter_n_times_with_results_resolved_differently_scales() {
    let what = "one generic body with n indexings resolved four ways, called at n places";
    let make = |n: usize| {
        let mut src =
            String::from("fi(x: int) = x;\nfu(x: int | f64) = 0;\ndrop(x) = 0;\nmany(t) = 0");
        for i in 0..n {
            src.push_str(match i % 4 {
                0 => " + drop(x: t[0])",
                1 => " + fi(x: t[0])",
                2 => " + fu(x: t[0])",
                _ => " + drop(x: t[0] + 1)",
            });
        }
        src.push_str(";\n");
        for i in 0..n {
            src.push_str(&format!("c{i}(y: int) = many(t: (y, {i}));\n"));
        }
        src
    };
    let n = 100;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        assert!(u.get(&format!("c{}", m - 1)).is_some(), "{what} at {m}");
    });
}

/// A call through a value that may hold either of two functions of p parameters, one declaring
/// them in the other's reverse order, run 200 times (DESIGN.md sec:values_morphisms, "The
/// function called places the arguments"): the function called places the p named arguments
/// by its own parameter list, a merge of two sorted lists, O(p) a call, so the run is linear
/// in p. Small instance:
/// `function_variance::a_call_through_functions_differing_in_places_or_defaults_runs`.
#[test]
fn placing_p_named_arguments_in_the_function_called_scales() {
    use zed_tests::step_helpers::l01_16_elaboration::with_prelude;
    use zed_tests::step_helpers::l01_36_cranelift::kernel;
    let what = "200 calls of p named arguments placed by the function called";
    let make = |p: usize| {
        let ps: Vec<String> = (0..p).map(|i| format!("x{i}: int")).collect();
        let rs: Vec<String> = (0..p).rev().map(|i| format!("x{i}: int")).collect();
        let args: Vec<String> = (0..p).map(|i| format!("x{i}: n")).collect();
        let xs: Vec<String> = (0..200).map(|i| i.to_string()).collect();
        let src = format!(
            "f({}) = x0 - x1;\ng({}) = x1 - x0 + 1;\npick(c: bool) = if c {{ f }} else {{ g }};\nh = pick(c: false);\nxs = [{}];\na = xs.map(n -> h({}))[199];\n",
            ps.join(", "),
            rs.join(", "),
            xs.join(", "),
            args.join(", ")
        );
        with_prelude(elab(&src).unwrap().get("a").unwrap())
    };
    let n = 40;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        assert_eq!(kernel(&inputs[&m]).map(|v| v.to_string()), Ok("1".into()));
    });
}

/// A curried call through the value of
/// [`placing_p_named_arguments_in_the_function_called_scales`], giving one argument by name and
/// leaving p - 1 out, then a call of its result with those p - 1 by name, run 200 times (row
/// CALL-curried-placed): the function held places the given and the left-out arguments by a
/// merge of sorted lists, O(p), and the result places the second call's by its own sorted
/// list, O(p), so the run is linear in p. Small instance:
/// `function_variance::a_curried_call_through_functions_differing_in_places_runs`.
#[test]
fn a_curried_call_placing_p_named_arguments_scales() {
    use zed_tests::step_helpers::l01_16_elaboration::with_prelude;
    use zed_tests::step_helpers::l01_36_cranelift::kernel;
    let what = "200 curried calls leaving p - 1 named arguments out, each result called by name";
    let make = |p: usize| {
        let ps: Vec<String> = (0..p).map(|i| format!("x{i}: int")).collect();
        let rs: Vec<String> = (0..p).rev().map(|i| format!("x{i}: int")).collect();
        let rest: Vec<String> = (1..p).map(|i| format!("x{i}: n")).collect();
        let xs: Vec<String> = (0..200).map(|i| i.to_string()).collect();
        let src = format!(
            "f({}) = x0 - x1;\ng({}) = x1 - x0 + 1;\npick(c: bool) = if c {{ f }} else {{ g }};\nh = pick(c: false);\nxs = [{}];\na = xs.map(n -> h(x0: n, ...)({}))[199];\n",
            ps.join(", "),
            rs.join(", "),
            xs.join(", "),
            rest.join(", ")
        );
        with_prelude(elab(&src).unwrap().get("a").unwrap())
    };
    let n = 40;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        assert_eq!(kernel(&inputs[&m]).map(|v| v.to_string()), Ok("1".into()));
    });
}

/// The functions of [`placing_p_named_arguments_in_the_function_called_scales`] at p
/// parameters, `h` the value of `pick`, and `a` the sum of 2^`levels` calls by name: `k0` holds
/// a call of `h`, which `h`'s function places, and the same call of `g` by its own name, one in
/// each arm of an `if`, and runs the first (`placed`) or the second; each `k{i}` calls
/// `k{i - 1}` twice. Both programs compile the same code, once, and differ only in which
/// call runs; a `map` or recursion would run in the kernel. Each call gives 1. `g` declares
/// its parameters in the reverse of the order the call names them, so the placed call moves
/// every argument.
fn placed_or_direct(p: usize, placed: bool, levels: usize) -> zed_kernel::Term {
    use zed_tests::step_helpers::l01_16_elaboration::with_prelude;
    let ps: Vec<String> = (0..p).map(|i| format!("x{i}: int")).collect();
    let rs: Vec<String> = (0..p).rev().map(|i| format!("x{i}: int")).collect();
    let args = (0..p)
        .map(|i| format!("x{i}: z"))
        .collect::<Vec<_>>()
        .join(", ");
    let ks: String = (1..=levels)
        .map(|i| format!("k{i}(z: int) = k{}(z: z) + k{}(z: z + 1);\n", i - 1, i - 1))
        .collect();
    let first = if placed { "z >= 0" } else { "z < 0" };
    let src = format!(
        "f({}) = x0 - x1;\ng({}) = x1 - x0 + 1;\npick(c: bool) = if c {{ f }} else {{ g }};\nh = pick(c: false);\nk0(z: int) = if {first} {{ h({args}) }} else {{ g({args}) }};\n{ks}a = k{levels}(z: 0);\n",
        ps.join(", "),
        rs.join(", "),
    );
    with_prelude(elab(&src).unwrap().get("a").unwrap())
}

/// [`placing_p_named_arguments_in_the_function_called_scales`] in native code (row
/// CALL-callee-places-native): one call by name in `run`, run 16384 times through `f`'s and
/// `g`'s parameter lists in turn, so that each run merges the call's sorted names with the
/// list, O(p), where a merge kept for one list would be reused; no call of the kernel, and the
/// functions' bodies run in native code. `k0` makes two calls and each `k{i}` calls `k{i - 1}`
/// twice, so compiling is linear in p too, and the runs outweigh it enough that an O(p²) merge
/// fails the test: one that also searched the list for each name gave 18.3 (sizes 40 and
/// 320, in instructions), against 3.9 for the code's. Small instance:
/// `function_variance::a_call_its_function_places_runs_in_native_code_alone`.
#[test]
fn placing_p_named_arguments_in_native_code_scales() {
    use zed_tests::step_helpers::l01_16_elaboration::with_prelude;
    use zed_tests::step_helpers::l01_36_cranelift::native;
    let what = "16384 calls of p named arguments placed by the function called in turn through \
                two lists, in native code";
    let make = |p: usize| {
        let ps: Vec<String> = (0..p).map(|i| format!("x{i}: int")).collect();
        let rs: Vec<String> = (0..p).rev().map(|i| format!("x{i}: int")).collect();
        let args = (0..p)
            .map(|i| format!("x{i}: z"))
            .collect::<Vec<_>>()
            .join(", ");
        let levels: String = (1..=13)
            .map(|i| format!("k{i}(z: int) = k{}(z: z) + k{}(z: z + 1);\n", i - 1, i - 1))
            .collect();
        let src = format!(
            "f({}) = x0 - x1;\ng({}) = x1 - x0 + 1;\npick(c: bool) = if c {{ f }} else {{ g }};\nrun(k, z) = k({args});\nk0(z: int) = run(k: pick(c: true), z: z) + run(k: pick(c: false), z: z);\n{levels}a = k13(z: 0);\n",
            ps.join(", "),
            rs.join(", "),
        );
        with_prelude(elab(&src).unwrap().get("a").unwrap())
    };
    let n = 40;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let o = native(&inputs[&m]).unwrap();
        assert_eq!((o.value.to_string(), o.kernel_calls), ("8192".into(), 0));
    });
}

/// In native code a program whose call by name the function called places costs about what
/// the same program calling that function by its own name costs, at p = 320, 65536 calls,
/// compiling included (row CALL-callee-places-native; before it, the placed call ran in the
/// kernel). While the merge kept for the call's node is for the closure's list, the call site
/// goes straight to the lambda's placed entry, which reads each argument where the call site
/// stored it, one load of its offset more than a direct call. Measured on 1.99.1: 815M
/// instructions against 777M (1.049); the run alone about 7.27K instructions a call against
/// 6.70K (1.085). On nightly-2026-11-18 this test gave 1.233 (run alone 10.2K against 6.44K),
/// all of it `rt_args` emptying and refilling its buffer at each call; with the buffer kept
/// (row CALL-direct-buffer-proof), 1061M against 1069M (0.993), the run alone 6.32K a call
/// against 6.44K.
/// When each call went through `rt_named`, which passes the arguments three times, the run
/// alone was 17.4K a call (2.60) and this test 1.97.
#[test]
fn a_placed_call_costs_about_a_direct_call_in_native_code() {
    use zed_tests::step_helpers::l01_36_cranelift::native;
    let (placed, direct) = (
        placed_or_direct(320, true, 16),
        placed_or_direct(320, false, 16),
    );
    let run = |t: &zed_kernel::Term| {
        let o = native(t).unwrap();
        assert_eq!((o.value.to_string(), o.kernel_calls), ("65536".into(), 0));
    };
    scaling::compare_costs(
        "65536 calls of 320 named arguments in native code, placed by the function called and \
         to the function by its name, compiling included",
        "both programs compile the same code and run the body in native code; the placed call \
         adds one runtime call and a load of each argument's offset",
        1.10,
        || run(&direct),
        || run(&placed),
    );
}

/// The placed call of [`a_placed_call_costs_about_a_direct_call_in_native_code`], 16384 calls
/// through one list, at p = 40 and 320: each call after the first goes to the placed entry of
/// `g`'s lambda, which reads each argument at its offset, O(p), and that entry, a second copy
/// of `g`'s body, compiles in O(p) (row CALL-callee-places-native). Instructions, 2026-11-17:
/// see COMPLEXITY.md CALL-callee-places-native.
#[test]
fn a_repeated_placed_call_of_p_named_arguments_in_native_code_scales() {
    use zed_tests::step_helpers::l01_36_cranelift::native;
    let n = 40;
    let inputs = scaling::inputs(n, |p| placed_or_direct(p, true, 14));
    scaling::check(
        "16384 calls of p named arguments placed by the function called through one list, in \
         native code",
        n,
        |m| {
            let o = native(&inputs[&m]).unwrap();
            assert_eq!((o.value.to_string(), o.kernel_calls), ("16384".into(), 0));
        },
    );
}

/// A class of a function parameter `T` narrowed at a closed parameter by calls
/// (FAIL-check-class-in-fn-arg-not-narrowed, `Ck::fit_classes`): n functions, each passed where
/// `(h: (x: int) -> int, y: int) -> int` is expected with `T` at both `int`s; and one function
/// whose `T` lies n function types deep, passed where the same depth of `int` is expected,
/// then called with a function of that type. Each level is one call of the function's
/// parameters, tried once at the outermost level and then run for good (`Ck::fitting`); with a
/// trial at each level, each run for good tried every level inside it again, O(n²) for the
/// depth. The deep one runs on a 2 MiB stack, 400 and 3200 deep: each level's fit waits for
/// the one around it to end (`Ck::fits_waiting`); run inside the call that found it, it
/// overflowed that stack 400 deep. Each level's call leaves the result `int` as it is, without
/// a walk of the parameters below it (`close`); with that walk, 28.9 times the work at 8n. The
/// same depth with each result a variable of its own (`U0 in int`, …), which `close` does walk
/// the parameters for, measured 8.1 times. Both deep series also compare each level's
/// arrows with every function the comparison has opened (`permitted`, `fn_holds_own`), O(n²)
/// in all: 17.9 and 22.2 times at 8n, against 7.7 and 7.9 without that scan (row
/// FAIL-l0126-bench-regressions, which also holds `a_power_returned_n_deep`). And n functions
/// passed at a partial parameter, where no call is made and each parameter of the function is
/// compared once with the arrow's (`Ck::result_into`). Besides its ratio: no errors at each
/// size. Small instances:
/// `function_variance::a_class_inside_a_function_argument_nested_is_narrowed`,
/// `function_variance::a_class_inside_a_function_argument_is_narrowed_at_a_partial_parameter` and
/// `function_variance::a_function_whose_results_are_variables_of_their_own_fits_int_results`.
#[test]
fn classes_inside_function_arguments_narrowed_by_calls_scale() {
    use super::super::type_errors;
    let many = |n: usize| {
        let mut src = String::from("p(f: (h: (x: int) -> int, y: int) -> int) = 0;\n");
        for i in 0..n {
            src.push_str(&format!(
                "q{i}(g: (h: (x: T) -> int, y: T) -> int) = p(f: g);\n"
            ));
        }
        src
    };
    let partial = |n: usize| {
        let mut src = String::from("p(f: (x: (int, int) | String) ->? int) = 0;\n");
        for i in 0..n {
            src.push_str(&format!("q{i}(g: (x: (T, T)) -> int) = p(f: g);\n"));
        }
        src
    };
    let deep = |n: usize| {
        let (mut pt, mut qt) = ("int".to_string(), "T".to_string());
        for _ in 0..n {
            pt = format!("(x: {pt}) -> int");
            qt = format!("(x: {qt}) -> int");
        }
        format!(
            "p(f: (h: {pt}, y: int) -> int) = 0;\nq(g: (h: {qt}, y: T) -> int) = p(f: g);\n\
             s(h: {pt}, y: int) = 0;\na = q(g: s);\n"
        )
    };
    for (what, n, make) in [
        (
            "n functions, each with a class narrowed by a call",
            400,
            &many as &dyn Fn(usize) -> String,
        ),
        (
            "n functions, each passed at a partial parameter",
            400,
            &partial,
        ),
    ] {
        let inputs = scaling::inputs(n, make);
        scaling::check(what, n, |m| {
            let errors = type_errors(&inputs[&m]);
            assert!(errors.is_empty(), "{what} at {m}: {errors:?}");
        });
    }
    let declared = |n: usize| {
        let (mut pt, mut qt) = ("int".to_string(), "int".to_string());
        for i in 0..n {
            pt = format!("(x: {pt}) -> int");
            qt = format!("((x: {qt}) -> U{i} for U{i} in int)");
        }
        format!(
            "p(f: (h: {pt}, y: int) -> int) = 0;\nq(g: (h: {qt}, y: int) -> int) = p(f: g);\n\
             s(h: {pt}, y: int) = 0;\na = q(g: s);\n"
        )
    };
    for (what, n, make) in [
        (
            "one function whose class lies n function types deep, narrowed by calls, on a 2 MiB \
             stack",
            400,
            &deep as &dyn Fn(usize) -> String,
        ),
        (
            "one function n function types deep, each result a variable of its own, on a 2 MiB \
             stack",
            400,
            &declared,
        ),
    ] {
        let inputs = scaling::inputs(n, make);
        zed_tests::deep::on_small_stack(|| {
            scaling::check(what, n, |m| {
                let errors = type_errors(&inputs[&m]);
                assert!(errors.is_empty(), "{what} at {m}: {errors:?}");
            });
        });
    }
}

/// A hot call through a value that agrees with the one function the value holds costs the same
/// in a unit where another call is placed by the function called: the value is then a closure
/// that carries its parameter list, which a call that agrees does not read (DESIGN.md
/// sec:values_morphisms, "The function called places the arguments").
#[test]
fn a_hot_agreeing_call_costs_the_same_beside_a_placed_call() {
    use zed_tests::step_helpers::l01_16_elaboration::with_prelude;
    use zed_tests::step_helpers::l01_36_cranelift::{kernel, native};
    let xs: Vec<String> = (0..5000).map(|i| i.to_string()).collect();
    let hot = format!(
        "f(a: int, b: int) = a - b;\nk = f;\nxs = [{}];\na = xs.map(i -> k(a: i, b: 1))[4999];\n",
        xs.join(", ")
    );
    let placed = format!(
        "{hot}g(b: int, a: int) = a * 10 + b;\npick(c: bool) = if c {{ f }} else {{ g }};\nh = pick(c: false);\nz = h(a: 1, b: 2);\n"
    );
    let term = |src: &str| with_prelude(elab(src).unwrap().get("a").unwrap());
    let (plain, beside) = (term(&hot), term(&placed));
    let why = "the agreeing call is compiled alike in both units; the value carries one more \
               pointer, read by no agreeing call";
    scaling::compare_costs(
        "5000 agreeing calls through a value, alone and beside a placed call, by the kernel",
        why,
        1.05,
        || assert_eq!(kernel(&plain).map(|v| v.to_string()), Ok("4998".into())),
        || assert_eq!(kernel(&beside).map(|v| v.to_string()), Ok("4998".into())),
    );
    scaling::compare_costs(
        "5000 agreeing calls through a value, alone and beside a placed call, in native code",
        why,
        1.05,
        || {
            assert_eq!(
                native(&plain).map(|o| o.value.to_string()),
                Ok("4998".into())
            )
        },
        || {
            assert_eq!(
                native(&beside).map(|o| o.value.to_string()),
                Ok("4998".into())
            )
        },
    );
}

/// Row FAIL-reorder-direct-two-fn-slot (PROOFDOC6-author-questions): a declared function with
/// its named parameters in another order, passed into a union of function types, is fitted to
/// every member it fits (`Ck::fn_members`, since row CHECK-fn-member-same-order-ambiguity):
/// O(k p) to match the names of `k` members of `p` parameters, then one trial fit per member.
/// Two programs: one call into a slot of n members whose last alone takes `re2`, and n calls
/// into a slot of two members. Both are linear. Besides its ratio: the program elaborates at
/// each size. Small instances:
/// `function_variance::a_reordered_function_the_generic_body_passes_only_into_a_union_slot_runs`.
/// The slot whose members all fit, and calls through values of several function types, are
/// measured in `fits_to_every_member_and_literals_through_several_functions_scale`.
#[test]
fn reordered_functions_passed_into_unions_of_function_types_scale() {
    let what = "a reordered function into a slot of n function types, and n into a slot of two";
    let make = |n: usize| {
        let wide: Vec<String> = (0..n)
            .map(|i| format!("((y: int, x: int) -> #r{i})"))
            .chain(std::iter::once("((y: int, x: int) -> int)".to_string()))
            .collect();
        let mut src = format!(
            "re2(x: int, y: int) = x * 10 + y;\nwide(k: {}) = 0;\nw = wide(k: re2);\n\
             app4(k: ((y: int, x: int) -> int) | ((y: int, x: int) -> f64)) = \
             {{ r = k(y: 2, x: 1); if r is int {{ r }} else {{ 0 }} }};\n",
            wide.join(" | ")
        );
        for i in 0..n {
            src.push_str(&format!("a{i} = app4(k: re2);\n"));
        }
        src
    };
    let n = 200;
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        assert!(u.get("w").is_some(), "{what} at {m}");
        assert!(u.get(&format!("a{}", m - 1)).is_some(), "{what} at {m}");
    });
}

/// Row CHECK-fn-member-same-order-ambiguity. First, a reordered `re2` passed into a slot of n
/// members that it all fits, so every one is fitted outside a trial and the n fits are joined
/// (`Ck::fit_members`, `join_fits`): one fit per member, and a join that visits each place of
/// each fit once, so linear in n, unless the union of the members' types grew with each one.
/// Second, calls through values of several function types with literal arguments
/// (`Ck::lits_alike` and the parameter carriers it reads, `lit_reads`): one call `k(2 + 1)`
/// through a value of n function types, whose literals are compared with each member's once,
/// O(n · literals), and n functions each making such a call through a value of two. Both are
/// linear. Besides its ratio: the program elaborates at each size, with no error. Small
/// instances:
/// `function_variance::a_reordered_function_in_a_union_slot_is_fitted_alike_in_either_order`
/// and `function_variance::a_literal_through_functions_of_different_carriers_is_refused`.
#[test]
fn fits_to_every_member_and_literals_through_several_functions_scale() {
    let n = 200;
    let what = "a reordered function into a slot of n function types it fits every one of";
    let make = |n: usize| {
        let all: Vec<String> = (0..n)
            .map(|i| format!("((y: int, x: int) -> int | #s{i})"))
            .collect();
        format!(
            "re2(x: int, y: int) = x * 10 + y;\nall(k: {}) = 0;\nv = all(k: re2);\n",
            all.join(" | ")
        )
    };
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        assert!(u.get("v").is_some(), "{what} at {m}");
    });
    let what = "a literal call through a value of n function types, and n through two";
    let make = |n: usize| {
        let wide: Vec<String> = (0..n).map(|i| format!("(int -> int | #t{i})")).collect();
        let mut src = format!(
            "re1(positional x: int) = x * 10;\n\
             wide(k: {}) = {{ r = k(2 + 1); if r is int {{ r }} else {{ 0 }} }};\n\
             w = wide(k: re1);\n",
            wide.join(" | ")
        );
        for i in 0..n {
            src.push_str(&format!(
                "two{i}(k: (int -> int) | (int -> int | String)) = \
                 {{ r = k({i} + 1); if r is int {{ r }} else {{ 0 }} }};\n\
                 c{i} = two{i}(k: re1);\n"
            ));
        }
        src
    };
    let inputs = scaling::inputs(n, make);
    scaling::check(what, n, |m| {
        let u = elab(&inputs[&m]).unwrap_or_else(|e| panic!("{what} at {m}: {e:?}"));
        assert!(u.get("w").is_some(), "{what} at {m}");
        assert!(u.get(&format!("c{}", m - 1)).is_some(), "{what} at {m}");
    });
}

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
            "opt(f: (x: int) ->? int) = f(x: 50) else 0;\napply(f: (x: int | f64) ->? int) = f(x: 2.5) else 0;\n",
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
            "useWide(b: ({slot},)) = b[0](x: 2.5) else 0;\napply(f: {slot}) = f(x: 2.5) else 0;\n\
             useDeep(b: {deep_t}) = {deep_get}(x: 2.5) else 0;\n"
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
/// and `function_variance::a_function_in_a_component_of_a_generic_argument_misses_outside_its_domain`.
#[test]
fn functions_passed_through_generic_parameters_to_partial_slots_scale() {
    let what = "n functions passed through generic parameters, a chain of n, and one n deep";
    let make = |n: usize| {
        let mut src = String::from(
            "apply(f: (x: int | f64) ->? int) = f(x: 2.5) else 0;\npass(x) = apply(f: x);\nq0(x) = apply(f: x);\n",
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

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

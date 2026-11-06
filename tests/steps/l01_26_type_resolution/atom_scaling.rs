//! The checker at the rule of low complexity (DESIGN.md Part G), on the loose atoms of a
//! parameter: tested, bound to names, handled by an `else`, passed on through calls and
//! passed by at a call (rule 6 of sec:type_resolution). Moved from `scaling` so that each
//! module runs in well under 60 s one test at a time.

use zed_kernel::types::Type as KType;
use zed_tests::scaling;
use zedc::check::ty::Ty;

use super::scaling::resolved;
use super::{info, sig_of};

/// A function whose undeclared parameter `line` is tested against `n` atoms, each test bound
/// to a name, then trimmed.
fn tests_of_atoms(n: usize) -> String {
    let tests: String = (0..n).map(|i| format!("b{i} = line is #a{i}; ")).collect();
    format!("r(positional line) = {{ {tests}trim(line) }};\n")
}

#[test]
fn a_parameter_tested_against_many_atoms_scales() {
    // Each test adds its atom to the parameter's set, the small set into the large one.
    let (i, _) = info(&tests_of_atoms(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    // The atoms `trim` passes by reach the result, so the second arrow takes them; the first,
    // for a parameter with none, gives none.
    let arrows = i.sigs.values().next().unwrap().expand();
    assert_eq!(arrows.len(), 2);
    assert!(arrows[0].params[0].atoms().is_empty());
    assert!(!arrows[1].params[0].atoms().is_empty());
    let units = resolved(400, tests_of_atoms);
    scaling::check("a parameter tested against n atoms", 400, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// A function whose undeclared parameter `line` is bound to `n` names in a chain, written
/// last first, each tested against an atom of its own, the last trimmed.
fn chain_of_names(n: usize) -> String {
    let names: String = (1..n)
        .rev()
        .map(|i| format!("s{i} = s{}; b{i} = s{i} is #a{i}; ", i - 1))
        .collect();
    format!(
        "r(positional line) = {{ {names}s0 = line; b0 = s0 is #a0; trim(s{}) }};\n",
        n - 1
    )
}

#[test]
fn a_parameter_bound_to_a_chain_of_names_scales() {
    // The union-find joins each name to the chain's class in near-constant time, whatever
    // order the bindings are written in, and each test then adds its atom to the class's set.
    let (i, _) = info(&chain_of_names(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    let a = i.sigs.values().next().unwrap().expand().pop().unwrap();
    for k in 0..3 {
        let atom = Ty::set(KType::atom(&format!("a{k}")));
        assert!(atom.subtype(&a.params[0]), "{}", a.params[0]);
    }
    let units = resolved(400, chain_of_names);
    scaling::check("a parameter bound to a chain of n names", 400, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// A function whose undeclared parameter `line` has its loose atoms handled by an `else`, and
/// whose result is `line` trimmed after a chain of `n` names, each the one before it or an
/// atom of its own: the atoms of the chain reach the result from elsewhere than `line`.
fn chain_of_own_atoms(n: usize) -> String {
    let names: String = (1..=n)
        .map(|i| {
            format!(
                "x{i} = if (line else \"\") == \"{i}\" {{ #a{i} }} else {{ x{} }}; ",
                i - 1
            )
        })
        .collect();
    format!("r(positional line) = {{ x0 = line; {names}trim(x{n}) }};\n")
}

#[test]
fn a_chain_of_atoms_from_elsewhere_than_the_parameter_scales() {
    // Each name passes on the atoms of the one before it from elsewhere than `line`, and adds
    // its own, the small set into the large one. The first arrow, for a `line` with no atom,
    // gives the chain's atoms and not `line`'s.
    let (i, _) = info(&chain_of_own_atoms(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    let arrows = i.sigs.values().next().unwrap().expand();
    assert_eq!(arrows.len(), 2);
    for k in 1..=3 {
        let atom = Ty::set(KType::atom(&format!("a{k}")));
        assert!(atom.subtype(&arrows[0].result), "{}", arrows[0].result);
    }
    let other = Ty::set(KType::atom("notFound"));
    assert!(!other.subtype(&arrows[0].result), "{}", arrows[0].result);
    assert!(other.subtype(&arrows[1].result), "{}", arrows[1].result);
    let units = resolved(200, chain_of_own_atoms);
    scaling::check("a chain of n names each adding an atom", 200, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(info.sigs.values().next().unwrap().arrows.len(), 2);
    });
}

/// `n` functions, each handling the atoms of its undeclared parameter `x` with an `else` and
/// passing `x` on to the one before it, the first trimming `x` or giving "empty".
fn chain_of_handlers(n: usize) -> String {
    chain_of_handlers_calling(n, |i| format!("h{}(x)", i - 1))
}

/// [`chain_of_handlers`], each function calling the one before it as `call(i)` writes it.
fn chain_of_handlers_calling(n: usize, call: impl Fn(usize) -> String) -> String {
    let mut src = String::from(
        "h0(positional x) = if (x else \"\") == \"\" { \"empty\" } else { trim(x) };\n",
    );
    for i in 1..n {
        src.push_str(&format!(
            "h{i}(positional x) = if (x else \"\") == \"{i}\" {{ \"d\" }} else {{ {} }};\n",
            call(i)
        ));
    }
    src
}

#[test]
fn a_chain_of_functions_passing_a_handled_parameter_on_scales() {
    // Each function's call of the one before it, with `x` holding no atom, takes that one's
    // first arrow, which gives no atom; so each function's first arrow gives a `String` alone.
    let (i, names) = info(&chain_of_handlers(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    for k in 0..3 {
        let (_, s) = i
            .sigs
            .iter()
            .find(|(id, _)| names[**id] == format!("h{k}"))
            .unwrap();
        let arrows = s.expand();
        assert_eq!(arrows.len(), 2, "h{k}");
        assert!(
            arrows[0].result.atoms().is_empty(),
            "h{k}: {}",
            arrows[0].result
        );
        let other = Ty::set(KType::atom("notFound"));
        assert!(
            other.subtype(&arrows[1].params[0]),
            "h{k}: {}",
            arrows[1].params[0]
        );
    }
    let units = resolved(200, chain_of_handlers);
    scaling::check(
        "a chain of n functions passing a handled parameter on",
        200,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn a_chain_of_functions_passing_a_handled_parameter_on_as_a_receiver_scales() {
    // `x.h0()` is `h0(x)`: the receiver fills the first parameter, so each function's first
    // arrow gives a `String` alone, as in the chain of calls written `h0(x)`.
    let method = |i: usize| format!("x.h{}()", i - 1);
    let (i, names) = info(&chain_of_handlers_calling(3, method));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    for k in 0..3 {
        let (_, s) = i
            .sigs
            .iter()
            .find(|(id, _)| names[**id] == format!("h{k}"))
            .unwrap();
        let arrows = s.expand();
        assert_eq!(arrows.len(), 2, "h{k}");
        assert!(
            arrows[0].result.atoms().is_empty(),
            "h{k}: {}",
            arrows[0].result
        );
    }
    let units = resolved(200, |n| chain_of_handlers_calling(n, method));
    scaling::check(
        "a chain of n functions passing a handled parameter on as a receiver",
        200,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn many_calls_passing_a_handled_parameter_on_scale() {
    // One function calls `r` n times on its handled parameter, as `r(x)`, `x.r()`, `x.r`,
    // through the higher-order `ap` and through a computed callee, and passes `x` to a lambda
    // through `ap`, whose atoms then pass by at the call of `ap`; each call takes `r`'s first
    // arrow from outside, so `g`'s first arrow gives a `String` alone. Each call whose
    // argument holds a loose atom is applied once more, on the atoms from outside alone.
    let r = "r(positional line) = if (line else \"\") == \"\" { \"empty\" } else { trim(line) };\n\
             ap(positional f, positional v) = f(v);\n";
    let calls = |n: usize, call: &str| {
        let body: String = (0..n).map(|i| format!("a{i} = {call}; ")).collect();
        format!("{r}g(positional x) = {{ d = x else \"\"; {body}a0 }};\n")
    };
    for call in [
        "r(x)",
        "x.r()",
        "x.r",
        "ap(r, x)",
        "(if true { r } else { r })(x)",
        "ap((positional y) -> trim(y), x)",
    ] {
        let first = sig_of(&calls(3, call), "g").expand()[0].result.clone();
        assert!(first.atoms().is_empty(), "{call}: {first}");
        let units = resolved(200, |n| calls(n, call));
        scaling::check(
            &format!("one function calling `{call}` n times"),
            200,
            |n| {
                let info = units[&n].check();
                assert!(info.errors.is_empty(), "{:?}", info.errors);
            },
        );
    }
}

#[test]
fn a_chain_of_method_calls_without_parentheses_scales() {
    // `x.r.r` … `.r`, n deep: each call is applied once more on the atoms from outside, and
    // that application takes its receiver's type as found, so the chain is checked in time
    // linear in n. The first arrow of `g` gives a `String` alone.
    let r = "r(positional line) = if (line else \"\") == \"\" { \"empty\" } else { trim(line) };\n";
    let chain = |n: usize| {
        format!(
            "{r}g(positional x) = {{ d = x else \"\"; x{} }};\n",
            ".r".repeat(n)
        )
    };
    let first = sig_of(&chain(3), "g").expand()[0].result.clone();
    assert!(first.atoms().is_empty(), "{first}");
    scaling::check("a chain of n method calls without parentheses", 1000, |n| {
        let (info, _) = info(&chain(n));
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// `n` functions, each testing its undeclared parameter `x` against an atom of its own and
/// passing `x` on to the one before it, and a function calling the last on a value that may
/// be a string, the first function's atom or another.
fn chain_of_atom_tests(n: usize) -> String {
    let mut src = String::from("h0(positional x) = if x is #a0 { \"0\" } else { trim(x) };\n");
    for i in 1..n {
        src.push_str(&format!(
            "h{i}(positional x) = if x is #a{i} {{ \"{i}\" }} else {{ h{}(x) }};\n",
            i - 1
        ));
    }
    format!(
        "{src}g(positional k) = h{}(if k == 1 {{ #a0 }} else {{ if k == 2 {{ #b }} else {{ \"s\" }} }});\n",
        n - 1
    )
}

#[test]
fn a_chain_of_functions_each_testing_an_atom_of_its_own_scales() {
    // Each `h{i}` takes `#a{i}` alone, so its call of the one before it, which omits that atom,
    // passes it by; the call in `g` passes `#a0` and `#b` by, which no arrow of the last takes,
    // and gives the string to its first arrow. Each pass-by costs a set difference per arrow.
    let (i, _) = info(&chain_of_atom_tests(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    let units = resolved(100, chain_of_atom_tests);
    scaling::check(
        "a chain of n functions each testing an atom of its own",
        100,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn many_calls_passing_some_atoms_of_their_argument_by_scale() {
    // `v` may be a string, `#a` or `#b`. `h` takes `#a` and omits `#b`, so each call `h(v)`
    // passes `#b` by and gives `#a` to the arrow that takes it; the lambda takes no atom, so
    // each call of `ap` passes both by, at that call, whose argument gave them.
    //
    // The sizes are those at which a cost per call in the number of calls fails: each call
    // `h(v)` checks in about 500,000 instructions, so at 200 and 1,600 calls a copy of
    // `Info::passes` at each pass-by (`Ck::pass_at`) still passed (`h(v)`: 18.6 times the
    // instructions, 15.3 times the bytes); at 1,000 and 8,000 the same copy takes 38.4 and
    // 32.4 times, and the code without it 8.0 and 8.0 (ISSUE1-passby-scale).
    let defs = "h(positional x) = if x is #a { \"a\" } else { trim(x) };\n\
                ap(positional f, positional v) = f(v);\n";
    let calls = |n: usize, call: &str| {
        let body: String = (0..n).map(|i| format!("c{i} = {call}; ")).collect();
        format!(
            "{defs}g(positional k) = {{ v = if k == 1 {{ #a }} else {{ if k == 2 {{ #b }} else {{ \"s\" }} }}; {body}c0 }};\n"
        )
    };
    for call in ["h(v)", "ap((positional y) -> trim(y), v)"] {
        let (i, _) = info(&calls(3, call));
        assert!(i.errors.is_empty(), "{call}: {:?}", i.errors);
        assert_eq!(i.passes.len(), 3, "{call}");
        let units = resolved(1000, |n| calls(n, call));
        scaling::check(
            &format!("one function calling `{call}` n times"),
            1000,
            |n| {
                let info = units[&n].check();
                assert!(info.errors.is_empty(), "{:?}", info.errors);
                assert_eq!(info.passes.len(), n, "{call}");
            },
        );
    }
}

/// A function of `n` parameters declared `String`, and one call of it whose arguments are
/// `args(i)`; `v` may be a string, `#a` or `#b`.
fn one_call_of_many_arguments(n: usize, args: impl Fn(usize) -> &'static str) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("positional x{i}: String")).collect();
    let args: Vec<&str> = (0..n).map(args).collect();
    format!(
        "h({}) = x0;\n\
         g(positional k) = {{ v = if k == 1 {{ #a }} else {{ if k == 2 {{ #b }} else {{ \"s\" }} }}; h({}) }};\n",
        params.join(", "),
        args.join(", ")
    )
}

#[test]
fn one_call_passing_the_atoms_of_many_arguments_by_scales() {
    // No parameter takes an atom, so each argument `v` passes `#a` and `#b` by. `Ck::pass_at`
    // copied the call's list of entries for each such argument and searched it, so one call of
    // n arguments cost n^2 (PASS-at-args); the entries are now a map by argument span.
    let passed = |text: &str| {
        let (i, _) = info(text);
        assert!(i.errors.is_empty(), "{:?}", i.errors);
        i.passes.values().map(|at| at.len()).sum::<usize>()
    };
    assert_eq!(passed(&one_call_of_many_arguments(3, |_| "v")), 3);
    // An argument with no atom passes nothing by.
    let some = one_call_of_many_arguments(5, |i| if i % 2 == 0 { "v" } else { "\"s\"" });
    assert_eq!(passed(&some), 3);
    // A call with no arguments passes nothing by, and records no entry.
    let (i, _) = info("h() = \"s\";\ng(positional k) = h();\n");
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    assert!(i.passes.is_empty());
    let units = resolved(1000, |n| one_call_of_many_arguments(n, |_| "v"));
    scaling::check(
        "one call of n arguments that each pass atoms by",
        1000,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
            assert_eq!(info.passes.len(), 1);
            assert_eq!(info.passes.values().map(|at| at.len()).sum::<usize>(), n);
        },
    );
}

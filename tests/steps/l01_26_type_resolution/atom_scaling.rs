//! The checker at the rule of low complexity (DESIGN.md Part G), on the loose atoms of a
//! parameter: tested, bound to names, handled by an `else`, passed on through calls and
//! passed by at a call (rule 6 of sec:type_resolution). Moved from `scaling` so that each
//! module runs in well under 60 s one test at a time. The benchmarks over these programs are
//! in `bench::atom_scaling`; the tests here check a small instance of each.

use zed_kernel::types::Type as KType;
use zedc::check::ty::Ty;

use super::{info, sig_of};

/// A function whose undeclared parameter `line` is tested against `n` atoms, each test bound
/// to a name, then trimmed.
pub(super) fn tests_of_atoms(n: usize) -> String {
    let tests: String = (0..n).map(|i| format!("b{i} = line is #a{i}; ")).collect();
    format!("r(positional line) = {{ {tests}trim(line) }};\n")
}

#[test]
fn a_parameter_tested_against_atoms_takes_them() {
    // A small instance of the benchmark
    // `bench::atom_scaling::a_parameter_tested_against_many_atoms_scales`.
    let (i, _) = info(&tests_of_atoms(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    // The atoms `trim` passes by reach the result, so the second arrow takes them; the first,
    // for a parameter with none, gives none.
    let arrows = i.sigs.values().next().unwrap().expand();
    assert_eq!(arrows.len(), 2);
    assert!(arrows[0].params[0].atoms().is_empty());
    assert!(!arrows[1].params[0].atoms().is_empty());
}

/// A function whose undeclared parameter `line` is bound to `n` names in a chain, each below
/// the one it reads (DESIGN.md sec:lexical), each tested against an atom of its own, the last
/// trimmed.
pub(super) fn chain_of_names(n: usize) -> String {
    let names: String = (1..n)
        .map(|i| format!("s{i} = s{}; b{i} = s{i} is #a{i}; ", i - 1))
        .collect();
    format!(
        "r(positional line) = {{ s0 = line; b0 = s0 is #a0; {names}trim(s{}) }};\n",
        n - 1
    )
}

#[test]
fn a_parameter_bound_to_a_chain_of_names_takes_each_name_s_atom() {
    // A small instance of the benchmark
    // `bench::atom_scaling::a_parameter_bound_to_a_chain_of_names_scales`.
    let (i, _) = info(&chain_of_names(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    let a = i.sigs.values().next().unwrap().expand().pop().unwrap();
    for k in 0..3 {
        let atom = Ty::set(KType::atom(&format!("a{k}")));
        assert!(atom.subtype(&a.params[0]), "{}", a.params[0]);
    }
}

/// A function whose undeclared parameter `line` has its loose atoms handled by an `else`, and
/// whose result is `line` trimmed after a chain of `n` names, each the one before it or an
/// atom of its own: the atoms of the chain reach the result from elsewhere than `line`.
pub(super) fn chain_of_own_atoms(n: usize) -> String {
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
fn a_chain_of_atoms_from_elsewhere_than_the_parameter_reaches_the_first_arrow() {
    // A small instance of the benchmark
    // `bench::atom_scaling::a_chain_of_atoms_from_elsewhere_than_the_parameter_scales`.
    // The first arrow, for a `line` with no atom, gives the chain's atoms and not `line`'s.
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
}

/// `n` functions, each handling the atoms of its undeclared parameter `x` with an `else` and
/// passing `x` on to the one before it, the first trimming `x` or giving "empty".
pub(super) fn chain_of_handlers(n: usize) -> String {
    chain_of_handlers_calling(n, |i| format!("h{}(x)", i - 1))
}

/// [`chain_of_handlers`], each function calling the one before it as `call(i)` writes it.
pub(super) fn chain_of_handlers_calling(n: usize, call: impl Fn(usize) -> String) -> String {
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
fn a_chain_of_functions_passing_a_handled_parameter_on_gives_no_atom_on_the_first_arrow() {
    // A small instance of the benchmark
    // `bench::atom_scaling::a_chain_of_functions_passing_a_handled_parameter_on_scales`.
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
}

#[test]
fn a_chain_of_functions_passing_a_handled_parameter_on_as_a_receiver_gives_no_atom_on_the_first_arrow()
 {
    // A small instance of the benchmark
    // `bench::atom_scaling::a_chain_of_functions_passing_a_handled_parameter_on_as_a_receiver_scales`.
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
}

/// `r`, which handles the atoms of its parameter, `ap`, which applies a function, and `g`,
/// which handles the atoms of its parameter `x` and calls `r` on it `n` times as `call`
/// writes the call.
pub(super) fn handled_calls(n: usize, call: &str) -> String {
    let r = "r(positional line) = if (line else \"\") == \"\" { \"empty\" } else { trim(line) };\n\
             ap(positional f, positional v) = f(v);\n";
    let body: String = (0..n).map(|i| format!("a{i} = {call}; ")).collect();
    format!("{r}g(positional x) = {{ d = x else \"\"; {body}a0 }};\n")
}

#[test]
fn calls_passing_a_handled_parameter_on_give_no_atom_on_the_first_arrow() {
    // A small instance of the benchmarks
    // `bench::atom_scaling::many_calls_passing_a_handled_parameter_on_scale_*`.
    // One function calls `r` n times on its handled parameter, as `r(x)`, `x.r()`, `x.r`,
    // through the higher-order `ap` and through a computed callee, and passes `x` to a lambda
    // through `ap`, whose atoms then pass by at the call of `ap`; each call takes `r`'s first
    // arrow from outside, so `g`'s first arrow gives a `String` alone. Each call whose
    // argument holds a loose atom is applied once more, on the atoms from outside alone.
    for call in [
        "r(x)",
        "x.r()",
        "x.r",
        "ap(r, x)",
        "(if true { r } else { r })(x)",
        "ap((positional y) -> trim(y), x)",
    ] {
        let first = sig_of(&handled_calls(3, call), "g").expand()[0]
            .result
            .clone();
        assert!(first.atoms().is_empty(), "{call}: {first}");
    }
}

/// `r`, which handles the atoms of its parameter, and `g`, which handles the atoms of its
/// parameter `x` and gives `x.r.r` … `.r`, `n` deep.
pub(super) fn method_chain(n: usize) -> String {
    let r = "r(positional line) = if (line else \"\") == \"\" { \"empty\" } else { trim(line) };\n";
    format!(
        "{r}g(positional x) = {{ d = x else \"\"; x{} }};\n",
        ".r".repeat(n)
    )
}

#[test]
fn a_chain_of_method_calls_without_parentheses_gives_no_atom_on_the_first_arrow() {
    // A small instance of the benchmark
    // `bench::atom_scaling::a_chain_of_method_calls_without_parentheses_scales`.
    let first = sig_of(&method_chain(3), "g").expand()[0].result.clone();
    assert!(first.atoms().is_empty(), "{first}");
}

/// `n` functions, each testing its undeclared parameter `x` against an atom of its own and
/// passing `x` on to the one before it, and a function calling the last on a value that may
/// be a string, the first function's atom or another.
pub(super) fn chain_of_atom_tests(n: usize) -> String {
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
fn a_chain_of_functions_each_testing_an_atom_of_its_own_is_accepted() {
    // A small instance of the benchmark
    // `bench::atom_scaling::a_chain_of_functions_each_testing_an_atom_of_its_own_scales`.
    // Each `h{i}` takes `#a{i}` alone, so its call of the one before it, which omits that atom,
    // passes it by; the call in `g` passes `#a0` and `#b` by, which no arrow of the last takes,
    // and gives the string to its first arrow.
    let (i, _) = info(&chain_of_atom_tests(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
}

/// `h`, which takes `#a` and omits `#b`, `ap`, which applies a function, and `g`, which calls
/// `call` `n` times on a value `v` that may be a string, `#a` or `#b`.
pub(super) fn passing_calls(n: usize, call: &str) -> String {
    let defs = "h(positional x) = if x is #a { \"a\" } else { trim(x) };\n\
                ap(positional f, positional v) = f(v);\n";
    let body: String = (0..n).map(|i| format!("c{i} = {call}; ")).collect();
    format!(
        "{defs}g(positional k) = {{ v = if k == 1 {{ #a }} else {{ if k == 2 {{ #b }} else {{ \"s\" }} }}; {body}c0 }};\n"
    )
}

#[test]
fn calls_passing_some_atoms_of_their_argument_by_record_one_pass_each() {
    // A small instance of the benchmarks
    // `bench::atom_scaling::many_calls_passing_some_atoms_of_their_argument_by_scale_*`.
    // `v` may be a string, `#a` or `#b`. `h` takes `#a` and omits `#b`, so each call `h(v)`
    // passes `#b` by and gives `#a` to the arrow that takes it; the lambda takes no atom, so
    // each call of `ap` passes both by, at that call, whose argument gave them.
    for call in ["h(v)", "ap((positional y) -> trim(y), v)"] {
        let (i, _) = info(&passing_calls(3, call));
        assert!(i.errors.is_empty(), "{call}: {:?}", i.errors);
        assert_eq!(i.passes.len(), 3, "{call}");
    }
}

/// A function of `n` parameters declared `String`, and one call of it whose arguments are
/// `args(i)`; `v` may be a string, `#a` or `#b`.
pub(super) fn one_call_of_many_arguments(n: usize, args: impl Fn(usize) -> &'static str) -> String {
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
fn one_call_passes_the_atoms_of_each_argument_by() {
    // A small instance of the benchmark
    // `bench::atom_scaling::one_call_passing_the_atoms_of_many_arguments_by_scales`.
    // No parameter takes an atom, so each argument `v` passes `#a` and `#b` by.
    let passed = |text: &str| {
        let (i, _) = info(text);
        assert!(i.errors.is_empty(), "{:?}", i.errors);
        assert!(i.passes.len() <= 1);
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
}

/// A function whose undeclared parameter `line` is trimmed through a chain of `n` names, each
/// bound to the one before it trimmed and written below it, each tested against an atom of its
/// own: every atom passes out of the chain's trims back to `line` (the author's Q5).
pub(super) fn chain_of_computed_names(n: usize) -> String {
    let names: String = (1..n)
        .map(|i| format!("s{i} = trim(s{}); b{i} = s{i} is #a{i}; ", i - 1))
        .collect();
    format!(
        "r(positional line) = {{ s0 = trim(line); b0 = s0 is #a0; {names}s{} else \"\" }};\n",
        n - 1
    )
}

#[test]
fn a_parameter_trimmed_through_a_chain_of_names_takes_each_name_s_atom() {
    // A small instance of the benchmark
    // `bench::atom_scaling::a_parameter_trimmed_through_a_chain_of_names_scales`.
    let (i, _) = info(&chain_of_computed_names(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    let a = i.sigs.values().next().unwrap().expand().pop().unwrap();
    for k in 0..3 {
        let atom = Ty::set(KType::atom(&format!("a{k}")));
        assert!(atom.subtype(&a.params[0]), "{}", a.params[0]);
    }
}

/// A function whose undeclared parameter `line` is trimmed inside `n` nested `else`s, each on
/// an atom of its own: the inner region passes on to each one around it.
pub(super) fn nested_handlers(n: usize) -> String {
    let open = "(".repeat(n);
    let handlers: String = (0..n).map(|i| format!(" else #a{i} -> \"{i}\")")).collect();
    format!("r(positional line) = {open}trim(line){handlers};\n")
}

#[test]
fn a_parameter_inside_nested_handlers_takes_each_handler_s_atom() {
    // A small instance of the benchmark
    // `bench::atom_scaling::a_parameter_inside_many_nested_handlers_scales`.
    let (i, _) = info(&nested_handlers(3));
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    let a = i.sigs.values().next().unwrap().expand().pop().unwrap();
    for k in 0..3 {
        let atom = Ty::set(KType::atom(&format!("a{k}")));
        assert!(atom.subtype(&a.params[0]), "{}", a.params[0]);
    }
}

/// A function whose parameter of any value is narrowed `n` times in a chain, each `else`
/// narrowing the value the one before left, the last added to `1`.
pub(super) fn chain_of_elses(n: usize) -> String {
    let elses: String = (1..n)
        .map(|i| format!("d{i} = d{} else {i}; ", i - 1))
        .collect();
    format!(
        "r(positional x) = {{ d0 = x else 0; {elses}d{} + 1 }};\n",
        n - 1
    )
}

/// A function testing its parameter with `==` against `n` atoms in turn, nested `else if`.
pub(super) fn chain_of_equalities(n: usize) -> String {
    let tests: String = (0..n)
        .map(|i| format!("if x == #a{i} {{ {i} }} else "))
        .collect();
    format!("r(positional x) = {tests}{{ x + 1 }};\n")
}

/// `n` functions, each handling the key it reads with beside the read, and `main` calling
/// each once.
pub(super) fn keys_handled(n: usize) -> String {
    let mut src: String = (0..n)
        .map(|i| format!("r{i}(args, k) {{ d = k else 0; return args[k] else \"\"; }}\n"))
        .collect();
    src.push_str("main(m: MainArgs) {\n");
    for i in 0..n {
        src.push_str(&format!("  a{i} = r{i}(args: m.args, k: {});\n", i + 1));
    }
    src.push_str("  m.stdout <- a0;\n}\n");
    src
}

#[test]
fn chains_of_tests_that_leave_values_of_their_own_are_accepted() {
    // A small instance of the benchmarks
    // `bench::atom_scaling::chains_of_tests_that_leave_values_of_their_own_scale_*`.
    // Each `else` and each failed `==` on a class that may still take other values leaves a
    // class of its own, joined with the class it tests where either takes a carrier. The key
    // of `args[k]` is followed as an argument is.
    for (what, text, want) in [
        (
            "a chain of n elses",
            chain_of_elses as fn(usize) -> String,
            Some("int | #_ -> int"),
        ),
        ("a chain of n equalities", chain_of_equalities, None),
        ("n functions handling their key", keys_handled, None),
    ] {
        let (i, _) = info(&text(3));
        assert!(i.errors.is_empty(), "{what}: {:?}", i.errors);
        if let Some(want) = want {
            assert_eq!(sig_of(&text(3), "r").to_string(), want, "{what}");
        }
    }
}

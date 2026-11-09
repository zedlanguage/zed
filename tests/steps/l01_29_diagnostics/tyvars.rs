//! A printed signature writes a type variable only with its bound of carriers (DESIGN.md L1.26,
//! sec:diagnostics "Printed types are syntax"): a parameter whose uses allow values other than
//! carriers, and the result of a use the call binds, are printed `_`, the type of every value,
//! so the text a message shows can be written back as a parameter's type (PRINT-tyvars).

use std::sync::Arc;

use zed_tests::scaling;
use zedc::check::read::parse_type;
use zedc::check::ty::{Arrow, Sig, Ty};

use super::rejected;
use zed_tests::step_helpers::l01_26_type_resolution::sig_of as sig;

/// The signature the rejection of `text` shows for the function it says is declared there.
fn declared(text: &str) -> String {
    let out = rejected(text);
    let (_, rest) = out
        .split_once("is declared here, `")
        .unwrap_or_else(|| panic!("no declaration shown:\n{out}"));
    rest[..rest.find("`\n").expect("the end of the signature")].into()
}

/// That `text` is type syntax: the parser and the resolver read it with nothing undefined
/// (`parse_type`), and as a parameter's written type the whole compiler refuses nothing in it
/// but `_` (InferType), whose layer L10 is not yet built.
fn writes_back(text: &str) {
    parse_type(text).unwrap_or_else(|why| panic!("{why}"));
    let src = format!("u(positional v: {text}) = 1;\nm(positional n: int) = u();\n");
    let out = rejected(&src);
    let errors: Vec<&str> = out
        .lines()
        .filter(|l| l.split(": ").next().is_some_and(|p| p.contains(':')))
        .collect();
    let only_the_layer = !errors.is_empty()
        && errors
            .iter()
            .all(|l| l.ends_with(zed_tests::not_yet!("the wildcard type `_`")));
    assert!(
        out.starts_with("2:24: this call of `u` gives no value to its parameter `v`")
            || only_the_layer,
        "`{text}` as a written type:\n{out}"
    );
}

#[test]
fn a_parameter_any_value_fits_is_printed_as_every_value() {
    // The finding: `(T) -> int` was printed, and `T` is no type a program can write.
    let shown = declared("h(positional p) = p[0] + int(1);\nm(positional n: int) = h(\"a\");\n");
    assert_eq!(shown, "(_) -> int");
    writes_back(&shown);
    // The variable is still the signature's own, which each call binds: the need of `p[0]` is
    // checked again at the call.
    let s = sig("h(positional p) = p[0] + int(1);\n", "h");
    assert_eq!(s.own.len(), 1);
    assert_eq!(s.needs.len(), 1);
    assert_eq!(s.to_string(), "(_) -> int");
}

#[test]
fn a_variable_only_in_the_result_is_printed_as_every_value() {
    // `fn(1)` gives what the call binds: a variable of the result alone.
    let shown = declared("n(positional fn) = fn(1);\nm(positional k: int) = n(k);\n");
    assert_eq!(shown, "(_) -> _");
    writes_back(&shown);
    let s = sig("first(p) = p[0];\n", "first");
    assert_eq!(s.to_string(), "(p: _) -> _");
    let (param, result) = (&s.arrows[0].params[0], &s.arrows[0].result);
    assert_eq!(param.vars.len(), 1);
    assert_eq!(result.vars.len(), 1);
    assert_ne!(
        param.vars, result.vars,
        "the result is the need's own variable"
    );
}

#[test]
fn several_variables_each_print_as_every_value_and_the_bounded_one_by_name() {
    // `x * y` bounds one variable by the numeric carriers; `z` is any value.
    let src = "f(positional x, positional y, positional z) = (x * y, z);\n";
    let s = sig(src, "f");
    assert_eq!(
        s.to_string(),
        "(T, T, _) -> (T, _) for T in int | f64 | rat"
    );
    writes_back(&s.to_string());
    // Two variables any value fits stay two in the signature, though both print `_`.
    let s = sig("pair(a, b) = (a, b);\n", "pair");
    assert_eq!(s.to_string(), "(a: _, b: _) -> (_, _)");
    assert_ne!(s.arrows[0].params[0], s.arrows[0].params[1]);
    assert_eq!(
        s.arrows[0].result,
        Ty::tuple(s.arrows[0].params.clone()),
        "the result is the pair of the parameters' variables"
    );
    writes_back(&s.to_string());
    // A union with a variable prints the variable once as `_`, beside the rest.
    let s = sig("g(r) = r else 0;\n", "g");
    assert_eq!(s.to_string(), "(r: _) -> 0 | _");
    writes_back(&s.to_string());
}

#[test]
fn a_bound_that_takes_other_values_is_printed_as_every_value() {
    // `<` also orders tuples, so `x` may be `(3, 4)`: its bound holds other values, which no
    // bounds clause can write, and the variable is `_`.
    let src = "lt(positional x) = x < (1, 2);\nmain() = lt((3, 4));\n";
    let s = sig(src, "lt");
    assert_eq!(s.to_string(), "(_) -> bool");
    assert_eq!(s.bounds.len(), 1, "the bound is still the signature's");
    writes_back(&s.to_string());
}

#[test]
fn a_bounded_variable_inside_a_function_parameter_is_printed_in_its_own_clause() {
    // The written `T` of the parameter's type and the inferred variable of `x * y` are two
    // variables: the inferred one takes the next name, so the two clauses bound different
    // names, and the inner clause closes at its parenthesis.
    let src =
        "ap(positional f: (T) -> T for T in int | rat, positional x, positional y) = x * y;\n";
    let s = sig(src, "ap");
    assert_eq!(
        s.to_string(),
        "((T) -> T for T in int | rat, U, U) -> U for U in int | f64 | rat"
    );
    writes_back(&s.to_string());
    // A higher-order parameter that is called: its type is `_`, and so is the call's result.
    let s = sig("twice(positional f, positional x) = f(f(x));\n", "twice");
    assert_eq!(s.to_string(), "(_, _) -> _");
    writes_back(&s.to_string());
}

/// The signature `(inner, T) -> T for T in int | rat` with `inner` as its first parameter's
/// type, a signature that bounds its own `T` again: a name the outer clause already bounds.
fn shadowing(inner: &str) -> Sig {
    let outer = parse_type("(int, T) -> T for T in int | rat").unwrap();
    let inner = parse_type(inner).unwrap();
    let mut s = (*outer.fns[0]).clone();
    s.arrows[0].params[0] = inner;
    s
}

#[test]
fn a_signature_that_bounds_a_name_already_bounded_around_it_takes_a_fresh_name() {
    // The checker names a signature's variables apart from those inside it, so this comes
    // only from a type built of two signatures; the resolver rejects `T` bounded twice, so the
    // printer renames the inner one.
    let text = shadowing("(T) -> T for T in int").to_string();
    assert_eq!(text, "((U) -> U for U in int, T) -> T for T in int | rat");
    writes_back(&text);
    // A fresh name avoids the inner signature's other names too: `U` is its own already.
    let text = shadowing("(T, U) -> (T, U) for T in int, U in rat").to_string();
    assert_eq!(
        text,
        "((V, U) -> (V, U) for V in int, U in rat, T) -> T for T in int | rat"
    );
    writes_back(&text);
    // An inner signature's own variable that no carriers bound is `_`, not the outer `T`.
    let mut inner = (*parse_type("(int) -> int").unwrap().fns[0]).clone();
    inner.arrows[0] = Arrow {
        params: vec![Ty::var("T".into())],
        result: Ty::var("T".into()),
    };
    inner.own.insert("T".into());
    let mut s = shadowing("(int) -> int");
    s.arrows[0].params[0] = Ty::func(Arc::new(inner));
    let text = s.to_string();
    assert_eq!(text, "((_) -> _, T) -> T for T in int | rat");
    writes_back(&text);
}

/// A function of `n` untyped parameters, the first `n / 2` multiplied together and the others
/// returned as they are: one bounded variable and `n - n / 2` that print `_`.
fn many(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let ps: Vec<String> = xs.iter().map(|x| format!("positional {x}")).collect();
    let product = xs[..n / 2].join(" * ");
    format!(
        "f({}) = ({product}, {});\n",
        ps.join(", "),
        xs[n / 2..].join(", ")
    )
}

/// `depth` signatures each nested as the first parameter of the next, each bounding its own
/// `T`: every one inside the outermost takes a fresh name.
fn nested(depth: usize) -> Ty {
    let mut t = parse_type("(T) -> T for T in int").unwrap();
    for _ in 1..depth {
        let mut s = (*parse_type("(int, T) -> T for T in int | rat").unwrap().fns[0]).clone();
        s.arrows[0].params[0] = t;
        t = Ty::func(Arc::new(s));
    }
    t
}

#[test]
fn printing_signatures_of_many_variables_scales() {
    let n = 300;
    let wide = [n, 8 * n].map(|m| (m, sig(&many(m), "f")));
    let input = |size: usize| &wide.iter().find(|(m, _)| *m == size).expect("built").1;
    let text = input(n).to_string();
    assert_eq!(text.matches('_').count(), 2 * (n - n / 2));
    assert!(text.ends_with(" for T in int | f64 | rat"), "{text}");
    scaling::check("printing a signature of n type variables", n, |size| {
        let text = input(size).to_string();
        assert_eq!(text.matches('_').count(), 2 * (size - size / 2));
    });
    let deep = [n, 8 * n].map(|m| (m, nested(m)));
    let input = |size: usize| &deep.iter().find(|(m, _)| *m == size).expect("built").1;
    let text = nested(4).to_string();
    assert_eq!(
        text,
        "((((W) -> W for W in int, V) -> V for V in int | rat, U) -> U for U in int | rat, T) -> T for T in int | rat"
    );
    writes_back(&text);
    scaling::check(
        "printing n nested signatures that bound one name",
        n,
        |size| {
            let text = input(size).to_string();
            assert_eq!(text.matches(" for ").count(), size);
        },
    );
}

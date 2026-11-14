//! A printed signature writes a type variable with its bound of carriers (DESIGN.md L1.26,
//! sec:diagnostics "Printed types are syntax"), and an unbounded one, as a parameter whose uses
//! allow values other than carriers or the result of a use the call binds, by a name where it
//! stands in two places or more and as `_`, the type of every value, where it stands once
//! (PRINT-tyvars, UNDERSCORE-print). The text a message shows reads back as the same type.

use std::sync::Arc;

use zedc::check::read::parse_type;
use zedc::check::ty::{Arrow, Sig, Ty};

use super::rejected;
use zed_tests::step_helpers::l01_26_type_resolution::sig_of as sig;

/// The signature the rejection of `text` shows for the function it says is declared there.
fn declared(text: &str) -> String {
    let out = rejected(text);
    let (_, rest) = out
        .split_once("is declared here with no type written for ")
        .unwrap_or_else(|| panic!("no declaration shown:\n{out}"));
    let (_, rest) = rest.split_once("` is `").expect("the type found");
    rest[..rest.find('`').expect("the end of the signature")].into()
}

/// That `text` is type syntax: the parser and the resolver read it with nothing undefined
/// (`parse_type`), and as a parameter's written type the whole compiler refuses nothing in it
/// but `_` (InferType) and a literal type, leaves of layer L10, which is not yet built, and the
/// names no `for` of the text bounds: a capitalized name a signature writes twice is a type
/// variable (sec:type_resolution, rule 4), which the resolver of this layer does not read yet
/// and reports as undefined.
pub(super) fn writes_back(text: &str) {
    parse_type(text).unwrap_or_else(|why| panic!("{why}"));
    let src = format!("u(positional v: {text}) = 1;\nm(positional n: int) = u();\n");
    let out = rejected(&src);
    let errors: Vec<&str> = out
        .lines()
        // An error opens at its line and column; the steps under it are indented.
        .filter(|l| !l.starts_with(' '))
        .filter(|l| l.split(": ").next().is_some_and(|p| p.contains(':')))
        .collect();
    let literal =
        |l: &str| l.contains(": the literal type `") && l.ends_with(zed_tests::not_yet!(""));
    let free = |l: &str| {
        l.split_once("The type `")
            .and_then(|(_, rest)| rest.split_once("` is not defined"))
            .is_some_and(|(name, _)| {
                name.starts_with(|c: char| c.is_ascii_uppercase())
                    && text
                        .split(|c: char| !c.is_alphanumeric())
                        .filter(|w| *w == name)
                        .count()
                        >= 2
                    && !text.contains(&format!("for {name} in"))
            })
    };
    let only_the_layer = !errors.is_empty()
        && errors.iter().all(|l| {
            l.ends_with(zed_tests::not_yet!("the wildcard type `_`")) || literal(l) || free(l)
        });
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
fn several_variables_each_print_by_name_where_they_stand_twice_and_the_bounded_one_in_its_clause() {
    // `x * y` bounds one variable by the numeric carriers; `z` is any value, and stands in a
    // parameter and in the result, so it takes the next name.
    let src = "f(positional x, positional y, positional z) = (x * y, z);\n";
    let s = sig(src, "f");
    assert_eq!(
        s.to_string(),
        "(T, T, U) -> (T, U) for T in int | f32 | f64 | rat"
    );
    writes_back(&s.to_string());
    // Two variables any value fits stay two in the signature, each named, as each stands in a
    // parameter and in the result.
    let s = sig("pair(a, b) = (a, b);\n", "pair");
    assert_eq!(s.to_string(), "(a: T, b: U) -> (T, U)");
    assert_ne!(s.arrows[0].params[0], s.arrows[0].params[1]);
    assert_eq!(
        s.arrows[0].result,
        Ty::tuple(s.arrows[0].params.clone()),
        "the result is the pair of the parameters' variables"
    );
    writes_back(&s.to_string());
    // A union with a variable prints it by name beside the rest: `0 | _` would be `_`, and
    // lose the `0`. The `T` of the result is `r` without the atoms `else` removes.
    let s = sig("g(r) = r else 0;\n", "g");
    assert_eq!(s.to_string(), "(r: T) -> 0 | T");
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
        "(((T) -> T for T in int | rat), U, U) -> U for U in int | f32 | f64 | rat"
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
    assert_eq!(text, "(((U) -> U for U in int), T) -> T for T in int | rat");
    writes_back(&text);
    // A fresh name avoids the inner signature's other names too: `U` is its own already.
    let text = shadowing("(T, U) -> (T, U) for T in int, U in rat").to_string();
    assert_eq!(
        text,
        "(((V, U) -> (V, U) for V in int, U in rat), T) -> T for T in int | rat"
    );
    writes_back(&text);
    // An inner signature's own variable that no carriers bound, standing twice, is named apart
    // from the outer `T`.
    let mut inner = (*parse_type("(int) -> int").unwrap().fns[0]).clone();
    inner.arrows[0] = Arrow {
        params: vec![Ty::var("T".into())],
        result: Ty::var("T".into()),
    };
    inner.own.insert("T".into());
    let mut s = shadowing("(int) -> int");
    s.arrows[0].params[0] = Ty::func(Arc::new(inner));
    let text = s.to_string();
    assert_eq!(text, "((U) -> U, T) -> T for T in int | rat");
    writes_back(&text);
}

/// A function of `n` untyped parameters, the first `n / 2` multiplied together and the others
/// returned as they are: one bounded variable and `n - n / 2` that print `_`.
pub(super) fn many(n: usize) -> String {
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
pub(super) fn nested(depth: usize) -> Ty {
    let mut t = parse_type("(T) -> T for T in int").unwrap();
    for _ in 1..depth {
        let mut s = (*parse_type("(int, T) -> T for T in int | rat").unwrap().fns[0]).clone();
        s.arrows[0].params[0] = t;
        t = Ty::func(Arc::new(s));
    }
    t
}

/// The number of distinct capitalized words of `text`: the names of its type variables.
fn names(text: &str) -> usize {
    let words: std::collections::HashSet<&str> = text
        .split(|c: char| !c.is_alphanumeric())
        .filter(|w| w.starts_with(|c: char| c.is_ascii_uppercase()))
        .collect();
    words.len()
}

/// `sig`, that of [`many`]`(n)`, prints the bounded `T` and a name for each of the `n - n / 2`
/// variables of the second half, and no `_`.
pub(super) fn a_signature_of_many_variables_printed(sig: &Sig, n: usize) {
    let text = sig.to_string();
    assert!(!text.contains('_'), "{text}");
    assert_eq!(names(&text), 1 + (n - n / 2), "{text}");
    assert!(text.ends_with(" for T in int | f32 | f64 | rat"), "{text}");
}

/// `ty`, [`nested`]`(depth)`, prints one clause for each of its `depth` signatures.
pub(super) fn nested_signatures_printed(ty: &Ty, depth: usize) {
    let text = ty.to_string();
    assert_eq!(text.matches(" for ").count(), depth, "{text}");
}

/// Signatures of 4, 6 and 11 variables, and 1, 2 and 4 nested signatures
/// (`bench::tyvars` times 300 and 2400 of each).
#[test]
fn printing_signatures_of_many_variables() {
    // The variables of the second half each stand in a parameter and in the result, so each
    // takes a name of its own after the bounded `T`.
    assert_eq!(
        sig(&many(4), "f").to_string(),
        "(T, T, U, V) -> (T, U, V) for T in int | f32 | f64 | rat"
    );
    for n in [4, 6, 11] {
        a_signature_of_many_variables_printed(&sig(&many(n), "f"), n);
    }
    let text = nested(4).to_string();
    assert_eq!(
        text,
        "(((((((W) -> W for W in int), V) -> V for V in int | rat), U) -> U for U in int | rat), T) -> T for T in int | rat"
    );
    writes_back(&text);
    for depth in [1, 2, 4] {
        nested_signatures_printed(&nested(depth), depth);
    }
}

// UNDERSCORE-print (DESIGN.md sec:diagnostics, "The type of a declaration in a message"): a
// variable of the checker that stands in two places or more of one printed type is written by a
// capitalized name, given in the order the variables first stand in the text and skipping the
// names in scope; one that stands once is `_`.

#[test]
fn a_variable_that_stands_twice_is_named() {
    let s = sig("id(x) = x;\n", "id");
    assert_eq!(s.to_string(), "(x: T) -> T");
    assert_eq!(s.arrows[0].params[0], s.arrows[0].result);
    writes_back(&s.to_string());
}

#[test]
fn two_variables_take_names_in_the_order_they_first_stand() {
    // `a` stands first, in the first parameter, so it is `T`, though the result gives `b` first.
    let s = sig("swap(positional a, positional b) = (b, a);\n", "swap");
    assert_eq!(s.to_string(), "(T, U) -> (U, T)");
    writes_back(&s.to_string());
}

#[test]
fn a_variable_that_stands_once_is_every_value() {
    // `x` stands once, `y` twice: only `y` takes a name, and it takes the first.
    let s = sig("k(positional x, positional y) = y;\n", "k");
    assert_eq!(s.to_string(), "(_, T) -> T");
    assert_ne!(s.arrows[0].params[0], s.arrows[0].params[1]);
    writes_back(&s.to_string());
}

#[test]
fn every_value_in_a_union_absorbs_the_other_members() {
    // The result of `f(0)` is a variable that stands once, so it prints `_`, and `int | _` is
    // `_`: every value holds `int`.
    let src = "g(positional c, positional f) = if c { int(1) } else { f(0) };\n";
    let s = sig(src, "g");
    assert_eq!(s.arrows[0].result.vars.len(), 1);
    assert_eq!(s.to_string(), "(bool, _) -> _");
    writes_back(&s.to_string());
    // Written, `int | f64 | _` is read as a union with a variable that stands once.
    let t = parse_type("(int | f64 | _) -> int").unwrap();
    assert_eq!(t.to_string(), "(_) -> int");
    // A variable that stands twice is no `_`, and absorbs nothing.
    let t = parse_type("(T, int | f64 | T) -> T").unwrap();
    assert_eq!(t.to_string(), "(T, int | f64 | T) -> T");
}

#[test]
fn the_names_skip_a_name_the_program_binds() {
    // The file binds `T`, a value, so in a message the variable that stands twice takes `U`.
    let src = "T = 5;\nh(positional a, positional b) = (b, b);\n";
    let shown = declared(&format!("{src}m(positional n: int) = h(n);\n"));
    assert_eq!(shown, "(_, U) -> (U, U)");
    // With no `T` bound, the first name is `T`.
    let shown = declared("h(positional a, positional b) = (b, b);\nm(positional n: int) = h(n);\n");
    assert_eq!(shown, "(_, T) -> (T, T)");
    // A lambda's parameter named `T` is bound by the file too.
    let shown = declared("g(positional a) = (T) -> (b) -> (c) -> a;\nm = g + 1;\n");
    assert_eq!(shown, "(U) -> (_) -> (_) -> (_) -> U");
    // A signature printed outside a message has no program around it, so its names start at
    // `T` whatever the file binds.
    assert_eq!(sig(src, "h").to_string(), "(_, T) -> (T, T)");
}

#[test]
fn a_printed_type_with_names_reads_back_as_itself() {
    // Each text reads back as a type that prints as the same text: the names are variables of
    // the signature, and stand in the same places.
    for src in [
        "id(x) = x;\n",
        "swap(positional a, positional b) = (b, a);\n",
        "g(r) = r else 0;\n",
        "pick(positional c, positional a, positional b) = if c { a } else { b };\n",
        "f(positional x, positional y, positional z) = (x * y, z);\n",
        "g(positional a) = (b) -> (c) -> (a, b, c);\n",
    ] {
        let name = &src[..src.find('(').expect("a declaration")];
        let printed = sig(src, name).to_string();
        let t = parse_type(&printed).unwrap_or_else(|e| panic!("{printed}: {e}"));
        assert_eq!(t.fns.len(), 1, "{printed}");
        assert_eq!(t.to_string(), printed, "{src}");
        // The read type has as many variables of its own as the text has names.
        let read = &t.fns[0];
        assert!(!read.own.is_empty(), "{printed}");
    }
}

/// `f(positional x0, …) = (x0, …);`: `n` variables, each standing in a parameter and in the
/// result.
pub(super) fn each_twice(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let ps: Vec<String> = xs.iter().map(|x| format!("positional {x}")).collect();
    format!("f({}) = ({});\n", ps.join(", "), xs.join(", "))
}

/// `sig`, that of [`each_twice`]`(n)` for `n` of 5 or more, names every variable, the last
/// `T<n>`.
pub(super) fn variables_that_each_stand_twice_named(sig: &Sig, n: usize) {
    let text = sig.to_string();
    assert!(!text.contains('_'), "{text}");
    assert!(text.ends_with(&format!("T{n})")), "{text}");
}

/// 5, 6 and 12 variables that each stand twice (`bench::tyvars` times 1000 and 8000).
#[test]
fn naming_many_variables_that_each_stand_twice() {
    assert_eq!(
        sig(&each_twice(5), "f").to_string(),
        "(T, U, V, W, T5) -> (T, U, V, W, T5)"
    );
    for n in [5, 6, 12] {
        variables_that_each_stand_twice_named(&sig(&each_twice(n), "f"), n);
    }
}

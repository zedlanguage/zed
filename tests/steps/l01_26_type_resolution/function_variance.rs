//! Function types and the variance faults of Dart (author, 2026-11-15, P286: "contravariance is
//! the root of numerous very hard-to-understand type errors in Dart, and some runtime errors.
//! Make sure Zed is not going to fall to the same problems").
//!
//! Dart treats a generic type as covariant even where its type parameter is a function's
//! parameter type, so `C<num> c = C<int>((i) => i.isEven); c.fun(10);` passes the checker and
//! fails at run time (dart.dev, lint `unsafe_variance`); `covariant` on an override and an
//! implicit downcast from `dynamic` move a check to run time the same way. In Zed a plain
//! function type `K -> V` is exact, so its domain neither widens nor narrows (DESIGN.md
//! sec:type_language, "Morphism types carry two domain bounds"); only a partial type `K ->? V`
//! varies, taking any function whose domain lies within `K`. A container or struct holding a
//! function inherits that rule, which makes it invariant in the function's domain, as Dart's
//! lint asks for and cannot enforce. Each case below is a verdict only: the messages for the
//! sound programs that exact domains reject are row MSG-fn-domain-wider-repair.

use super::type_errors;

/// `src` is accepted.
fn accepted(src: &str) {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
}

/// `src` gives exactly one error.
fn rejected(src: &str) {
    assert_eq!(type_errors(src).len(), 1, "{src}: {:?}", type_errors(src));
}

/// A function with a narrower domain where a wider one is wanted would be called outside its
/// domain, the run-time fault of Dart's `covariant`: rejected, at any depth.
#[test]
fn a_narrower_domain_is_rejected_where_a_wider_one_is_called() {
    rejected(
        "small(x: int) = 1;\napply(f: (x: int | f64) -> int) = f(x: 3);\nr = apply(f: small);\n",
    );
    rejected("tag(x: #a) = 1;\napply(f: (x: #a | #b) -> int) = f(x: #b);\nr = apply(f: tag);\n");
    rejected(
        "small(x: int) = 1;\nuseWide(b: ((x: int | f64) -> int,)) = 0;\nr = useWide(b: (small,));\n",
    );
    // An empty domain is not a subtype of an exact one: the bottom-type fault of Dart.
    rejected("none(x: Never) = 1;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: none);\n");
}

/// A wider result than the slot's is rejected; a narrower one is accepted.
#[test]
fn results_are_covariant() {
    accepted("one(x: int) = 1;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: one);\n");
    rejected(
        "both(x: int) = rat(x) / 2;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: both);\n",
    );
}

/// A partial slot `K ->? V` takes a function whose domain lies within `K`, the empty one too:
/// its caller handles `#notFound`, so no call reaches a value outside the domain.
#[test]
fn a_partial_slot_takes_a_narrower_domain() {
    accepted(
        "small(x: int) = 1;\napply(f: (x: int | f64) ->? int) = f(x: 3) else 0;\nr = apply(f: small);\n",
    );
    accepted(
        "none(x: Never) = 1;\napply(f: (x: int) ->? int) = f(x: 3) else 0;\nr = apply(f: none);\n",
    );
}

/// The value of `name` in `src`, from the reference evaluator and from native code, which
/// agree.
fn runs_to(src: &str, name: &str, want: &str) {
    use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};
    use zed_tests::step_helpers::l01_36_cranelift::{kernel, native};
    let u = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let t = with_prelude(
        u.get(name)
            .unwrap_or_else(|| panic!("no definition `{name}`")),
    );
    let k = kernel(&t).map(|v| v.to_string());
    let n = native(&t).map(|o| o.value.to_string());
    assert_eq!(k, Ok(want.to_string()), "reference evaluator: {src}");
    assert_eq!(n, Ok(want.to_string()), "native code: {src}");
}

/// A call through a partial slot of a value outside the domain of the function passed misses
/// with `#notFound`, which the caller handles (DESIGN.md sec:type_language, "Morphism types
/// carry two domain bounds": a key in `U` only yields `V | #notFound`); within the domain the
/// call is the function's. The empty domain misses on every call.
#[test]
fn a_call_through_a_partial_slot_outside_the_domain_misses() {
    let apply = |arg: &str| {
        format!(
            "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: {arg}) else 0;\na = apply(f: small);\n"
        )
    };
    runs_to(&apply("2.5"), "a", "0");
    runs_to(&apply("3"), "a", "4");
    runs_to(
        "none(x: Never) = 1;\napply(f: (x: int) ->? int) = f(x: 3) else 0;\na = apply(f: none);\n",
        "a",
        "0",
    );
    // The miss is the atom `#notFound`, which a handler names.
    runs_to(
        "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: 2.5) else #notFound -> 7;\na = apply(f: small);\n",
        "a",
        "7",
    );
    // A parameter of exact function type passed on to a partial slot: its exact domain is
    // the one the function passed to it has.
    let passed = |arg: &str| {
        format!(
            "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: {arg}) else 5;\npass(g: (x: int) -> int) = apply(f: g);\na = pass(g: small);\n"
        )
    };
    runs_to(&passed("2.5"), "a", "5");
    runs_to(&passed("3"), "a", "4");
    // Named parameters in another order: the test reads each argument at its own parameter.
    let reordered = |arg: &str| {
        format!(
            "sub(b: int, a: int) = a - b;\napply(f: (a: int | f64, b: int) ->? int) = f(a: {arg}, b: 1) else 0;\na = apply(f: sub);\n"
        )
    };
    runs_to(&reordered("2.5"), "a", "0");
    runs_to(&reordered("5"), "a", "4");
}

/// Row FAIL-fn-range-domain-partial-slot: a function whose parameter is declared with a range
/// fits a partial slot whose parameter type holds the range (`(x: int[0..=9]) -> int[0..=9] <:
/// (x: int) ->? int`), and a call through the slot outside the range misses with `#notFound`;
/// an exact slot stays refused, since it may pass any `int`.
#[test]
fn a_partial_slot_takes_a_function_on_a_narrower_range() {
    accepted(
        "small(x: int[0..<10]) = x;\nopt(f: (x: int) ->? int) = f(x: 5) else 0;\nr = opt(f: small);\n",
    );
    // The exact slot stays refused: `apply` may call `small` with 100.
    rejected(
        "small(x: int[0..<10]) = x;\napply(f: (x: int) -> int) = f(x: 100);\nr = apply(f: small);\n",
    );
    // A lambda adopts the slot's domain `int`, and its call of `small` is then refused.
    rejected(
        "small(x: int[0..<10]) = x;\nopt(f: (x: int) ->? int) = f(x: 5) else 0;\nr = opt(f: x -> small(x: x));\n",
    );
    let opt = |arg: &str| {
        format!(
            "small(x: int[0..<10]) = x;\nopt(f: (x: int) ->? int) = f(x: {arg}) else 0;\na = opt(f: small);\n"
        )
    };
    runs_to(&opt("5"), "a", "5");
    runs_to(&opt("50"), "a", "0");
    runs_to(&opt("-1"), "a", "0");
    runs_to(&opt("9"), "a", "9");
    runs_to(&opt("10"), "a", "0");
    // An open end: only the low end is tested.
    runs_to(
        "big(x: int[3..]) = x;\nopt(f: (x: int) ->? int) = f(x: 2) else 7;\na = opt(f: big);\n",
        "a",
        "7",
    );
}

/// A wider exact domain is not a narrower one, as a domain is observable (`::domain`), and not
/// within a partial slot's `K` either. These programs never fail at run time, and they are
/// rejected; a lambda written at the slot adopts its domain (sec:type_resolution, rule 2), so
/// `x -> inc(x: x)` is the repair, and `xs.map(inc)` is accepted.
#[test]
fn a_wider_domain_is_rejected_and_its_lambda_accepted() {
    rejected("inc(x: int | f64) = 1;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: inc);\n");
    rejected("tag(x: #a | #b) = 1;\napply(f: (x: #a) -> int) = f(x: #a);\nr = apply(f: tag);\n");
    rejected(
        "inc(x: int | f64) = 1;\napply(f: (x: int) ->? int) = f(x: 3) else 0;\nr = apply(f: inc);\n",
    );
    rejected(
        "inc(x: int | f64) = 1;\nuseNarrow(b: ((x: int) -> int,)) = 0;\nr = useNarrow(b: (inc,));\n",
    );
    rejected(
        "useF(g: (x: int) -> int) = g(x: 1);\nouter(h: (g: (x: int | f64) -> int) -> int) = 0;\nr = outer(h: useF);\n",
    );
    accepted(
        "inc(x: int | f64) = 1;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: x -> inc(x: x));\n",
    );
    accepted("apply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: x -> 1);\n");
    accepted("inc(x: int) = 1;\nuse(b: ((x: int) -> int,)) = 0;\nr = use(b: (inc,));\n");
    accepted("inc(x: int | f64) = 1;\nxs = [1, 2, 3];\nys = xs.map(inc);\n");
}

/// Row MSG-fn-domain-wider-repair, part (1): a function whose exact domain is wider than the
/// slot's, where the lambda that calls it on the slot's arguments fits, is refused with a
/// headline that says the domain is wider, naming each parameter, and ends with the call
/// rewritten with that lambda, as code. The lambda each repair writes is accepted (the
/// `accepted` cases), and none is offered where it would be refused too: a narrower domain,
/// and a result the slot's arrow does not take (`x -> inc(x: x)` gives `int | f64` there).
#[test]
fn a_wider_domain_says_so_and_offers_its_lambda_as_code() {
    assert_eq!(
        type_errors(
            "inc(x: int | f64) = 1;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: inc);\n"
        ),
        vec![
            "`inc` is `(x: int | f64) -> 1`, not `(x: int) -> int`: its domain is wider than \
             `(x: int) -> int`'s, `x` in `int | f64` where `(x: int) -> int` takes `int`, and a \
             function passed as `(x: int) -> int` must take exactly that domain. Try \
             `apply(f: x -> inc(x: x))` instead. [inc]"
        ]
    );
    assert_eq!(
        type_errors(
            "inc(positional a: int | f64, b: int) = 1;\napply(f: (positional p: int, b: int) -> int) = f(3, b: 4);\nr = apply(f: inc);\n"
        ),
        vec![
            "`inc` is `(int | f64, b: int) -> 1`, not `(int, b: int) -> int`: its domain is \
             wider than `(int, b: int) -> int`'s, `p` in `int | f64` where \
             `(int, b: int) -> int` takes `int`, and a function passed as \
             `(int, b: int) -> int` must take exactly that domain. Try \
             `apply(f: (p, b) -> inc(p, b: b))` instead. [inc]"
        ]
    );
    accepted(
        "inc(positional a: int | f64, b: int) = 1;\napply(f: (positional p: int, b: int) -> int) = f(3, b: 4);\nr = apply(f: (p, b) -> inc(p, b: b));\n",
    );
    for src in [
        "inc(x: int) = 1;\napply(f: (x: int | f64) -> int) = 0;\nr = apply(f: inc);\n",
        "inc(x: int | f64) = x;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: inc);\n",
    ] {
        let errors = type_errors(src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(
            !errors[0].contains("Try") && errors[0].contains("does not fit that one"),
            "{src}: {errors:?}"
        );
    }
    rejected(
        "inc(x: int | f64) = x;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: x -> inc(x: x));\n",
    );
}

/// Row MSG-fn-domain-wider-repair, part (2): a function whose parameter is declared with a
/// range, passed at an exact slot whose parameter type is wider, is refused with the carrier
/// form of part (1), the domain named narrower, and the repairs as code: the declaration on
/// the slot's parameter type, or a function of the slot's type. Only that one error: no
/// second one about a value out of range. A refusal for something else keeps its own message.
#[test]
fn a_narrower_range_domain_says_so_in_the_carrier_form() {
    let src = "small(x: int[0..<10]) = x;\napply(f: (x: int) -> int) = f(x: 100);\nr = apply(f: small);\n";
    assert_eq!(
        type_errors(src),
        vec![
            "`small` is `(x: int[0..=9]) -> int[0..=9]`, not `(x: int) -> int`: its domain is \
             narrower than `(x: int) -> int`'s, `x` in `int[0..=9]` where `(x: int) -> int` \
             passes any `int`, and a function passed as `(x: int) -> int` must take exactly \
             that domain. [small]"
        ]
    );
    let (info, _) = super::info(src);
    let repairs: Vec<&str> = (info.errors[0].notes.iter())
        .map(|n| &*n.text)
        .filter(|t| t.starts_with("repair: "))
        .collect();
    assert_eq!(
        repairs,
        vec![
            "repair: declare `small(x: int)`, which takes what `(x: int) -> int` passes",
            "repair: pass a function of type `(x: int) -> int` in place of `small`",
        ]
    );
    accepted("small(x: int) = x;\napply(f: (x: int) -> int) = f(x: 100);\nr = apply(f: small);\n");
    // Two parameters, one ranged, the slot's order differing from the declaration's.
    let two = "sub(a: int[0..=9], b: int) = a - b;\napply(f: (b: int, a: int) -> int) = f(b: 1, a: 50);\nr = apply(f: sub);\n";
    let errors = type_errors(two);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].contains("its domain is narrower")
            && errors[0].contains("`a` in `int[0..=9]` where"),
        "{errors:?}"
    );
    let (info, _) = super::info(two);
    assert!(
        (info.errors[0].notes.iter())
            .any(|n| n.text == "repair: declare `sub(a: int, b: int)`, which takes what `(b: int, a: int) -> int` passes"),
        "{:?}",
        info.errors[0].notes
    );
    // A refusal for something else as well (a result the slot does not take) keeps its own
    // message.
    let wide = "half(x: int[0..=9]) = rat(x) / 2;\napply(f: (x: int) -> int) = f(x: 3);\nr = apply(f: half);\n";
    let errors = type_errors(wide);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(!errors[0].contains("narrower"), "{errors:?}");
    // At a partial slot the range domain is accepted (FAIL-fn-range-domain-partial-slot).
    accepted(
        "small(x: int[0..<10]) = x;\napply(f: (x: int) ->? int) = f(x: 100) else 0;\nr = apply(f: small);\n",
    );
}

/// Row FAIL-fit-declared-permuted-needs: a declared function passed with its named parameters
/// in another order keeps its needs on its own parameters, so a declared range is checked on
/// the parameter it is declared on, whichever order the slot writes. `sub`'s `b` takes
/// `int[0..=9]`, and the slot passes any `int` there: refused, as with both parameters `int`.
/// Before the fix the range need read the slot's parameter at `b`'s own place, `a: bool`,
/// found no range there, and the call gave 40, outside `b`'s domain.
#[test]
fn a_reordered_function_keeps_its_ranges_on_its_own_parameters() {
    for (a, b) in [("bool", "true"), ("int", "3")] {
        let src = format!(
            "sub(a: {a}, b: int[0..=9]) = if {b} == {b} {{ b }} else {{ 0 }};\napply(f: (b: int, a: {a}) -> int) = f(b: 40, a: {b});\nr = apply(f: sub);\n"
        );
        let errors = type_errors(&src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(
            errors[0].contains("`b` in `int[0..=9]` where"),
            "{src}: {errors:?}"
        );
    }
    // Within the range at a partial slot: the call runs, outside it misses.
    let partial = |arg: &str| {
        format!(
            "sub(a: bool, b: int[0..=9]) = if a {{ b }} else {{ 0 }};\napply(f: (b: int, a: bool) ->? int) = f(b: {arg}, a: true) else 7;\nr = apply(f: sub);\n"
        )
    };
    runs_to(&partial("4"), "r", "4");
    runs_to(&partial("40"), "r", "7");
}

/// Row FAIL-partial-slot-nested-guard: a function of exact domain that reaches a partial slot
/// inside another value (a tuple), or as the value of any expression (a call, an `if`, the
/// result of a function passed), is rebuilt where the partial type is expected, so that a call
/// through it outside its domain misses with `#notFound`, as for a name. Before the fix each
/// of these called `small` with 2.5, and the run stopped with a bug in zedc.
#[test]
fn a_function_inside_a_value_misses_outside_its_domain() {
    let small = "small(x: int) = x + 1;\n";
    let tuple = "useWide(b: ((x: int | f64) ->? int,)) = b[0](x: K) else 9;\n";
    let apply = "apply(f: (x: int | f64) ->? int) = f(x: K) else 6;\n";
    let cases = [
        (tuple, "a = useWide(b: (small,));\n", "9"),
        (tuple, "t = (small,);\na = useWide(b: t);\n", "9"),
        (apply, "get() = small;\na = apply(f: get());\n", "6"),
        (
            apply,
            "a = apply(f: if true { small } else { small });\n",
            "6",
        ),
        (
            apply,
            "q(g: (x: int) -> int, n: int) = apply(f: if n > 0 { g } else { g });\na = q(g: small, n: 1);\n",
            "6",
        ),
        (
            "apply(f: () -> ((x: int | f64) ->? int)) = f()(x: K) else 6;\n",
            "get() = small;\na = apply(f: get);\n",
            "6",
        ),
    ];
    for (slot, rest, miss) in cases {
        let src = |k: &str| format!("{small}{}{rest}", slot.replace('K', k));
        runs_to(&src("2.5"), "a", miss);
        runs_to(&src("3"), "a", "4");
    }
}

/// Row FAIL-partial-slot-generic-pass: a function of exact domain passed through a parameter
/// whose type is a type variable to a partial slot misses with `#notFound` outside its domain,
/// as when it is passed straight to the slot: through two such parameters, beside another
/// parameter, to two partial slots, and where the body also gives the function back, whose
/// exact uses still call it. Before the fix the run called `small` with 2.5 and stopped with a
/// bug in zedc.
#[test]
fn a_function_passed_through_a_generic_parameter_misses_outside_its_domain() {
    let head = "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: K) else 6;\npass(x) = apply(f: x);\n";
    let cases = [
        ("a = pass(x: small);\n", "6", "4"),
        ("pass2(y) = pass(x: y);\na = pass2(y: small);\n", "6", "4"),
        (
            "pass2(x, y) = apply(f: x) + y;\na = pass2(x: small, y: 10);\n",
            "16",
            "14",
        ),
        (
            "apply2(f: (x: int | #b) ->? int) = f(x: 7) else 7;\npass2(x) = apply(f: x) + apply2(f: x);\na = pass2(x: small);\n",
            "14",
            "12",
        ),
        (
            "pass2(x) = (apply(f: x), x);\nb = pass2(x: small);\na = b[1](x: 3) + b[0];\n",
            "10",
            "8",
        ),
        (
            "b = (pass(x: small), pass(x: small));\na = b[1];\n",
            "6",
            "4",
        ),
        (
            "pass2(x) = { y = x; apply(f: y) };\na = pass2(x: small);\n",
            "6",
            "4",
        ),
        (
            "pass2(x) = [x].map(g -> apply(f: g))[0];\na = pass2(x: small);\n",
            "6",
            "4",
        ),
        (
            "pass2(x, y) = apply(f: if true { x } else { y });\na = pass2(x: small, y: small);\n",
            "6",
            "4",
        ),
    ];
    for (rest, miss, hit) in cases {
        let src = |k: &str| format!("{}{rest}", head.replace('K', k));
        runs_to(&src("2.5"), "a", miss);
        runs_to(&src("3"), "a", hit);
    }
}

/// Row FAIL-partial-slot-generic-pass: a function that is a component of a tuple argument, at
/// any depth, taken by index or by destructuring, is rebuilt in its place in that argument, so
/// it misses outside its domain too; a component that is a literal leaves the other untouched.
#[test]
fn a_function_in_a_component_of_a_generic_argument_misses_outside_its_domain() {
    let head = "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: K) else 6;\n";
    let cases = [
        (
            "pass(p) = apply(f: p[0]);\na = pass(p: (small, 1));\n",
            "6",
            "4",
        ),
        (
            "pass(p) = apply(f: p[0]);\nq = (small, 1);\na = pass(p: q);\n",
            "6",
            "4",
        ),
        (
            "pass(p) = { g, n = p; apply(f: g) };\na = pass(p: (small, 1));\n",
            "6",
            "4",
        ),
        (
            "pass(p) = apply(f: p[1][0]);\na = pass(p: (1, (small,)));\n",
            "6",
            "4",
        ),
        (
            "pass(p) = apply(f: p[0]) + apply(f: p[1]);\na = pass(p: (small, small));\n",
            "12",
            "8",
        ),
        (
            "pass(p) = apply(f: p[0]) + p[1];\na = pass(p: (small, 10));\n",
            "16",
            "14",
        ),
    ];
    for (rest, miss, hit) in cases {
        let src = |k: &str| format!("{}{rest}", head.replace('K', k));
        runs_to(&src("2.5"), "a", miss);
        runs_to(&src("3"), "a", hit);
    }
}

/// Row PROOF-generic-body-values-from-args, the cases of the proof at `Ck::coerce_forwarded`
/// that run: a function passed to a generic parameter reaches a partial slot by every route a
/// generic body has for a value of a type variable (a closure that captures it, a closure
/// returned, a lambda's parameter, a generic call that gives it back, a tuple built and read,
/// a partial application, a method call, a local function, a positional parameter, an `if`
/// over two arguments, the body giving it back), and each route reaches the argument the call
/// rebuilds, so each misses outside the function's domain and calls it inside. A use that
/// needs no test (an exact slot, a call of the value given back) gets the function's own
/// values.
#[test]
fn a_generic_body_passes_on_only_its_arguments_by_every_route() {
    let head = "small(x: int) = x + 1;\nbig(x: int | f64) = 1;\napply(f: (x: int | f64) ->? int) = f(x: K) else 6;\n";
    let cases = [
        // A closure that captures the argument, called in the body.
        (
            "pass(x) = { h = y -> apply(f: x); h(1) };\na = pass(x: small);\n",
            "6",
            "4",
        ),
        // A closure that captures the argument, returned and called by the caller.
        (
            "mk(x) = y -> apply(f: x);\na = mk(x: small)(1);\n",
            "6",
            "4",
        ),
        // The argument passed to a lambda's parameter.
        (
            "pass(x) = { h = y -> apply(f: y); h(x) };\na = pass(x: small);\n",
            "6",
            "4",
        ),
        // A generic call that gives back its argument, or a component of a tuple built of it.
        (
            "id(v) = v;\npass(x) = apply(f: id(v: x));\na = pass(x: small);\n",
            "6",
            "4",
        ),
        (
            "fst(p) = p[0];\npass(x) = apply(f: fst(p: (x, 1)));\na = pass(x: small);\n",
            "6",
            "4",
        ),
        (
            "k(v, g) = g(v);\npass(x) = apply(f: k(v: 1, g: z -> x));\na = pass(x: small);\n",
            "6",
            "4",
        ),
        (
            "pass(x) = apply(f: (x, 1)[0]);\na = pass(x: small);\n",
            "6",
            "4",
        ),
        // The generic function called through a lambda, a name, a partial application, a
        // method call, a positional parameter, and a parameter of another function.
        (
            "pass(x) = apply(f: x);\nh = y -> pass(x: y);\na = h(small);\n",
            "6",
            "4",
        ),
        (
            "pass(x) = apply(f: x);\nh = pass;\na = h(x: small);\n",
            "6",
            "4",
        ),
        (
            "pass(x, y) = apply(f: x) + y;\nc = pass(y: 1, ...);\na = c(x: small);\n",
            "7",
            "5",
        ),
        ("pass(x) = apply(f: x);\na = small.pass();\n", "6", "4"),
        ("pass(x) = apply(f: x);\na = small.pass;\n", "6", "4"),
        (
            "pass(positional x) = apply(f: x);\na = pass(small);\n",
            "6",
            "4",
        ),
        (
            "pass(x) = apply(f: x);\nq(g: (x: int) -> int) = pass(x: g);\na = q(g: small);\n",
            "6",
            "4",
        ),
        (
            "pass(x) = apply(f: x);\nq(g: (x: int | f64) ->? int) = pass(x: g);\na = q(g: small);\n",
            "6",
            "4",
        ),
        // A local function that captures the argument.
        (
            "pass(x) { g(y) = apply(f: x); return g(y: 1); }\na = pass(x: small);\n",
            "6",
            "4",
        ),
        // Two arguments of two variables, chosen by `if`, or each passed on.
        (
            "pass(x, y) = apply(f: if true { x } else { y });\na = pass(x: small, y: big);\n",
            "6",
            "4",
        ),
        (
            "pass(x) = apply(f: if false { small } else { x });\na = pass(x: big);\n",
            "1",
            "1",
        ),
        (
            "mk(x) = y -> apply(f: x) + apply(f: y);\na = mk(x: small)(big);\n",
            "7",
            "5",
        ),
        (
            "mk(x) = (y -> apply(f: y), x);\nb = mk(x: big);\na = b[0](small);\n",
            "6",
            "4",
        ),
        // The same function passed straight to the slot beside the call.
        (
            "pass(x) = apply(f: x);\na = pass(x: small) + apply(f: small);\n",
            "12",
            "8",
        ),
        (
            "apply2(f: (x: int | bool) ->? int) = f(x: true) else 9;\npass(x) = apply(f: x) + apply2(f: x);\na = pass(x: small);\n",
            "15",
            "13",
        ),
        // The body gives the argument back: a partial slot misses, an exact use calls it.
        (
            "pass(x) = if apply(f: x) > 0 { x } else { x };\na = apply(f: pass(x: small));\n",
            "6",
            "4",
        ),
        (
            "pass(x) = if apply(f: x) > 0 { x } else { x };\na = pass(x: small)(x: 2);\n",
            "3",
            "3",
        ),
        (
            "q(f: (x: int) -> int) = f(x: 2);\npass(x) = if apply(f: x) > 0 { x } else { x };\na = q(f: pass(x: small));\n",
            "3",
            "3",
        ),
    ];
    for (rest, miss, hit) in cases {
        let src = |k: &str| format!("{}{rest}", head.replace('K', k));
        runs_to(&src("2.5"), "a", miss);
        runs_to(&src("3"), "a", hit);
    }
}

/// Row PROOF-generic-body-values-from-args, the cases of the proof where a value of a type
/// variable does not come from a place in one argument that the call shows: a default (of the
/// argument or of a function written in the program), an entry of a family, a value with an
/// `else`, a generic function called through a parameter, a lambda inside `map`, and the
/// result of calling a parameter. Each is refused rather than run without a test of the
/// domain; before the fix of FAIL-partial-slot-generic-pass these ran `small` on 2.5.
#[test]
fn a_value_of_a_variable_from_no_argument_is_refused_for_a_partial_slot() {
    let head = "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: 2.5) else 6;\n";
    let cases = [
        "pass(x, y = x) = apply(f: y);\na = pass(x: small);\n",
        "pass(x, y = small) = apply(f: y);\na = pass(x: 1);\n",
        "pass(x) = apply(f: { 1 -> x }[1] else x);\na = pass(x: small);\n",
        "pass(x) = apply(f: x else x);\na = pass(x: small);\n",
        "pass(x) = apply(f: x);\nrun(g, v) = g(x: v);\na = run(g: pass, v: small);\n",
        "pass(x) = apply(f: x);\ntwice(g) = g(x: small);\na = twice(g: pass);\n",
        "pass(x) = apply(f: x);\na = [small].map(g -> pass(x: g))[0];\n",
        "pass(x, y) = apply(f: y(x));\na = pass(x: 1, y: n -> small);\n",
    ];
    for rest in cases {
        let src = format!("{head}{rest}");
        let errors = type_errors(&src);
        assert!(
            errors.iter().any(|e| e.contains("must give `#notFound`")
                && e.contains("is not one argument of this call, or a component of one")),
            "{src}: {errors:?}"
        );
    }
}

/// Row PROOF-generic-body-values-from-args, the cases of the proof that this zedc does not
/// compile yet: each is refused before the checker reaches the call, so no rebuilding is put
/// for it. When one of them is compiled, this test fails, and the proof at
/// `Ck::coerce_forwarded` must cover that construct (a test of it in
/// [`a_generic_body_passes_on_only_its_arguments_by_every_route`] or a refusal in
/// [`a_value_of_a_variable_from_no_argument_is_refused_for_a_partial_slot`]).
#[test]
fn constructs_the_proof_leaves_for_later_are_not_compiled_yet() {
    let head = "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: 2.5) else 6;\n";
    let cases = [
        // `initial` in a loop: a value of a generation, carried from frame to frame.
        "pass(x) { r = loop t { while t < 1; initial g = x; g' = g; }; return apply(f: r.g); }\na = pass(x: small);\n",
        // A memo table, whose entry a later call would read.
        "@memoized\npass(x) = apply(f: x);\na = pass(x: small);\n",
        // `match`, whose arms may bind a value of the variable.
        "pass(x) = apply(f: match 1 { 1 -> x, _ -> x });\na = pass(x: small);\n",
        // Recursion, which passes the argument on to the next call.
        "pass(x, n: int) = if n <= 0 { apply(f: x) } else { pass(x: x, n: n - 1) };\na = pass(x: small, n: 2);\n",
        // A declared type variable in a result, a generic struct, a binding with a declared
        // type that fixes a variable from the result.
        "pass(x: T) -> (T, int) = (x, apply(f: x));\na = pass(x: small)[1];\n",
        "struct Box(X) { v: X }\npass(b) = apply(f: b.v);\na = pass(b: Box(v: small));\n",
        "pass(x) = if apply(f: x) > 0 { x } else { x };\ng: (x: int | f64) ->? int = pass(x: small);\na = g(x: 2.5) else 7;\n",
    ];
    let compiled: Vec<_> = cases
        .iter()
        .map(|rest| (rest, front_errors(&format!("{head}{rest}"))))
        .filter(|(_, errors)| !errors.iter().any(|e| e.contains("does not compile it yet")))
        .collect();
    assert!(compiled.is_empty(), "{compiled:#?}");
}

/// The errors of the first pass before the checker that refuses `src`, else the checker's.
fn front_errors(src: &str) -> Vec<String> {
    let tokens = match zedc::lex::lex_fence(src) {
        Ok(t) => t,
        Err(e) => return vec![format!("{e:?}")],
    };
    let tree = match zedc::parse::parse(src, &tokens, "Unit", zedc::parse::TOP) {
        Ok(t) => t,
        Err(e) => return vec![format!("{e:?}")],
    };
    let stmts = match zedc::ast::unit(src, &tokens, &tree) {
        Ok(s) => s,
        Err(e) => return vec![format!("{e:?}")],
    };
    match zedc::resolve::resolve(&stmts) {
        Ok(_) => type_errors(src),
        Err(e) => vec![format!("{e:?}")],
    }
}

/// Row MSG-partial-slot-rebuild-kind-reason: a function passed on to two partial slots whose
/// types rebuild it in two ways, one testing its domain and the result it gives, the other its
/// domain alone, is rebuilt once with both, in either order. Before the fix it was refused as
/// passed on to partial function types "that test its domain in different ways", which they do
/// not: both test the domain `int | f64` of `mid`.
#[test]
fn a_function_rebuilt_in_two_ways_at_one_call_gets_both() {
    let slots = "small(x: int) = x + 1;\nmid(x: int | f64) = small;\napply3(f: (x: int | f64 | bool) ->? ((x: int) -> int)) = 0;\napplyB(f: (x: int | f64 | bool) ->? ((x: int | f64) ->? int)) = f(x: 1)(x: K) else 6 else 7;\n";
    let cases = [
        "pass(x) = applyB(f: x) + apply3(f: x);\na = pass(x: mid);\n",
        "pass(x) = apply3(f: x) + applyB(f: x);\na = pass(x: mid);\n",
        "pass(x) = applyB(f: x) + apply3(f: x) + applyB(f: x);\na = pass(x: mid);\n",
    ];
    for rest in cases {
        let src = |k: &str| format!("{}{rest}", slots.replace('K', k));
        let n = rest.matches("applyB").count();
        runs_to(&src("2.5"), "a", &(6 * n).to_string());
        runs_to(&src("2"), "a", &(3 * n).to_string());
    }
}

/// A function the generic body takes out of a family argument has no place in the argument
/// where the call can put a test of its domain, so the pass to the partial slot is refused,
/// where before the fix the run called `small` with 2.5.
#[test]
fn a_function_taken_from_a_family_argument_is_refused_for_a_partial_slot() {
    let src = "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: 2.5) else 6;\npass(m) = apply(f: m[1]);\na = pass(m: { 1 -> small });\n";
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{src}: {errors:?}");
    assert!(
        errors[0].contains("must give `#notFound`")
            && errors[0].contains("is not one argument of this call, or a component of one"),
        "{src}: {errors:?}"
    );
}

/// A family passed to a partial slot is not rebuilt as a function: its lookup of a key it
/// does not hold gives `#notFound` already, and it stays data for the operations on data the
/// slot allows (the remaps of l08_02, which broke when a family was rebuilt as a lambda).
#[test]
fn a_family_passed_to_a_partial_slot_stays_a_family() {
    let tuple = "useWide(b: ((int | f64) ->? int,)) = b[0](K) else 9;\n";
    let apply = "apply(f: (int | f64) ->? int) = f(K) else 6;\n";
    let cases = [
        (tuple, "a = useWide(b: ({ 3 -> 4 },));\n", "9"),
        (apply, "m = { 3 -> 4 };\na = apply(f: m);\n", "6"),
        (apply, "a = apply(f: { 3 -> 4 });\n", "6"),
    ];
    for (slot, rest, miss) in cases {
        let src = |k: &str| format!("{}{rest}", slot.replace('K', k));
        runs_to(&src("2.5"), "a", miss);
        runs_to(&src("5"), "a", miss);
        runs_to(&src("3"), "a", "4");
    }
}

/// Row FAIL-partial-slot-untestable-domain: a parameter whose type is a variable bounded by
/// one carrier is tested by that carrier, since a call fixes the variable to one carrier of
/// its bound; a domain no test at run time can read (a parameter of function type, a variable
/// bounded by several carriers, a function beside other values) is refused, with the repair
/// as code, where before the call ran the function's body on a value it does not take.
#[test]
fn a_domain_no_test_can_read_is_refused() {
    let one = |k: &str| {
        format!(
            "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: {k}) else 6;\nq(g: (x: V) -> int for V in int) = apply(f: g);\na = q(g: small);\n"
        )
    };
    runs_to(&one("2.5"), "a", "6");
    runs_to(&one("3"), "a", "4");
    let refused = [
        (
            "useH(h: (x: int) -> int) = h(x: 1);\napply(f: (h: ((x: int) -> int) | int) ->? int) = f(h: 3) else 6;\na = apply(f: useH);\n",
            "`h` is a function, whose domain its value does not show",
        ),
        (
            "apply(f: (x: int | f64) ->? int) = f(x: 2.5) else 6;\nq(g: (x: V) -> int for V in int | f64) = apply(f: g);\n",
            "`x` is `V`, which a call may fix to any of `int | f64`",
        ),
        (
            "small(x: int) = x + 1;\nuseWide(b: ((x: int | f64) ->? int) | int) = 9;\npick(n: int) = if n > 0 { small } else { 1 };\na = useWide(b: pick(n: 1));\n",
            "sits beside other values",
        ),
    ];
    for (src, why) in refused {
        let errors = type_errors(src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(
            errors[0].contains(why) && errors[0].contains("must give `#notFound`"),
            "{src}: {errors:?}"
        );
    }
}

/// Row FAIL-generic-pass-reordered-arrow: named parameters match by name, so a declared
/// function whose named parameters are in another order than a slot's is passed to it with
/// its parameters put in the slot's order ([`Fit::Adapter`] at the name), and so it is when
/// it reaches the slot through a generic parameter: the call of the generic function puts
/// the same fit at its argument. Before the fix the program was refused, as "`app2` does not
/// take (y: f64, x: int) -> int, only (x: int, y: f64) -> int". The cases: one generic
/// function, two in a chain, two slots that want one order, a partial slot that also tests
/// the domain, and parameters of one type, where the order alone tells the parameters apart.
#[test]
fn a_reordered_function_passed_through_a_generic_parameter_runs() {
    let head = "re(y: f64, x: int) = x;\napp2(f: (x: int, y: f64) -> int) = f(x: 1, y: 2.0);\npass(g) = app2(f: g);\n";
    let cases = [
        ("a = pass(g: re);\n", "1"),
        ("pass2(h) = pass(g: h);\na = pass2(h: re);\n", "1"),
        (
            "both(g) = app2(f: g) + app2(f: g);\na = both(g: re);\n",
            "2",
        ),
        ("b = (pass(g: re), pass(g: re));\na = b[1];\n", "1"),
        // The repair the refusal of a body that gives the function back offers.
        (
            "back(g: (x: int, y: f64) -> int) = (app2(f: g), g);\nb = back(g: re);\na = b[1](y: 2.0, x: 1) + b[0];\n",
            "2",
        ),
    ];
    for (rest, want) in cases {
        runs_to(&format!("{head}{rest}"), "a", want);
    }
    runs_to(
        "re(y: int, x: int) = x;\napp2(f: (x: int, y: int) -> int) = f(x: 1, y: 2);\npass(g) = app2(f: g);\na = pass(g: re);\n",
        "a",
        "1",
    );
    let partial = |k: &str| {
        format!(
            "re(y: f64, x: int) = x + 1;\napp2(f: (x: int | f64, y: f64) ->? int) = f(x: {k}, y: 2.0) else 6;\npass(g) = app2(f: g);\na = pass(g: re);\n"
        )
    };
    runs_to(&partial("2.5"), "a", "6");
    runs_to(&partial("3"), "a", "4");
}

/// Row FAIL-generic-pass-reordered-arrow: the fit put at the argument changes the order of
/// the parameters of the value the generic body holds, for every use of it there. So where
/// the body also uses it in its own order, or in a third one, or gives it back, or calls it,
/// no one order serves all the uses, and the call is refused with the reason, where a run
/// would call the function with its arguments swapped.
#[test]
fn a_reordered_function_the_generic_body_uses_in_another_order_is_refused() {
    let head = "re(y: f64, x: int) = x;\napp2(f: (x: int, y: f64) -> int) = f(x: 1, y: 2.0);\nown(f: (y: f64, x: int) -> int) = f(y: 2.0, x: 1);\n";
    let cases = [
        (
            "pass(g) = app2(f: g) + own(f: g);\na = pass(g: re);\n",
            "in another order, and also passes it on as `(y: f64, x: int) -> int`",
        ),
        (
            "pass(g) = own(f: g) + app2(f: g);\na = pass(g: re);\n",
            "in another order, and also passes it on as `(y: f64, x: int) -> int`",
        ),
        (
            "pass(g) = (app2(f: g), g);\nb = pass(g: re);\na = b[1](y: 2.0, x: 1);\n",
            "in another order, and also gives it back. Try `g: (x: int, y: f64) -> int` instead.",
        ),
        (
            "pass(g) = app2(f: g) + g(y: 2.0, x: 1);\na = pass(g: re);\n",
            "in another order, and also uses it in its own order. Try `g: (x: int, y: f64) -> int` instead.",
        ),
        (
            "id(h) = h;\npass(g) = app2(f: g) + id(h: g)(y: 2.0, x: 1);\na = pass(g: re);\n",
            "in another order, and also",
        ),
        (
            "wide(f: (x: int | f64, y: f64) ->? int) = f(x: 2.5, y: 2.0) else 6;\npass(g) = app2(f: g) + wide(f: g);\na = pass(g: re);\n",
            "is rebuilt here already",
        ),
    ];
    for (rest, why) in cases {
        let src = format!("{head}{rest}");
        let errors = type_errors(&src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(errors[0].contains(why), "{src}: {errors:?}");
    }
}

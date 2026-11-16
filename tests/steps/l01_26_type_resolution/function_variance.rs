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

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

/// A generic body that calls its parameter by name is called as the function each call passes
/// says (DESIGN.md sec:values_morphisms, "A function value is called as its type says"): the
/// checker meets `g` at `call(g: small)` with `(x: int) -> int`, and that signature places the
/// argument `x: 3` (row FAIL-elab-named-call-generic-param). So does a function taken from a
/// tuple argument.
#[test]
fn a_named_call_of_a_generic_parameter_runs() {
    runs_to(
        "small(x: int) = x + 1;\ncall(g) = g(x: 3);\na = call(g: small);\n",
        "a",
        "4",
    );
    runs_to(
        "small(x: int) = x + 1;\npass(p) = p[1](x: 3);\na = pass(p: (small, small));\n",
        "a",
        "4",
    );
    // Through a second generic function, which passes `h` on to `call`.
    runs_to(
        "small(x: int) = x + 1;\ncall(g) = g(x: 3);\ncall2(h) = call(g: h) + 1;\na = call2(h: small);\n",
        "a",
        "5",
    );
    // Two calls by name in one body, each recorded at its own place in the text.
    runs_to(
        "small(x: int) = x + 1;\ncall(g) = g(x: 3) * 10 + g(x: 4);\na = call(g: small);\n",
        "a",
        "45",
    );
    // A call by position that leaves out a defaulted parameter gets the default.
    runs_to(
        "f(positional x: int, y: int = 1) = x + y;\ncall(g) = g(3);\na = call(g: f);\n",
        "a",
        "4",
    );
    // Two functions with the same parameters in the same order, passed at two calls.
    runs_to(
        "f(a: int, b: int) = a - b;\ng(a: int, b: int) = a * 10 + b;\ncall(k) = k(b: 2, a: 5);\na = call(k: f) * 100 + call(k: g);\n",
        "a",
        "352",
    );
    // A curried call by name.
    runs_to(
        "f(x: int, y: int) = x * 10 + y;\ncur(k) = k(x: 1, ...);\na = cur(k: f)(y: 2);\n",
        "a",
        "12",
    );
    // Defaults that differ are passed over when the call passes the parameter.
    runs_to(
        "f(x: int, y: int = 1) = x + y;\ng(x: int, y: int = 2) = x * y;\ncall(k) = k(x: 3, y: 5);\na = call(k: f) * 100 + call(k: g);\n",
        "a",
        "815",
    );
}

/// A union of functions whose parameter names differ is refused at the call that names a
/// parameter one of them lacks, whether the call is direct or in a generic body met at the
/// union; the call through the value cannot place the argument for both.
#[test]
fn a_named_call_of_a_union_with_different_names_is_refused() {
    let pick = "small(x: int) = x + 1;\nother(y: int) = y * 2;\npick(c: bool) = if c { small } else { other };\n";
    let direct = format!("{pick}h = pick(c: false);\na = h(x: 3);\n");
    let errors = type_errors(&direct);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].contains("has no parameter of that name"),
        "{errors:?}"
    );
    let generic = format!("{pick}call(g) = g(x: 3);\na = call(g: pick(c: false));\n");
    let errors = type_errors(&generic);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].contains("`g` has no parameter of that name"),
        "{errors:?}"
    );
}

/// Elaboration builds a call through a value once, by one signature, so the functions the
/// value may be must take the call's arguments in the same places and fill the parameters it
/// leaves out with the same defaults. When they do not, the checker refuses the call as not
/// compiled yet, with a repair, instead of letting elaboration refuse it or, for differing
/// defaults, run the wrong one (row FAIL-elab-named-call-generic-param).
#[test]
fn a_call_one_signature_cannot_place_for_every_function_is_refused() {
    let cases = [
        // A union with the parameters in different orders.
        (
            "f(a: int, b: int) = a - b;\ng(b: int, a: int) = a * 10 + b;\npick(c: bool) = if c { f } else { g };\nh = pick(c: false);\na = h(a: 5, b: 2);\n",
            "which have the parameter `a` in different places",
            "give the functions passed as this value the same parameters, in the same order",
        ),
        // The same two functions passed at two calls of a generic function.
        (
            "f(a: int, b: int) = a - b;\ng(b: int, a: int) = a * 10 + b;\ncall(k) = k(a: 5, b: 2);\na = call(k: f) * 100 + call(k: g);\n",
            "and at an earlier call one of type `(a: int, b: int) -> int`",
            "give the functions passed as this value the same parameters, in the same order",
        ),
        // A union whose defaults for a parameter the call leaves out differ.
        (
            "f(x: int, y: int = 1) = x + y;\ng(x: int, y: int = 2) = x * y;\npick(c: bool) = if c { f } else { g };\nh = pick(c: false);\na = h(x: 3);\n",
            "may be either of two functions of type `(x: int, y: int) -> int`, whose defaults for `y`",
            "pass `y` in this call, as `y: …`",
        ),
        // The same at two calls of a generic function.
        (
            "f(x: int, y: int = 1) = x + y;\ng(x: int, y: int = 2) = x * y;\ncall(k) = k(x: 3);\na = call(k: f) * 100 + call(k: g);\n",
            "other than the one an earlier call passes",
            "pass `y` in this call, as `y: …`",
        ),
        // A union of functions with different numbers of parameters.
        (
            "f(x: int, y: int = 1) = x + y;\ng(x: int) = x * 7;\npick(c: bool) = if c { f } else { g };\nh = pick(c: false);\na = h(x: 3);\n",
            "which take different numbers of parameters",
            "give the functions passed as this value the same parameters, in the same order",
        ),
    ];
    for (src, reason, repair) in cases {
        let errors = type_errors(src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(errors[0].contains(reason), "{src}: {errors:?}");
        assert!(
            errors[0].contains("does not compile it yet"),
            "{src}: {errors:?}"
        );
        let (info, _) = super::info(src);
        assert!(
            (info.errors[0].notes.iter()).any(|n| n.text == format!("repair: {repair}")),
            "{src}: {:?}",
            info.errors[0].notes
        );
    }
}

/// Calls by name in one generic body whose arguments are alike are one use of the parameter,
/// checked once at each call of the body; each is still built by the signature of the function
/// passed (row TEST-call-site-need-key). So is a call alike to one a function the body calls
/// makes, and that function called alone.
#[test]
fn named_calls_with_arguments_alike_run() {
    runs_to(
        "small(x: int) = x + 1;\ncall(g, v: int) = g(x: v) * 10 + g(x: v);\na = call(g: small, v: 3);\n",
        "a",
        "44",
    );
    runs_to(
        "small(x: int) = x + 1;\nh0(g, v: int) = g(x: v);\nh1(g, v: int) = h0(g: g, v: v) * 10 + g(x: v);\na = h1(g: small, v: 3);\n",
        "a",
        "44",
    );
    runs_to(
        "small(x: int) = x + 1;\nh0(g, v: int) = g(x: v);\nh1(g, v: int) = h0(g: g, v: v) * 10 + g(x: v);\na = h0(g: small, v: 1) + h1(g: small, v: 3);\n",
        "a",
        "46",
    );
    // Two functions, each placing the arguments in the same order, at two calls.
    runs_to(
        "f(a: int, b: int) = a - b;\ng(a: int, b: int) = a * 10 + b;\ncall(k, v: int) = k(b: v, a: 5) * 1000 + k(b: v, a: 5);\na = call(k: f, v: 2) + call(k: g, v: 2);\n",
        "a",
        "55055",
    );
}

/// The call of a generic function that passes a function its body's call cannot be built for
/// is the one later in the text than the first call; the message names the first call's type,
/// and a note points at that call. The order the checker meets the calls in, which follows
/// what each definition uses and not the text, does not change which call is refused (row
/// TEST-call-site-need-key). Each program gives the same answer checked alone, after the
/// others, and after the others in reverse order.
#[test]
fn the_earlier_call_is_the_first_in_the_text() {
    let head = "f(a: int, b: int) = a - b;\nf2(a: int, b: int) = a + b;\ng(b: int, a: int) = a * 10 + b;\ncall(k) = k(a: 5, b: 2);\n";
    let ab = "(a: int, b: int) -> int";
    let ba = "(b: int, a: int) -> int";
    // The rest of the program; the calls refused; the type and the call the message names.
    let cases: [(&str, &[&str], &str, &str); 8] = [
        (
            "x = call(k: f);\ny = call(k: g);\nz = call(k: f2);\n",
            &["call(k: g)"],
            ab,
            "call(k: f)",
        ),
        (
            "x = call(k: g);\ny = call(k: f);\nz = call(k: f2);\n",
            &["call(k: f)", "call(k: f2)"],
            ba,
            "call(k: g)",
        ),
        (
            "y = x + call(k: g);\nx = call(k: f);\n",
            &["call(k: f)"],
            ba,
            "call(k: g)",
        ),
        (
            "x = call(k: f);\ny = x + call(k: g);\n",
            &["call(k: g)"],
            ab,
            "call(k: f)",
        ),
        (
            "v() = u() + call(k: f);\nu() = call(k: g);\n",
            &["call(k: g)"],
            ab,
            "call(k: f)",
        ),
        (
            "a = call(k: g) * 100 + call(k: f);\n",
            &["call(k: f)"],
            ba,
            "call(k: g)",
        ),
        (
            "z = y + call(k: f2);\ny = x + call(k: g);\nx = call(k: f);\n",
            &["call(k: g)"],
            ab,
            "call(k: f2)",
        ),
        (
            "z = y + call(k: g);\ny = x + call(k: f2);\nx = call(k: f);\n",
            &["call(k: f2)", "call(k: f)"],
            ba,
            "call(k: g)",
        ),
    ];
    let srcs: Vec<String> = cases.iter().map(|c| format!("{head}{}", c.0)).collect();
    for (src, (_, refused, ty, first)) in srcs.iter().zip(&cases) {
        let (info, _) = super::info(src);
        let at = |start: usize, end: usize| &src[start..end];
        let mut got: Vec<&str> = (info.errors.iter())
            .map(|e| at(e.span.start, e.span.end))
            .collect();
        got.sort_unstable();
        let mut want = refused.to_vec();
        want.sort_unstable();
        assert_eq!(got, want, "{src}: {:?}", info.errors);
        for e in &info.errors {
            let named = format!("and at an earlier call one of type `{ty}`");
            assert!(e.message.contains(&named), "{src}: {}", e.message);
            assert!(
                (e.notes.iter()).any(|n| at(n.span.start, n.span.end) == *first
                    && n.text
                        == format!("the earlier call, where `k` is a function of type `{ty}`")),
                "{src}: {:?}",
                e.notes
            );
        }
    }
    let answer = |src: &str| zedc::run::load(src.as_bytes()).err();
    let alone: Vec<Option<String>> = (srcs.iter().cloned())
        .map(|src| std::thread::spawn(move || answer(&src)).join().unwrap())
        .collect();
    let batch: Vec<Option<String>> = srcs.iter().map(|src| answer(src)).collect();
    let mut reversed: Vec<Option<String>> = srcs.iter().rev().map(|src| answer(src)).collect();
    reversed.reverse();
    assert_eq!(alone, batch, "alone, then in a batch");
    assert_eq!(alone, reversed, "alone, then in a reversed batch");
    assert!(alone.iter().all(Option::is_some));
}

/// Brackets, level words, scans, folds `><` and `.sum` written alike in one generic body are
/// one use of the parameter, checked once at each call of the body, recorded at the first
/// written; each still has the meaning and the fold its own need would have given it (row
/// TEST-component-site-need-key), at a tuple and a list, at two calls.
#[test]
fn uses_alike_in_one_body_run() {
    runs_to(
        "many(t) = t[0] * 10 + t[0];\na = many(t: (3, 4)) * 1000 + many(t: (5, \"x\"));\n",
        "a",
        "33055",
    );
    for (word, want) in [
        ("t.count", "33"),
        ("t.sum", "66"),
        ("(t >< (+))", "66"),
        ("t.scan((+)).count", "33"),
    ] {
        runs_to(
            &format!("many(t) = {word} * 10 + {word};\na = many(t: [1, 2, 3]);\n"),
            "a",
            want,
        );
    }
    // Uses alike but for their component or their receiver are not one use.
    runs_to(
        "many(t) = t[0] * 10 + t[1] + t[0] * 100;\na = many(t: (3, 4));\n",
        "a",
        "334",
    );
    runs_to(
        "many(t, s) = t.sum * 100 + s.sum * 10 + t.sum;\na = many(t: [1, 2], s: [3, 4]);\n",
        "a",
        "373",
    );
    runs_to(
        "many(t, s) = t.scan((+)).count * 100 + s.scan((+)).count * 10 + t.scan((+)).count;\na = many(t: [1, 2], s: [3]);\n",
        "a",
        "212",
    );
    // Two calls, at `int` and at `f64`.
    runs_to(
        "many(t) = (t >< (+)) * 10 + (t >< (+));\na = (many(t: [1, 2]), many(t: [0.5, 1.5]));\n",
        "a",
        "(33, 22.0)",
    );
}

/// A fold written twice alike in one generic body, which two calls run at carriers whose empty
/// levels fold to different identities, is split at both: each call folds each of the two to
/// the identity of its own carrier, `#empty` at `int` and `-inf` at `f64` (DESIGN.md
/// sec:reduction, "Identity as data"; row TEST-component-site-need-key).
#[test]
fn a_fold_alike_to_one_split_by_its_calls_is_split_too() {
    let levels = "mi = { \"a\" -> [1], \"b\" -> [5] }.map(r -> r.where(v -> v > 3));\n\
                  m = { \"a\" -> [1.0], \"b\" -> [5.0] }.map(r -> r.where(v -> v > 3.0));\n";
    runs_to(
        &format!(
            "{levels}two(positional xs) = (xs >< max, xs >< max);\na = (two(mi[\"a\"]), two(m[\"a\"]));\n"
        ),
        "a",
        "((#empty, #empty), (-inf, -inf))",
    );
    runs_to(
        &format!(
            "{levels}two(positional xs) = (xs >< max, xs >< max);\na = (two(m[\"b\"]), two(mi[\"b\"]), two(m[\"a\"]));\n"
        ),
        "a",
        "((5.0, 5.0), (5, 5), (-inf, -inf))",
    );
}

/// A body whose brackets alike read a component the argument lacks gives at each call that
/// passes too short a tuple the error a body with one such bracket gives, once for each
/// bracket, each with its note at its own bracket, as each would give without the others;
/// whatever the order of the calls in the text and in the checker's walk, checked alone, after
/// the others, and after the others in reverse order (row TEST-component-site-need-key).
#[test]
fn brackets_alike_give_the_errors_of_one_bracket_in_any_order() {
    let calls = [
        "x = many(t: (1, 2));\ny = many(t: (1, 2, 3));\nz = many(t: (4,));\n",
        "z = many(t: (4,));\ny = many(t: (1, 2, 3));\nx = many(t: (1, 2));\n",
        "y = x + many(t: (1, 2, 3));\nx = many(t: (1, 2)) + z;\nz = many(t: (4,));\n",
        "v() = u() + many(t: (4,));\nu() = many(t: (1, 2));\nw = many(t: (1, 2, 3)) + v();\n",
    ];
    // Each error: the call it is at, its message, and where its notes are in the body's line.
    let errors = |body: &str, src: &str| -> Vec<(String, String, Vec<usize>)> {
        let (info, _) = super::info(src);
        let mut got: Vec<(String, String, Vec<usize>)> = (info.errors.iter())
            .map(|e| {
                let notes = (e.notes.iter())
                    .map(|n| n.span.start)
                    .filter(|&s| s < body.len())
                    .collect();
                let at = src[e.span.start..e.span.end].to_string();
                (at, e.message.clone(), notes)
            })
            .collect();
        got.sort();
        got
    };
    let mut srcs = Vec::new();
    for rest in calls {
        let (one_body, body) = (
            "many(t) = t[2];\n",
            "many(t) = t[2] * 10 + t[2] * 100 + t[2];\n",
        );
        let one = errors(one_body, &format!("{one_body}{rest}"));
        let at: Vec<&str> = one.iter().map(|(s, _, _)| s.as_str()).collect();
        assert_eq!(at, ["many(t: (1, 2))", "many(t: (4,))"], "{rest}: {one:?}");
        // The note at the bracket (at 10 in the one-bracket body), and the one at the
        // definition (at 0).
        assert!(one.iter().all(|(_, _, n)| n == &[10, 0]), "{one:?}");
        let mut want: Vec<(String, String, Vec<usize>)> = (one.iter())
            .flat_map(|(at, m, _)| {
                (body.match_indices("t[2]")).map(|(b, _)| (at.clone(), m.clone(), vec![b, 0]))
            })
            .collect();
        want.sort();
        let alike = format!("{body}{rest}");
        assert_eq!(errors(body, &alike), want, "{alike}");
        srcs.push(alike);
    }
    let answer = |src: &str| zedc::run::load(src.as_bytes()).err();
    let alone: Vec<Option<String>> = (srcs.iter().cloned())
        .map(|src| std::thread::spawn(move || answer(&src)).join().unwrap())
        .collect();
    let batch: Vec<Option<String>> = srcs.iter().map(|src| answer(src)).collect();
    let mut reversed: Vec<Option<String>> = srcs.iter().rev().map(|src| answer(src)).collect();
    reversed.reverse();
    assert_eq!(alone, batch, "alone, then in a batch");
    assert_eq!(alone, reversed, "alone, then in a reversed batch");
    assert!(alone.iter().all(Option::is_some));
}

/// The bounds of a type variable in the signature a body is shown with do not change where
/// uses alike share one need (`Ck::share_alike`, row TEST-component-site-need-key): for each
/// body, the type shown now, with the set of its bounds equal to the set of the bounds in the
/// type shown at commit 7322e2a94, before the sharing, which each row also records. What does
/// change: two result variables that the sharing makes one show as one (`(U, V)` became
/// `(U, U)`; a variable seen once shows as `_`, so `(_, _)` became `(T, T)`), and no variable
/// that the type does not hold is listed after `for` (row MSG-type-vars-printed-unused), so
/// the bounds compared are those of the variables each text writes.
#[test]
fn uses_alike_keep_the_bounds_of_the_signature() {
    let shown = [
        // A bracket left free, twice.
        ("(t[0], t[0])", "(t: _) -> (_, _)", "(t: _) -> (T, T)"),
        // Added to 1: a variable bounded to the numbers.
        (
            "(t[0] + 1, t[0] + 1)",
            "(t: _) -> (U, V) for U in int | f32 | f64 | rat, V in int | f32 | f64 | rat",
            "(t: _) -> (U, U) for U in int | f32 | f64 | rat",
        ),
        // Resolved to `int` in the body.
        (
            "(fi(x: t[0]), fi(x: t[0]))",
            "(t: _) -> (int, int)",
            "(t: _) -> (int, int)",
        ),
        // Resolved to `int | f64`, a type the signature does not show.
        (
            "(fu(x: t[0]), fu(x: t[0]))",
            "(t: _) -> (0, 0) for U in int | f64, V in int | f64",
            "(t: _) -> (0, 0)",
        ),
        (
            "(t[0], t[0] + 1, t[0], t[0] + 1)",
            "(t: _) -> (_, V, _, T5) for V in int | f32 | f64 | rat, T5 in int | f32 | f64 | rat",
            "(t: _) -> (T, V, T, V) for V in int | f32 | f64 | rat",
        ),
        // The four forms, twice.
        (
            "(t[0], fi(x: t[0]), fu(x: t[0]), t[0] + 1, t[0], fi(x: t[0]), fu(x: t[0]), t[0] + 1)",
            "(t: _) -> (_, int, 0, V, _, int, 0, T5) for T6 in int | f64, \
             V in int | f32 | f64 | rat, T7 in int | f64, T5 in int | f32 | f64 | rat",
            "(t: _) -> (T, int, 0, V, T, int, 0, V) for V in int | f32 | f64 | rat",
        ),
        (
            "0 + t[0] + t[0]",
            "(t: _) -> U for U in int | f32 | f64 | rat",
            "(t: _) -> U for U in int | f32 | f64 | rat",
        ),
        ("(t.count, t.count)", "(t: _) -> (_, _)", "(t: _) -> (T, T)"),
        // Three uses of different kinds on one bracket's result.
        (
            "(t[0] - 1, -t[0], t[0] + 1)",
            "(t: _) -> (U, V, W) for U in int | f32 | f64 | rat, V in int | f32 | f64 | rat, \
             W in int | f32 | f64 | rat",
            "(t: _) -> (U, U, U) for U in int | f32 | f64 | rat",
        ),
    ];
    // The bounds after `for` of the variables written before it, as a set.
    let bounds = |t: &str| -> std::collections::BTreeSet<String> {
        let Some((arrows, clause)) = t.split_once(" for ") else {
            return Default::default();
        };
        let words = arrows.split(|c: char| !c.is_ascii_alphanumeric());
        (clause.split(", "))
            .map(|v| v.split_once(" in ").expect("`X in B`"))
            .filter(|(v, _)| words.clone().any(|w| w == *v))
            .map(|(_, b)| b.to_string())
            .collect()
    };
    let lead = "the type the checker found for `many` is `";
    for (body, before, now) in shown {
        assert_eq!(bounds(before), bounds(now), "{body}");
        // A call each body refuses, whose notes show where `many` is declared.
        let src = format!(
            "fi(x: int) = x;\nfu(x: int | f64) = 0;\nmany(t) = {body};\n\
             c0(y: int) = many(t: (\"a\", 0));\nc1(y: int) = many(t: 5);\n"
        );
        let (info, _) = super::info(&src);
        let got: std::collections::BTreeSet<&str> = (info.errors.iter())
            .flat_map(|e| e.notes.iter())
            .filter_map(|n| n.text.split_once(lead))
            .map(|(_, t)| t.strip_suffix('`').expect("ends with `"))
            .collect();
        assert_eq!(got, [now].into(), "{src}");
    }
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
/// variable does not come from a place in one argument that the call shows: a default that is
/// a function written in the program, an entry of a family (alone, or with an `else` of the
/// bare name met before or after it), a lambda inside `map`, and the result of calling a
/// parameter. Each is refused rather than run without a test of the domain; before the fix of
/// FAIL-partial-slot-generic-pass these ran `small` on 2.5. Row
/// MSG-partial-slot-no-place-repair-code: the headline is code, and ends with the repair as
/// code where a declaration this zedc compiles repairs it ([`the_repairs_the_no_place_refusal_offers_run`]);
/// `y: _ -> (x: int) -> int`, for `y(x)`, writes `_`, so none is offered there.
#[test]
fn a_value_of_a_variable_from_no_argument_is_refused_for_a_partial_slot() {
    let head = "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: 2.5) else 6;\n";
    let passes = "passes `(x: int) -> int` as `(x: int | f64) ->? int`, from no argument of the call \
                  where its domain can be tested.";
    let entry = "apply(f: { 1 -> x }[1] else x)";
    let try_x = " Try `x: (x: int) -> int` instead.";
    let cases = [
        (
            "pass(x, y = small) = apply(f: y);\na = pass(x: 1);\n",
            "apply(f: y)",
            "",
        ),
        (
            "pass(x) = apply(f: { 1 -> x }[1] else x);\na = pass(x: small);\n",
            entry,
            try_x,
        ),
        (
            "pass(x) = apply(f: x else x) + apply(f: { 1 -> x }[1] else x);\na = pass(x: small);\n",
            "apply(f: x else x)",
            try_x,
        ),
        (
            "pass(x) = apply(f: { 1 -> x }[1] else x) + apply(f: x else x);\na = pass(x: small);\n",
            entry,
            try_x,
        ),
        (
            "pass(x) = apply(f: x);\na = [small].map(g -> pass(x: g))[0];\n",
            "pass(x: g)",
            " Try `g: (x: int) -> int` instead.",
        ),
        (
            "pass(x, y) = apply(f: y(x));\na = pass(x: 1, y: n -> small);\n",
            "apply(f: y(x))",
            "",
        ),
    ];
    for (rest, code, repair) in cases {
        let src = format!("{head}{rest}");
        let errors = type_errors(&src);
        let want = format!("`{code}` {passes}{repair} [{code}]");
        assert!(errors.contains(&want), "{src}: {want}\n{errors:#?}");
    }
}

/// Row MSG-partial-slot-no-place-repair-code: the repairs the refusal above offers, and the
/// declaration of the default the parameter left out, written into the program, make it run:
/// each function is then of a declared type where the body passes it on, so the slot rebuilds
/// it there, and it misses outside its domain.
#[test]
fn the_repairs_the_no_place_refusal_offers_run() {
    let head = |k: &str| {
        format!("small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: {k}) else 6;\n")
    };
    let cases = [
        "pass(x: (x: int) -> int) = apply(f: { 1 -> x }[1] else x);\na = pass(x: small);\n",
        "pass(x) = apply(f: x);\na = [small].map((g: (x: int) -> int) -> pass(x: g))[0];\n",
        "pass(x, y: (x: int) -> int = small) = apply(f: y);\na = pass(x: 1);\n",
    ];
    for rest in cases {
        runs_to(&format!("{}{rest}", head("2.5")), "a", "6");
        runs_to(&format!("{}{rest}", head("3")), "a", "4");
    }
}

/// Row FAIL-partial-slot-generic-needless-refusals: a value the generic body passes on from an
/// argument by a route `CallFrame::place` did not follow at first is rebuilt at that argument
/// too, so it misses outside the function's domain and calls it inside, where before it was
/// refused, soundly but needlessly: a default that reads another parameter, `x else x` where
/// `x` holds no atom, the generic function passed as a value and called there with an
/// argument of the outer call or one written in its body (once or twice, and through two
/// calls of one function value). The fifth case of the row, the generic function called from a
/// lambda inside `map`, stays refused ([`a_value_of_a_variable_from_no_argument_is_refused_for_a_partial_slot`]):
/// the lambda's parameter is checked once for every type the lambda meets, so no one test can
/// be put at it; row FAIL-partial-slot-generic-lambda-map holds it.
#[test]
fn values_a_generic_body_passes_on_from_its_arguments_miss_outside_the_domain() {
    let head = |k: &str| {
        format!("small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: {k}) else 6;\n")
    };
    let cases = [
        ("pass(x, y = x) = apply(f: y);\na = pass(x: small);\n", 1),
        ("pass(x) = apply(f: x else x);\na = pass(x: small);\n", 1),
        (
            "pass(x) = apply(f: x);\nrun(g, v) = g(x: v);\na = run(g: pass, v: small);\n",
            1,
        ),
        (
            "pass(x) = apply(f: x);\ntwice(g) = g(x: small);\na = twice(g: pass);\n",
            1,
        ),
        (
            "pass(x) = apply(f: x);\nrun(g, v) = g(x: v) + g(x: v);\na = run(g: pass, v: small);\n",
            2,
        ),
    ];
    for (rest, n) in cases {
        runs_to(&format!("{}{rest}", head("2.5")), "a", &(6 * n).to_string());
        runs_to(&format!("{}{rest}", head("3")), "a", &(4 * n).to_string());
    }
}

/// A call through a parameter that names its arguments is built once for every function the
/// parameter takes (`Ck::record_call`); a second function there that takes another number of
/// parameters, one of them with a default, is refused at the call that passes it.
#[test]
fn a_named_call_through_a_parameter_of_two_differing_functions_is_refused() {
    let src = "one(x: int) = x;\ntwo(x: int, y: int = 1) = x + y;\nrun(g) = g(x: 1);\na = run(g: one) + run(g: two);\n";
    let errors = type_errors(src);
    assert!(
        errors.iter().any(
            |e| e.contains("and at an earlier call one of type `(x: int) -> int`")
                && e.contains("which take different numbers of parameters")
        ),
        "{src}: {errors:#?}"
    );
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

/// Row FAIL-partial-slot-generic-family-entry: a function the generic body takes out of a
/// family argument (`m[1]`), whose entries that are no atom are all of one type, is rebuilt at
/// the call by rebuilding every entry of the family (`CallFrame::entries`,
/// `Coercion::Entries`), so a call through the partial slot misses outside its domain and
/// calls it inside. Before the fix it was refused as passed "from no argument of the call
/// where its domain can be tested", soundly but needlessly; before FAIL-partial-slot-generic-pass
/// the run called `small` with 2.5. The cases: a family, an array, an entry of a family that
/// is a component of a tuple argument, a component of a tuple entry, two entries of one type,
/// a family with an atom entry, and an exact call of the entry beside the partial one, which
/// gets the entry's own values.
#[test]
fn a_function_taken_from_a_family_argument_misses_outside_its_domain() {
    let head = |k: &str| {
        format!(
            "small(x: int) = x + 1;\nbig(x: int) = x + 10;\napply(f: (x: int | f64) ->? int) = f(x: {k}) else 6;\n"
        )
    };
    let cases = [
        (
            "pass(m) = apply(f: m[1]);\na = pass(m: { 1 -> small });\n",
            "6",
            "4",
        ),
        (
            "pass(m) = apply(f: m[0]);\na = pass(m: [small]);\n",
            "6",
            "4",
        ),
        (
            "pass(p) = apply(f: p[0][1]);\na = pass(p: ({ 1 -> small }, 0));\n",
            "6",
            "4",
        ),
        (
            "pass(m) = apply(f: m[1][0]);\na = pass(m: { 1 -> (small, 0) });\n",
            "6",
            "4",
        ),
        (
            "pass(m) = apply(f: m[2]);\na = pass(m: { 1 -> small, 2 -> big });\n",
            "6",
            "13",
        ),
        (
            "pass(m) = apply(f: m[0]) + apply(f: m[1]);\na = pass(m: [small, big]);\n",
            "12",
            "17",
        ),
        (
            "pass(m) = apply(f: m[1]) + m[1](x: 3);\na = pass(m: { 1 -> small });\n",
            "10",
            "8",
        ),
    ];
    for (rest, miss, hit) in cases {
        runs_to(&format!("{}{rest}", head("2.5")), "a", miss);
        runs_to(&format!("{}{rest}", head("3")), "a", hit);
    }
}

/// Row FAIL-partial-slot-generic-family-entry, a neighbor that stays refused: a family whose
/// entries are functions of two types, so an entry read is one of two functions, and no one
/// rebuilding fits both. (A family built in the body lies in no argument and stays refused
/// too: `{ 1 -> x }[1]` in [`a_value_of_a_variable_from_no_argument_is_refused_for_a_partial_slot`].)
#[test]
fn a_function_taken_from_a_family_of_two_function_types_is_refused_for_a_partial_slot() {
    let src = "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: 2.5) else 6;\npass(m) = apply(f: m[1]);\nwide(x: int | f64) = 1;\na = pass(m: { 1 -> small, 2 -> wide });\n";
    let errors = type_errors(src);
    let want = "`apply(f: m[1])` is `((x: int) -> int) | ((x: int | f64) -> 1)`, passed as \
                `(x: int | f64) ->? int`";
    assert!(
        errors.len() == 1 && errors[0].starts_with(want),
        "{src}: {want}\n{errors:#?}"
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

/// Row TEST-partial-slot-port-pe-routes, the second part: the cases the proof at
/// `Ck::coerce_at` names for the "rebuilt here already" refusal, which is a debug assertion
/// now, each run to its values. A lambda passed to a generic function that calls it at two
/// function types, `small` on `int` and `small4` on `f64`, passes each on with its own test
/// (8 at 2.5: `#notFound` then 2; 10 at 3: 4 then `#notFound`); a lambda with a default, or
/// with its parameters in another order, at a slot whose domain is a variable, and a declared
/// function in another order there, keep their fits beside the test of the domain.
#[test]
fn arguments_the_rebuilt_here_proof_names_run_to_their_values() {
    let head = |k: &str| {
        format!(
            "small(x: int) = x + 1;\nsmall4(x: f64) = 2;\napply(f: (x: int | f64) ->? int) = f(x: {k}) else 6;\npass(x) = apply(f: x);\npassT(t) = apply(f: t[0]);\n"
        )
    };
    let twice = "twice(f) = f(small) + f(small4);\n";
    let cases = [
        (format!("{twice}a = twice(f: g -> pass(x: g));\n"), "8", "10"),
        (format!("{twice}a = twice(f: g -> passT(t: (g, 1)));\n"), "8", "10"),
        (format!("{twice}a = twice(f: g -> pass(x: (g, 1)[0]));\n"), "8", "10"),
        (
            "twice(f) = f((small, 1)) + f((small4, 1));\na = twice(f: p -> passT(t: p));\n".into(),
            "8",
            "10",
        ),
        ("h(g) = passT(t: (g, 1));\na = h(g: small) + h(g: small4);\n".into(), "8", "10"),
        (
            "q(g: (x: V) -> int for V in int) = apply(f: g);\na = q(g: (x: int, z: int = 0) -> x + 1 + z);\n".into(),
            "6",
            "4",
        ),
        (
            "apply2(f: (x: int | f64, y: int) ->? int) = f(x: 1, y: 2) else 6;\nq(g: (x: V, y: int) -> int for V in int) = apply2(f: g) + g(x: 3, y: 4);\na = q(g: (y: int, x: int) -> x + 10 * y);\n".into(),
            "64",
            "64",
        ),
        (
            "sm(y: int, x: int) = x + 10 * y;\napply2(f: (x: int | f64, y: int) ->? int) = f(x: 1, y: 2) else 6;\nq(g: (x: V, y: int) -> int for V in int) = apply2(f: g) + g(x: 3, y: 4);\na = q(g: sm);\n".into(),
            "64",
            "64",
        ),
    ];
    for (rest, miss, hit) in cases {
        runs_to(&format!("{}{rest}", head("2.5")), "a", miss);
        runs_to(&format!("{}{rest}", head("3")), "a", hit);
    }
}

/// Row PROOF-twice-lambda-placement: where the checker puts the rebuildings the proof at
/// `Ck::coerce_at` names for a lambda passed to a generic function that calls it at two
/// function types. For `twice(f) = f(small) + f(small4)` and `twice(f: g -> pass(x: g))`, each
/// rebuilding sits at its own argument of `f` in `twice`, the same as `pass(x: small)` and
/// `pass(x: small4)` put there written alone, and none at the `g` of `pass(x: g)`, where the
/// two would meet at one place and not join. The values show the same from outside: at 2.5
/// `small` misses and `small4` gives 2, at 3 `small` gives 4 and `small4` misses, in every
/// order of the calls and with a function called twice.
#[test]
fn the_twice_lambda_rebuilds_each_function_at_its_own_argument() {
    use zedc::check::Fit;
    let head = |k: &str| {
        format!(
            "small(x: int) = x + 1;\nsmall4(x: f64) = 2;\napply(f: (x: int | f64) ->? int) = f(x: {k}) else 6;\npass(x) = apply(f: x);\n"
        )
    };
    // The rebuilding of each function passed alone to `pass`, as the call writes it.
    let alone = |name: &str| {
        let src = format!("{}a = pass(x: {name});\n", head("3"));
        let at = src.rfind(&format!("x: {name})")).expect("the argument") + 3;
        let (info, _) = super::info(&src);
        match info.fits.into_iter().find(|(s, _)| s.start == at) {
            Some((s, Fit::Coerce(c))) if s.end == at + name.len() => c,
            other => panic!("{src}: no rebuilding of `{name}` alone: {other:?}"),
        }
    };
    let (small, small4) = (alone("small"), alone("small4"));
    assert_ne!(small, small4, "the two domains differ");
    for (twice, calls) in [
        (
            "twice(f) = f(small) + f(small4);\n",
            ["small", "small4"].as_slice(),
        ),
        ("twice(f) = f(small4) + f(small);\n", &["small4", "small"]),
        (
            "twice(f) = f(small) + f(small4) + f(small);\n",
            &["small", "small4", "small"],
        ),
    ] {
        let rest = format!("{twice}a = twice(f: g -> pass(x: g));\n");
        let src = format!("{}{rest}", head("3"));
        // The argument of each call of `f` in `twice`, by where it starts, and the rebuilding
        // of that function alone.
        let line = src.find("twice(f) =").expect("twice");
        let mut want = Vec::new();
        let mut from = line;
        for &name in calls {
            let at = from + src[from..].find(&format!("f({name})")).expect("a call") + 2;
            want.push((
                at,
                at + name.len(),
                if name == "small" { &small } else { &small4 },
            ));
            from = at + name.len();
        }
        let g = src.rfind("pass(x: g)").expect("the lambda's call") + 8;
        let (info, _) = super::info(&src);
        let mut got: Vec<_> = (info.fits.iter())
            .map(|(s, f)| (s.start, s.end, f.clone()))
            .collect();
        got.sort_by_key(|&(start, end, _)| (start, end));
        let shown = || {
            (got.iter())
                .map(|(s, e, f)| format!("`{}` at {s}: {f:?}", &src[*s..*e]))
                .collect::<Vec<_>>()
        };
        assert!(
            got.iter().all(|&(s, _, _)| s != g),
            "{src}: a fit at the `g` of `pass(x: g)`: {:?}",
            shown()
        );
        let want: Vec<_> = (want.iter())
            .map(|&(s, e, c)| (s, e, Fit::Coerce(c.clone())))
            .collect();
        assert_eq!(got, want, "{src}: {:?}", shown());
        // At 2.5: `small` misses (6), `small4` gives 2; at 3: `small` gives 4, `small4` misses.
        let (miss, hit) = match calls.len() {
            3 => ("14", "14"),
            _ => ("8", "10"),
        };
        runs_to(&format!("{}{rest}", head("2.5")), "a", miss);
        runs_to(&src, "a", hit);
    }
}

/// Row PROOF-twice-lambda-placement, the other route: a lambda passed at an intersection of
/// function types is checked once for each arrow, so a function its parameter passes into a
/// partial slot needs a test of `int` at one arrow and of `f64` at the other, both at the one
/// `g`. The program runs one version of the lambda, so it is refused: through a generic
/// function (`pass`, the rebuilding at `Ck::coerce_at`) and directly (`apply`, the rebuilding
/// of the argument itself). Before the refusal the first stopped a debug build on the
/// assertion at `Ck::coerce_at`, and the second kept the test of `f64` alone and called
/// `small` on 2.5, a fault of zedc at run time. The same lambda with one arrow runs. Both
/// refusals, and the one a parameter declared at the partial type meets (`typed`), name the
/// lambda and the intersection and offer the lambda once at each arrow, which runs to the
/// value DESIGN gives the refused program (MSG-arrow-lambda-rebuild-repair; making the
/// refused programs run is row FAIL-arrow-lambda-partial-slot).
#[test]
fn a_lambda_checked_at_each_arrow_is_rebuilt_once() {
    let head = "small(x: int) = x + 1;\nsmall4(x: f64) = 2;\napply(f: (x: int | f64) ->? int) = f(x: 2.5) else 6;\npass(x) = apply(f: x);\n";
    let both = "both(h: ((g: (x: int) -> int) -> int) & ((g: (x: f64) -> int) -> int)) = h(g: small) + h(g: small4);\n";
    for body in ["pass(x: g)", "apply(f: g)", "typed(x: g)"] {
        let typed = "typed(x: (x: int | f64) ->? int) = apply(f: x);\n";
        let src = format!("{head}{typed}{both}a = both(h: g -> {body});\n");
        let want = format!(
            "`g -> {body}` is passed as `((g: (x: int) -> int) -> int) & ((g: (x: f64) -> int) \
             -> int)` and rebuilds `g` in another way at each arrow. Try `g -> {body}` once at \
             each arrow instead, as arguments of types `(g: (x: int) -> int) -> int` and `(g: \
             (x: f64) -> int) -> int`. [g]"
        );
        assert_eq!(type_errors(&src), [want], "{src}");
        // The repair offered: a parameter for each arrow, the lambda passed to each.
        let split = "split(h1: (g: (x: int) -> int) -> int, h2: (g: (x: f64) -> int) -> int) = h1(g: small) + h2(g: small4);\n";
        let lam = format!("g -> {body}");
        let fixed = format!("{head}{typed}{split}a = split(h1: {lam}, h2: {lam});\n");
        runs_to(&fixed, "a", "8");
    }
    let one = "one(h: (g: (x: int) -> int) -> int) = h(g: small);\n";
    for body in ["pass(x: g)", "apply(f: g)"] {
        runs_to(&format!("{head}{one}a = one(h: g -> {body});\n"), "a", "6");
    }
}

/// Row MSG-arrow-lambda-rebuild-repair (filed by twice-proof while doing
/// PROOF-twice-lambda-placement): for a lambda passed at an intersection of function types and
/// checked once per arrow, the refusal at `Ck::coerce_at` offered a parameter declared at the
/// partial type, which, applied, met the refusal at `Ck::put`, and that refusal offered no
/// repair as code. Each now offers a repair as code, and none that is refused.
#[test]
fn the_arrow_lambda_refusals_offer_a_repair_that_is_accepted() {
    let head = "small(x: int) = x + 1;\nsmall4(x: f64) = 2;\napply(f: (x: int | f64) ->? int) = f(x: 2.5) else 6;\npass(x) = apply(f: x);\ntyped(x: (x: int | f64) ->? int) = apply(f: x);\n";
    let both = "both(h: ((g: (x: int) -> int) -> int) & ((g: (x: f64) -> int) -> int)) = h(g: small) + h(g: small4);\n";
    let errs = type_errors(&format!("{head}{both}a = both(h: g -> pass(x: g));\n"));
    assert_eq!(errs.len(), 1);
    // The repair offered before: a parameter declared at the partial type.
    let repaired = format!("{head}{both}a = both(h: g -> typed(x: g));\n");
    assert!(
        !errs[0].contains("Try `x: (x: int | f64) ->? int`") || type_errors(&repaired).is_empty(),
        "the repair offered is refused: {:?}",
        type_errors(&repaired)
    );
    // The second refusal ends with a repair as code.
    let errs = type_errors(&format!("{head}{both}a = both(h: g -> apply(f: g));\n"));
    assert!(errs[0].contains("Try `"), "{errs:?}");
}

/// Row TEST-partial-slot-port-pe-routes, the port-read case of the proof at
/// `Ck::coerce_forwarded`, run by `zedc run`: a key read from a port reaches the function a
/// generic body passes on, which misses outside its domain and is called inside it, whichever
/// line the port gives; a function chosen by a value read from a port is rebuilt the same way.
/// The `Lines` port itself, passed through a generic body, is of its declared type
/// `int ->? String | #ioError(…)`, so the slot `(int | f64) ->? String` refuses it by its
/// values, as the proof says, before any rebuilding.
#[test]
fn a_function_a_generic_body_passes_on_misses_on_keys_a_port_reads() {
    use zed_tests::step_helpers::l01_19_whole_file_ports::run;
    let key = "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int, v: int | f64) = f(x: v) else 6;\npass(x, v: int | f64) = apply(f: x, v: v);\nmain(m: MainArgs) {\n  v = int(m.stdin[0] else \"\") else f64(0);\n  m.stdout <- \"${pass(x: small, v: v)}\";\n}\n";
    // A line that is no `int` gives the key `f64(0)`, outside `small`'s domain.
    for (stdin, want) in [("a\nb\n", "6\n"), ("3\n", "4\n")] {
        let o = run(&format!("port_key_{}", stdin.len()), key, stdin, &[]);
        assert_eq!(
            (o.status, o.stdout.as_str()),
            (0, want),
            "{stdin:?}: {}",
            o.stderr
        );
    }
    let chosen = |k: &str| {
        format!(
            "small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: {k}) else 6;\npass(x) = apply(f: x);\nmain(m: MainArgs) {{\n  n = int(m.stdin[0] else \"\") else 0;\n  m.stdout <- \"${{pass(x: if n > 0 {{ small }} else {{ small }})}}\";\n}}\n"
        )
    };
    for (k, want) in [("2.5", "6\n"), ("3", "4\n")] {
        for stdin in ["1\n", "0\n"] {
            let o = run(
                &format!("port_chosen_{}_{}", k.len(), stdin.len()),
                &chosen(k),
                stdin,
                &[],
            );
            assert_eq!(
                (o.status, o.stdout.as_str()),
                (0, want),
                "{k} {stdin:?}: {}",
                o.stderr
            );
        }
    }
    let lines = "apply(f: (int | f64) ->? String) = f(2.5) else \"none\";\napply1(f: (int | f64) ->? String) = f(1) else \"none\";\npass(x) = apply(f: x) ++ \"|\" ++ apply1(f: x);\nmain(m: MainArgs) {\n  m.stdout <- pass(x: m.stdin);\n}\n";
    let o = run("port_lines", lines, "a\n", &[]);
    assert_eq!(o.status, 1, "{}", o.stderr);
    assert!(
        o.stderr.contains("does not take int ->? String | #ioError(op: String, path: String, why: String), only (int | f64) ->? String."),
        "{}",
        o.stderr
    );
}

/// Row TEST-partial-slot-port-pe-routes, the partial-evaluation case of the proof at
/// `Ck::coerce_forwarded`: a function a generic body passes on, by a call staging meets (a
/// call of a generic identity in the body or at the argument, a build-stage definition that
/// names it, an `if` on a build-stage condition, a literal argument beside it), keeps the test
/// of its domain in the staged program, and `zedc run`, which runs the staged program, misses
/// outside the domain and calls it inside. In this zedc staging folds none of these calls: it
/// leaves `pass(…)` to run, since the test's form does not show that it ends, and a
/// build-stage definition whose value is a function is left to run too; so the staged `a` is
/// still the call with the test, and a fold, if staging learns one, must give the value.
#[test]
fn a_function_a_generic_body_passes_on_keeps_its_test_through_staging() {
    use zed_tests::step_helpers::l01_19_whole_file_ports::run;
    let head = |k: &str| {
        format!("small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: {k}) else 6;\n")
    };
    let main = "main(m: MainArgs) {\n  m.stdout <- \"${a}\";\n}\n";
    let cases = [
        "id(v) = v;\npass(x) = apply(f: id(v: x));\na = pass(x: small);\n",
        "id(v) = v;\npass(x) = apply(f: x);\na = pass(x: id(v: small));\n",
        "id(v) = v;\ng = id(v: small);\npass(x) = apply(f: x);\na = pass(x: g);\n",
        "pick(k: int) = if k > 1 { small } else { small };\ng = pick(k: 2);\npass(x) = apply(f: x);\na = pass(x: g);\n",
        "k = 2;\npass(x) = apply(f: if k > 1 { x } else { small });\na = pass(x: small);\n",
        "pass(x, k) = apply(f: if k > 1 { x } else { x });\na = pass(x: small, k: 2);\n",
    ];
    for (i, rest) in cases.iter().enumerate() {
        for (k, want) in [("2.5", "6"), ("3", "4")] {
            let src = format!("{}{rest}{main}", head(k));
            let p = zedc::run::load(src.as_bytes()).unwrap_or_else(|e| panic!("{src}: {e}"));
            let staged = p.stage().0;
            let a = staged
                .unit()
                .defs
                .iter()
                .find(|d| d.name == "a")
                .map(|d| d.term.to_string());
            let a = a.unwrap_or_else(|| panic!("{src}: no `a` staged"));
            assert!(a == want || a.contains("#notFound"), "{src}: a = {a}");
            let o = run(&format!("staged_{i}_{}", k.len()), &src, "", &[]);
            assert_eq!(
                (o.status, o.stdout.as_str()),
                (0, format!("{want}\n").as_str()),
                "{src}: {}",
                o.stderr
            );
        }
    }
}

/// A parameter with no written type whose uses bound it is printed with its bound, not as `_`,
/// which is every value (QUESTIONS A92), in both messages that print the type the checker found
/// for a generic function (plan row MSG-bounded-param-printed-underscore).
#[test]
fn a_parameter_with_a_bound_is_printed_with_its_bound() {
    let head = "small(x: int) = x + 1;\nbig(x: int | f64) = 0;\napply(f: (x: int | f64) ->? int) = f(x: 2.5) else 6;\npass(x) = apply(f: x);\n";
    let twice = format!(
        "{head}pass2(x, y: int = 1) = apply(f: x) + y;\ntwice(g) = g(x: small);\na = twice(g: pass) + twice(g: pass2);\n"
    );
    let errors = type_errors(&twice);
    let built = errors
        .iter()
        .find(|e| e.contains("the call through `g` is built once for both functions"))
        .unwrap_or_else(|| panic!("{twice}: {errors:#?}"));
    assert!(!built.contains("(x: _"), "{twice}: {built}");
    let want = "`g` here is a function of type `(x: (x: int | f64) ->? int, y: int) -> int`, and \
                at an earlier call one of type `(x: (x: int | f64) ->? int) -> int`";
    assert!(built.contains(want), "{twice}: {built}");

    let pick = format!(
        "{head}pick(k: int) = if k > 1 {{ small }} else {{ big }};\ng = pick(k: 2);\na = pass(x: g);\n"
    );
    let report = match zedc::run::load(pick.as_bytes()) {
        Ok(_) => panic!("{pick}: accepted"),
        Err(e) => e.to_string(),
    };
    assert!(
        report.contains("the type the checker found for `pass` is"),
        "{pick}: {report}"
    );
    assert!(!report.contains("`(x: _) -> int`"), "{pick}: {report}");
    let want = "the type the checker found for `pass` is `(x: (x: int | f64) ->? int) -> int`";
    assert!(report.contains(want), "{pick}: {report}");

    // Passed to two parameters, the value fits both types: their meet. A partial function
    // whose domain lies in `int` fits `(x: int | f64) ->? int` too.
    let both = "apply(f: (x: int | f64) ->? int) = f(x: 2.5) else 6;\napply2(f: (x: int) ->? int) = f(x: 2) else 6;\nboth(x) = apply(f: x) + apply2(f: x);\na = both(x: 3);\n";
    let report = match zedc::run::load(both.as_bytes()) {
        Ok(_) => panic!("{both}: accepted"),
        Err(e) => e.to_string(),
    };
    let want = "the type the checker found for `both` is `(x: (x: int) ->? int) -> int`";
    assert!(report.contains(want), "{both}: {report}");
    // A use of another kind beside the pass, here `+`, restricts the carrier, and the type
    // printed is the meet of the two.
    let num = "takes(n: int | f64 | String) = 1;\nnum(x) = takes(n: x) + x;\nb = num(x: \"s\");\n";
    let report = match zedc::run::load(num.as_bytes()) {
        Ok(_) => panic!("{num}: accepted"),
        Err(e) => e.to_string(),
    };
    let want = "the type the checker found for `num` is `(x: int) -> int`";
    assert!(report.contains(want), "{num}: {report}");
}

/// Row TEST-arrow-lambda-stack-replay: a lambda passed at an intersection of function types
/// inside a generic function, `outer`, calls `outer`'s parameter `f` on its own parameter `g`.
/// That call is a need of `outer`, met at `outer(f: …)` once with `g` of each arrow's type,
/// after the lambda's body was checked, and it rebuilds `g` with a test of `int` and of `f64`.
/// Before the fix the lambda was no longer recorded then, and the refusal offered `x: (x: int |
/// f64) ->? int`, a parameter `g` does not have; it now names the lambda, as it does when the
/// refusal arises while the body is checked (`a_lambda_checked_at_each_arrow_is_rebuilt_once`),
/// and the repair it offers runs. The program stays refused.
#[test]
fn an_arrow_lambda_refused_through_a_call_s_needs_is_named() {
    let head = "small(x: int) = x + 1;\nsmall4(x: f64) = 2;\napply(f: (x: int | f64) ->? int) = f(x: 2.5) else 6;\npass(x) = apply(f: x);\n";
    let both = "both(h: ((g: (x: int) -> int) -> int) & ((g: (x: f64) -> int) -> int)) = h(g: small) + h(g: small4);\n";
    let split = "split(h1: (g: (x: int) -> int) -> int, h2: (g: (x: f64) -> int) -> int) = h1(g: small) + h2(g: small4);\n";
    for (call, f) in [("f(g)", "x -> pass(x: x)"), ("f(x: g)", "pass")] {
        let lam = format!("g -> ({call}, 1)[1]");
        let src = format!("{head}{both}outer(f) = both(h: {lam});\na = outer(f: {f});\n");
        let want = format!(
            "`{lam}` is passed as `((g: (x: int) -> int) -> int) & ((g: (x: f64) -> int) -> \
             int)` and rebuilds `g` in another way at each arrow. Try `{lam}` once at each arrow \
             instead, as arguments of types `(g: (x: int) -> int) -> int` and `(g: (x: f64) -> \
             int) -> int`. [g]"
        );
        assert_eq!(type_errors(&src), [want], "{src}");
        // The repair offered: the lambda passed once at each arrow.
        let fixed =
            format!("{head}{split}outer(f) = split(h1: {lam}, h2: {lam});\na = outer(f: {f});\n");
        runs_to(&fixed, "a", "2");
    }
}

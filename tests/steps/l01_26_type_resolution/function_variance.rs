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

/// A call through a value passes its arguments as written, and the function the value holds
/// places them by its own parameter list and fills each parameter left out with its own
/// default (DESIGN.md sec:values_morphisms, "The function called places the arguments"; row
/// CALL-callee-places): a union of functions, or a generic body met at two calls with
/// different functions, whose parameters lie in different places, number differently or have
/// different defaults, gives the value of the function the call reaches, never another one's
/// default (row FAIL-call-through-functions-differing-places).
#[test]
fn a_call_through_functions_differing_in_places_or_defaults_runs() {
    let reordered = "f(a: int, b: int) = a - b;\ng(b: int, a: int) = a * 10 + b;\n";
    let pick = "pick(c: bool) = if c { f } else { g };\nh = pick(c: false);\n";
    runs_to(&format!("{reordered}{pick}a = h(a: 5, b: 2);\n"), "a", "52");
    runs_to(
        &format!("{reordered}call(k) = k(a: 5, b: 2);\na = call(k: f) * 100 + call(k: g);\n"),
        "a",
        "352",
    );
    let defaults = "f(x: int, y: int = 1) = x + y;\ng(x: int, y: int = 2) = x * y;\n";
    runs_to(&format!("{defaults}{pick}a = h(x: 3);\n"), "a", "6");
    runs_to(
        &format!("{defaults}call(k) = k(x: 3);\na = call(k: f) * 100 + call(k: g);\n"),
        "a",
        "406",
    );
    runs_to(
        &format!("f(x: int, y: int = 1) = x + y;\ng(x: int) = x * 7;\n{pick}a = h(x: 3);\n"),
        "a",
        "21",
    );
    runs_to(
        &format!(
            "f(x: int, y: int = 1) = x + y;\ng(x: int, y: int = 1) = x * y;\n{pick}a = h(x: 3);\n"
        ),
        "a",
        "3",
    );
}

/// The value of `name` in `src` from native code, which calls the kernel for no node: as
/// [`runs_to`], and the run's `kernel_calls` is 0. Gives the run's `placed_calls`.
fn runs_natively_to(src: &str, name: &str, want: &str) -> u64 {
    use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};
    use zed_tests::step_helpers::l01_36_cranelift::native;
    runs_to(src, name, want);
    let u = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let t = with_prelude(u.get(name).expect("checked by runs_to"));
    let o = native(&t).unwrap_or_else(|e| panic!("{src}: {e}"));
    assert_eq!(o.kernel_calls, 0, "native code called the kernel: {src}");
    assert_eq!(o.value.to_string(), want, "native code's value: {src}");
    o.placed_calls
}

/// The calls of [`a_call_through_functions_differing_in_places_or_defaults_runs`] and of the
/// curried calls below run in native code with no call of the kernel: the function value
/// carries its parameter list, and the call places its arguments by a merge of the two sorted
/// lists in the runtime, O(p + a), then calls the function's entry (row
/// CALL-callee-places-native). Before, each `place` and each call by name ran in the kernel.
#[test]
fn a_call_its_function_places_runs_in_native_code_alone() {
    let reordered = "f(a: int, b: int) = a - b;\ng(b: int, a: int) = a * 10 + b;\n";
    let pick = "pick(c: bool) = if c { f } else { g };\nh = pick(c: false);\n";
    runs_natively_to(&format!("{reordered}{pick}a = h(a: 5, b: 2);\n"), "a", "52");
    runs_natively_to(
        &format!("{reordered}call(k) = k(a: 5, b: 2);\na = call(k: f) * 100 + call(k: g);\n"),
        "a",
        "352",
    );
    let defaults = "f(x: int, y: int = 1) = x + y;\ng(x: int, y: int = 2) = x * y;\n";
    runs_natively_to(&format!("{defaults}{pick}a = h(x: 3);\n"), "a", "6");
    runs_natively_to(&format!("{defaults}{pick}a = h(y: 4, x: 3);\n"), "a", "12");
    runs_natively_to(
        &format!("{defaults}call(k) = k(x: 3);\na = call(k: f) * 100 + call(k: g);\n"),
        "a",
        "406",
    );
    runs_natively_to(
        &format!("f(x: int, y: int = 1) = x + y;\ng(x: int) = x * 7;\n{pick}a = h(x: 3);\n"),
        "a",
        "21",
    );
    runs_natively_to(
        "g(x: int, y: int = x) = x + y;\nk = g;\nm = [k, k];\na = m[0](x: 3) + m[1](x: 4, y: 1);\n",
        "a",
        "11",
    );
    runs_natively_to(
        &format!("{reordered}{pick}p = h(a: 5, ...);\na = p(b: 2);\n"),
        "a",
        "52",
    );
    runs_natively_to(
        &format!("{defaults}{pick}p = h(x: 3, ...);\na = p() * 100 + p(y: 5);\n"),
        "a",
        "615",
    );
}

/// A call by name that runs again through the same list goes straight to the placed entry of
/// the function's lambda, which reads each argument where the call site stored it (row
/// CALL-callee-places-native): `k0`'s call runs four times, the first merging the names, so
/// the run's `placed_calls`, counted by the entry, is 3 (row CALL-direct-buffer-proof); `q`,
/// the function `u` itself and not a closure a `place` made, takes no placed entry. The
/// arguments include a function, a cell whose count the entry raises for the body (a list
/// would run in the kernel), and the closure reads what it captures.
#[test]
fn a_repeated_placed_call_runs_in_native_code_through_its_placed_entry() {
    let pick = "pick(c: bool) = if c { f } else { g };\nh = pick(c: false);\n";
    let ks = "k1(z: int) = k0(z: z) + k0(z: z + 1);\nk2(z: int) = k1(z: z) + k1(z: z + 2);\na = k2(z: 0);\n";
    let placed = runs_natively_to(
        &format!(
            "u(x: int) = x + 1;\nf(q, b: int) = q(x: b) - 1;\ng(b: int, q) = q(x: b) * 10;\n{pick}k0(z: int) = h(q: u, b: z);\n{ks}"
        ),
        "a",
        "100",
    );
    assert_eq!(placed, 3, "calls through a placed entry");
    let placed = runs_natively_to(
        &format!(
            "pick(c: bool, d: int) = {{\n  f(a: int, b: int) = a - b + d;\n  g(b: int, a: int) = a * 10 + b + d;\n  if c {{ f }} else {{ g }}\n}};\nh = pick(c: false, d: 100);\nk0(z: int) = h(a: z, b: 2);\n{ks}"
        ),
        "a",
        "468",
    );
    assert_eq!(placed, 3, "calls through a placed entry");
}

/// A call through a value that leaves out a parameter whose default reads an earlier
/// parameter, or a name the function holds, gets the value the call by the function's name
/// gives: the function fills the default in the scope of its declaration (row
/// FAIL-call-through-value-open-default). Named arguments in another order than the
/// parameters, and a value held in a list, are placed the same way.
#[test]
fn a_call_through_a_value_fills_a_default_that_reads_a_parameter_or_a_held_name() {
    let reads_x = "g(x: int, y: int = x) = x + y;\n";
    runs_to(&format!("{reads_x}k = g;\na = k(x: 3);\n"), "a", "6");
    runs_to(
        &format!(
            "{reads_x}pick(c: bool) = if c {{ g }} else {{ g }};\nh = pick(c: false);\na = h(x: 3);\n"
        ),
        "a",
        "6",
    );
    runs_to(
        &format!("{reads_x}call(k) = k(x: 3);\na = call(k: g);\n"),
        "a",
        "6",
    );
    runs_to(
        "mk(k: int) = {\n  g(x: int, y: int = k) = x + y;\n  return g;\n};\nh = mk(k: 10);\na = h(x: 1);\n",
        "a",
        "11",
    );
    runs_to(
        "tax(price, rate = price / 10.0) = price * rate;\nt = tax;\ny = t(price: 10.0);\n",
        "y",
        "10.0",
    );
    runs_to(&format!("{reads_x}k = g;\na = k(y: 1, x: 3);\n"), "a", "4");
    runs_to(
        &format!("{reads_x}k = g;\nm = [k, k];\na = m[0](x: 3) + m[1](x: 4, y: 1);\n"),
        "a",
        "11",
    );
}

/// A function with a default that reads a parameter, used as a value inside its own cycle and
/// called through it with that default left out, is recursion, and "Before step L6.4 the
/// recursion is rejected as recursion" (DESIGN.md sec:checking_in_zed, the example "Mutual
/// recursion"): the checker refuses each program as recursion, before the elaborator
/// would build the value's defaults (`Elab::placed_value`). From step L6.4 they run, to 8, 8
/// and 4 (row CALL-placed-value-recursive, its programs carried into row SCHED-scc-unit).
#[test]
fn a_function_used_as_a_value_in_its_own_cycle_is_refused_as_recursion() {
    let not_yet = "which is recursion: recursion is not supported by this version of zedc.";
    let apply = "apply(k, v: int) = k(x: v);\n";
    let g1 = "g(x: int, y: int = x) = if x > 3 { x + y } else { apply(k: g, v: x + 1) };";
    assert_eq!(
        type_errors(&format!("{g1}\n{apply}a = apply(k: g, v: 1);\n")),
        [format!(
            "`g` is defined in terms of itself, {not_yet} [{g1}]"
        )]
    );
    let g2 = "g(x: int, y: int = x) = if x > 3 { x + y } else { h(v: x + 1) };";
    assert_eq!(
        type_errors(&format!(
            "{g2}\nh(v: int) = apply(k: g, v: v);\n{apply}a = h(v: 1);\n"
        )),
        [format!(
            "`g`, `h` are defined in terms of each other, {not_yet} [{g2}]"
        )]
    );
    let f3 = "f(x: int, y: int = x) = if x > 3 { x } else { apply(k: f, v: x + 1) + apply(k: g, v: 0) };";
    assert_eq!(
        type_errors(&format!(
            "g(x: int, y: int = x) = x + y;\n{f3}\n{apply}a = f(x: 1);\n"
        )),
        [format!(
            "`f` is defined in terms of itself, {not_yet} [{f3}]"
        )]
    );
}

/// A curried call (`...`) through a value is the function of the named parameters that the
/// function held leaves out, with that function's defaults (DESIGN.md sec:values_morphisms,
/// "The function called places the arguments"; row CALL-curried-placed): where the functions
/// the value may be take the parameters in different places, the curried call and the calls of
/// its result give what the calls by the functions' names give.
#[test]
fn a_curried_call_through_functions_differing_in_places_runs() {
    let reordered = "f(a: int, b: int) = a - b;\ng(b: int, a: int) = a * 10 + b;\n";
    let pick = "pick(c: bool) = if c { f } else { g };\nh = pick(c: false);\n";
    runs_to(
        &format!("{reordered}{pick}p = h(a: 5, ...);\na = p(b: 2);\n"),
        "a",
        "52",
    );
    runs_to(
        &format!("{reordered}call(k) = k(a: 5, ...)(b: 2);\na = call(k: f) * 100 + call(k: g);\n"),
        "a",
        "352",
    );
    // The parameters left out lie in different places, though the one given does not.
    runs_to(
        "f(a: int, b: int, c: int) = a * 100 + b * 10 + c;\ng(a: int, c: int, b: int) = a + b * 1000 + c * 10000;\npick(c: bool) = if c { f } else { g };\nh = pick(c: false);\np = h(a: 1, ...);\na = p(c: 3, b: 2);\n",
        "a",
        "32001",
    );
    // The functions take different numbers of parameters: `g` fills `c` with its default.
    runs_to(
        &format!(
            "f(a: int, b: int) = a - b;\ng(b: int, a: int, c: int = 7) = a * 10 + b + c * 100;\n{pick}p = h(a: 5, ...);\na = p(b: 2);\n"
        ),
        "a",
        "752",
    );
}

/// The function a curried call through a value gives keeps the defaults of the function held:
/// a call of it that leaves a parameter out gets that function's default, one that reads an
/// earlier parameter or differs between the functions the value may be too (row
/// CALL-curried-placed).
#[test]
fn a_curried_call_through_a_value_keeps_the_held_function_s_defaults() {
    let defaults = "f(x: int, y: int = 1) = x + y;\ng(x: int, y: int = 2) = x * y;\n";
    let pick = "pick(c: bool) = if c { f } else { g };\nh = pick(c: false);\n";
    runs_to(
        &format!("{defaults}{pick}p = h(x: 3, ...);\na = p() * 100 + p(y: 5);\n"),
        "a",
        "615",
    );
    runs_to(
        &format!("{defaults}cur(k) = k(x: 3, ...)();\na = cur(k: f) * 100 + cur(k: g);\n"),
        "a",
        "406",
    );
    let reads_x = "g(x: int, y: int = x) = x + y;\n";
    runs_to(
        &format!("{reads_x}k = g;\np = k(x: 3, ...);\na = p() * 100 + p(y: 1);\n"),
        "a",
        "604",
    );
    runs_to(
        &format!("{reads_x}cur(k) = k(x: 3, ...);\na = cur(k: g)();\n"),
        "a",
        "6",
    );
}

/// A curried call of a generic body met with a function that has no default for the
/// parameter left out, and with two that have different defaults for it: which function the
/// checker meets first changes which calls are placed (`unaligned` in walk.rs), and neither
/// order changes what runs. The curried result is called with the parameter given, so each
/// function runs on its own `y`; a call of a result that leaves it out is refused while the
/// function with no default is among those the value may hold.
#[test]
fn functions_with_and_without_a_default_curried_alike_run_in_either_order() {
    let three = "f(x: int, y: int) = x + y;\ng(x: int, y: int = 1) = x * y;\n\
                 h(x: int, y: int = 2) = x + y + 10;\n";
    let fns = format!("{three}cur(k) = k(x: 3, ...)(y: 5);\n");
    runs_to(
        &format!("{fns}a = cur(k: f) * 10000 + cur(k: g) * 100 + cur(k: h);\n"),
        "a",
        "81518",
    );
    runs_to(
        &format!("{fns}a = cur(k: g) * 100 + cur(k: h) + cur(k: f) * 10000;\n"),
        "a",
        "81518",
    );
    runs_to(
        &format!("{fns}a = cur(k: h) + cur(k: g) * 100 + cur(k: f) * 10000;\n"),
        "a",
        "81518",
    );
    let pick = "pick(c: int) = if c == 0 { f } else if c == 1 { g } else { h };\n";
    runs_to(
        &format!("{three}{pick}p = pick(c: 1)(x: 3, ...);\na = p(y: 5);\n"),
        "a",
        "15",
    );
    rejected(&format!(
        "{three}{pick}p = pick(c: 1)(x: 3, ...);\na = p();\n"
    ));
}

/// The function a curried call gives, through a declared function or through a value whose
/// functions take the arguments alike, may itself reach a call that its function places,
/// beside one that takes the parameters left out in another order; it carries its own list
/// there, with the defaults of the function it calls (row CALL-curried-placed). Before, it was
/// a lambda with no list, and the run stopped: "a function value without a parameter list was
/// called with named arguments".
#[test]
fn a_curried_call_s_result_reaches_a_call_its_function_places() {
    let fg = "f(a: int, b: int, c: int) = a * 100 + b * 10 + c;\ng(c: int, b: int, a: int) = a + b * 1000 + c * 10000;\n";
    let declared = "pick(k: bool) = if k { f(a: 1, ...) } else { g(a: 1, ...) };\n";
    let through =
        "app(k) = k(a: 1, ...);\npick(k: bool) = if k { app(k: f) } else { g(a: 1, ...) };\n";
    for (pick, k, want) in [
        (declared, "false", "32001"),
        (declared, "true", "123"),
        (through, "true", "123"),
        (through, "false", "32001"),
    ] {
        let src = format!("{fg}{pick}h = pick(k: {k});\na = h(c: 3, b: 2);\n");
        runs_to(&src, "a", want);
    }
    let defaults = "f(a: int, b: int, c: int = 4) = a * 100 + b * 10 + c;\ng(c: int = 5, b: int, a: int) = a + b * 1000 + c * 10000;\n";
    for (k, want) in [("false", "52001"), ("true", "124")] {
        let src = format!("{defaults}{declared}h = pick(k: {k});\na = h(b: 2);\n");
        runs_to(&src, "a", want);
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

/// A generic function whose body makes a curried call through its parameter runs for every
/// function its calls pass, whatever places each takes the parameters in, and whatever order
/// the checker meets the calls in, which follows what each definition uses and not the text
/// (rows TEST-call-site-need-key, CALL-curried-placed). Each program gives the same answer
/// checked alone, after the others, and after the others in reverse order.
#[test]
fn a_generic_curried_call_runs_in_any_order_of_the_text() {
    let head = "f(a: int, b: int) = a - b;\nf2(a: int, b: int) = a + b;\ng(b: int, a: int) = a * 10 + b;\ncall(k) = k(a: 5, ...)(b: 2);\n";
    // The rest of the program, a name it defines, and that name's value: `call(k: f)` is 3,
    // `call(k: f2)` 7 and `call(k: g)` 52.
    let cases: [(&str, &str, &str); 8] = [
        (
            "x = call(k: f);\ny = call(k: g);\nz = call(k: f2);\n",
            "y",
            "52",
        ),
        (
            "x = call(k: g);\ny = call(k: f);\nz = call(k: f2);\n",
            "z",
            "7",
        ),
        ("y = x + call(k: g);\nx = call(k: f);\n", "y", "55"),
        ("x = call(k: f);\ny = x + call(k: g);\n", "y", "55"),
        (
            "v() = u() + call(k: f);\nu() = call(k: g);\nw = v();\n",
            "w",
            "55",
        ),
        ("a = call(k: g) * 100 + call(k: f);\n", "a", "5203"),
        (
            "z = y + call(k: f2);\ny = x + call(k: g);\nx = call(k: f);\n",
            "z",
            "62",
        ),
        (
            "z = y + call(k: g);\ny = x + call(k: f2);\nx = call(k: f);\n",
            "z",
            "62",
        ),
    ];
    let srcs: Vec<String> = cases.iter().map(|c| format!("{head}{}", c.0)).collect();
    for (src, (_, name, want)) in srcs.iter().zip(&cases) {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        runs_to(src, name, want);
    }
    // A program to run needs a `main`.
    let answer = |src: &str| {
        let src = format!("{src}main(m: MainArgs) {{ m.stdout <- \"hello\"; }}\n");
        zedc::run::load(src.as_bytes()).err()
    };
    let alone: Vec<Option<String>> = (srcs.iter().cloned())
        .map(|src| std::thread::spawn(move || answer(&src)).join().unwrap())
        .collect();
    let batch: Vec<Option<String>> = srcs.iter().map(|src| answer(src)).collect();
    let mut reversed: Vec<Option<String>> = srcs.iter().rev().map(|src| answer(src)).collect();
    reversed.reverse();
    assert_eq!(alone, batch, "alone, then in a batch");
    assert_eq!(alone, reversed, "alone, then in a reversed batch");
    assert!(alone.iter().all(Option::is_none), "{alone:?}");
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

/// The value of `name` in `src` from the reference evaluator, which native code agrees with.
fn value_of(src: &str, name: &str) -> String {
    use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};
    use zed_tests::step_helpers::l01_36_cranelift::{kernel, native};
    let u = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let t = with_prelude(
        u.get(name)
            .unwrap_or_else(|| panic!("no definition `{name}`")),
    );
    let k = kernel(&t).map(|v| v.to_string());
    let n = native(&t).map(|o| o.value.to_string());
    assert_eq!(k, n, "reference evaluator against native code: {src}");
    k.unwrap_or_else(|e| panic!("{src}: {e:?}"))
}

/// What the checker records at each span inside `src[at..at + len]`, by its distance from
/// `at`: the adopted values, the carriers followed, the witnesses, the quotients of `*`, and
/// the warnings; each as text, sorted.
fn records_in(info: &zedc::check::Info, at: usize, len: usize) -> Vec<String> {
    let inside = |s: &zedc::lex::Span| s.start >= at && s.end <= at + len;
    let rel = |s: &zedc::lex::Span| (s.start - at, s.end - at);
    let mut out: Vec<String> = Vec::new();
    out.extend(
        (info.adopt.iter())
            .filter(|(s, _)| inside(s))
            .map(|(s, v)| format!("adopt {:?} {v:?}", rel(s))),
    );
    out.extend(
        (info.follows.iter())
            .filter(|(s, _)| inside(s))
            .map(|(s, v)| format!("follows {:?} {v:?}", rel(s))),
    );
    out.extend(
        (info.witness.iter())
            .filter(|(s, _)| inside(s))
            .map(|(s, v)| format!("witness {:?} {v:?}", rel(s))),
    );
    out.extend(
        (info.quotients.iter())
            .filter(|(s, _)| inside(s))
            .map(|(s, v)| format!("quotient {:?} {v}", rel(s))),
    );
    out.extend(
        (info.warnings.iter())
            .filter(|e| inside(&e.span))
            .map(|e| format!("warning {:?} {}", rel(&e.span), e.message)),
    );
    out.sort_unstable();
    out
}

/// Remaps whose key computes from the remap's own binders (`k + 1`, `v * 2`), folded levels
/// `><` among them, written alike in one generic body are one use of the parameter, checked
/// once at each call (row FAIL-remap-computed-key-need-site-product). Each still runs as it
/// would alone, at `int` and at `f64`, and has at its own key the records it would have had
/// alone: those of the same remap in a body that holds only it.
#[test]
fn remaps_alike_with_computed_keys_run_and_record_as_each_alone() {
    // Literals in keys meet `k`, an `int` at every call, or `v` at `int` and at `f64`: a key
    // such as `v * 2`, or a value `v / 2` (at `f64` alone, as `/` takes no two `int`s), follows
    // the carrier of `v` at run time (row
    // FAIL-remap-key-literal-f64). A folded level is checked at one carrier per program: a fold
    // whose empty level folds to one identity at `int` and another at `f64` is not compiled
    // yet at two carriers.
    let two = ["t: [1, 2, 3]", "t: [0.5, 1.5, 2.5]"];
    let ints = ["t: [1, 2, 3]", "t: [4, 5, 6, 7]"];
    let floats = ["t: [0.5, 1.5, 2.5]", "t: [4.0]"];
    let cases = [
        ("(t as (k -> v) into (k + 1 -> v))", two),
        ("(t as (k -> v) into (k * 3 - 1 -> v))", two),
        ("(t as (k -> v) into (k mod 2 -> k >< (+) -> v))", ints),
        ("(t as (k -> v) into (k mod 2 -> k >< (+) -> v))", floats),
        ("(t as (k -> v) into (-k + 10 -> k * 2 >< (*) -> v))", ints),
        (
            "(t as (k -> v) into (-k + 10 -> k * 2 >< (*) -> v))",
            floats,
        ),
        ("(t as (k -> v) into (v * 2 -> k))", two),
        ("(t as (k -> v) into (k -> v / 2))", floats),
        (
            "(t as (k -> v) into (k div 2 -> k + 1 >< (+) -> v))",
            floats,
        ),
    ];
    for (r, args) in cases {
        let many = format!(
            "many(t) = ({r}, {r});\na = (many({}), many({}));\n",
            args[0], args[1]
        );
        let one = format!(
            "one(t) = {r};\na = ((one({0}), one({0})), (one({1}), one({1})));\n",
            args[0], args[1]
        );
        let want = value_of(&one, "a");
        assert_eq!(value_of(&many, "a"), want, "{many}");
        let (mi, _) = super::info(&many);
        let (oi, _) = super::info(&one);
        assert_eq!(mi.errors.len(), 0, "{many}: {:?}", mi.errors);
        let alone = records_in(&oi, one.find(r).expect("the remap is in `one`"), r.len());
        let first = many.find(r).expect("the remap is in `many`");
        let second = first + r.len() + 2;
        assert_eq!(&many[second..second + r.len()], r);
        assert_eq!(
            records_in(&mi, first, r.len()),
            alone,
            "the first remap of {many}"
        );
        assert_eq!(
            records_in(&mi, second, r.len()),
            alone,
            "the second remap of {many}"
        );
    }
}

/// A number literal in a remap's `into` pattern that meets a binder of type `f64`, in a key or
/// in a value, is read as an `f64`, as `2.0` written out is, at one call, and where `int` is
/// taken too, at calls at `int` and at `f64` as at each alone (row FAIL-remap-key-literal-f64).
/// `/` takes no two `int`s, so `v / 2` is called at `f64` alone.
#[test]
fn a_literal_in_a_remap_pattern_meets_an_f64_binder() {
    runs_to(
        "one(t) = (t as (k -> v) into (v * 2 -> k));\na = one(t: [0.5, 1.5]);\n",
        "a",
        "{1.0 -> {0}, 3.0 -> {1}}",
    );
    runs_to(
        "one(t) = (t as (k -> v) into (k -> v / 2));\na = one(t: [0.5, 1.5]);\n",
        "a",
        "{0 -> 0.25, 1 -> 0.75}",
    );
    for (r, int_too) in [
        ("(t as (k -> v) into (v * 2 -> k))", true),
        ("(t as (k -> v) into (k -> 1 + v * 2))", true),
        ("(t as (k -> v) into (k -> v / 2))", false),
        (
            "(t as (k -> v) into (k div 2 -> k + 1 >< (+) -> v / 2))",
            false,
        ),
    ] {
        let floats = format!("one(t) = {r};\na = one(t: [0.5, 1.5, 2.5]);\n");
        let written = floats.replace(" 2 ->", " 2.0 ->").replace(" 2)", " 2.0)");
        let written = written.replace("div 2.0", "div 2");
        assert_ne!(floats, written);
        assert_eq!(value_of(&floats, "a"), value_of(&written, "a"), "{floats}");
        if !int_too {
            continue;
        }
        let both = format!("one(t) = {r};\na = (one(t: [0.5, 1.5]), one(t: [1, 2]));\n");
        let apart = format!(
            "oneF(t) = {r};\noneI(t) = {r};\na = (oneF(t: [0.5, 1.5]), oneI(t: [1, 2]));\n"
        );
        assert_eq!(value_of(&both, "a"), value_of(&apart, "a"), "{both}");
    }
}

/// A key that computes and is refused at a call is refused at each remap written alike, each
/// at its own span, with the message it has alone (`k div 2` folds two entries to one key).
#[test]
fn remaps_alike_with_a_refused_computed_key_each_report() {
    let r = "(t as (k -> v) into (k div 2 -> v))";
    let many = format!("many(t) = ({r}, {r});\na = many(t: [1, 2, 3]);\n");
    let one = format!("one(t) = {r};\na = one(t: [1, 2, 3]);\n");
    let (mi, _) = super::info(&many);
    let (oi, _) = super::info(&one);
    assert_eq!(oi.errors.len(), 1, "{one}: {:?}", oi.errors);
    let at = one.find(r).expect("the remap is in `one`");
    let rel = |s: &zedc::lex::Span, base: usize| (s.start - base, s.end - base);
    let want = (rel(&oi.errors[0].span, at), oi.errors[0].message.clone());
    let first = many.find(r).expect("the remap is in `many`");
    let second = first + r.len() + 2;
    let mut got: Vec<_> = (mi.errors.iter())
        .map(|e| {
            let base = if e.span.start >= second {
                second
            } else {
                first
            };
            (base, rel(&e.span, base), e.message.clone())
        })
        .collect();
    got.sort();
    assert_eq!(
        got,
        [
            (first, want.0, want.1.clone()),
            (second, want.0, want.1.clone())
        ],
        "{many}"
    );
}

/// A computed key that reads a name bound outside the remap is not paired, since a test around
/// one remap may narrow that name and not the other: each is checked on its own, and runs.
#[test]
fn remaps_reading_an_outer_name_in_their_key_run() {
    let r = "(t as (k -> v) into (k + j -> k -> v))";
    let many = format!(
        "many(t, j) = ({r}, if j > 0 {{ {r} }} else {{ {r} }});\na = (many(t: [1, 2], j: 1), many(t: [0.5], j: 0));\n"
    );
    let one = format!(
        "one(t, j) = {r};\na = ((one(t: [1, 2], j: 1), one(t: [1, 2], j: 1)), (one(t: [0.5], j: 0), one(t: [0.5], j: 0)));\n"
    );
    assert_eq!(value_of(&many, "a"), value_of(&one, "a"), "{many}");
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

/// A body whose remaps alike take a source that is not a family gives one error at each remap,
/// as it would with each remap alone: called directly, and called through a generic function in
/// between, where the need of the remap the signature kept is made again on the class of the
/// function around and must carry the remaps left out with it (rows FAIL-remap-need-site-product
/// and PROOF-need-site-read-only).
#[test]
fn remaps_alike_each_give_their_error_through_a_generic_function_between() {
    let body = "many(t) = (t as (k -> v) into (v -> k)).count + (t as (k -> v) into (v -> k)).count \
                + (t as (k -> v) into (v -> k)).count;\n";
    let sources: Vec<usize> = body.match_indices("t as").map(|(at, _)| at).collect();
    assert_eq!(sources.len(), 3);
    for rest in [
        "x = many(t: 5);\n",
        "mid(u) = many(t: u);\nx = mid(u: 5);\n",
        "mid(u) = many(t: u);\nouter(w) = mid(u: w);\nx = outer(w: 5);\n",
    ] {
        let src = format!("{body}{rest}");
        let (info, _) = super::info(&src);
        let mut at: Vec<usize> = info.errors.iter().map(|e| e.span.start).collect();
        at.sort();
        assert_eq!(at, sources, "{src}: {:?}", info.errors);
        assert!(
            (info.errors.iter()).all(|e| e.message.contains("its source `t` is 5")),
            "{src}: {:?}",
            info.errors
        );
    }
}

/// A body whose brackets alike are given two meanings by two calls, a function of 2 parameters
/// at one and a tuple at the other, gives at the later call the error a body with one such
/// bracket gives, once for each bracket, each with its note at its own bracket, in either
/// order of the calls (row PROOF-need-site-read-only: the meaning an earlier call gave a
/// bracket is recorded at its site, and a bracket left out of the signature is checked again
/// at the site of the one kept, which holds what its own would).
#[test]
fn brackets_alike_given_two_meanings_each_give_their_error() {
    // Each error by the call it is at, its message, and where its notes are in the body.
    let errors = |body: &str, src: &str| -> Vec<(String, String, Vec<usize>)> {
        let (info, _) = super::info(src);
        let mut got: Vec<(String, String, Vec<usize>)> = (info.errors.iter())
            .map(|e| {
                let notes = (e.notes.iter())
                    .map(|n| n.span.start)
                    .filter(|&s| s < body.len())
                    .collect();
                (
                    src[e.span.start..e.span.end].to_string(),
                    e.message.clone(),
                    notes,
                )
            })
            .collect();
        got.sort();
        got
    };
    let g = "g(a, b) = a + b;\n";
    for calls in [
        "x = many(t: g);\ny = many(t: (5, 6));\n",
        "y = many(t: (5, 6));\nx = many(t: g);\n",
    ] {
        let (one_body, body) = ("many(t) = t[1];\n", "many(t) = (t[1], t[1]);\n");
        let one = errors(one_body, &format!("{one_body}{g}{calls}"));
        assert_eq!(one.len(), 1, "{calls}: {one:?}");
        // The note at the bracket (at 10 in the one-bracket body), and the one at the
        // definition (at 0).
        assert_eq!(one[0].2, [10, 0], "{one:?}");
        let mut want: Vec<(String, String, Vec<usize>)> = (body.match_indices("t[1]"))
            .map(|(b, _)| (one[0].0.clone(), one[0].1.clone(), vec![b, 0]))
            .collect();
        want.sort();
        let alike = format!("{body}{g}{calls}");
        assert_eq!(errors(body, &alike), want, "{alike}");
    }
}

/// A body whose brackets, folds or `.sum`s alike fail at a call gives the errors that body
/// would give with each use alone. Called directly: one error per use, with its note at that
/// use. Called through generic functions in between: one error per use too, each noting the
/// calls between and then its own use (row DIAG-call-chain-full: each left-out use carries its
/// own path; before it, each error noted the call in the function between and not the use, so
/// the errors were those of a body with one such use, PROOF-need-site-read-only).
#[test]
fn uses_alike_each_give_their_error_through_a_generic_function_between() {
    // Each error by its message and the places of its span and notes: inside the body, the
    // place itself; after it, the place counted from the body's end, as `!` and that count.
    let errors = |body: &str, rest: &str| -> Vec<(String, String, Vec<String>)> {
        let src = format!("{body}{rest}");
        let (info, _) = super::info(&src);
        let place = |s: usize| match s.checked_sub(body.len()) {
            Some(after) => format!("!{after}"),
            None => s.to_string(),
        };
        let mut got: Vec<_> = (info.errors.iter())
            .map(|e| {
                let notes = e.notes.iter().map(|n| place(n.span.start)).collect();
                (place(e.span.start), e.message.clone(), notes)
            })
            .collect();
        got.sort();
        got
    };
    for (one, body, use_text) in [
        (
            "many(t) = t[2];\n",
            "many(t) = t[2] * 10 + t[2] * 100 + t[2];\n",
            "t[2]",
        ),
        (
            "many(t) = t >< (+);\n",
            "many(t) = (t >< (+)) * 10 + (t >< (+)) * 100 + (t >< (+));\n",
            "(t >< (+))",
        ),
        (
            "many(t) = t.sum;\n",
            "many(t) = t.sum * 10 + t.sum * 100 + t.sum;\n",
            "t.sum",
        ),
    ] {
        let direct = "x = many(t: 5);\n";
        let got = errors(body, direct);
        let mut at: Vec<String> = got.iter().map(|(_, _, n)| n[0].clone()).collect();
        at.sort();
        let mut uses: Vec<String> = body
            .match_indices(use_text)
            .map(|(s, _)| s.to_string())
            .collect();
        uses.sort();
        assert_eq!(at, uses, "{body}{direct}: {got:?}");
        for between in [
            "mid(u) = many(t: u);\nx = mid(u: 5);\n",
            "mid(u) = many(t: u);\nouter(w) = mid(u: w);\nx = outer(w: 5);\n",
        ] {
            let alone = errors(one, between);
            assert_eq!(alone.len(), 1, "{one}{between}: {alone:?}");
            // The error alone, with each note inside its body moved by the same offset into
            // each use of `body`, as written there (with the parentheses `body` may put
            // around it, which the use's span takes in).
            let start = "many(t) = ".len();
            assert!(
                (alone[0].2.iter()).any(|p| p.parse::<usize>().is_ok()),
                "{one}{between}: the error notes the use: {alone:?}"
            );
            let mut want: Vec<_> = (body.match_indices(use_text))
                .map(|(u, _)| {
                    let (at, message, notes) = alone[0].clone();
                    let notes = (notes.into_iter())
                        .map(|p| match p.parse::<usize>() {
                            Ok(q) => (q - start + u).to_string(),
                            Err(_) => p,
                        })
                        .collect();
                    (at, message, notes)
                })
                .collect();
            want.sort();
            assert_eq!(errors(body, between), want, "{body}{between}");
        }
    }
}

/// The errors of `src`, whose first line is a body `body` of uses `use_text`: each by its place
/// and the places of its notes, a place in a use as `use<j>+<offset>` for the `j`-th use, the
/// definition's start as `def`, another place in the body as `body`, and a place after the body
/// as `!` and its distance from the body's end; with the text at the error and its message.
fn errors_by_use(
    body: &str,
    use_text: &str,
    src: &str,
) -> Vec<(String, String, String, Vec<String>)> {
    let (info, _) = super::info(src);
    let uses: Vec<usize> = body.match_indices(use_text).map(|(s, _)| s).collect();
    let place = |s: usize| match s.checked_sub(body.len()) {
        Some(after) => format!("!{after}"),
        None => match uses.iter().position(|&u| u <= s && s < u + use_text.len()) {
            Some(j) => format!("use{j}+{}", s - uses[j]),
            None if s == 0 => "def".to_string(),
            None => "body".to_string(),
        },
    };
    let mut got: Vec<_> = (info.errors.iter())
        .map(|e| {
            let notes = e.notes.iter().map(|n| place(n.span.start)).collect();
            let at = src[e.span.start..e.span.end].to_string();
            (place(e.span.start), at, e.message.clone(), notes)
        })
        .collect();
    got.sort();
    got
}

/// Whether `body`, whose uses `use_text` are alike, gives in `body` followed by `rest` the
/// errors `one`, a body of one such use, gives followed by `rest`: each error that is placed or
/// noted at the use once at each use of `body`, placed and noted at that use, and the other
/// errors as they are. `None` if so, else the program and the two lists of errors.
fn errors_as_each_alone(one: &str, body: &str, use_text: &str, rest: &str) -> Option<String> {
    let alone = errors_by_use(one, use_text, &format!("{one}{rest}"));
    let n = body.matches(use_text).count();
    let at_use = |e: &(String, String, String, Vec<String>)| {
        e.0.starts_with("use") || e.3.iter().any(|p| p.starts_with("use"))
    };
    let mut want: Vec<_> = (alone.iter())
        .flat_map(|e| {
            let copies = if at_use(e) { n } else { 1 };
            (0..copies).map(move |j| {
                let at = |p: &String| p.replacen("use0", &format!("use{j}"), 1);
                (
                    at(&e.0),
                    e.1.clone(),
                    e.2.clone(),
                    e.3.iter().map(at).collect(),
                )
            })
        })
        .collect();
    want.sort();
    let src = format!("{body}{rest}");
    let got = errors_by_use(body, use_text, &src);
    (got != want).then(|| format!("{src}\n  got:  {got:?}\n  want: {want:?}"))
}

/// Uses alike in one generic body, called at two calls whose arguments give the uses different
/// meanings or carriers, or make one of them fail, give in either order of the calls the errors
/// each use would give alone, at each use (row PROOF-need-site-read-only's claim that a check
/// at a later call reads back from a use's site only the meaning a bracket was given,
/// `Ck::bracket_meaning`, which `Ck::replay` gives a use left out; tested here for every kind
/// of use that is paired, at every pair of these arguments, directly and through a generic
/// function between).
#[test]
fn uses_alike_at_two_calls_give_the_errors_of_each_use_alone() {
    let args = [
        "g",
        "(5, 6)",
        "(5,)",
        "[1, 2]",
        "[0.5, 1.5]",
        "[]",
        "{1 -> 2}",
        "5",
        "\"s\"",
    ];
    let mut wrong = Vec::new();
    for use_text in [
        "t[1]",
        "(t >< (+))",
        "(t >< max)",
        "t.sum",
        "sum(t)",
        "t.count",
        "(t as (k -> v) into (v -> k)).count",
    ] {
        let one = format!("many(t) = {use_text};\n");
        let body = format!("many(t) = ({use_text}, {use_text}, {use_text});\n");
        for a in args {
            for b in args.iter().filter(|&&b| b != a) {
                for rest in [
                    format!("g(x, y) = x + y;\nx = many(t: {a});\ny = many(t: {b});\n"),
                    format!(
                        "g(x, y) = x + y;\nmid(u) = many(t: u);\nx = mid(u: {a});\ny = mid(u: {b});\n"
                    ),
                ] {
                    wrong.extend(errors_as_each_alone(&one, &body, use_text, &rest));
                }
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "{} programs:\n{}",
        wrong.len(),
        wrong.join("\n\n")
    );
}

/// `sum(t)` and `t.sum` in one generic body are one use (`AlikeSite::Sum` keys the receiver as
/// written, `t` for both), and each still gives its own error in its own words, and the value
/// each gives alone (the claim of commit bbdf92520 that pairing them at one site is safe).
#[test]
fn sum_of_t_and_t_sum_alike_each_keep_their_own_error_and_value() {
    for (first, second) in [("sum(t)", "t.sum"), ("t.sum", "sum(t)")] {
        let body = format!("many(t) = ({first}, {second});\n");
        for arg in ["5", "\"s\"", "(1, 2)", "g"] {
            for rest in [
                format!("g(x, y) = x + y;\nx = many(t: {arg});\n"),
                format!("g(x, y) = x + y;\nmid(u) = many(t: u);\nx = mid(u: {arg});\n"),
            ] {
                // The errors of each use alone, at its place in `body`, against the errors of
                // `body`: placed and noted at the uses by their order in `body`.
                let mut want = Vec::new();
                for (j, use_text) in [first, second].into_iter().enumerate() {
                    let one = format!("many(t) = {use_text};\n");
                    for e in errors_by_use(&one, use_text, &format!("{one}{rest}")) {
                        let at = |p: &String| p.replacen("use0", &format!("use{j}"), 1);
                        want.push((at(&e.0), e.1, e.2, e.3.iter().map(at).collect::<Vec<_>>()));
                    }
                }
                // An error placed and noted at no use, which both give alike, is one error of
                // `body`, as it is of a body of two uses alike written the same.
                zed_collections::sorted::sort_dedup(&mut want);
                // Each use's place, by its own text, since the two texts differ.
                let src = format!("{body}{rest}");
                let (info, _) = super::info(&src);
                let starts = [body.find(first).unwrap(), body.rfind(second).unwrap()];
                let lens = [first.len(), second.len()];
                let place = |s: usize| match s.checked_sub(body.len()) {
                    Some(after) => format!("!{after}"),
                    None => match (0..2).find(|&j| starts[j] <= s && s < starts[j] + lens[j]) {
                        Some(j) => format!("use{j}+{}", s - starts[j]),
                        None if s == 0 => "def".to_string(),
                        None => "body".to_string(),
                    },
                };
                let mut got: Vec<_> = (info.errors.iter())
                    .map(|e| {
                        let notes = e.notes.iter().map(|n| place(n.span.start)).collect();
                        let at = src[e.span.start..e.span.end].to_string();
                        (place(e.span.start), at, e.message.clone(), notes)
                    })
                    .collect();
                got.sort();
                assert_eq!(got, want, "{src}");
            }
        }
        for (arg, want) in [("[1, 2, 3]", "(6, 6)"), ("[0.5, 1.5]", "(2.0, 2.0)")] {
            runs_to(&format!("{body}a = many(t: {arg});\n"), "a", want);
        }
    }
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
/// bare name met before or after it), and the result of calling a parameter. Each is refused rather than run without a test of the domain; before the fix of
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
/// lambda inside `map`, is [`a_generic_function_called_from_a_map_lambda_misses_outside_the_domain`].
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

/// Row FAIL-partial-slot-generic-lambda-map: the generic function `pass`, called from a lambda
/// that `map` or `where` calls on each entry of a family of functions of one type, passes the
/// entry on to a partial slot; the entry lies at the receiver's entries, so the receiver is
/// rebuilt there, entry by entry, and the call misses outside the function's domain and calls
/// it inside. The receiver may be written there, or be an argument of a generic body. Before
/// the fix each was refused, soundly but needlessly, as from no argument of the call.
#[test]
fn a_generic_function_called_from_a_map_lambda_misses_outside_the_domain() {
    let head = |k: &str| {
        format!("small(x: int) = x + 1;\napply(f: (x: int | f64) ->? int) = f(x: {k}) else 6;\n")
    };
    let cases = [
        (
            "pass(x) = apply(f: x);\na = [small].map(g -> pass(x: g))[0];\n",
            "6",
            "4",
        ),
        (
            "pass(x) = apply(f: x);\na = [small, small].map(g -> pass(x: g))[1];\n",
            "6",
            "4",
        ),
        (
            "pass(x) = apply(f: x);\nh(m) = m.map(g -> pass(x: g))[0];\na = h(m: [small]);\n",
            "6",
            "4",
        ),
        (
            "pass(x) = apply(f: x);\na = [small].where(g -> pass(x: g) > 5).map(g -> 1)[0] else 0;\n",
            "1",
            "0",
        ),
    ];
    for (rest, miss, hit) in cases {
        runs_to(&format!("{}{rest}", head("2.5")), "a", miss);
        runs_to(&format!("{}{rest}", head("3")), "a", hit);
    }
}

/// Row FAIL-partial-slot-generic-lambda-map: a family whose entries are functions of two
/// types is not rebuilt entry by entry, as no one test of a domain fits both; a lambda of
/// `map` on it that passes its entry on to a partial slot stays refused, written there or as
/// the receiver of a generic body. A lambda that is not written at `map`, passed in as an
/// argument over a family of one function type, runs: it misses outside the domain, never
/// run on 2.5, and calls the function inside it (plan row TEST-map-param-lambda-partial-slot,
/// which found that it runs; this test accepted a refusal too until then).
#[test]
fn a_map_lambda_over_entries_of_two_function_types_is_refused_for_a_partial_slot() {
    let head = "small(x: int) = x + 1;\nbig(x: int | f64) = 1;\n\
                apply(f: (x: int | f64) ->? int) = f(x: 2.5) else 6;\npass(x) = apply(f: x);\n";
    let refused = [
        "a = [small, big].map(g -> pass(x: g))[0];\n",
        "h(m) = m.map(g -> pass(x: g))[0];\na = h(m: [small, big]);\n",
    ];
    for rest in refused {
        let src = format!("{head}{rest}");
        assert!(
            !type_errors(&src).is_empty(),
            "{src}: ran without a test of the domain"
        );
    }
    let rest = "h(m, k) = m.map(k)[0];\na = h(m: [small], k: g -> pass(x: g));\n\
                b = h(m: [small, small], k: g -> pass(x: g));\n";
    let src = format!("{head}{rest}");
    assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
    runs_to(&src, "a", "6");
    runs_to(&src, "b", "6");
    let src = format!("{}{rest}", head.replace("f(x: 2.5)", "f(x: 3)"));
    runs_to(&src, "a", "4");
    runs_to(&src, "b", "4");
}

/// A call through a parameter that names its arguments is built once for every function the
/// parameter takes (`Ck::record_call`); a second function there that takes another number of
/// parameters, one of them with a default, places the arguments itself and fills its default.
#[test]
fn a_named_call_through_a_parameter_of_two_differing_functions_runs() {
    let src = "one(x: int) = x;\ntwo(x: int, y: int = 1) = x + y;\nrun(g) = g(x: 1);\na = run(g: one) + run(g: two);\n";
    runs_to(src, "a", "3");
}

/// Row PROOF-generic-body-values-from-args, the cases of the proof that this zedc does not
/// support: each is refused before the checker reaches the call, so no rebuilding is put
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
        .filter(|(_, errors)| {
            !errors
                .iter()
                .any(|e| e.contains("not supported by this version of zedc"))
        })
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

/// The functions of the use-kind tests of row PROOF-reorder-forwarded-uses-complete: `re`
/// takes `y` first and `app2`'s slot takes `x` first. Called by name, `re(x: 1, y: 2)` is 12;
/// called with its arguments in each other's places it would be 21. The claim tested is that
/// [`Fit::Adapter`] put at `re` for `app2`'s slot (`Ck::reorder_forwarded`) is put only where
/// `Ck::note_fn_uses` saw every other use of the generic parameter, so a body that also uses
/// it in any other way is refused and never runs with its arguments swapped.
const REORDER_HEAD: &str =
    "re(y: int, x: int) = x * 10 + y;\napp2(f: (x: int, y: int) -> int) = f(x: 1, y: 2);\n";

/// Each of `rests`, after [`REORDER_HEAD`], is refused with exactly one error for the order of
/// `re`'s parameters, and that error gives the reason `why`.
fn reorder_refused(rests: &[&str], why: &str) {
    for rest in rests {
        let src = format!("{REORDER_HEAD}{rest}");
        let errors = type_errors(&src);
        let order: Vec<_> = (errors.iter())
            .filter(|e| e.contains("with its parameters in another order"))
            .collect();
        assert_eq!(order.len(), 1, "{src}: {errors:?}");
        assert!(order[0].contains(why), "{src}: {errors:?}");
    }
}

/// Row PROOF-reorder-forwarded-uses-complete, use by a call: a body that calls the parameter
/// in its own order, directly, through a partial application, through a generic callee,
/// after passing it to a generic forwarder, through a local name, or after taking it back out
/// of a tuple, is refused.
#[test]
fn a_reordered_function_the_generic_body_also_calls_is_refused() {
    reorder_refused(
        &[
            "pass(g) = app2(f: g) + g(y: 2, x: 1);\na = pass(g: re);\n",
            "pass(g) = app2(f: g) + g(y: 2, ...)(x: 1);\na = pass(g: re);\n",
            "callit(h) = h(y: 2, x: 1);\npass(g) = app2(f: g) + callit(h: g);\na = pass(g: re);\n",
            "fwd(h) = app2(f: h);\npass(g) = fwd(h: g) + g(y: 2, x: 1);\na = pass(g: re);\n",
            "pass(g) = { h = g; app2(f: h) + g(y: 2, x: 1) };\na = pass(g: re);\n",
            "pass(g) = app2(f: (g, 0)[0]) + g(y: 2, x: 1);\na = pass(g: re);\n",
        ],
        "also uses it in its own order",
    );
}

/// Row PROOF-reorder-forwarded-uses-complete, use by passing it on: a body that also passes
/// the parameter to a slot in its own order, directly or through a generic forwarder, is
/// refused.
#[test]
fn a_reordered_function_the_generic_body_also_passes_on_in_another_order_is_refused() {
    let own = "own(f: (y: int, x: int) -> int) = f(y: 2, x: 1);\n";
    reorder_refused(
        &[
            &format!("{own}pass(g) = app2(f: g) + own(f: g);\na = pass(g: re);\n"),
            &format!(
                "{own}fwd(h) = own(f: h);\npass(g) = app2(f: g) + fwd(h: g);\na = pass(g: re);\n"
            ),
        ],
        "also passes it on as `(y: int, x: int) -> int`, in that order",
    );
}

/// Row FAIL-reorder-union-slot (proofdoc4d, reading 516e1324a): a body that also passes the
/// parameter into a slot whose type holds a function of the other order beside an atom, or
/// beside another function type, is refused as one that passes it on into one function type
/// is. Before the fix `Ck::reorder_forwarded` searched only the slots that are one function
/// type alone (`only_fn`), so it put the adapter for `app2` and `app3` called `re` with its
/// arguments swapped: `a` ran to 33 where a call by name gives 24.
#[test]
fn a_reordered_function_the_generic_body_also_passes_into_a_union_slot_is_refused() {
    let app3 = "app3(k: ((y: int, x: int) -> int) | #none) = k(y: 2, x: 1) else 0;\n";
    let app4 = "app4(k: ((y: int, x: int) -> int) | ((y: int, x: int) -> f64)) = \
                { r = k(y: 2, x: 1); if r is int { r } else { 0 } };\n";
    reorder_refused(
        &[
            &format!("{app3}pass(g) = app2(f: g) + app3(k: g);\na = pass(g: re);\n"),
            &format!("{app3}pass(g) = app3(k: g) + app2(f: g);\na = pass(g: re);\n"),
            &format!("{app4}pass(g) = app2(f: g) + app4(k: g);\na = pass(g: re);\n"),
        ],
        "also passes it on as `",
    );
}

/// Row PROOF-reorder-forwarded-uses-complete, use by storing it: a body that puts the
/// parameter in a tuple, a map or a family and calls it from there is refused.
#[test]
fn a_reordered_function_the_generic_body_also_stores_is_refused() {
    reorder_refused(
        &[
            "pass(g) = { t = (g, 0); app2(f: g) + t[0](y: 2, x: 1) };\na = pass(g: re);\n",
            "pass(g) = { m = { 1 -> g }; app2(f: g) + m[1](y: 2, x: 1) };\na = pass(g: re);\n",
            "pass(g) = app2(f: g) + [g].map(h -> h(y: 2, x: 1))[0];\na = pass(g: re);\n",
            "pass(g) = { m = [g, re]; app2(f: g) + m[1](y: 2, x: 1) };\na = pass(g: re);\n",
        ],
        "also uses it in its own order",
    );
}

/// Row PROOF-reorder-forwarded-uses-complete, use by a closure: a closure that calls the
/// parameter is refused; one that only passes it on in the slot's order runs, to the value of
/// a call by name.
#[test]
fn a_reordered_function_a_closure_of_the_generic_body_captures_is_refused_or_runs() {
    reorder_refused(
        &[
            "pass(g) = { c = z -> g(y: 2, x: z); app2(f: g) + c(1) };\na = pass(g: re);\n",
            "pass(g) = { c = z -> app2(f: g); c(1) + g(y: 2, x: 1) };\na = pass(g: re);\n",
        ],
        "also uses it in its own order",
    );
    runs_to(
        &format!("{REORDER_HEAD}pass(g) = {{ c = z -> app2(f: g); c(1) }};\na = pass(g: re);\n"),
        "a",
        "12",
    );
}

/// Row PROOF-reorder-forwarded-uses-complete, use by giving it back: a result that holds the
/// parameter in a map or a family is refused for giving it back, and one that holds a closure
/// calling it is refused for the call.
#[test]
fn a_reordered_function_the_generic_body_returns_inside_another_value_is_refused() {
    reorder_refused(
        &[
            "pass(g) = (app2(f: g), { 1 -> g });\nb = pass(g: re);\na = b[1][1](y: 2, x: 1) + b[0];\n",
            "pass(g) = (app2(f: g), [g]);\nb = pass(g: re);\na = b[1][0](y: 2, x: 1) + b[0];\n",
        ],
        "also gives it back",
    );
    reorder_refused(
        &["pass(g) = (app2(f: g), z -> g(y: 2, x: z));\nb = pass(g: re);\na = b[1](1) + b[0];\n"],
        "also uses it in its own order",
    );
}

/// Row PROOF-reorder-forwarded-uses-complete, use by a comparison: comparing a function is
/// refused in any case, and the reordering is refused beside it.
#[test]
fn a_reordered_function_the_generic_body_compares_is_refused() {
    for rest in [
        "pass(g) = app2(f: g) + (if g == re { 100 } else { 0 });\na = pass(g: re);\n",
        "pass(g) = app2(f: g) + (if g == g { 100 } else { 0 });\na = pass(g: re);\n",
    ] {
        let src = format!("{REORDER_HEAD}{rest}");
        let errors = type_errors(&src);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("Cannot compare a value that may hold a function")),
            "{src}: {errors:?}"
        );
    }
    reorder_refused(
        &["pass(g) = app2(f: g) + (if g == g { 100 } else { 0 });\na = pass(g: re);\n"],
        "also uses it in its own order",
    );
}

/// Row PROOF-reorder-forwarded-uses-complete, use by a struct: a struct declaration is not
/// supported yet, so a struct holding the parameter never reaches the checker. When structs
/// are compiled, this test fails, and the struct cases join the tests above.
#[test]
fn a_reordered_function_in_a_struct_is_not_compiled_yet() {
    let head = "struct Box { v: (y: int, x: int) -> int }\n";
    for rest in [
        "pass(g) = { b = Box(v: g); app2(f: g) + b.v(y: 2, x: 1) };\na = pass(g: re);\n",
        "pass(g) = (app2(f: g), Box(v: g));\nb = pass(g: re);\na = b[1].v(y: 2, x: 1) + b[0];\n",
    ] {
        let src = format!("{head}{REORDER_HEAD}{rest}");
        let errors = front_errors(&src);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("not supported by this version of zedc")),
            "{src}: {errors:?}"
        );
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
/// `[String | #ioError(…)]`, the list `int ->? String | #ioError(…)`, so the slot `(int | f64) ->? String` refuses it by its
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
        o.stderr.contains("does not take [String | #ioError(op: String, path: String, why: String)], only (int | f64) ->? String."),
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
    // A curried call through two functions of different parameter lists was refused with a
    // message that printed both types; the function held now places it, and it runs (row
    // CALL-curried-placed): `small` called with 2.5 gives 6 through the partial slot, so
    // `twice(g: pass1)` is 6 and `twice(g: pass2)` is 6 + 1.
    let twice = format!(
        "{head}pass1(x, z: int = 0) = apply(f: x) + z;\npass2(x, y: int = 1, z: int = 0) = apply(f: x) + y + z;\ntwice(g) = g(x: small, ...)(z: 0);\na = twice(g: pass1) + twice(g: pass2);\n"
    );
    assert_eq!(type_errors(&twice), Vec::<String>::new(), "{twice}");
    runs_to(&twice, "a", "13");

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

/// A generic function whose variable, with no bound, stands in a parameter's function type is
/// passed where its instance is expected: `g` at `T = int` is `(h: (x: int) -> int, y: int) ->
/// int`. Before (row TEST-types-unreached-paths-6), the variable inside the function type was
/// compared as itself, which nothing binds, and the call `p(f: g)` was refused. An instance
/// that does not exist stays refused: no `T` makes `(x: T) -> int` and `y: T` take `int` and
/// `f64`.
#[test]
fn a_generic_function_with_its_variable_in_a_parameter_function_is_passed_at_an_instance() {
    let fits = [
        "p(f: (h: (x: int) -> int, y: int) -> int) = f(h: x -> x + 1, y: 2);\ng(h: (x: T) -> int, y: T) = h(x: y);\na = p(f: g);\n",
        "p(f: (y: int, h: (x: int) -> int) -> int) = f(h: x -> x + 1, y: 2);\ng(y: T, h: (x: T) -> int) = h(x: y);\na = p(f: g);\n",
    ];
    for src in fits {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        runs_to(src, "a", "3");
    }
    // The variable also in the result of the function type, and in the result.
    let src = "p(f: (h: (x: int) -> int, y: int) -> int) = f(h: x -> x + 1, y: 2);\ng(h: (x: T) -> T, y: T) = h(x: y);\na = p(f: g);\n";
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    runs_to(src, "a", "3");
    // No instance: `T` would be `int` and `f64` at once, or the result is not `String`, or
    // the function returns `f64` where `T` is `int`.
    let g = "g(h: (x: T) -> T, y: T) = h(x: y);\na = p(f: g);\n";
    for p in [
        "p(f: (h: (x: int) -> int, y: f64) -> int) = 0;\n",
        "p(f: (h: (x: int) -> int, y: int) -> String) = \"s\";\n",
        "p(f: (h: (x: int) -> f64, y: int) -> int) = 0;\n",
    ] {
        let src = format!("{p}{g}");
        assert!(!type_errors(&src).is_empty(), "{src}");
    }
}

/// A call that every function the value may hold places alike is compiled as before, with no
/// placing (DESIGN.md sec:values_morphisms, "The function called places the arguments": "a
/// call that agrees is placed when it is compiled, at no cost"); a call that differs is placed
/// at run time, also in a built executable.
#[test]
fn an_agreeing_call_is_compiled_as_before_and_a_differing_one_runs_in_an_executable() {
    use zed_tests::step_helpers::l01_16_elaboration::elab;
    use zed_tests::step_helpers::l01_19_whole_file_ports::run;
    let agree = "f(a: int, b: int) = a - b;\nk = f;\na = k(b: 1, a: 5);\n";
    let t = elab(agree).unwrap().get("a").unwrap().to_string();
    assert!(!t.contains("place") && !t.contains("callNamed"), "{t}");
    runs_to(agree, "a", "4");
    let ro = "f(a: int, b: int) = a - b;\ng(b: int, a: int) = a * 10 + b;\n";
    let pick = "pick(c: bool) = if c { f } else { g };\nh = pick(c: false);\n";
    let main = "main(m: MainArgs) {\n  m.stdout <- \"${a}\";\n}\n";
    let cases = [
        (format!("{ro}{pick}a = h(a: 5, b: 2);\n{main}"), "52\n"),
        (
            format!("{ro}call(k) = k(a: 5, b: 2);\na = call(k: f) * 100 + call(k: g);\n{main}"),
            "352\n",
        ),
        (
            format!(
                "tax(price, rate = price / 10.0) = price * rate;\nt = tax;\na = t(price: 10.0);\n{main}"
            ),
            "10.0\n",
        ),
    ];
    for (i, (src, want)) in cases.iter().enumerate() {
        let o = run(&format!("callee_places_{i}"), src, "", &[]);
        assert_eq!(
            (o.status, o.stdout.as_str()),
            (0, *want),
            "{src}{}",
            o.stderr
        );
    }
}

/// Row FAIL-check-class-in-fn-arg-not-narrowed (a wrong yes): inside `q`, `T` is written in
/// `g`'s function type and nowhere else that fixes it, so the checker gives it a class.
/// `p(f: g)` passes `g` at `p`'s closed parameter `(h: int, y: int) -> int`; the comparison of
/// types took the class as `int` there in a binding it then dropped, so `q(g: s)` with `s` at
/// `bool` was accepted and `p` called `s` with two `int`s. The class is now narrowed by calling
/// `g` with the parameter types of the slot, as `p` calls it.
#[test]
fn a_class_inside_a_function_argument_is_narrowed_at_a_closed_parameter() {
    let head = "p(f: (h: int, y: int) -> int) = f(h: 1, y: 2);\n";
    for src in [
        format!(
            "{head}q(g: (h: T, y: T) -> int) = p(f: g);\ns(h: bool, y: bool) = 0;\na = q(g: s);\n"
        ),
        format!(
            "{head}q(g: (h: T, y: T) -> int, z: T) = p(f: g);\ns(h: bool, y: bool) = 0;\n\
             a = q(g: s, z: true);\n"
        ),
        // The parameters in another order: the slot's names decide.
        format!(
            "{head}q(g: (y: T, h: T) -> int) = p(f: g);\ns(y: bool, h: bool) = 0;\na = q(g: s);\n"
        ),
        // Two type variables, each narrowed at its own parameter.
        format!(
            "{head}q(g: (h: T, y: U) -> int, z: T, w: U) = p(f: g);\ns(h: int, y: bool) = 0;\n\
             a = q(g: s, z: 1, w: true);\n"
        ),
    ] {
        assert!(!type_errors(&src).is_empty(), "{src}");
    }
    // At `int` it is accepted.
    accepted(&format!(
        "{head}q(g: (h: T, y: T) -> int) = p(f: g);\ns(h: int, y: int) = h + y;\na = q(g: s);\n"
    ));
}

/// The class in the result of the function argument: `(h: int) -> T` passed where `(h: int) ->
/// int` is expected makes `T` `int`, alone and inside a tuple, and against a generic slot
/// `(x: int) -> U` whose `U` is fixed by another argument.
#[test]
fn a_class_in_the_result_of_a_function_argument_is_narrowed() {
    let one = "p(f: (h: int) -> int) = f(h: 1);\n";
    accepted(&format!(
        "{one}q(g: (h: int) -> T, z: T) = p(f: g);\ns(h: int) = h;\na = q(g: s, z: 3);\n"
    ));
    for src in [
        format!(
            "{one}q(g: (h: int) -> T, z: T) = p(f: g);\ns(h: int) = true;\na = q(g: s, z: true);\n"
        ),
        "p(f: (h: int) -> (int, int)) = f(h: 1);\nq(g: (h: int) -> (T, int), z: T) = p(f: g);\n\
         s(h: int) = (true, 1);\na = q(g: s, z: true);\n"
            .to_string(),
        "m(f: (x: int) -> U, z: U) = f(x: 1);\nq(g: (x: T) -> T, z: T) = m(f: g, z: z);\n\
         s(x: bool) = x;\na = q(g: s, z: true);\n"
            .to_string(),
    ] {
        assert!(!type_errors(&src).is_empty(), "{src}");
    }
}

/// The class one function deeper, at a doubly contravariant place: `T` in `(h: (x: T) -> int,
/// y: T) -> int` passed where `(h: (x: int) -> int, y: int) -> int` is expected is `int`. The
/// comparison of types could not bind a class there, so `q` alone was refused (a wrong no); now
/// it is accepted and the call with `s` at `bool` is refused. The same holds where `g` is
/// called with a declared function, `g(h: k, y: 1)`.
#[test]
fn a_class_inside_a_function_argument_nested_is_narrowed() {
    let q_of = |body: &str| format!("q(g: (h: (x: T) -> int, y: T) -> int) = {body};\n");
    let p = "p(f: (h: (x: int) -> int, y: int) -> int) = 0;\n";
    let k = "k(x: int) = x;\n";
    for pre in [
        format!("{p}{}", q_of("p(f: g)")),
        format!("{k}{}", q_of("g(h: k, y: 1)")),
    ] {
        accepted(&pre);
        accepted(&format!(
            "{pre}s(h: (x: int) -> int, y: int) = 0;\na = q(g: s);\n"
        ));
        let src = format!("{pre}s(h: (x: bool) -> int, y: bool) = 0;\na = q(g: s);\n");
        assert!(!type_errors(&src).is_empty(), "{src}");
    }
}

/// A refusal inside `q` prints the class of `q`'s `T` as `T`, a type the user can write there,
/// not `_`, which says every value: "`p` does not take ((h: (x: _) -> int, y: _) -> int)" before.
#[test]
fn a_class_of_a_written_type_variable_prints_as_its_name() {
    let src = "p(f: (h: (x: int) -> int, y: int) -> bool) = true;\n\
               q(g: (h: (x: T) -> int, y: T) -> int) = p(f: g);\n";
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{src}: {errors:?}");
    assert!(
        errors[0].contains("((h: (x: T) -> int, y: T) -> int)") && !errors[0].contains('_'),
        "{src}: {errors:?}"
    );
}

/// The same at a partial parameter (FAIL-check-class-in-fn-arg-not-narrowed). DESIGN.md
/// sec:type_language ("Morphism types carry two domain bounds"): `K ->? V` has an empty lower
/// domain and the upper one `K`, so a function fits it whose domain is within `K`; with `T`
/// in `g`'s domain, `p(f: g)` makes `T` one of `K`'s. Before, the comparison of types bound
/// `T` and dropped the binding, so `q(g: s)` with `s` taking `bool` was accepted, and `p` would
/// call it with ints. A tuple is matched to the one shape of its length in `K`
/// (FAIL-fn-domain-bindable-variable, whose programs keep their verdicts).
#[test]
fn a_class_inside_a_function_argument_is_narrowed_at_a_partial_parameter() {
    let two = "p(f: (x: int, y: int) ->? int) = f(x: 1, y: 2);\n\
               q(g: (x: T, y: T) -> int) = p(f: g);\n";
    let pair = "p(f: (x: (int, int) | String) ->? int) = f(x: (1, 2));\n\
                q(g: (x: (T, T)) -> int) = p(f: g);\n";
    for head in [two, pair] {
        assert_eq!(type_errors(head), Vec::<String>::new(), "{head}");
    }
    for src in [
        format!("{two}s(x: int, y: int) = 0;\na = q(g: s);\n"),
        format!("{pair}s(x: (int, int)) = 0;\na = q(g: s);\n"),
    ] {
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
    }
    for src in [
        format!("{two}s(x: bool, y: bool) = 0;\na = q(g: s);\n"),
        format!("{pair}s(x: (bool, bool)) = 0;\na = q(g: s);\n"),
    ] {
        assert_eq!(type_errors(&src).len(), 1, "{src}: {:?}", type_errors(&src));
    }
    // A result outside the partial arrow's is refused, and the clause names `T` as written.
    let src = "p(f: (x: (int, int) | String) ->? int) = 0;\n\
               q(g: (x: (T, T)) -> String) = p(f: g);\n";
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{src}: {errors:?}");
    assert!(
        errors[0].contains("`(x: (T, T)) -> String`") && !errors[0].contains('_'),
        "{src}: {errors:?}"
    );
}

/// A function whose parameter takes functions whose results are variables of their own, two
/// deep, is passed where the same depth with `int` results is expected, and called with such
/// a function: the small instance of the second deep series of
/// `bench::function_variance::classes_inside_function_arguments_narrowed_by_calls_scale`. The
/// call of `q` with an `s` taking `bool` is refused.
#[test]
fn a_function_whose_results_are_variables_of_their_own_fits_int_results() {
    let head = "p(f: (h: (x: (x: int) -> int) -> int, y: int) -> int) = 0;\n\
                q(g: (h: ((x: ((x: int) -> U0 for U0 in int)) -> U1 for U1 in int), y: int) -> \
                int) = p(f: g);\n";
    let ok = format!("{head}s(h: (x: (x: int) -> int) -> int, y: int) = 0;\na = q(g: s);\n");
    assert_eq!(type_errors(&ok), Vec::<String>::new(), "{ok}");
    let bad = format!("{head}s(h: (x: (x: int) -> int) -> int, y: bool) = 0;\na = q(g: s);\n");
    assert_eq!(type_errors(&bad).len(), 1, "{bad}: {:?}", type_errors(&bad));
}

//! The checker at the rule of low complexity (DESIGN.md Part G). A signature search tried
//! each carrier for each untyped parameter, up to a budget, and began each run from a copy of
//! everything found so far. An untyped parameter is now a class of a union-find forest, and
//! each body is checked once. The programs and types here are checked small; their time, at
//! sizes where a cost above linear shows, is measured in `bench::scaling`.

use std::collections::{BTreeMap, HashMap};

use zed_kernel::types::Type as KType;
use zed_tests::scaling;
use zedc::check::ty::Ty;

use super::{Resolved, info, sig, sig_of, type_errors};

/// The units `text(m)` at `n` and `FACTOR * n`, read and resolved before the timing, so that a
/// test times the checker alone (COMPLEXITY.md F85).
pub(super) fn resolved(n: usize, text: impl Fn(usize) -> String) -> HashMap<usize, Resolved> {
    scaling::inputs(n, |m| Resolved::new(&text(m)))
}

/// `20 n` constants, each adopting its literal with no search, and `n` functions of one untyped
/// parameter: what the unit has found is large beside the searches.
pub(super) fn constants_and_functions(n: usize) -> String {
    let mut text: String = (0..20 * n)
        .map(|j| format!("k{j} = 0.5f64 + {j};\n"))
        .collect();
    text.extend((0..n).map(|i| format!("h{i}(x) = x / {}.0;\n", i + 1)));
    text
}

/// A function of `n` untyped parameters, all added together.
pub(super) fn sum(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let ps: Vec<String> = xs.iter().map(|x| format!("positional {x}")).collect();
    format!("f({}) = {};\n", ps.join(", "), xs.join(" + "))
}

/// `n` functions, each calling the one before with its untyped parameter.
pub(super) fn chain(n: usize) -> String {
    let mut src = "g0(positional x) = -x;\n".to_string();
    for i in 1..n {
        src += &format!("g{i}(positional x) = g{}(x) * x;\n", i - 1);
    }
    src
}

/// `n` bindings, each with an `else` pattern.
pub(super) fn else_patterns(n: usize) -> String {
    (0..n)
        .map(|i| format!("v{i} = #e(code: {i}) else #e(code:) -> code;\n"))
        .collect()
}

/// A function of `n` untyped parameters that returns them all, so that its signature has `n`
/// type variables.
pub(super) fn tuple(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let ps: Vec<String> = xs.iter().map(|x| format!("positional {x}")).collect();
    format!("f({}) = ({});\n", ps.join(", "), xs.join(", "))
}

/// `n` functions, each calling the one before twice with its untyped parameter, the first
/// taking a component of it.
pub(super) fn fan(n: usize) -> String {
    let mut src = "g0(positional t) = t[0];\n".to_string();
    for i in 1..n {
        let call = format!("g{}(t)", i - 1);
        src += &format!("g{i}(positional t) = {call} + {call};\n");
    }
    src
}

/// `n` atoms, each with a payload of one field: of `n` names, or of one name with `n` shapes.
pub(super) fn payloads(n: usize, one_name: bool) -> Vec<zedc::check::ty::Ty> {
    use zed_kernel::types::Type;
    use zedc::check::ty::{Shape, Ty};
    (0..n)
        .map(|i| {
            let name = if one_name {
                "e".to_string()
            } else {
                format!("e{i}")
            };
            let mut t = Ty::set(Type::atom_with(&name, &Type::top()));
            let shape = Shape::new(
                Vec::new(),
                [(format!("f{i}").into(), Ty::empty())]
                    .into_iter()
                    .collect(),
            );
            t.payloads.insert(name.into(), Some(vec![shape]));
            t
        })
        .collect()
}

/// `g(positional a0) = (a1) -> (a2) -> … -> (an) -> (a0, a1, …, an);`, `n` curried lambdas,
/// the innermost using every parameter around it.
pub(super) fn curried(n: usize) -> String {
    let lambdas: String = (1..=n).map(|i| format!("(a{i}) -> ")).collect();
    let all: Vec<String> = (0..=n).map(|i| format!("a{i}")).collect();
    format!("g(positional a0) = {lambdas}({});\n", all.join(", "))
}

/// `g(positional a0) = (a1) -> … -> (an) -> (a0 + int(1), …, an + int(1));`, `n` curried
/// lambdas whose parameters each take the carrier int when their lambda ends. The `1` is
/// `int(1)`: a bare `1` takes the carrier of its operand (steps L1.26a, L1.26b) and leaves
/// each parameter generic, and curried lambdas generic in their parameters check in time
/// quadratic in `n`, on main too (follow-up GENERIC-nested-quadratic).
pub(super) fn curried_sums(n: usize) -> String {
    let lambdas: String = (1..=n).map(|i| format!("(a{i}) -> ")).collect();
    let all: Vec<String> = (0..=n).map(|i| format!("a{i} + int(1)")).collect();
    format!("g(positional a0) = {lambdas}({});\n", all.join(", "))
}

/// `g(positional a0) = (a1) -> … -> (an) -> (a0 + 1, …, an + 1);`, [`curried_sums`] with a
/// bare `1`, which takes the carrier of its operand (steps L1.26a, L1.26b), so each parameter
/// stays generic (GENERIC-nested-quadratic).
pub(super) fn curried_bare_sums(n: usize) -> String {
    let lambdas: String = (1..=n).map(|i| format!("(a{i}) -> ")).collect();
    let all: Vec<String> = (0..=n).map(|i| format!("a{i} + 1")).collect();
    format!("g(positional a0) = {lambdas}({});\n", all.join(", "))
}

/// [`curried_sums`] with `h = g(0)` put in a tuple and tested by `is` against its written
/// type, whose `n` arrows take int.
pub(super) fn curried_tested(n: usize) -> String {
    let arrows: String = (0..n).map(|_| "(int) -> (").collect();
    let ints = vec!["int"; n + 1].join(", ");
    let shut = ")".repeat(n);
    format!(
        "{}h = g(0);\nt = (h, 1);\nr = if t is (({arrows}({ints}){shut}), int) {{ 1 }} else {{ t }};\n",
        curried_sums(n)
    )
}

#[test]
fn nested_lambdas_name_their_variables_as_before() {
    // The names a lambda takes skip those of the lambdas inside it, found from their facts.
    // A variable bounded by carriers is printed by name; of the others, one that stands in two
    // places or more takes the next free name, and one that stands once is `_` (DESIGN.md
    // sec:diagnostics, PRINT-tyvars, UNDERSCORE-print). A signature printed alone has no program
    // around it, so its names start at `T` (a message skips the names the file binds: l01_29
    // `tyvars`).
    for (text, want) in [
        (
            "g(positional a) = (b) -> (c) -> (a, b, c);\n",
            "T -> U -> V -> (T, U, V)",
        ),
        (
            "g(positional a) = (b) -> (c) -> (d) -> (e) -> (f) -> (h) -> (a, b, c, d, e, f, h);\n",
            "T -> U -> V -> W -> T5 -> T6 -> T7 -> (T, U, V, W, T5, T6, T7)",
        ),
        (
            "g(positional a) = (t) -> (b) -> (c) -> a;\n",
            "T -> _ -> _ -> _ -> T",
        ),
        (
            "g(positional f) = (x) -> (y) -> f(x, y) + x;\n",
            "((U, T) -> U) -> U -> T -> U for U in int | f32 | f64 | rat",
        ),
        (
            "g(positional a, positional b) = ((c) -> (d) -> (c, d), a + b);\n",
            "(V, V) -> (T -> U -> (T, U), V) for V in int | f32 | f64 | rat",
        ),
        // The results of `h(x)` and `f(x)` are classes of `g`'s level that first appear
        // inside the lambdas, and are named in the order they appear there.
        (
            "g(positional f, positional h) = (x) -> (y) -> (h(y, x), f(x), y);\n",
            "(T -> U, (V, T) -> W) -> T -> V -> (W, U, V)",
        ),
        (
            "g(positional f) = ((x) -> f(x), (y) -> (f(y), y));\n",
            "((T -> U) & (V -> W)) -> (T -> U, V -> (W, V))",
        ),
    ] {
        assert_eq!(sig(text, "g"), want, "{text}");
    }
}

/// `curried_sums(n)` and `y = g(0)(1)…(n);`: a chain of n calls on one value, each through
/// the function the call before gives.
pub(super) fn call_chain(n: usize) -> String {
    let args: String = (1..=n).map(|i| format!("({i})")).collect();
    format!("{}y = g(0){args};\n", curried_sums(n))
}

/// A unit whose function `q` passes its parameter, an overload of `n` arrows, to `p`, whose
/// slot is the same overload: `q`'s function has an arrow for each of `p`'s.
pub(super) fn overloads(n: usize) -> String {
    let ov = (0..n)
        .map(|i| format!("((x: #a{i}) -> #b{i})"))
        .collect::<Vec<_>>()
        .join(" & ");
    format!("p(f: {ov}) = 0;\nq(g: {ov}) = p(f: g);\n")
}

/// Like [`overloads`], but each arrow of the slot returns its atom or `#z`, so no arrow of
/// `q`'s function equals the arrow of the slot it fits. The wider part is in the result: a
/// domain is exact (FAIL-types-fn-param-exact-domain), so an arrow whose parameter took `#z`
/// as well would permit a value the slot does not.
pub(super) fn wider_overloads(n: usize) -> String {
    let ov = |wide: &str| {
        (0..n)
            .map(|i| format!("((x: #a{i}) -> #b{i}{wide})"))
            .collect::<Vec<_>>()
            .join(" & ")
    };
    format!("p(f: {}) = 0;\nq(g: {}) = p(f: g);\n", ov(" | #z"), ov(""))
}

/// Like [`wider_overloads`], but every arrow of `q`'s function and of the slot takes `#c`:
/// every arrow of the function offers what each arrow of the slot needs, and only the results
/// tell them apart.
pub(super) fn shared_overloads(n: usize) -> String {
    let ov = |wide: &str| {
        (0..n)
            .map(|i| format!("((x: #c) -> #b{i}{wide})"))
            .collect::<Vec<_>>()
            .join(" & ")
    };
    format!("p(f: {}) = 0;\nq(g: {}) = p(f: g);\n", ov(" | #z"), ov(""))
}

/// A unit whose function `p` has a slot written as an overload of `n` arrows nested `n` deep
/// in parentheses: resolve and the checker read each intersection once, with the one around
/// it.
pub(super) fn nested_overload(n: usize) -> String {
    let arrow = |i: usize| format!("((x: #a{i}) -> #b{i})");
    let ov = (1..n).fold(arrow(0), |inner, i| format!("({inner}) & {}", arrow(i)));
    format!("p(f: {ov}) = 0;\n")
}

/// A slot `(x: #a0 | ... | #a(n-1)) -> String` and an overload of `n` arrows `(x: #ai) ->
/// String` that cover it only together: each arrow is compared once with the slot's arrow, and
/// the union of their parameter types once with its parameter (`check::ty::covered`,
/// COMPLEXITY.md F82).
pub(super) fn covering_overload(n: usize) -> String {
    let slot = (0..n)
        .map(|i| format!("#a{i}"))
        .collect::<Vec<_>>()
        .join(" | ");
    let ov = (0..n)
        .map(|i| format!("((x: #a{i}) -> String)"))
        .collect::<Vec<_>>()
        .join(" & ");
    format!("p(f: (x: {slot}) -> String) = 0;\nq(g: {ov}) = p(f: g);\n")
}

/// A slot of `w` parameters and a function of one arrow that takes all but the last, where it
/// takes `int` and the slot passes `int | bool`: the cover compares the arrow's parameters in
/// one pass, not once for each parameter left out (`check::ty::part_of`; that cost the
/// square of the width, 38.8 times the bytes at w = 100 and 800).
pub(super) fn wide_arrows(w: usize) -> String {
    let params = |last: &str| {
        (0..w)
            .map(|j| format!("x{j}: {}", if j + 1 == w { last } else { "int" }))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!(
        "p(f: ({}) -> String) = 0;\nq(g: ({}) -> String) = p(f: g);\n",
        params("int | bool"),
        params("int")
    )
}

/// The cases of rule 6 that `check::ty::covered` builds or refuses with a reason, each at `n`
/// and `8 * n` arrows: the source of `p(f: g)` for the slot `slot` and the overload of
/// `arrows`.
fn slot_and_overload(slot: &str, arrows: impl Iterator<Item = String>) -> String {
    let ov = arrows.collect::<Vec<_>>().join(" & ");
    format!("p(f: {slot}) = 0;\nq(g: {ov}) = p(f: g);\n")
}

/// The atoms `#{name}0 | ... | #{name}(n-1)`.
fn atoms(name: &str, n: usize) -> String {
    (0..n)
        .map(|i| format!("#{name}{i}"))
        .collect::<Vec<_>>()
        .join(" | ")
}

/// Case (3), built: `n` arrows `(x: #ai) -> String` within the slot's result, and `n` arrows
/// `(x: #c | #ai) -> String | #bi` outside it, each taking `#c`, what the others leave; the
/// intersection of their `n` results is `String` (`check::ty::met`).
pub(super) fn met_and_within(n: usize) -> String {
    let within = (0..n).map(|i| format!("((x: #a{i}) -> String)"));
    let outside = (0..n).map(|i| format!("((x: #c | #a{i}) -> String | #b{i})"));
    let slot = format!("(x: #c | {}) -> String", atoms("a", n));
    slot_and_overload(&slot, within.chain(outside))
}

/// Case (3), refused with the reason: `(x: #ai | #a(i+1)) -> String | #bi` meet in `String` at
/// each atom, but no one set of them takes every atom; the message names the `n` arrows in
/// one pass (`check::ty::refused_cover`).
pub(super) fn meeting_on_different_sets(n: usize) -> String {
    let arrows = (0..n).map(|i| format!("((x: #a{i} | #a{}) -> String | #b{i})", i + 1));
    slot_and_overload(&format!("(x: {}) -> String", atoms("a", n + 1)), arrows)
}

/// Case (2), built: `n` arrows `(x: #ai) -> String` and one whose parameter is a function type,
/// which binds nothing, cover `(x: #a0 | ... | ((y: int) -> int)) -> String`
/// (`check::ty::binds_nothing`).
pub(super) fn with_a_function_arrow(n: usize) -> String {
    let arrows = (0..n).map(|i| format!("((x: #a{i}) -> String)"));
    let fun = std::iter::once("((x: (y: int) -> int) -> String)".to_string());
    let slot = format!("(x: {} | ((y: int) -> int)) -> String", atoms("a", n));
    slot_and_overload(&slot, arrows.chain(fun))
}

/// A bounded variable at `w` parameters, bound to `int | f64`, refused with the count of its
/// places, found by one walk of the arrow (`check::ty::one_place`).
pub(super) fn bounded_at_many_parameters(w: usize) -> String {
    let params = |t: &str| {
        (0..w)
            .map(|j| format!("x{j}: {t}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!(
        "p(f: ({}) -> int | f64) = 0;\nq(g: ({}) -> T for T in int | f64) = p(f: g);\n",
        params("int | f64"),
        params("T")
    )
}

/// The intersection built where results hold a rigid variable or a function: `n` arrows
/// `(x: T) -> T | String | #bi for T in int | f64` and one `(x: int | f64) -> String | ((y:
/// int) -> int)`, at the slot `(x: U) -> U | String for U in int | f64`. The piece `U` of each
/// result is within the slot's, and the function is in no other result; the carriers of all
/// results but one are read off a pass from each end (`check::ty::meet_within`).
pub(super) fn results_holding_a_variable(n: usize) -> String {
    let arrows = (0..n).map(|i| format!("((x: T) -> T | String | #b{i} for T in int | f64)"));
    let fun = std::iter::once("((x: int | f64) -> String | ((y: int) -> int))".to_string());
    slot_and_overload("(x: U) -> U | String for U in int | f64", arrows.chain(fun))
}

/// The intersection of [`results_holding_a_variable`] alone: `n` results `U | String | #bi`,
/// `U` bounded by `int | f64`, to meet within `U | String`.
pub(super) fn results_met_alone(n: usize) -> zedc::check::ty::Meet {
    use zedc::check::ty::{Carrier, Meet};
    let u_or_string = || Ty::var("U".into()).union(&Ty::carrier(Carrier::Str));
    let results = (0..n)
        .map(|i| u_or_string().union(&Ty::set(KType::atom(&format!("b{i}")))))
        .collect();
    let bound: &[Carrier] = &[Carrier::Int, Carrier::F64];
    Meet::new(results, u_or_string(), &[("U", bound)])
}

/// The source form of [`results_with_functions_met`]: `p(f: g)` for the slot `(x: #c | U) -> U
/// | String | ((y: int) -> int | f64) for U in int | f64` and the overload of `n` arrows
/// `(x: #c | int | f64) -> String | #bi | ((y: {fn_param}) -> int)`.
pub(super) fn results_holding_functions(n: usize, fn_param: &str) -> String {
    let arrows = (0..n)
        .map(|i| format!("((x: #c | int | f64) -> String | #b{i} | ((y: {fn_param}) -> int))"));
    slot_and_overload(
        "(x: #c | U) -> U | String | ((y: int) -> int | f64) for U in int | f64",
        arrows,
    )
}

/// The intersection of `n` results that each hold a function, in the state of a real call
/// (`check::ty::MeetInCall`): the overload `s` of `n` arrows `(x: #c | int | f64) -> String |
/// #bi | ((y: int) -> int)`, met within the result of `q`, `(x: #c | U) -> U | String | ((y:
/// int) -> int | f64) for U in int | f64`. Read as a call reads them, each function is a
/// variable of its own (each built apart, so none shares a reading or a verdict with another)
/// and `U` is rigid; every result holds a function, so none is left out, and each of the `n`
/// is compared with `q`'s, which it fits: the same exact domain, a narrower result. The kernel
/// parts meet in `String`. A function with a wider domain, `(y: int | #bi) -> int`, would not
/// fit: a plain function type's domain is exact (`function_variance.rs`; run of 2026-11-22).
pub(super) fn results_with_functions_met(n: usize) -> zedc::check::ty::MeetInCall {
    use std::sync::Arc;
    use zedc::check::ty::{Arrow, Carrier, MeetInCall, SParam, Sig};
    let named = |name: &str| {
        vec![SParam {
            name: name.into(),
            positional: false,
            default: None,
            range: None,
        }]
    };
    let atom = |name: &str| Ty::set(KType::atom(name));
    let int = || Ty::carrier(Carrier::Int);
    let int_or_f64 = || int().union(&Ty::carrier(Carrier::F64));
    let string = || Ty::carrier(Carrier::Str);
    let function =
        |param: Ty, result: Ty| Ty::func(Arc::new(Sig::one(named("y"), vec![param], result)));
    let results = (0..n).map(|i| {
        let b = atom(&format!("b{i}"));
        let f = function(int(), int());
        string().union(&b).union(&f)
    });
    let mut s = Sig::one(named("x"), vec![atom("c").union(&int_or_f64())], string());
    s.arrows = results
        .map(|r| Arrow::exact(vec![atom("c").union(&int_or_f64())], r))
        .collect();
    let u = || Ty::var("U".into());
    let g = function(int(), int_or_f64());
    let mut q = Sig::one(
        named("x"),
        vec![atom("c").union(&u())],
        u().union(&string()).union(&g),
    );
    q.own.insert("U".into());
    q.bounds
        .insert("U".into(), Carrier::Int.bit() | Carrier::F64.bit());
    q.note_held();
    MeetInCall::new(s, q)
}

/// `f`, which destructures its parameter into `n` names and gives the last and the first, and
/// a call of it on a tuple of `n`: `n` needs of one class, each checked at the call.
pub(super) fn wide_destructuring(n: usize) -> String {
    let names: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
    let items: Vec<String> = (0..n).map(|i| i.to_string()).collect();
    format!(
        "f(positional p) {{\n  {} = p;\n  return (a{}, a0);\n}}\ny = f(({}));\n",
        names.join(", "),
        n - 1,
        items.join(", ")
    )
}

/// `n` functions, each destructuring its parameter into a pair, each called on a pair.
pub(super) fn many_destructurings(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "swap{i}(positional p) {{\n  a, b = p;\n  return (b, a);\n}}\ny{i} = swap{i}(({i}, 0));\n"
            )
        })
        .collect()
}

/// `app`, which applies its parameter `g` to each of its `n` other parameters, called with the
/// generic `id` and `n` numbers: `n` needs of `g`'s class, each naming the type variable of
/// `id` that the call leaves unbound, checked at a call that binds `2n` variables.
pub(super) fn generic_applied_to_many(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("positional a{i}")).collect();
    let calls: Vec<String> = (0..n).map(|i| format!("g(a{i})")).collect();
    let args: Vec<String> = (0..n).map(|i| i.to_string()).collect();
    format!(
        "id(positional x) = x;\napp(positional g, {}) = ({});\ny = app(id, {});\n",
        params.join(", "),
        calls.join(", "),
        args.join(", ")
    )
}

/// The variables named `{prefix}0` to `{prefix}(n-1)`.
pub(super) fn variables(prefix: &str, n: usize) -> Vec<Ty> {
    (0..n)
        .map(|i| Ty::var(format!("{prefix}{i}").into()))
        .collect()
}

/// The rows `t(k) = (t(k-1), (t(k-1), vs[k]))`, `t(0) = vs[0]`: each row merges the variables of
/// its two components, and the last has `2^n` paths through `n` rows.
pub(super) fn overlapping_rows(vs: &[Ty]) -> Ty {
    vs[1..].iter().fold(vs[0].clone(), |s, v| {
        Ty::tuple(vec![s.clone(), Ty::tuple(vec![s, v.clone()])])
    })
}

/// The rows `z(k) = (x(k), y(k))`, with `x(k) = (x(k-1), a[k])` and `y(k) = (y(k-1), b[k])`:
/// each `z(k)` holds `2k + 2` variables no other row holds, made from two sets that share no
/// node.
pub(super) fn disjoint_rows(a: &[Ty], b: &[Ty]) -> Vec<Ty> {
    let (mut x, mut y) = (a[0].clone(), b[0].clone());
    let mut zs = Vec::with_capacity(a.len());
    for (a, b) in a[1..].iter().zip(&b[1..]) {
        x = Ty::tuple(vec![x, a.clone()]);
        y = Ty::tuple(vec![y, b.clone()]);
        zs.push(Ty::tuple(vec![x.clone(), y.clone()]));
    }
    zs
}

/// The functions `(os[i]) -> (os[i], hs[i])`, each holding the one variable `hs[i]` and owning
/// `os[i]`, in one type, and the binds of every `os[i]` and `hs[i]` to `ws[i]`.
pub(super) fn functions_holding_one(
    os: &[Ty],
    hs: &[Ty],
    ws: &[Ty],
) -> (Ty, zedc::check::ty::Binds) {
    use std::sync::Arc;
    use zedc::check::ty::{Arrow, Facts, Sig};
    let name = |t: &Ty| t.vars.first().cloned().unwrap();
    let fns = os.iter().zip(hs).map(|(o, h)| {
        Arc::new(Sig {
            arrows: vec![Arrow {
                params: vec![o.clone()],
                result: Ty::tuple(vec![o.clone(), h.clone()]),
                partial: false,
                stores_not_found: false,
            }],
            own: [name(o)].into(),
            held: [name(h)].into(),
            params: Vec::new(),
            bounds: BTreeMap::new(),
            data: false,
            dense: zedc::check::ty::Dense::No,
            keys: None,
            word: None,
            needs: Default::default(),
            named: 0,
            hull: None,
            facts: Facts::default(),
        })
    });
    let binds: zedc::check::ty::Binds = (os.iter().zip(ws))
        .chain(hs.iter().zip(ws))
        .map(|(v, w)| (name(v), w.clone()))
        .collect();
    (
        Ty {
            fns: fns.collect(),
            ..Ty::empty()
        },
        binds,
    )
}

/// `p(s, v) = (s, (s, v))` applied `n` times, `f(a0, ..., an) = p(p(p(a0, a1), a2), ...)`, and,
/// if `call`, `f` called on `0, ..., n`: the type of each `p` holds the row of the one inside
/// twice, so the result's type has `2^n` paths through `n` rows (REPLACE-shared-rows).
pub(super) fn shared_rows(n: usize, call: bool) -> String {
    let params: Vec<String> = (0..=n).map(|i| format!("positional a{i}")).collect();
    let body = (1..=n).fold("a0".to_string(), |s, i| format!("p({s}, a{i})"));
    let mut text = format!(
        "p(positional s, positional v) = (s, (s, v));\nf({}) = {body};\n",
        params.join(", ")
    );
    if call {
        let args: Vec<String> = (0..=n).map(|i| i.to_string()).collect();
        text.push_str(&format!("y = f({});\n", args.join(", ")));
    }
    text
}

#[test]
fn rows_shared_on_many_paths_are_replaced_once() {
    let (info, _) = info(&shared_rows(2, true));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    // MSG-derive-type-size: the row `(0, (0, 1))`, written twice and once inside another, is
    // named, so the type of `y` at n steps is written in O(n), not O(2^n). Before:
    // `((0, (0, 1)), ((0, (0, 1)), 2))`.
    assert_eq!(
        info.tops["y"].to_string(),
        "type Part1 = (0, (0, 1));\n(Part1, (Part1, 2))"
    );
    assert_eq!(
        sig(&shared_rows(2, false), "f"),
        "(T, U, V) -> ((T, (T, U)), ((T, (T, U)), V))"
    );
}

/// Row PRINT-shared-part-exponential: the result of `f` in `shared_rows(n)` holds the row of
/// each level twice at the next, and each row holds variables. Before the row the printer wrote
/// such a row in full at each place, so the text held `2^n` copies of the innermost row; now
/// each is written once, as a definition, and the text grows linearly in `n`. The print runs
/// on a thread of its own with a time limit, so that the old path fails at the limit and does
/// not run on. Each text reads back as the signature it prints (`read::parse_type`, which
/// counts each name in a definition once for each use of the definition): for small `n`
/// compared both ways, and at 40 levels printed again to the same text. The benchmark is
/// `bench::scaling::a_function_of_n_shared_rows_prints_in_linear_time`.
#[test]
fn a_function_of_forty_shared_rows_prints_in_linear_text() {
    let (sent, got) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let read = |n: usize| printed_back(&shared_rows(n, false), n);
        let texts: Result<Vec<String>, String> = [2, 3, 6, 40].into_iter().map(read).collect();
        let _ = sent.send(texts);
    });
    let texts = got
        .recv_timeout(std::time::Duration::from_secs(10))
        .expect("the signature of 40 shared rows prints within 10 s")
        .unwrap_or_else(|e| panic!("{e}"));
    for (n, text) in [2, 3, 6, 40].into_iter().zip(&texts) {
        assert!(
            text.len() <= 64 * (n + 1),
            "{} bytes at {n} levels:\n{text}",
            text.len()
        );
    }
    assert_eq!(texts[0], "(T, U, V) -> ((T, (T, U)), ((T, (T, U)), V))");
}

/// The signature of `f` in `src` printed, read back with `read::parse_type` and printed again
/// to the same text; at `n` ≤ 6 levels the type read back is also compared with the signature
/// both ways.
fn printed_back(src: &str, n: usize) -> Result<String, String> {
    let s = sig_of(src, "f");
    let text = s.to_string();
    let back = zedc::check::read::parse_type(&text).map_err(|e| format!("{text}: {e}"))?;
    if n <= 6 {
        let want = Ty::func(s);
        if !(back.subtype(&want) && want.subtype(&back)) {
            return Err(format!("{text} reads back as another type: {back}"));
        }
    }
    match back.to_string() == text {
        true => Ok(text),
        false => Err(format!("{text} reads back as {back}")),
    }
}

/// Where a union written `_` stands in [`underscore_rows`].
#[derive(Clone, Copy, Debug)]
pub(super) enum Underscore {
    /// Beside the shared rows: `(rows, if c { (0, 0) } else { xs[i] })`.
    Beside,
    /// Around them: `if c { rows } else { xs[i] }`.
    Holding,
    /// At the first of their two places: `{ r = rows; (if c { r } else { xs[i] }, r) }`.
    First,
    /// At the first place of a tuple that holds them beside another such union: `{ r = (rows,
    /// if c { (0, 0) } else { xs[i] }); (if d { r } else { ys[j] }, r) }`.
    Cascade,
}

/// The `n` shared rows of [`shared_rows`] in the result of `f`, with a union written `_` (a
/// pair of ints beside an element of a parameter that stands once) placed as `form` says (row
/// PRINT-shared-underscore-union-tuple).
pub(super) fn underscore_rows(n: usize, form: Underscore) -> String {
    let params: Vec<String> = (0..=n).map(|i| format!("positional a{i}")).collect();
    let rows = (1..=n).fold("a0".to_string(), |s, i| format!("p({s}, a{i})"));
    let blank = "if c { (0, 0) } else { xs[i] }";
    let result = match form {
        Underscore::Beside => format!("({rows}, {blank})"),
        Underscore::Holding => format!("if c {{ {rows} }} else {{ xs[i] }}"),
        Underscore::First => format!("{{ r = {rows}; (if c {{ r }} else {{ xs[i] }}, r) }}"),
        Underscore::Cascade => {
            format!("{{ r = ({rows}, {blank}); (if d {{ r }} else {{ ys[j] }}, r) }}")
        }
    };
    format!(
        "p(positional s, positional v) = (s, (s, v));\nf({}, xs, i, ys, j, c: bool, d: bool) = {result};\n",
        params.join(", ")
    )
}

/// The signature of `f` in [`underscore_rows`] written as a tree, each tuple in full at each
/// place: `2^n` copies of the innermost row, so only for small `n`.
fn underscore_rows_in_full(n: usize, form: Underscore) -> String {
    let names = ["T", "U", "V", "W", "X", "Y", "Z"];
    let rows = (1..=n).fold("T".to_string(), |s, i| {
        format!("({s}, ({s}, {}))", names[i])
    });
    let vars = match form {
        Underscore::Holding => vec!["_"; n + 1].join(", "),
        _ => names[..=n].join(", "),
    };
    let result = match form {
        Underscore::Beside => format!("({rows}, _)"),
        Underscore::Holding => "_".to_string(),
        Underscore::First => format!("(_, {rows})"),
        Underscore::Cascade => format!("(_, ({rows}, _))"),
    };
    format!("({vars}, xs: _, i: _, ys: _, j: _, c: bool, d: bool) -> {result}")
}

/// Row PRINT-shared-underscore-union-tuple: a union written `_` beside, around, or at the
/// first place of the shared rows of [`shared_rows`] leaves the rows written once each, so the
/// text grows linearly in `n`. Before the row a union written `_` in a text that wrote a tuple
/// once made the printer write the text again with every tuple in full, `2^n` copies of the
/// innermost row. The print runs on a thread of its own with a time limit, so that the old path
/// fails at the limit. The benchmark is
/// `bench::scaling::shared_rows_beside_a_union_written_blank_print_in_linear_time`.
///
/// Each text reads back, and at `n` ≤ 6 the type read back is compared both ways with the type
/// read from [`underscore_rows_in_full`], not with the signature as [`printed_back`] does: a
/// `_` does not say which variables its union holds, so no type read back from a text with a
/// `_` compares both ways with the signature (measured: false at one level, where the text
/// names nothing). Nor is the type read back printed again to the same text: a `_` takes the
/// places it covers out of the text, so the type read back holds a tuple at fewer places and
/// may write it in full (`First` at three levels).
#[test]
fn forty_shared_rows_beside_a_union_written_blank_print_in_linear_text() {
    use Underscore::*;
    use zedc::check::read::parse_type;
    let forms = [Beside, Holding, First, Cascade];
    let (sent, got) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let texts: Result<Vec<(Underscore, usize, String)>, String> = (forms.iter())
            .flat_map(|&form| [2, 3, 6, 40].map(|n| (form, n)))
            .map(|(form, n)| {
                let at = format!("{form:?} at {n} levels");
                let text = sig_of(&underscore_rows(n, form), "f").to_string();
                let back = parse_type(&text).map_err(|e| format!("{at}: {text}: {e}"))?;
                if n <= 6 {
                    let full = underscore_rows_in_full(n, form);
                    let whole = parse_type(&full).map_err(|e| format!("{at}: {full}: {e}"))?;
                    if !(back.subtype(&whole) && whole.subtype(&back)) {
                        return Err(format!("{at}: {text} reads back as {back}, not as {full}"));
                    }
                }
                Ok((form, n, text))
            })
            .collect();
        let _ = sent.send(texts);
    });
    let texts = got
        .recv_timeout(std::time::Duration::from_secs(10))
        .expect("the signatures of 40 shared rows beside a union written _ print within 10 s")
        .unwrap_or_else(|e| panic!("{e}"));
    for (form, n, text) in &texts {
        assert!(
            text.len() <= 64 * (n + 2),
            "{form:?}: {} bytes at {n} levels:\n{text}",
            text.len()
        );
    }
    // At three levels the rows' second level is shared below a tuple written once, and is
    // named where the rows stand once outside the `_`: before the row, `First` and `Cascade`
    // were written in full.
    let at_three: Vec<&str> = (texts.iter())
        .filter(|(_, n, _)| *n == 3)
        .map(|(_, _, t)| t.as_str())
        .collect();
    let params = "(T, U, V, W, xs: _, i: _, ys: _, j: _, c: bool, d: bool) -> ";
    let part = "type Part1 = ((T, (T, U)), ((T, (T, U)), V));\n";
    let beside = format!(
        "{params}((((T, (T, U)), ((T, (T, U)), V)), (((T, (T, U)), ((T, (T, U)), V)), W)), _)"
    );
    let holding = "(_, _, _, _, xs: _, i: _, ys: _, j: _, c: bool, d: bool) -> _".to_string();
    let first = format!("{part}{params}(_, (Part1, (Part1, W)))");
    let cascade = format!("{part}{params}(_, ((Part1, (Part1, W)), _))");
    assert_eq!(at_three, [beside, holding, first, cascade], "{at_three:#?}");
}

/// Row PRINT-bounded-var-in-shared-tuple-exponential: the rows of [`shared_rows`] with the
/// parameter `a{bounded}` passed at `w`, of `int | f64`, so that it is a variable bounded by
/// carriers: `a0` stands in the innermost row, held twice at each of the `n` levels; `an`
/// stands in the outermost row only.
pub(super) fn bounded_rows(n: usize, bounded: usize) -> String {
    let params: Vec<String> = (0..=n).map(|i| format!("positional a{i}")).collect();
    let rows = (1..=n).fold("a0".to_string(), |s, i| format!("p({s}, a{i})"));
    format!(
        "w(positional x: int | f64) = 0;\np(positional s, positional v) = (s, (s, v));\nf({}) = (w(a{bounded}), {rows});\n",
        params.join(", ")
    )
}

/// Row PRINT-bounded-var-in-shared-tuple-exponential: a variable bounded by carriers in the
/// shared rows of [`bounded_rows`] leaves each row written once, as a definition that names the
/// variable, with the bounds clause written once at the end of the signature (DESIGN.md
/// sec:diagnostics, "Types in a message"). Before the row a tuple holding a variable bounded by
/// carriers was never written once, so the text doubled at each level: 346 bytes at 6 levels
/// with the bound inside the rows, against 167 with it outside. The print runs on a thread of
/// its own with a time limit, so that the old path fails at the limit. Each text reads back,
/// compared both ways with the signature at `n` ≤ 6 and printed again to the same text
/// ([`printed_back`]). The benchmark is
/// `bench::scaling::shared_rows_holding_a_bounded_variable_print_in_linear_time`.
#[test]
fn forty_shared_rows_holding_a_bounded_variable_print_in_linear_text() {
    let (sent, got) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let texts: Result<Vec<(usize, usize, String)>, String> = [2, 3, 6, 40]
            .into_iter()
            .flat_map(|n| [(n, 0), (n, n)])
            .map(|(n, b)| printed_back(&bounded_rows(n, b), n).map(|t| (n, b, t)))
            .collect();
        let _ = sent.send(texts);
    });
    let texts = got
        .recv_timeout(std::time::Duration::from_secs(10))
        .expect("the signatures of 40 shared rows holding a bounded variable print within 10 s")
        .unwrap_or_else(|e| panic!("{e}"));
    for (n, b, text) in &texts {
        assert!(
            text.len() <= 64 * (n + 2),
            "a{b} bounded: {} bytes at {n} levels:\n{text}",
            text.len()
        );
        assert_eq!(text.matches(" for ").count(), 1, "a{b} bounded:\n{text}");
    }
    // At 6 levels, as the unbounded rows print: a row is named once it stands in another
    // part's body, so the two innermost rows are written in full inside `Part1`.
    let at_six = |b: usize| {
        (texts.iter())
            .find(|(n, bb, _)| *n == 6 && *bb == b)
            .map(|(_, _, t)| t.as_str())
            .expect("a text at six levels")
    };
    assert_eq!(
        at_six(0),
        "type Part1 = ((T, (T, U)), ((T, (T, U)), V));\ntype Part2 = (Part1, (Part1, W));\ntype Part3 = (Part2, (Part2, T5));\ntype Part4 = (Part3, (Part3, T6));\n(T, U, V, W, T5, T6, T7) -> (0, (Part4, (Part4, T7))) for T in int | f64"
    );
}

/// The function `h` that `f` returns bounds its own variable, `y`, which stands in rows held
/// twice at each level: `f`'s text names no part that holds `h`'s variable, as the bounds clause
/// of `h` is written inside `f`'s text, where `h` stands, and a definition is read at the top of
/// the text; so `h`'s rows are written in full. The text reads back as the signature.
///
/// Five levels (XR-heldname-print-batch r1, B4: at two, a row is short enough to be written in
/// full even where it could be named), with the control that letting a tuple holding a name
/// another function binds be written once (`set_ignore_other_binders`) makes the text name
/// parts, and so fails the test.
#[test]
fn a_returned_function_with_its_own_bound_writes_its_rows_in_full() {
    let src = "w(positional x: int | f64) = 0;\np(positional s, positional v) = (s, (s, v));\nf(positional a1, positional a2) = {\n  h(positional y) = (w(y), p(p(p(p(p(y, a1), a2), a1), a2), a1));\n  h\n};\n";
    let check = || -> Result<String, String> {
        let text = printed_back(src, 5)?;
        match !text.contains("type ") && text.matches(" for ").count() == 1 {
            true => Ok(text),
            false => Err(format!("names parts or clauses wrongly:\n{text}")),
        }
    };
    check().unwrap_or_else(|e| panic!("{e}"));
    zedc::check::ty::set_ignore_other_binders(true);
    let control = check();
    zedc::check::ty::set_ignore_other_binders(false);
    // The control's text itself names a part (round 3, Codex B-oracles), so that a failure to
    // print or read back cannot pass for it.
    assert!(
        matches!(&control, Err(e) if e.starts_with("names parts") && e.contains("type Part")),
        "the control prints as the test wants:\n{control:?}"
    );
}

/// A name bound by two functions in one text: `f` bounds `a0`, which stands in its shared
/// rows, five levels deep, and the function `h` it returns bounds `y` of its own. `f`'s rows
/// are written once, as definitions naming `f`'s variable; `h`'s variable keeps a name of its
/// own, with its own clause, and the text reads back as the signature.
#[test]
fn a_bound_of_the_outer_function_and_one_of_a_returned_function_print_apart() {
    let src = "w(positional x: int | f64) = 0;\np(positional s, positional v) = (s, (s, v));\nf(positional a0, positional a1, positional a2) = {\n  h(positional y) = (w(y), y);\n  (w(a0), p(p(p(p(p(a0, a1), a2), a1), a2), a1), h)\n};\n";
    let text = printed_back(src, 5).unwrap_or_else(|e| panic!("{e}"));
    assert!(text.contains("type Part1 = "), "{text}");
    assert_eq!(text.matches(" for ").count(), 2, "{text}");
}

/// The text of the signature `s`, read back with `read::parse_type`: the type read back,
/// compared with `s` both ways, and the read signature's bounded and held variables.
fn read_back_bounds(s: zedc::check::ty::Sig) -> Result<(String, Vec<String>, Vec<String>), String> {
    use std::sync::Arc;
    let text = s.to_string();
    let back = zedc::check::read::parse_type(&text).map_err(|e| format!("{text}\n  error: {e}"))?;
    let want = Ty::func(Arc::new(s));
    if !(back.subtype(&want) && want.subtype(&back)) {
        return Err(format!("{text}\n  reads back as another type: {back}"));
    }
    let read = (back.fns.iter().next()).ok_or_else(|| format!("{text}: no function"))?;
    let bounds = read.bounds.keys().map(|v| v.to_string()).collect();
    let held = read.held.iter().map(|v| v.to_string()).collect();
    Ok((text, bounds, held))
}

/// XR-heldname-print-batch round 1, Codex B1: a variable bounded by carriers that the printed
/// function binds, standing only inside rows written once as definitions and nowhere directly
/// in the arrow, must read back bounded. The fixture is Codex's: a one-arrow signature with `T`
/// its own variable, the carriers of `T -> T for T in int | f64`, and the result R_n, with R_0
/// = `(T, T)` and R_{i+1} = `(R_i, R_i)`, one row node at both places. Controls: the rows at one
/// level, written in full, read back bounded; and with `T` written directly at the parameter,
/// the six levels read back bounded.
#[test]
fn a_bound_used_only_in_lifted_parts_reads_back_as_bounded() {
    use super::standing_twice::read_sig;
    use std::sync::Arc;
    let bounded = read_sig("(a: T) -> T for T in int | f64");
    let t = bounded.arrows[0].result.clone();
    let rows = |n: usize| {
        (0..n).fold(Ty::tuple(vec![t.clone(), t.clone()]), |r, _| {
            Ty::tuple(vec![r.clone(), r])
        })
    };
    // `T` at no parameter: its own variable, bounded, held by none. With `T` at the parameter,
    // the parsed signature's own, held and bounds are taken as they are.
    let mut only = read_sig("(a: int) -> int");
    only.own.insert(Arc::from("T"));
    only.bounds = bounded.bounds.clone();
    let with = |base: &zedc::check::ty::Sig, n: usize| {
        let mut s = base.clone();
        s.arrows[0].result = rows(n);
        s
    };
    let cases = [
        ("lifted only, 6 levels", with(&only, 6), true),
        ("control: in full, 1 level", with(&only, 1), false),
        (
            "control: T at the parameter, 6 levels",
            with(&bounded, 6),
            true,
        ),
    ];
    let mut report = Vec::new();
    let mut bad = 0;
    for (name, s, lifted) in cases {
        match read_back_bounds(s) {
            Ok((text, bounds, held)) => {
                let named = text.contains("type Part");
                let ok = named == lifted && bounds == ["T"];
                bad += usize::from(!ok);
                report.push(format!(
                    "{name}: {}\n{text}\n  bounds read back {bounds:?}, held {held:?}",
                    if ok { "ok" } else { "WRONG" }
                ));
            }
            Err(e) => {
                bad += 1;
                report.push(format!("{name}: FAILS\n{e}"));
            }
        }
    }
    assert_eq!(bad, 0, "\n{}", report.join("\n"));
    // Control: a clause whose variable stands only in a definition the type never names
    // bounds nothing, and the reading still rejects it; the names a definition writes do not
    // excuse a clause the reader has not found on a signature.
    let unnamed = "type Part1 = (T, T);\n(a: int) -> int for T in int | f64";
    match zedc::check::read::parse_type(unnamed) {
        Ok(t) => panic!("`{unnamed}` reads back as {t}"),
        Err(e) => assert!(e.contains("is on no signature that names it"), "{e}"),
    }
}

/// XR-heldname-print-batch round 1, Codex B1, the held case: `T` stands directly only in the
/// result, so its bound reads back, but the parameters hold it only through `Part1`. The
/// signature's held variables (`Sig::held`, those a parameter holds) must be those of the text
/// written in full.
#[test]
fn a_bound_held_only_through_a_definition_is_held() {
    use super::standing_twice::read_sig;
    let full = read_sig("((T, T), (T, T)) -> T for T in int | f64");
    let named = read_sig("type Part1 = (T, T);\n(Part1, Part1) -> T for T in int | f64");
    let show = |s: &zedc::check::ty::Sig| format!("bounds {:?}, held {:?}", s.bounds, s.held);
    assert_eq!(
        (named.bounds.clone(), named.held.clone()),
        (full.bounds.clone(), full.held.clone()),
        "\nnamed: {}\nfull:  {}",
        show(&named),
        show(&full)
    );
}

/// XR-heldname-print-batch round 1, Claude C-1: the example of DESIGN.md (sec:diagnostics,
/// "Types in a message") of a bound in shared rows. At zed ad1433e it gave a text with two
/// definitions for `bounded_rows(3, 0)`, which the printer writes in full: there the would-be
/// `Part1` holds no named part and stands only in the type itself, not inside a definition,
/// so `defs::lift` writes it in full where it stands (round 2, Claude C-1: the reason is that
/// rule, not the length of the definitions). The example is now `bounded_rows(6, 0)`, whose
/// text is this, and reads back as the signature, bound and all ([`printed_back`]); the text at
/// three levels is pinned too.
#[test]
fn the_design_example_of_a_bound_in_shared_rows_prints_as_written() {
    assert_eq!(
        printed_back(&bounded_rows(3, 0), 3).unwrap_or_else(|e| panic!("{e}")),
        "(T, U, V, W) -> (0, (((T, (T, U)), ((T, (T, U)), V)), (((T, (T, U)), ((T, (T, U)), V)), W))) for T in int | f64"
    );
    assert_eq!(
        printed_back(&bounded_rows(6, 0), 6).unwrap_or_else(|e| panic!("{e}")),
        "type Part1 = ((T, (T, U)), ((T, (T, U)), V));\ntype Part2 = (Part1, (Part1, W));\ntype Part3 = (Part2, (Part2, T5));\ntype Part4 = (Part3, (Part3, T6));\n(T, U, V, W, T5, T6, T7) -> (0, (Part4, (Part4, T7))) for T in int | f64"
    );
}

/// XR-heldname-print-batch round 2, Claude C-2 and Gemini C2-1: the example of DESIGN.md
/// (sec:diagnostics, "Types in a message") of shared rows beside a union written `_`, `First`
/// of [`underscore_rows`] at three levels. The outer row stands at two places, one inside the
/// `_`, so it is written in full at the one place left; `Part1` stands inside it, a tuple the
/// type holds twice, so it is named. Read back, the outer row stands once, so `Part1` no longer
/// stands inside another part and the text printed again writes it in full.
#[test]
fn the_design_example_of_shared_rows_beside_a_blank_prints_as_written() {
    let text = sig_of(&underscore_rows(3, Underscore::First), "f").to_string();
    let params = "(T, U, V, W, xs: _, i: _, ys: _, j: _, c: bool, d: bool) -> ";
    assert_eq!(
        text,
        format!("type Part1 = ((T, (T, U)), ((T, (T, U)), V));\n{params}(_, (Part1, (Part1, W)))")
    );
    let back = zedc::check::read::parse_type(&text).unwrap_or_else(|e| panic!("{text}: {e}"));
    assert_eq!(
        back.to_string(),
        format!(
            "{params}(_, (((T, (T, U)), ((T, (T, U)), V)), (((T, (T, U)), ((T, (T, U)), V)), W)))"
        )
    );
}

/// XR-heldname-print-batch round 2, Gemini C1-1b and Codex C1: the example of DESIGN.md
/// (sec:diagnostics, "Types in a message") of rows over a variable bounded by a need, as the
/// fixes of round 2 (D4) print it. The need-bounded variable prints with no bounds clause, so
/// its rows are named as those of an unbounded variable, and the text reads back to itself with
/// that variable unbounded (row PRINT-need-bound-clause). One test per example (round 3): an
/// earlier single test stopped at its first example, so the second was never run alone.
#[test]
fn the_design_example_of_need_bounded_rows_prints_as_written() {
    use zedc::check::read::parse_type;
    use zedc::check::ty::OTHER;
    let need = sig_of(&need_bounded_rows(4), "f");
    assert!(need.bounds.values().any(|m| m & OTHER != 0), "{need}");
    let text = need.to_string();
    assert_eq!(
        text,
        "type Part1 = ((T, (T, U)), ((T, (T, U)), V));\ntype Part2 = (Part1, (Part1, W));\n(T, U, V, W, T5) -> (int, (Part2, (Part2, T5)))"
    );
    let back = parse_type(&text).unwrap_or_else(|e| panic!("{text}: {e}"));
    assert_eq!(back.to_string(), text);
    let read = back
        .fns
        .first()
        .unwrap_or_else(|| panic!("{text} reads back as no function"));
    assert!(read.bounds.values().all(|m| m & OTHER == 0), "{text}");
}

/// XR-heldname-print-batch round 2, Gemini C1-1b and Codex C1: the example of DESIGN.md
/// (sec:diagnostics, "Types in a message") of rows over a leftover. The rows over the leftover
/// `T \ #a` of [`leftover_rows`] at two levels are named, and the text reads back to itself
/// with the signature's one need.
#[test]
fn the_design_example_of_leftover_rows_prints_as_written() {
    use zedc::check::read::parse_type;
    let left = sig_of(&leftover_rows(2), "f");
    let text = left.to_string();
    assert_eq!(
        text,
        "type Part1 = #a | #a(..);\ntype Part2 = ((T \\ Part1) | 0, ((T \\ Part1) | 0, U));\n(T, U, V) -> (Part2, (Part2, V))"
    );
    let back = parse_type(&text).unwrap_or_else(|e| panic!("{text}: {e}"));
    assert_eq!(back.to_string(), text);
    let read = back
        .fns
        .first()
        .unwrap_or_else(|| panic!("{text} reads back as no function"));
    assert_eq!((read.needs.len(), left.needs.len()), (1, 1), "{text}");
}

/// XR-heldname-print-batch round 2, Gemini C1-2 and Codex C1: the example of DESIGN.md
/// (sec:diagnostics, "Types in a message") of an atom with a known payload shape in shared rows.
/// `(a0, #a(1))` holds one, so every row over it is written in full at each place
/// ([`Shared::of`] reads `payload_shapes`); `(a0, #a)` holds an atom with no payload, and its
/// rows are named. The full text doubles at each level, a gap of the printer that the text
/// states.
#[test]
fn a_known_payload_shape_writes_shared_rows_in_full() {
    let rows = |inner: &str| {
        let rows = (1..=3).fold(inner.to_string(), |s, i| format!("p({s}, a{i})"));
        let src = format!(
            "p(positional s, positional v) = (s, (s, v));\nf(positional a0, positional a1, positional a2, positional a3) = {rows};\n"
        );
        sig_of(&src, "f").to_string()
    };
    let r1 = "((T, #a(1)), ((T, #a(1)), U))";
    let r2 = format!("({r1}, ({r1}, V))");
    assert_eq!(
        rows("(a0, #a(1))"),
        format!("(T, U, V, W) -> ({r2}, ({r2}, W))")
    );
    assert_eq!(
        rows("(a0, #a)"),
        "type Part1 = ((T, #a), ((T, #a), U));\ntype Part2 = (Part1, (Part1, V));\n(T, U, V, W) -> (Part2, (Part2, W))"
    );
}

/// The function `(a: T) -> R_m for T in int | f64`, R_0 = `(T, c)` and R_{k+1} = `(R_k, R_k)`,
/// one row node at both places of each level.
fn rows_beside(c: Ty, m: usize) -> zedc::check::ty::Sig {
    let mut s = super::standing_twice::read_sig("(a: T) -> T for T in int | f64");
    let t = s.arrows[0].result.clone();
    s.arrows[0].result = (0..m).fold(Ty::tuple(vec![t, c]), |r, _| Ty::tuple(vec![r.clone(), r]));
    s
}

/// XR-heldname-print-batch round 3, Codex C-payload-control (D8 of META3): a set of atoms that
/// admits any payload, `#a(..)` (a kernel set, as the checker makes it for `#a` with a payload
/// it does not know), beside the function's own variable in shared rows does not keep the rows
/// from being named: the rows are written once. Control: an atom with a known payload shape,
/// `#a(int)` (`Ty::atom_of`), writes them in full at each place ([`Shared::of`] reads
/// `payload_shapes`). A guard of the text of DESIGN.md "Types in a message".
#[test]
fn kernel_any_payload_does_not_veto_local_rows() {
    let int = super::standing_twice::read_sig("(a: int) -> int").arrows[0]
        .result
        .clone();
    let any = Ty::set(KType::atom_with("a", &KType::top()));
    let known = Ty::atom_of("a", vec![int], BTreeMap::new());
    let (any, known) = (
        rows_beside(any, 4).to_string(),
        rows_beside(known, 4).to_string(),
    );
    assert!(any.contains("type Part"), "{any}");
    assert!(!known.contains("type Part"), "{known}");
}

/// XR-heldname-print-batch round 3, Codex C-eligibility (D8 of META3): shared rows over a
/// variable `X` that the function neither binds nor bounds are not named as definitions in
/// the function's text: only a variable the function owns or bounds may stand in a part it
/// names. Control: the same rows once the function owns `X` are named. A guard of the text of
/// DESIGN.md "Types in a message".
#[test]
fn a_repeated_row_with_an_external_variable_is_not_local() {
    use std::sync::Arc;
    let x = Ty::var(Arc::from("X"));
    let rows = (0..4).fold(Ty::tuple(vec![x.clone(), x]), |r, _| {
        Ty::tuple(vec![r.clone(), r])
    });
    let mut s = super::standing_twice::read_sig("(a: int) -> int");
    s.arrows[0].result = rows;
    let external = s.to_string();
    s.own.insert(Arc::from("X"));
    let owned = s.to_string();
    assert!(!external.contains("type Part"), "{external}");
    assert!(owned.contains("type Part"), "{owned}");
}

/// XR-heldname-print-batch round 3, Codex C-erasure-cost (D8 of META3): a union written `_`
/// beside shared rows holding a known payload shape does not make their text shorter: the rows
/// are still written in full at each place, 2^n copies of `#a(1)` at n levels for n = 2, 3, 4.
/// Control: with `#a` in place of `#a(1)` the rows are named at 3 and 4 levels, and `#a` is
/// written as often at each. At 2 levels no row is named, with `#a`, with `a0` in its place or
/// with no union beside it (b30-check's probe, round 3): the printer names a row only from that
/// depth on, as DESIGN.md's example of need-bounded rows writes `(T, (T, U))` four times. A
/// guard of the text of DESIGN.md "Types in a message", which no longer says the text stays
/// linear; row PLAN-print-payload-rows-exponential is to make it so.
#[test]
fn absorbed_union_beside_known_payload_rows_does_not_imply_compression() {
    let text = |inner: &str, n: usize| {
        let params: Vec<String> = (1..=n).map(|i| format!("positional a{i}")).collect();
        let rows = (1..=n).fold(inner.to_string(), |s, i| format!("p({s}, a{i})"));
        let src = format!(
            "p(positional s, positional v) = (s, (s, v));\nf(positional a0, {}, xs, i, c: bool) = ({rows}, if c {{ (0, 0) }} else {{ xs[i] }});\n",
            params.join(", ")
        );
        sig_of(&src, "f").to_string()
    };
    let mut bad = Vec::new();
    let (mut known, mut bare) = (Vec::new(), Vec::new());
    for n in [2, 3, 4] {
        let (k, b) = (text("(a0, #a(1))", n), text("(a0, #a)", n));
        if !k.contains(", _)") || !b.contains(", _)") {
            bad.push(format!("no union written `_`:\n{k}\n{b}"));
        }
        known.push(k.matches("#a(1)").count());
        if n == 2 {
            continue;
        }
        if !b.contains("type Part") {
            bad.push(format!("the bare atom's rows are not named:\n{b}"));
        }
        bare.push(b.matches("#a").count());
    }
    if known != [4, 8, 16] || bare.iter().any(|&c| c != bare[0]) {
        bad.push(format!("copies of #a(1) {known:?}, of #a {bare:?}"));
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// The rows of [`shared_rows`] over `a0`, which is passed to `apply` at a function that may
/// fail, so that it is bounded by what it is not (a need), not by carriers, at `n` levels.
fn need_bounded_rows(n: usize) -> String {
    let apply = "apply(f: (x: int | f64) ->? int) = f(x: 2.5) else #notFound -> 6;\n";
    let params: Vec<String> = (0..=n).map(|i| format!("positional a{i}")).collect();
    let rows = (1..=n).fold("a0".to_string(), |s, i| format!("p({s}, a{i})"));
    format!(
        "{apply}p(positional s, positional v) = (s, (s, v));\nf({}) = (apply(f: a0), {rows});\n",
        params.join(", ")
    )
}

/// XR-heldname-print-batch round 1, Claude C-2, and round 2, Codex B6-expansion: a variable
/// bounded by a need, not by carriers, that stands in shared rows six levels deep. Its bound
/// prints no clause, so the variable prints as one the function binds, and its rows are named
/// as definitions as the rows of an unbounded variable are ([`Shared::of`]). Round 1 wrote
/// them in full at each place, which doubled the text at each level (row
/// PRINT-need-bound-clause holds the missing clause, a gap of the printer older than this
/// batch).
#[test]
fn a_variable_bounded_by_a_need_is_named_in_shared_rows() {
    for (n, named) in [(1, false), (6, true)] {
        let s = sig_of(&need_bounded_rows(n), "f");
        let need = (s.bounds.iter()).find(|(_, m)| **m & zedc::check::ty::OTHER != 0);
        assert!(need.is_some(), "no variable bounded by a need: {s}");
        let text = s.to_string();
        assert_eq!(text.contains("type "), named, "{n} levels: {text}");
    }
}

/// XR-heldname-print-batch round 2, Codex B6-expansion: the text of [`need_bounded_rows`] at
/// `n` and `8n` levels is linear in `n`: at most 64 bytes a level, and at most 10.5 times longer
/// at 8 times the levels. Round 1 wrote the rows in full, 2^n copies of the innermost. The
/// print runs on a thread of its own with a time limit, so that the old path fails at the
/// limit.
#[test]
fn need_bounded_shared_rows_do_not_expand_paths() {
    let (sent, got) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let texts: Vec<(usize, String)> = [5, 40]
            .into_iter()
            .map(|n| (n, sig_of(&need_bounded_rows(n), "f").to_string()))
            .collect();
        let _ = sent.send(texts);
    });
    let texts = got
        .recv_timeout(std::time::Duration::from_secs(10))
        .expect("the signatures of 40 shared rows over a need-bounded variable print within 10 s");
    for (n, text) in &texts {
        assert!(
            text.len() <= 64 * (n + 2),
            "{} bytes at {n} levels:\n{text}",
            text.len()
        );
    }
    let (small, large) = (texts[0].1.len() as f64, texts[1].1.len() as f64);
    assert!(
        large <= 10.5 * small,
        "{small} bytes, then {large} at 8 times the levels"
    );
}

/// XR-heldname-print-batch round 1, Codex B3b, row PRINT-returned-bound-shared-rows-exponential:
/// the outer function returns `h`, which bounds its own `N`, with result R_m, R_0 = `(N, int)`
/// and R_{i+1} = `(R_i, R_i)`, one row node at both places. `N` is bound by `h`, not by the
/// outer function, so the print writes the rows in full (a definition would be read outside
/// `h`'s clause); a walk that only counts (`Sig::standing_twice`) writes each row's text once
/// for the opening of `h` ([`Walk::local`]) and enters O(m) tuples, where it entered each once
/// per path, 2^m. Checked at m and 8m, the work counted (`row_entries`). The outer function
/// binds a variable `A` of its own, at its parameter and in its result beside `h` (round 3,
/// Codex B-oracles), so the walk has an outer variable to count, which stands twice.
#[test]
fn returned_bound_shared_rows_do_not_expand_paths() {
    use super::standing_twice::read_sig;
    use std::sync::Arc;
    use zedc::check::ty::{reset_row_entries, row_entries};
    let h = read_sig("(x: N) -> N for N in int | f64");
    let n = h.arrows[0].result.clone();
    let int = read_sig("(a: int) -> int").arrows[0].result.clone();
    let outer = |m: usize| {
        let mut h = h.clone();
        h.arrows[0].result = (0..m).fold(Ty::tuple(vec![n.clone(), int.clone()]), |r, _| {
            Ty::tuple(vec![r.clone(), r])
        });
        let mut s = read_sig("(a: A) -> A for A in int | f64");
        let a = s.arrows[0].result.clone();
        s.arrows[0].result = Ty::tuple(vec![a, Ty::func(Arc::new(h))]);
        s
    };
    let mut work = Vec::new();
    for m in [20, 160] {
        let s = outer(m);
        reset_row_entries();
        let twice = s.standing_twice();
        let entries = row_entries();
        assert!(twice.contains("A") && !twice.contains("N"), "{twice:?}");
        assert!(
            entries > 0 && entries <= 8 * (m as u64 + 2),
            "{entries} tuples entered counting the places of {m} levels"
        );
        work.push(entries);
    }
    assert!(work[1] <= 10 * work[0], "{work:?}");
}

/// XR-heldname-print-batch round 1, Codex B4-N: [`Sig::standing_twice`] on 18 levels of
/// shared rows, unbounded and with a bound inside them, enters each row's text once, not once
/// per path: a deterministic count of the tuples it enters (`row_entries`), where the walk
/// before row PERF-standing-twice-shared-empty entered 2^18. Also 40 levels with a bound inside
/// the rows (Gemini B4-2), within a time limit: the bounded variable stands twice (at the
/// parameter and in the rows), as the printed text has it.
#[test]
fn standing_twice_enters_each_shared_row_a_bounded_number_of_times() {
    use zedc::check::ty::{reset_row_entries, row_entries};
    for (src, n) in [(shared_rows(18, false), 18), (bounded_rows(18, 0), 18)] {
        let s = sig_of(&src, "f");
        reset_row_entries();
        let _ = s.standing_twice();
        let entries = row_entries();
        assert!(
            entries > 0 && entries <= 8 * (n + 2),
            "{entries} tuples entered at {n} levels"
        );
    }
    let (sent, got) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let s = sig_of(&bounded_rows(40, 0), "f");
        reset_row_entries();
        let twice = s.standing_twice();
        let _ = sent.send((s, twice, row_entries()));
    });
    let (s, twice, entries) = got
        .recv_timeout(std::time::Duration::from_secs(10))
        .expect("the variables standing twice in 40 levels of shared rows are found within 10 s");
    assert!(entries <= 8 * 42, "{entries} tuples entered at 40 levels");
    let bounded: Vec<_> = s.bounds.keys().cloned().collect();
    assert!(!bounded.is_empty(), "{s}");
    for v in bounded {
        assert!(twice.contains(&v), "`{v}` does not stand twice: {twice:?}");
    }
}

/// The rows of [`shared_rows`] over what `a0 else #a -> 0` leaves of `a0`, at `n` levels: the
/// innermost row holds the leftover, printed `T \ s` with `s` = `#a | #a(..)`, which the
/// printer may name as a part (Gemini's witness in XR-heldname-print-batch round 1, B1-2).
fn leftover_rows(n: usize) -> String {
    let params: Vec<String> = (0..=n).map(|i| format!("positional a{i}")).collect();
    let rows = (1..=n).fold("r".to_string(), |s, i| format!("p({s}, a{i})"));
    format!(
        "p(positional s, positional v) = (s, (s, v));\nf({}) = {{ r = a0 else #a -> 0; {rows} }};\n",
        params.join(", ")
    )
}

/// XR-heldname-print-batch round 1, B1-2, and round 2, Codex B6-expansion: a row holding what
/// a test leaves of a variable is named as a definition, as other rows are. The reader makes
/// the difference `T \ #a` written in a definition once, by its variable and the text of what
/// it removes, and gives the signature that names the definition its need (zedc-check
/// `Denote::left_of`, `Denote::put_left`); round 1 read it only inside a function type, so in
/// a definition the need was lost, and wrote such rows in full, 2^n copies. Read back, the
/// text gives the same text and the same needs, one for each the signature has, of the same
/// kinds, at 6 levels and at 1. At 1
/// level, where no row is shared, it did not either: the reader made a new leftover, with its
/// own need, at each of the two places `T \ s` is written, and the need `Narrow::Not(s)`, not
/// the `Narrow::Atom` of `else #a`, which the printer writes as that `s` (zedc-check
/// `Denote::left_of`). The types are not compared both ways ([`printed_back`]): no signature
/// with a leftover, even `g(r) = r else #a -> 0`, is a subtype of the text read back, since
/// the leftover read has another name (`T\0`) than the signature's (`U`); measured, row
/// SUBTYPE-leftover-renamed.
#[test]
fn a_lifted_row_keeps_its_leftover_need_beside_an_absorbed_union() {
    let kinds = |s: &zedc::check::ty::Sig| -> Vec<String> {
        s.needs.iter().map(|n| format!("{:?}", n.kind)).collect()
    };
    let mut bad = Vec::new();
    for n in [1, 6] {
        let s = sig_of(&leftover_rows(n), "f");
        let text = s.to_string();
        let back = match zedc::check::read::parse_type(&text) {
            Ok(back) => back,
            Err(e) => {
                bad.push(format!("{n} levels: {text}: {e}"));
                continue;
            }
        };
        let (want, got) = (kinds(&s), back.fns.first().map(|b| kinds(b)));
        match () {
            () if !text.contains(" \\ ") => bad.push(format!("{n} levels, no leftover: {text}")),
            () if back.to_string() != text => {
                bad.push(format!("{n} levels: {text} reads back as {back}"))
            }
            () if want.len() != 1 || got.as_ref() != Some(&want) => bad.push(format!(
                "{n} levels: {text}\n  needs {want:?}\n  read  {got:?}"
            )),
            () => {}
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// [`leftover_rows`] beside a union the print writes `_` (a pair of ints or an element of `xs`
/// at a key the caller gives, which stand once): the absorbed union of Gemini's B1-2-N.
fn leftover_rows_beside_blank(n: usize) -> String {
    let params: Vec<String> = (0..=n).map(|i| format!("positional a{i}")).collect();
    let rows = (1..=n).fold("r".to_string(), |s, i| format!("p({s}, a{i})"));
    format!(
        "p(positional s, positional v) = (s, (s, v));\nf({}, xs, i, c: bool) = {{ r = a0 else #a -> 0; ({rows}, if c {{ (0, 0) }} else {{ xs[i] }}) }};\n",
        params.join(", ")
    )
}

/// XR-heldname-print-batch round 2, Gemini B1-2-N: the need read back from a text with a
/// leftover in rows named as definitions is on the variable of the first parameter, and what
/// it gives stands in the result, beside a union printed `_` and without one, at 1 and 6
/// levels; and the text reads back to itself with the signature's one narrowing need.
#[test]
fn a_leftover_need_read_back_is_on_the_parameter_and_gives_the_result() {
    use zedc::check::ty::{Need, NeedKind, Sig, Vars};
    let mut bad = Vec::new();
    for (form, rows) in [
        ("alone", leftover_rows as fn(usize) -> String),
        ("beside _", leftover_rows_beside_blank),
    ] {
        for n in [1, 6] {
            let s = sig_of(&rows(n), "f");
            let text = s.to_string();
            let back = match zedc::check::read::parse_type(&text) {
                Ok(back) => back,
                Err(e) => {
                    bad.push(format!("{form}, {n} levels: {text}: {e}"));
                    continue;
                }
            };
            let Some(read) = back.fns.first() else {
                bad.push(format!("{form}, {n} levels: {text}: no function"));
                continue;
            };
            // The leftover's need only: beside `_`, `xs[i]` gives `xs` an `Index` need too,
            // and `xs` prints `_`, so that need does not read back.
            let narrow = |n: &&Need| matches!(n.kind, NeedKind::Narrow(_));
            let kinds = |s: &Sig| -> Vec<String> {
                (s.needs.iter().filter(narrow))
                    .map(|n| format!("{:?}", n.kind))
                    .collect()
            };
            let (want, got) = (kinds(s.as_ref()), kinds(read.as_ref()));
            let (Some(need), [arrow]) = (read.needs.iter().find(narrow), &read.arrows[..]) else {
                bad.push(format!("{form}, {n} levels: {text}: needs {got:?}"));
                continue;
            };
            let on_param = need.on.as_var().is_some() && need.on == arrow.params[0];
            let mut in_result = Vars::default();
            arrow.result.vars_in(&mut in_result);
            let gives = (need.result.as_ref().and_then(|r| r.as_var()))
                .is_some_and(|v| in_result.contains(v));
            match () {
                () if back.to_string() != text => {
                    bad.push(format!("{form}, {n} levels: {text} reads back as {back}"))
                }
                () if want.len() != 1 || got != want => bad.push(format!(
                    "{form}, {n} levels: {text}\n  needs {want:?}\n  read  {got:?}"
                )),
                () if !on_param || !gives => bad.push(format!(
                    "{form}, {n} levels: {text}\n  need on {:?}, gives {:?}",
                    need.on, need.result
                )),
                () => {}
            }
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// The paths in `t` to each type that holds the variable `v`: a path is the row and component
/// index at each tuple on the way, the empty path `t` itself.
fn var_paths(t: &Ty, v: &str, at: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
    if t.vars.iter().any(|x| &**x == v) {
        out.push(at.clone());
    }
    for (r, row) in t.tuples.iter().enumerate() {
        for (i, c) in row.iter().enumerate() {
            at.extend([r, i]);
            var_paths(c, v, at, out);
            at.truncate(at.len() - 2);
        }
    }
}

/// The needs of `s`, in order, with no variable named: for each, the parameter it is on (its
/// slot in the first arrow), what it does, and the paths in the first arrow's result to what
/// it gives. Two signatures that differ only in the names of their variables and the spans of
/// their needs have the same graph, which subtyping cannot see for a need that leaves a
/// variable (row SUBTYPE-leftover-renamed).
type NeedGraph = Vec<(Option<usize>, String, Vec<Vec<usize>>)>;
fn need_graph(s: &zedc::check::ty::Sig) -> NeedGraph {
    let Some(arrow) = s.arrows.first() else {
        return Vec::new();
    };
    (s.needs.iter())
        .map(|n| {
            let slot = arrow.params.iter().position(|p| *p == n.on);
            let mut paths = Vec::new();
            if let Some(v) = n.result.as_ref().and_then(|r| r.as_var()) {
                var_paths(&arrow.result, v, &mut Vec::new(), &mut paths);
            }
            (slot, format!("{:?}", n.kind), paths)
        })
        .collect()
}

/// The need graph ([`need_graph`]) of each function `text` reads as: the type itself, or each
/// function in the tuple it is, in order.
fn need_graphs(text: &str) -> Result<Vec<NeedGraph>, String> {
    let t = zedc::check::read::parse_type(text)?;
    let fns: Vec<_> = match t.tuples.iter().next() {
        Some(r) => r.iter().flat_map(|c| c.fns.iter().cloned()).collect(),
        None => t.fns.iter().cloned().collect(),
    };
    Ok(fns.iter().map(|s| need_graph(s)).collect())
}

/// XR-heldname-print-batch round 3, Codex B-left-order (D6 of META3): the needs of the
/// leftovers definitions write are put on the function in the order their uses stand in the
/// text written out: `#a`'s, in `Part1`, then `#b`'s. Needs are compared in order (`Needs::eq`,
/// the digests), so two orders are two signatures. Before, the walk put the need of the
/// definition it entered first before those of the definitions it names, `#b` then `#a`.
/// Control: the text written out with the two removed sets swapped has the other order, so the
/// comparison sees an order.
#[test]
fn leftover_needs_are_installed_in_inlined_first_use_order() {
    let named =
        need_graphs("type Part1 = (T \\ #a, T);\ntype Part2 = (Part1, T \\ #b);\nT -> Part2");
    let full = need_graphs("T -> ((T \\ #a, T), T \\ #b)");
    let swapped = need_graphs("T -> ((T \\ #b, T), T \\ #a)");
    assert!(full.is_ok() && swapped.is_ok(), "{full:?}\n{swapped:?}");
    assert_ne!(full, swapped);
    assert_eq!(named, full);
}

/// XR-heldname-print-batch round 3, Codex two owners (D7 of META3): a definition holding a
/// leftover, named by two sibling functions through a second definition, gives each function
/// its own need on its own `T`, with what it gives at each place, as the text written out does.
/// A guard: Gemini ran this case on 91ad6f5a4 and each function had its need.
#[test]
fn a_leftover_definition_installs_one_need_per_outer_signature() {
    let named = "type Part1 = (T \\ #a, T);\ntype Part2 = (Part1, Part1);\n(T -> Part2, ((T, int) -> Part2))";
    let full = "(T -> ((T \\ #a, T), (T \\ #a, T)), ((T, int) -> ((T \\ #a, T), (T \\ #a, T))))";
    let (a, b) = (need_graphs(named), need_graphs(full));
    match &b {
        Ok(gs) if gs.len() == 2 && gs.iter().all(|g| g.len() == 1 && g[0].2.len() == 2) => {}
        _ => panic!("`{full}` reads as {b:?}"),
    }
    assert_eq!(a, b, "{named}");
}

/// XR-heldname-print-batch round 3, Codex B-oracles (D7 of META3): the signature of
/// [`leftover_rows`] at 1 and 6 levels and the type its text reads back as have the same need
/// graph ([`need_graph`]): the need on the first parameter, what it removes, and every place
/// of what it gives. Controls: moving what the need gives to another place of the result, or
/// the need to another parameter, changes the graph.
#[test]
fn a_leftover_read_back_keeps_its_need_graph() {
    let mut bad = Vec::new();
    for n in [1, 6] {
        let s = sig_of(&leftover_rows(n), "f");
        let text = s.to_string();
        match need_graphs(&text) {
            Ok(back) if back.len() == 1 && back[0] == need_graph(&s) => {}
            got => bad.push(format!(
                "{n} levels: {text}\n  wants {:?}\n  reads {got:?}",
                need_graph(&s)
            )),
        }
    }
    for (a, b) in [
        ("T -> (T \\ #a, T)", "T -> (T, T \\ #a)"),
        ("(T, U) -> (T \\ #a, U)", "(T, U) -> (U \\ #a, T)"),
    ] {
        match (need_graphs(a), need_graphs(b)) {
            (Ok(x), Ok(y)) if x != y => {}
            got => bad.push(format!("`{a}` and `{b}` read as {got:?}")),
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// XR-heldname-print-batch round 2, Codex B6-expansion: the text of [`leftover_rows`] at `n` and
/// `8n` levels is linear in `n`: at most 64 bytes a level, at most 10.5 times longer at 8 times
/// the levels, and at `n` it reads back to itself with the signature's one need. Round 1 wrote
/// rows holding a leftover in full, 2^n copies of the innermost; the print runs on a thread of
/// its own with a time limit, so that the old path fails at the limit.
#[test]
fn leftover_shared_rows_print_in_linear_text() {
    let (sent, got) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let texts: Vec<(usize, zedc::check::ty::Sig, String)> = [5, 40]
            .into_iter()
            .map(|n| {
                let s = sig_of(&leftover_rows(n), "f");
                let text = s.to_string();
                (n, (*s).clone(), text)
            })
            .collect();
        let _ = sent.send(texts);
    });
    let texts = got
        .recv_timeout(std::time::Duration::from_secs(10))
        .expect("the signatures of 40 shared rows over a leftover print within 10 s");
    for (n, _, text) in &texts {
        assert!(
            text.len() <= 64 * (n + 2),
            "{} bytes at {n} levels:\n{text}",
            text.len()
        );
    }
    let (small, large) = (texts[0].2.len() as f64, texts[1].2.len() as f64);
    assert!(
        large <= 10.5 * small,
        "{small} bytes, then {large} at 8 times the levels"
    );
    let (_, s, text) = &texts[0];
    assert!(text.contains("type Part"), "{text}");
    let back = zedc::check::read::parse_type(text).unwrap_or_else(|e| panic!("{text}: {e}"));
    assert_eq!(back.to_string(), *text);
    let kinds = |s: &zedc::check::ty::Sig| -> Vec<String> {
        s.needs.iter().map(|n| format!("{:?}", n.kind)).collect()
    };
    assert_eq!(back.fns.first().map(|b| kinds(b)), Some(kinds(s)), "{text}");
}

/// XR-heldname-print-batch round 2, Codex B1-clause and Gemini B1-NEW: a definition that a
/// clause's signature names supplies that clause, and no other. Each text has a sibling clause
/// whose signature names no `T` (or a type that is no function), which bounds nothing and is
/// rejected, though another signature names `T` through `Part1`; round 2 excused every clause
/// of a name some definition writes. Controls: the same sibling naming `Part1` reads, and the
/// text without the sibling reads.
#[test]
fn a_used_definition_does_not_excuse_a_vacant_sibling_clause() {
    let part = "type Part1 = (T, T);\n";
    let rejected = [
        "(((a: Part1) -> int for T in int | f64), ((b: int) -> int for T in int | f64))",
        "(((a: T) -> int for T in int | f64), ((b: int) -> int for T in int | f64))",
        "(((a: Part1) -> int for T in int | f64), int for T in int | f64)",
        // Round 3, Gemini B1-A: the sibling's clause stands on `Part1`, not on a function type.
        "(((a: Part1) -> int for T in int | f64), ((b: int) -> (Part1 for T in int | f64)))",
    ];
    let read = [
        "(((a: Part1) -> int for T in int | f64), ((b: Part1) -> int for T in int | f64))",
        "(a: Part1) -> int for T in int | f64",
    ];
    let mut bad = Vec::new();
    for (text, ok) in (rejected.iter().map(|t| (t, false))).chain(read.iter().map(|t| (t, true))) {
        let text = format!("{part}{text}");
        match (zedc::check::read::parse_type(&text), ok) {
            (Ok(t), false) => bad.push(format!("`{text}` reads as {t}")),
            (Err(e), true) => bad.push(format!("`{text}` is rejected: {e}")),
            _ => {}
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// The resolver's words for a bounded variable used outside every function type of its clause
/// (`zedc_resolve::resolve`'s `type_var`).
const OUTSIDE: &str = "stands outside a function type";
/// The resolver's words for a bounded variable used in two function types of its clause.
const TWO: &str = "stands in two function types";

/// Checks each of `cases`, a text after `type Part1 = (T, T);` and the resolver's words it is
/// rejected with (`None`: it reads): the text, and the text with `Part1` written out, which the
/// reader must treat alike (a use of a bounded variable through a definition meets the rules of
/// a written use). A rejection in other words, as a parse error before the reading, is reported
/// as such, so that a text the grammar refuses is seen and replaced, not passed.
fn clause_home_cases(cases: &[(&str, Option<&str>)]) -> Vec<String> {
    let mut bad = Vec::new();
    for &(text, want) in cases {
        let full = text.replace("Part1", "(T, T)");
        let named = format!("type Part1 = (T, T);\n{text}");
        for t in [&named, &full] {
            match (zedc::check::read::parse_type(t), want) {
                (Ok(_), None) => {}
                (Err(e), Some(w)) if e.contains(w) => {}
                (Ok(ty), Some(w)) => bad.push(format!("`{t}` reads as {ty}; wants `{w}`")),
                (Err(e), w) => bad.push(format!("`{t}` is rejected: {e}; wants {w:?}")),
            }
        }
    }
    bad
}

/// XR-heldname-print-batch round 3, Claude F1 (D1 of META3): a use of a bounded variable
/// through a definition meets the two rules the resolver applies to a written use: it stands
/// in a function type of its clause, and in one only (an overload is one). Before, a name for a
/// definition read under a clause marked the clause used before it looked for the clause's
/// function type, and checked neither rule, so (a)-(d) read though written out each is
/// rejected. Controls that read: the same uses in one function type, or with a clause each.
#[test]
fn a_use_through_a_definition_meets_the_rules_of_a_written_use() {
    let bad = clause_home_cases(&[
        (
            "(((a: T) -> int for T in int | f64), ((b: int) -> (Part1 for T in f64)))",
            Some(OUTSIDE),
        ),
        (
            "(((a: Part1) -> int), ((b: Part1) -> int)) for T in int | f64",
            Some(TWO),
        ),
        (
            "(((a: T) -> int), ((b: Part1) -> int)) for T in int | f64",
            Some(TWO),
        ),
        (
            "(Part1, (a: Part1) -> int) for T in int | f64",
            Some(OUTSIDE),
        ),
        ("(a: Part1) -> (Part1, int) for T in int | f64", None),
        (
            "(((a: Part1) -> int), ((b: int) -> int)) for T in int | f64",
            None,
        ),
        (
            "(((a: Part1) -> int for T in int | f64), ((b: Part1) -> int for T in int | f64))",
            None,
        ),
        // An overload is one function type: its arrows share the clause (the reader gave each
        // arrow its own function type in the first form of the fix).
        (
            "(((a: Part1) -> int) & ((a: Part1) -> f64)) for T in int | f64",
            None,
        ),
        (
            "(((a: T) -> int) & ((a: T) -> Part1)) for T in int | f64",
            None,
        ),
    ]);
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// XR-heldname-print-batch round 3, Codex B-clause-home (D1 of META3): the clause home of a use
/// through a definition is the one of its literal expansion. Rejected: two sibling function
/// types under one clause, each naming `Part1`; and a clause on `Part1` beside a function type,
/// inside an outer one, after a sibling that supplies `T` under a clause of its own. Read:
/// both names under one function type, and a clause on each sibling.
#[test]
fn a_definition_use_obeys_the_clause_home_of_literal_expansion() {
    let bad = clause_home_cases(&[
        ("(int -> Part1, f64 -> Part1) for T in int", Some(TWO)),
        (
            "int -> ((int -> Part1 for T in int), (Part1 for T in f64))",
            Some(OUTSIDE),
        ),
        ("int -> (Part1, Part1) for T in int", None),
        (
            "((int -> Part1 for T in int), (f64 -> Part1 for T in int))",
            None,
        ),
    ]);
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// Whether `a` and `b` read alike: both rejected, or both read, each type a subtype of the
/// other.
fn read_alike(a: &str, b: &str) -> Result<(), String> {
    use zedc::check::read::parse_type;
    match (parse_type(a), parse_type(b)) {
        (Err(_), Err(_)) => Ok(()),
        (Ok(x), Ok(y)) if x.subtype(&y) && y.subtype(&x) => Ok(()),
        (x, y) => Err(format!("`{a}` reads {x:?}\n`{b}` reads {y:?}")),
    }
}

/// XR-heldname-print-batch round 2, Codex B1-edge: a field label that spells a definition's
/// name, as `Part1` in `#x(Part1: int)`, is no use of the definition: it supplies no variable to
/// a clause (round 2 took the label for an edge to `Part1`, so `T` read as held and the clause
/// was accepted), and it does not count toward the times a name is written (`Times`). Each text
/// reads as the text with the definitions written out. Control: a true reference,
/// `#x(v: Part1)`, supplies `T`.
#[test]
fn a_part_field_label_is_not_a_definition_use() {
    let cases = [
        (
            "type Part1 = (T, T);\ntype Part2 = #x(Part1: int);\n(a: Part2) -> int for T in int | f64",
            "(a: #x(Part1: int)) -> int for T in int | f64",
        ),
        (
            "type Part1 = (T, int);\ntype Part2 = #x(Part1: int);\n(a: Part2, b: Part1) -> int",
            "(a: #x(Part1: int), b: (T, int)) -> int",
        ),
    ];
    let mut bad: Vec<String> = cases
        .iter()
        .filter_map(|(named, full)| read_alike(named, full).err())
        .collect();
    let labelled = cases[0].0;
    if zedc::check::read::parse_type(labelled).is_ok() {
        bad.push(format!("`{labelled}` reads"));
    }
    let control =
        "type Part1 = (T, T);\ntype Part2 = #x(v: Part1);\n(a: Part2) -> int for T in int | f64";
    match read_back_bounds_of(control) {
        Ok(bounds) if bounds == ["T"] => {}
        got => bad.push(format!("`{control}`: {got:?}")),
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// The own variables of each function `text` reads as, the type itself or each function in the
/// tuple it is, in order.
fn own_sets(text: &str) -> Result<Vec<Vec<String>>, String> {
    let t = zedc::check::read::parse_type(text)?;
    let fns: Vec<_> = match t.tuples.iter().next() {
        Some(r) => r.iter().flat_map(|c| c.fns.iter().cloned()).collect(),
        None => t.fns.iter().cloned().collect(),
    };
    Ok(fns
        .iter()
        .map(|s| s.own.iter().map(|v| v.to_string()).collect())
        .collect())
}

/// XR-heldname-print-batch round 3, Codex B-label-free and Gemini B5-free-label (D4 of META3):
/// a field label `T` in a definition, as in `#x(T: int)`, is no use of a variable `T`, so a
/// sibling function type that writes `T` twice does not give the definition's function type an
/// own variable `T`. Before, the scan for a definition's free names took every capitalized
/// token written twice in the text, the label included. Each text gives the own variables of
/// the text written out. Control: a true field type `T`, `#x(v: T)`, is a use.
#[test]
fn a_field_label_does_not_add_an_own_variable_from_a_sibling() {
    let cases = [
        (
            "type Part1 = #x(T: int);\n",
            "(int -> Part1, T -> T)",
            "#x(T: int)",
        ),
        (
            "type Part1 = #x(T: int);\n",
            "((a: Part1) -> int, (b: T, c: T) -> int)",
            "#x(T: int)",
        ),
        (
            "type Part1 = #x(v: T);\n",
            "((a: Part1) -> int, (b: T, c: T) -> int)",
            "#x(v: T)",
        ),
    ];
    let mut bad = Vec::new();
    for (def, text, body) in cases {
        let named = format!("{def}{text}");
        let full = text.replace("Part1", body);
        match (own_sets(&named), own_sets(&full)) {
            (Ok(a), Ok(b)) if a == b => {}
            (a, b) => bad.push(format!("`{named}` owns {a:?}\n`{full}` owns {b:?}")),
        }
    }
    match own_sets("type Part1 = #x(v: T);\n((a: Part1) -> int, (b: T, c: T) -> int)") {
        Ok(owns) if owns.first().is_some_and(|o| o.iter().any(|v| v == "T")) => {}
        got => bad.push(format!("the control's first function owns no `T`: {got:?}")),
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// The bounded variables of the first function `text` reads as.
fn read_back_bounds_of(text: &str) -> Result<Vec<String>, String> {
    let t = zedc::check::read::parse_type(text)?;
    let read = t.fns.first().ok_or("no function")?;
    Ok(read.bounds.keys().map(|v| v.to_string()).collect())
}

/// A chain of `m` definitions over `T`, R_1 = `(T, T)` and R_{k+1} = `(R_k, R_k)`, and one
/// function bounding `T` whose result holds `f` functions `(x: int) -> (R_m, i)`, for `i` from
/// 0; with `outer`, its parameter is R_m as well. Codex's witness of XR-heldname-print-batch
/// round 2, B1-cost.
fn inner_arrows(m: usize, f: usize, outer: bool) -> String {
    let mut text = "type Part1 = (T, T);\n".to_string();
    for k in 2..=m {
        text += &format!("type Part{k} = (Part{0}, Part{0});\n", k - 1);
    }
    let inner: Vec<String> = (0..f)
        .map(|i| format!("((x: int) -> (Part{m}, {i}))"))
        .collect();
    let param = if outer {
        format!("Part{m}")
    } else {
        "int".into()
    };
    text + &format!("(a: {param}) -> ({}) for T in int | f64", inner.join(", "))
}

/// [`inner_arrows`] with each definition written out where it is named.
fn inner_arrows_full(m: usize, f: usize, outer: bool) -> String {
    let row = (1..m).fold("(T, T)".to_string(), |r, _| format!("({r}, {r})"));
    let inner: Vec<String> = (0..f)
        .map(|i| format!("((x: int) -> ({row}, {i}))"))
        .collect();
    let param = if outer { row.clone() } else { "int".into() };
    format!("(a: {param}) -> ({}) for T in int | f64", inner.join(", "))
}

/// XR-heldname-print-batch round 2, Codex B1-cost: reading [`inner_arrows`] enters each
/// definition a bounded number of times, not once for each inner function: at most
/// 2(m + f) + 8 entries (`read::def_entries`) at m = f = 64 and 512, with `T` at the outer
/// parameter and without. Round 2 began each inner function's reading with no definition
/// walked, Θ(m·f) entries. At m = f = 3 the text reads as the text written out, with the same
/// bounded and held variables.
#[test]
fn reading_shared_definitions_across_inner_arrows_scales() {
    use zedc::check::read::{def_entries, parse_type, reset_def_entries};
    let mut bad = Vec::new();
    for outer in [false, true] {
        for n in [64, 512] {
            let text = inner_arrows(n, n, outer);
            reset_def_entries();
            let read = parse_type(&text);
            let entries = def_entries();
            match read {
                Err(e) => bad.push(format!("{n}, outer {outer}: {e}")),
                Ok(_) if entries == 0 || entries > 2 * (2 * n as u64) + 8 => {
                    bad.push(format!("{n}, outer {outer}: {entries} definitions entered"))
                }
                Ok(_) => {}
            }
        }
        let (named, full) = (inner_arrows(3, 3, outer), inner_arrows_full(3, 3, outer));
        let sigs = |t: &str| -> Result<(Ty, Vec<String>, Vec<String>), String> {
            let ty = parse_type(t)?;
            let s = ty.fns.first().ok_or("no function")?.clone();
            let bounds = s.bounds.keys().map(|v| v.to_string()).collect();
            let held = s.held.iter().map(|v| v.to_string()).collect();
            Ok((ty, bounds, held))
        };
        match (sigs(&named), sigs(&full)) {
            (Ok((a, ab, ah)), Ok((b, bb, bh)))
                if a.subtype(&b) && b.subtype(&a) && ab == bb && ah == bh => {}
            (a, b) => bad.push(format!(
                "outer {outer}:\n`{named}` reads {a:?}\n`{full}` reads {b:?}"
            )),
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// [`inner_arrows`] without the outer parameter, each inner function with a clause of its
/// own, `((x: U) -> (Partm, U) for U in int)`, as the printer writes an inner signature that
/// bounds a variable: a clause that names no name a definition writes.
fn inner_clauses(m: usize, f: usize) -> String {
    let mut text = "type Part1 = (T, T);\n".to_string();
    for k in 2..=m {
        text += &format!("type Part{k} = (Part{0}, Part{0});\n", k - 1);
    }
    let inner: Vec<String> = (0..f)
        .map(|_| format!("((x: U) -> (Part{m}, U) for U in int)"))
        .collect();
    text + &format!("(a: T) -> ({}) for T in int | f64", inner.join(", "))
}

/// XR-heldname-print-batch round 3, Claude F3 (D3 of META3): reading [`inner_clauses`] enters
/// each definition a bounded number of times, at most 2(2n) + 8 (`read::def_entries`) at
/// m = f = n = 64 and 512, and more than none. Before, each inner clause pushed a clause and
/// walked every definition again, m·f entries, though no definition writes `U`.
#[test]
fn reading_shared_definitions_across_inner_clauses_scales() {
    use zedc::check::read::{def_entries, parse_type, reset_def_entries};
    let mut bad = Vec::new();
    for n in [64, 512] {
        let text = inner_clauses(n, n);
        reset_def_entries();
        let read = parse_type(&text);
        let entries = def_entries();
        match read {
            Err(e) => bad.push(format!("{n}: {e}")),
            Ok(_) if entries == 0 || entries > 2 * (2 * n as u64) + 8 => {
                bad.push(format!("{n}: {entries} definitions entered"))
            }
            Ok(_) => {}
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// A chain of `m` closed definitions, R_1 = `(int, int)` and R_{k+1} = `(R_k, R_k)`, and a
/// tuple of `f` sibling functions `(x: int) -> (R_m, i)`, for `i` from 0, with no clause:
/// Codex's witness of XR-heldname-print-batch round 3, B-neutral-DAG. With `full`, each
/// definition is written out where it is named.
fn closed_sibling_arrows(m: usize, f: usize, full: bool) -> String {
    let mut text = "type Part1 = (int, int);\n".to_string();
    for k in 2..=m {
        text += &format!("type Part{k} = (Part{0}, Part{0});\n", k - 1);
    }
    let row = match full {
        true => (1..m).fold("(int, int)".to_string(), |r, _| format!("({r}, {r})")),
        false => format!("Part{m}"),
    };
    let inner: Vec<String> = (0..f)
        .map(|i| format!("((x: int) -> ({row}, {i}))"))
        .collect();
    match full {
        true => format!("({})", inner.join(", ")),
        false => text + &format!("({})", inner.join(", ")),
    }
}

/// XR-heldname-print-batch round 3, Codex B-neutral-DAG (D3 of META3): reading
/// [`closed_sibling_arrows`] enters each definition a bounded number of times, at most
/// 2(2n) + 8 (`read::def_entries`) at m = f = n = 64 and 512. The definitions hold no free,
/// unbound or leftover name, so walking them changes nothing; before, each sibling opened its
/// own outermost frame and walked all m, m·f entries. At m = f = 3 the text reads as the text
/// written out. Guard: a definition that holds no variable itself but names one that holds a
/// bounded `T` still gives `T` to the function that names it.
#[test]
fn reading_closed_shared_definitions_across_sibling_arrows_scales() {
    use zedc::check::read::{def_entries, parse_type, reset_def_entries};
    let mut bad = Vec::new();
    for n in [64, 512] {
        let text = closed_sibling_arrows(n, n, false);
        reset_def_entries();
        let read = parse_type(&text);
        let entries = def_entries();
        match read {
            Err(e) => bad.push(format!("{n}: {e}")),
            Ok(_) if entries > 2 * (2 * n as u64) + 8 => {
                bad.push(format!("{n}: {entries} definitions entered"))
            }
            Ok(_) => {}
        }
    }
    let (named, full) = (
        closed_sibling_arrows(3, 3, false),
        closed_sibling_arrows(3, 3, true),
    );
    if let Err(e) = read_alike(&named, &full) {
        bad.push(e);
    }
    let chain = "type Part1 = (T, T);\ntype Part2 = (Part1, int);\n(a: int) -> (Part2, int) for T in int | f64";
    match read_back_bounds_of(chain) {
        Ok(b) if b == ["T"] => {}
        got => bad.push(format!("`{chain}` bounds {got:?}")),
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// XR-heldname-print-batch round 3, Codex B-left-index and Gemini B3-new-lefts-scan (D2 of
/// META3): one definition of k distinct leftovers `T \ #k0` … `T \ #k(k-1)`, each written
/// twice, read in `T -> (Part1, Part1)`. Finding the variable of each leftover's key looks at
/// no more than 4k leftovers (`read::left_probes`) at k = 64 and 512; before, each looked at
/// every distinct leftover read before it in the definition, about k² in all. Each repeated
/// key reuses its first variable: the function has k needs, each giving a variable of its own.
#[test]
fn reading_one_definition_with_many_distinct_leftovers_scales() {
    use zedc::check::read::{left_probes, parse_type, reset_left_probes};
    let text = |k: usize| {
        let parts: Vec<String> = (0..k)
            .flat_map(|i| [format!("T \\ #k{i}"), format!("T \\ #k{i}")])
            .collect();
        format!("type Part1 = ({});\nT -> (Part1, Part1)", parts.join(", "))
    };
    let mut bad = Vec::new();
    for k in [64, 512] {
        reset_left_probes();
        let read = parse_type(&text(k));
        let probes = left_probes();
        let read = match read {
            Ok(read) => read,
            Err(e) => {
                bad.push(format!("{k}: {e}"));
                continue;
            }
        };
        if probes == 0 || probes > 4 * k as u64 {
            bad.push(format!("{k} distinct leftovers: {probes} probes"));
        }
        let Some(s) = read.fns.first() else {
            bad.push(format!("{k}: no function"));
            continue;
        };
        // By the variable's name: printed alone, each variable prints by a name drawn anew, `T`.
        let gives: std::collections::BTreeSet<String> = (s.needs.iter())
            .filter_map(|n| n.result.as_ref()?.as_var().map(|v| v.to_string()))
            .collect();
        if s.needs.len() != k || gives.len() != k {
            bad.push(format!(
                "{k} distinct leftovers: {} needs giving {} variables",
                s.needs.len(),
                gives.len()
            ));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// XR-heldname-print-batch round 2, Gemini B5-REG: [`Sig::standing_twice`] on a function whose
/// result holds `m` functions `(x: int) -> (R_m, i)`, over rows R_0 = `(T, T)` and R_{k+1} =
/// `(R_k, R_k)` that hold only the outer function's `T`, enters each row a bounded number of
/// times, not once for each inner function: at most 8(m + 2) tuples (`row_entries`) at m = 64
/// and 512. Round 2 keyed every row by the inner function it stood in, Θ(m²) entries. Control:
/// a row `(T, int)` that stands once in the outer function and once in a function `h` that
/// binds a `T` of its own holds each `T` once, so neither stands twice.
#[test]
fn standing_twice_does_not_reenter_owner_rows_per_inner_lambda() {
    use super::standing_twice::read_sig;
    use std::sync::Arc;
    use zedc::check::ty::{reset_row_entries, row_entries};
    let bounded = read_sig("(a: T) -> T for T in int | f64");
    let t = bounded.arrows[0].result.clone();
    let mut bad = Vec::new();
    for m in [64, 512] {
        let row = (0..m).fold(Ty::tuple(vec![t.clone(), t.clone()]), |r, _| {
            Ty::tuple(vec![r.clone(), r])
        });
        let inner: Vec<Ty> = (0..m)
            .map(|i| {
                let mut h = read_sig(&format!("(x: int) -> {i}"));
                let lit = h.arrows[0].result.clone();
                h.arrows[0].result = Ty::tuple(vec![row.clone(), lit]);
                Ty::func(Arc::new(h))
            })
            .collect();
        let mut s = bounded.clone();
        s.arrows[0].result = Ty::tuple(inner);
        reset_row_entries();
        let twice = s.standing_twice();
        let entries = row_entries();
        if entries == 0 || entries > 8 * (m as u64 + 2) {
            bad.push(format!("{entries} tuples entered at {m} inner functions"));
        }
        if !twice.contains("T") {
            bad.push(format!("`T` does not stand twice at {m}: {twice:?}"));
        }
    }
    let row = read_sig("(x: (T, int)) -> int").arrows[0].params[0].clone();
    let mut h = read_sig("(x: int) -> int");
    h.own.insert(Arc::from("T"));
    h.arrows[0].result = row.clone();
    let mut s = read_sig("(a: int) -> int");
    s.own.insert(Arc::from("T"));
    s.arrows[0].result = Ty::tuple(vec![row, Ty::func(Arc::new(h))]);
    let twice = s.standing_twice();
    if twice.contains("T") {
        bad.push(format!("shadowed `T` stands twice in {s}: {twice:?}"));
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// The function of [`standing_twice_does_not_reenter_owner_rows_per_inner_lambda`] at `m`, with
/// one more inner function beside the `m`: one that binds a `T` of its own, `(x: int) -> T`.
fn rows_beside_a_shadow(m: usize) -> zedc::check::ty::Sig {
    use super::standing_twice::read_sig;
    use std::sync::Arc;
    let bounded = read_sig("(a: T) -> T for T in int | f64");
    let t = bounded.arrows[0].result.clone();
    let row = (0..m).fold(Ty::tuple(vec![t.clone(), t.clone()]), |r, _| {
        Ty::tuple(vec![r.clone(), r])
    });
    let mut inner: Vec<Ty> = (0..m)
        .map(|i| {
            let mut h = read_sig(&format!("(x: int) -> {i}"));
            let lit = h.arrows[0].result.clone();
            h.arrows[0].result = Ty::tuple(vec![row.clone(), lit]);
            Ty::func(Arc::new(h))
        })
        .collect();
    let mut shadow = read_sig("(x: int) -> int");
    shadow.own.insert(Arc::from("T"));
    shadow.arrows[0].result = t;
    inner.push(Ty::func(Arc::new(shadow)));
    let mut s = bounded.clone();
    s.arrows[0].result = Ty::tuple(inner);
    s
}

/// XR-heldname-print-batch round 3, Gemini B2-shadow-fan and Claude F2 (D5 of META3):
/// [`Sig::standing_twice`] on [`rows_beside_a_shadow`] enters each row a bounded number of
/// times, at most 8(m + 2) tuples (`row_entries`) at m = 64 and 512, and finds that the outer
/// `T` stands twice. The inner function that binds `T` makes every row over `T` one that holds
/// a name another function binds, and the walk keyed such a row by the innermost opening, which
/// each of the `m` functions that bind nothing pushes: Θ(m²) entries.
#[test]
fn standing_twice_does_not_reenter_rows_per_lambda_beside_a_shadow() {
    use zedc::check::ty::{reset_row_entries, row_entries};
    let mut bad = Vec::new();
    for m in [64, 512] {
        let s = rows_beside_a_shadow(m);
        reset_row_entries();
        let twice = s.standing_twice();
        let entries = row_entries();
        if entries == 0 || entries > 8 * (m as u64 + 2) {
            bad.push(format!("{entries} tuples entered at {m} inner functions"));
        }
        if !twice.contains("T") {
            bad.push(format!("`T` does not stand twice at {m}: {twice:?}"));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// The signature `(a: int) -> (X0 | … | X(n-1), Q | (X0, …, X(n-1)))`: the union `Q | (…)`
/// is written `_`, since `Q` stands once, and each `Xi` then falls from two places to one,
/// each time looking again at the wide union of the `Xi`, which is not written `_` at the end.
pub(super) fn wide_live_union(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("X{i}")).collect();
    format!("(a: int) -> ({}, Q | ({}))", xs.join(" | "), xs.join(", "))
}

/// XR-heldname-print-batch round 1, B3a: deciding which unions are written `_` (`Walk::weigh`)
/// does work linear in the size of the type on `wide_live_union(n)`, for the print and for
/// `Sig::standing_twice`. Before, each of the `n` falls looked at the whole union of the `Xi`
/// again, n² variables read. The work is counted by `ty::union_looks`; at 64 and 512 variables
/// it must stay under 16 per variable. The time is benched by `bench::scaling::
/// a_wide_live_union_is_weighed_in_linear_time`.
#[test]
fn wide_live_union_is_not_rescanned_per_falling_variable() {
    use super::standing_twice::read_sig;
    use zedc::check::ty::{reset_union_looks, union_looks};
    let mut bad = Vec::new();
    for n in [64, 512] {
        let s = read_sig(&wide_live_union(n));
        reset_union_looks();
        let text = s.to_string();
        let printing = union_looks();
        reset_union_looks();
        let twice = s.standing_twice();
        let counting = union_looks();
        for (what, looks) in [("print", printing), ("standing_twice", counting)] {
            if looks > 16 * n as u64 {
                bad.push(format!("{what} at {n}: {looks} looks"));
            }
        }
        if n == 64 && !twice.is_empty() {
            bad.push(format!("standing twice at 64: {twice:?} in {text}"));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// Over seeded random signatures whose result is a tree of tuples, each tuple built over two
/// of the parts before it and so shared where both pick one, over an own variable `T`, a
/// variable `U` bounded by carriers, `int` and a function bounding a variable of its own: each
/// text reads back as the signature both ways and prints again to the same text.
#[test]
fn random_shared_rows_with_bounded_variables_print_and_read_back() {
    use std::sync::Arc;
    use zedc::check::read::parse_type;
    let (mut rng, seed) = zed_tests::seed::Rng::fresh(
        "random_shared_rows_with_bounded_variables_print_and_read_back",
    );
    // `T` stands at two parameters, so it is printed by name wherever it stands: a variable
    // that stands once is printed `_`, and `(a: _) -> int` does not read back as a type below
    // `(a: T) -> int` (measured; row PRINT-lone-var-underscore-readback), which is not this
    // test's subject. The variables are the parameters' own types, so they are the
    // signature's variables.
    let base = super::standing_twice::read_sig(
        "(a: T, d: T, b: U, c: (z: V) -> V for V in int | f64) -> int for U in int | f64",
    );
    let p = &base.arrows[0].params;
    let leaves = [
        p[0].clone(),
        p[2].clone(),
        Ty::set(KType::int()),
        p[3].clone(),
    ];
    let mut bad = Vec::new();
    for case in 0..64 {
        let mut parts: Vec<Ty> = leaves.to_vec();
        let depth = 1 + (rng.next_u64() % 7) as usize;
        for _ in 0..depth {
            let mut pick = || parts[(rng.next_u64() % parts.len() as u64) as usize].clone();
            let row = Ty::tuple(vec![pick(), pick()]);
            parts.push(row);
        }
        let mut s = base.clone();
        s.arrows[0].result = parts.pop().expect("a tuple");
        let text = s.to_string();
        let want = Ty::func(Arc::new(s));
        match parse_type(&text) {
            Err(e) => bad.push(format!("case {case}: {text}: {e}")),
            Ok(back) if !(back.subtype(&want) && want.subtype(&back)) => bad.push(format!(
                "case {case}: {text} reads back as another type: {back}"
            )),
            Ok(back) if back.to_string() != text => {
                bad.push(format!("case {case}: {text} reads back as {back}"))
            }
            Ok(_) => {}
        }
    }
    assert!(
        bad.is_empty(),
        "seed {seed}: {} of 64:\n{}",
        bad.len(),
        bad.join("\n")
    );
}

/// `r(positional line, bump = 1) = { a1 = (line else #none -> 0) + bump; a2 = (line else
/// #none -> a1) + bump; … an }`: each sum meets the parameter's class beside an int on one
/// path and an int alone on another, so each keeps two states where it kept one
/// (ISSUE1-tvar-else). The `else` names `#none`, as a bare `else` is refused (DESIGN.md
/// sec:failure, row ELSE-explicit-atoms).
pub(super) fn sums_of_a_line_or_a_count(n: usize) -> String {
    let steps: String = (1..=n)
        .map(|i| {
            format!(
                "a{i} = (line else #none -> {}) + bump; ",
                if i == 1 {
                    "0".into()
                } else {
                    format!("a{}", i - 1)
                }
            )
        })
        .collect();
    format!("r(positional line, bump = 1) = {{ {steps}a{n} }};\n")
}

/// `f(positional x: int) = if x > 2n { 0 } else if x > 2n - 1 { 1 } … else if x > 0 && x < 0
/// { n } else { n + 1 }`, with every other test made unreachable by those before it, nested `n`
/// deep: each `if` with a comparison computes the scopes of its arms to find which no value
/// reaches, where before only a read of an int under them did (EMPTY-bottom-arm).
pub(super) fn a_chain_of_tests(n: usize) -> String {
    let mut text = String::from("f(positional x: int) = ");
    for i in 0..n {
        // The odd tests ask for more than the test before them failed to give.
        let bound = if i % 2 == 0 { 2 * n - i } else { 2 * n + i };
        text.push_str(&format!("if x > {bound} {{ {i} }} else "));
    }
    text.push_str(&format!(
        "if x > 0 && x < 0 {{ {n} }} else {{ {} }};\n",
        n + 1
    ));
    text
}

/// `g(positional x1, … positional xn) = (x1, … xn); f(positional n: Never) = g(n, … n)`: each
/// argument of type `Never` binds its parameter's variable to `Never`, and each component's
/// need that it holds no function is checked on `Never` (EMPTY-arg-needs).
pub(super) fn never_arguments(n: usize) -> String {
    let params: Vec<String> = (1..=n).map(|i| format!("positional x{i}")).collect();
    let comps: Vec<String> = (1..=n).map(|i| format!("x{i}")).collect();
    let args = vec!["n"; n].join(", ");
    format!(
        "g({}) = ({});\nf(positional n: Never) = g({args});\n",
        params.join(", "),
        comps.join(", ")
    )
}

// Small instances of the benchmarks in `bench::scaling`, each keeping every check the
// benchmark makes besides its ratio.

#[test]
fn a_few_functions_beside_their_constants_find_their_signatures() {
    // A small instance of the benchmark
    // `bench::scaling::searching_the_signatures_of_many_functions_scales`.
    let info = Resolved::new(&constants_and_functions(3)).check();
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(info.sigs.len(), 3);
    assert_eq!(info.adopt.len(), 60);
}

#[test]
fn a_function_of_untyped_parameters_takes_one_class() {
    // A small instance of the benchmark
    // `bench::scaling::a_function_of_many_untyped_parameters_scales`.
    // Six parameters take more than the 256 combinations of carriers the old search tried
    // before it gave `_`.
    assert_eq!(
        sig(&sum(3), "f"),
        "(T, T, T) -> T for T in int | f32 | f64 | rat"
    );
    assert_eq!(
        sig(&sum(6), "f"),
        "(T, T, T, T, T, T) -> T for T in int | f32 | f64 | rat"
    );
}

#[test]
fn a_chain_of_functions_takes_the_bound_of_the_one_called() {
    // A small instance of the benchmark
    // `bench::scaling::a_chain_of_functions_with_untyped_parameters_scales`.
    assert_eq!(
        sig(&chain(3), "g2"),
        "T -> T for T in int | f32 | f64 | rat"
    );
    let info = Resolved::new(&chain(3)).check();
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(info.sigs.len(), 3);
}

#[test]
fn bindings_with_else_patterns_check() {
    // A small instance of the benchmark `bench::scaling::many_else_patterns_scale`.
    let (info, _) = info(&else_patterns(4));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
}

#[test]
fn a_signature_names_each_of_its_type_variables() {
    // A small instance of the benchmark
    // `bench::scaling::a_signature_of_many_type_variables_scales`.
    let s = sig_of(&tuple(2), "f");
    assert_eq!(s.to_string(), "(T, U) -> (T, U)");
    assert_eq!(s.own.len(), 2, "two variables, each named");
}

#[test]
fn needs_replayed_through_a_fan_of_calls_are_met_once() {
    // A small instance of the benchmark
    // `bench::scaling::needs_replayed_through_a_fan_of_calls_scale`.
    let s = sig_of(&fan(3), "g2");
    assert_eq!(
        s.to_string(),
        "(0 -> U) -> U for U in int | f32 | f64 | rat"
    );
    assert_eq!(s.needs.len(), 1, "one need, met once for both calls");
}

#[test]
fn the_union_of_atoms_with_payloads_keeps_each_payload() {
    // A small instance of the benchmark
    // `bench::scaling::the_union_of_many_atoms_with_payloads_scales`.
    let u = Ty::union_all(&payloads(4, false));
    assert_eq!(u.payloads.len(), 4);
    assert!(u.payloads.values().all(Option::is_some));
    let u = Ty::union_all(&payloads(4, true));
    assert_eq!(u.payloads["e"].as_ref().map(Vec::len), Some(4));
}

#[test]
fn curried_lambdas_name_their_parameters_and_take_their_carriers() {
    // Small instances of the benchmarks `bench::scaling::curried_lambdas_using_every_parameter_…`
    // and `bench::scaling::curried_lambdas_whose_parameters_take_a_carrier_…`.
    assert_eq!(sig(&curried(3), "g"), "T -> U -> V -> W -> (T, U, V, W)");
    assert_eq!(
        sig(&curried_sums(2), "g"),
        "int -> int -> int -> (int, int, int)"
    );
}

#[test]
fn an_is_test_of_curried_lambdas_narrows_its_else_branch_to_nothing() {
    // A small instance of the benchmark
    // `bench::scaling::an_is_test_of_curried_lambdas_whose_parameters_take_a_carrier_scales`.
    let (info, _) = info(&curried_tested(2));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(info.tops["r"].to_string(), "1");
}

#[test]
fn a_chain_of_calls_on_one_value_gives_each_result() {
    // A small instance of the benchmark
    // `bench::scaling::a_chain_of_calls_on_one_value_checks_in_linear_time`.
    let (info, _) = info(&call_chain(3));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(info.tops["y"].to_string(), "(int, int, int, int)");
}

#[test]
fn overloads_passed_to_slots_of_arrows_check() {
    // Small instances of the benchmarks `bench::scaling::passing_an_overload_…`,
    // `bench::scaling::a_slot_written_as_an_overload_nested_in_parentheses_scales`,
    // `bench::scaling::an_overload_of_many_arrows_that_cover_a_slot_together_scales` and
    // `bench::scaling::a_function_of_many_parameters_that_misses_one_scales`.
    let info = Resolved::new(&overloads(4)).check();
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(info.sigs.len(), 2);
    for text in [wider_overloads(4), shared_overloads(4)] {
        let info = Resolved::new(&text).check();
        assert!(info.errors.is_empty(), "{text}: {:?}", info.errors);
    }
    let info = Resolved::new(&nested_overload(4)).check();
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(info.sigs.len(), 1);
    assert_eq!(type_errors(&covering_overload(4)), Vec::<String>::new());
    let errors = type_errors(&wide_arrows(4));
    assert_eq!(errors.len(), 1, "{errors:?}");
}

#[test]
fn results_of_arrows_meet_within_the_slots_or_are_refused() {
    // Small instances of the benchmarks in `bench::scaling` from
    // `many_arrows_whose_results_intersect_within_the_slots_scale` to
    // `many_results_that_hold_a_function_meet_in_linear_time_in_a_call`.
    for text in [
        met_and_within(3),
        with_a_function_arrow(3),
        results_holding_a_variable(3),
    ] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
    }
    let errors = type_errors(&meeting_on_different_sets(3));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].contains("grows with the product of their number"),
        "{errors:?}"
    );
    let errors = type_errors(&bounded_at_many_parameters(3));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].contains("places the arguments give"),
        "{errors:?}"
    );
    assert!(results_met_alone(4).within());
    // The same intersection checked from source, where the call builds the state itself: the
    // checker and `MeetInCall` agree.
    assert_eq!(
        type_errors(&results_holding_functions(4, "int")),
        Vec::<String>::new()
    );
    assert!(results_with_functions_met(4).within());
    // A near miss: a function whose domain is wider than that of the slot's function is not
    // within it, since a plain function type's domain is exact (`function_variance.rs`).
    let errors = type_errors(&results_holding_functions(4, "int | #c"));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("as the checker builds it"), "{errors:?}");
}

#[test]
fn needs_that_name_a_variable_the_call_leaves_unbound_check() {
    // A small instance of the benchmark
    // `bench::scaling::needs_that_name_a_variable_the_call_leaves_unbound_check_in_linear_time`.
    let (info, _) = info(&generic_applied_to_many(3));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(info.tops["y"].to_string(), "(0, 1, 2)");
}

#[test]
fn destructured_parameters_check() {
    // Small instances of the benchmarks
    // `bench::scaling::a_parameter_destructured_into_many_names_checks_in_linear_time` and
    // `bench::scaling::many_parameters_each_destructured_check_in_linear_time`.
    let (info, _) = info(&wide_destructuring(3));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    assert_eq!(info.tops["y"].to_string(), "(2, 0)");
    assert_eq!(type_errors(&many_destructurings(3)), Vec::<String>::new());
}

#[test]
fn rows_of_overlapping_or_disjoint_variable_sets_list_their_variables() {
    // Small instances of the benchmarks `bench::scaling::rows_made_from_…_variable_sets_scale`.
    let t = overlapping_rows(&variables("V", 5));
    assert_eq!(t.var_facts().names.len(), 5);
    let zs = disjoint_rows(&variables("A", 5), &variables("B", 5));
    assert_eq!(zs.last().map(|z| z.var_facts().names.len()), Some(10));
}

#[test]
fn replacing_in_rows_shared_on_many_paths_replaces_each_variable() {
    // A small instance of the benchmarks
    // `bench::scaling::replacing_in_rows_shared_on_many_paths_scales_by_…`.
    let (vs, ws) = (variables("V", 5), variables("W", 5));
    let binds: zedc::check::ty::Binds = (vs.iter().zip(&ws))
        .map(|(v, w)| (v.vars.first().cloned().unwrap(), w.clone()))
        .collect();
    let shared = overlapping_rows(&vs);
    for t in [
        shared.replace(&binds),
        shared.subst(&binds),
        shared.settle(&|v: &str| binds.get(v).cloned()),
    ] {
        let f = t.var_facts();
        assert_eq!(f.names.len() + f.classes.len(), 5);
        assert!(f.names.iter().chain(&f.classes).all(|v| v.starts_with('W')));
    }
}

#[test]
fn functions_that_each_hold_one_bound_variable_keep_their_own() {
    // A small instance of the benchmark
    // `bench::scaling::replacing_in_many_functions_that_each_hold_one_bound_variable_scales`.
    let (os, hs, ws) = (variables("O", 4), variables("H", 4), variables("W", 4));
    let (t, binds) = functions_holding_one(&os, &hs, &ws);
    let out = t.replace(&binds);
    assert_eq!(out.fns.len(), 4);
    for (s, (o, w)) in out.fns.iter().zip(os.iter().zip(&ws)) {
        assert_eq!(s.arrows[0].result, Ty::tuple(vec![o.clone(), w.clone()]));
    }
}

#[test]
fn rows_shared_on_many_paths_check_in_a_function_and_its_call() {
    // A small instance of the benchmarks `bench::scaling::rows_shared_on_many_paths_scale_…`.
    for call in [false, true] {
        assert_eq!(type_errors(&shared_rows(5, call)), Vec::<String>::new());
    }
}

#[test]
fn sums_tests_and_never_arguments_give_their_signatures() {
    // Small instances of the benchmarks
    // `bench::scaling::sums_of_a_line_or_a_count_check_in_linear_time`,
    // `bench::scaling::a_chain_of_tests_is_linear_in_its_length` and
    // `bench::scaling::never_arguments_check_in_linear_time`.
    // The `else` names `#none`, so the parameter takes `#none` and its family beside an int,
    // where a bare `else` took any atom (`int | #_`).
    assert_eq!(
        sig(&sums_of_a_line_or_a_count(3), "r"),
        "(int | #none | #none(..), bump: int) -> int"
    );
    assert_eq!(sig(&a_chain_of_tests(4), "f"), "int -> 0 | 2 | 5");
    assert_eq!(sig(&never_arguments(3), "f"), "Never -> Never");
}

/// A small instance of
/// `bench::scaling::replacing_variables_no_row_holds_in_rows_on_every_bit_scales`, with the
/// check the benchmark cannot make: once replacements that leave the rows unchanged
/// have made each row keep the set of its variables (CK-every-bit, `Replacer::wasted`), a
/// replacement of a variable a row holds, at its top or only in the shared row below, still
/// changes it, and one of a variable none holds still gives the type back equal. What it cannot
/// catch: the variables of functions and payload shapes in a row, which the set takes from
/// their facts and bits, are not exercised here.
#[test]
fn rows_that_keep_their_variables_are_still_replaced_where_they_hold_one() {
    use std::sync::Arc;
    use zedc::check::ty::Binds;
    let class = |k: usize| Ty::var(format!("${k}").into());
    let bind =
        |v: String| -> Binds { [(Arc::<str>::from(v), Ty::dynamic())].into_iter().collect() };
    let c = Ty::tuple((0..64).map(class).collect());
    let rows = (1..=6).map(|i| {
        Ty::tuple(
            std::iter::once(c.clone())
                .chain((0..64).map(|b| class(128 * i + b)))
                .collect(),
        )
    });
    let t = Ty::tuple(rows.collect());
    let names = Ty::tuple(
        (0..4)
            .map(|i| {
                Ty::tuple(
                    (0..300)
                        .map(|b| Ty::var(format!("N{i}_{b}").into()))
                        .collect(),
                )
            })
            .collect(),
    );
    // Enough unchanged replacements for every row to make its set: the work told doubles at
    // each, and each try's budget is the work told.
    for round in 0..40 {
        assert!(t.replace(&bind(format!("${}", 128 * (round % 6) + 64))) == t);
        assert!(names.replace(&bind(format!("M{round}"))) == names);
    }
    for held in ["$5", "$63", "$128", "$400", "$831"] {
        assert!(
            t.replace(&bind(held.into())) != t,
            "replacing {held} changed nothing"
        );
    }
    for held in ["N0_0", "N3_299", "N2_150"] {
        assert!(
            names.replace(&bind(held.into())) != names,
            "replacing {held} changed nothing"
        );
    }
    assert!(t.replace(&bind("$70".into())) == t);
}

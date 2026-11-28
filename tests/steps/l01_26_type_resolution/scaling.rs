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
#[test]
fn a_returned_function_with_its_own_bound_writes_its_rows_in_full() {
    let src = "w(positional x: int | f64) = 0;\np(positional s, positional v) = (s, (s, v));\nf(positional a1, positional a2) = {\n  h(positional y) = (w(y), p(p(y, a1), a2));\n  h\n};\n";
    let text = printed_back(src, 2).unwrap_or_else(|e| panic!("{e}"));
    assert!(!text.contains("type "), "{text}");
    assert_eq!(text.matches(" for ").count(), 1, "{text}");
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

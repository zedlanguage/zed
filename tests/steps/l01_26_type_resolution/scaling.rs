//! The checker at the rule of low complexity (DESIGN.md Part G). A signature search tried
//! each carrier for each untyped parameter, up to a budget, and began each run from a copy of
//! everything found so far. An untyped parameter is now a class of a union-find forest, and
//! each body is checked once. The programs and types here are checked small; their time, at
//! sizes where a cost above linear shows, is measured in `bench::scaling`.

use std::collections::BTreeMap;

use zed_kernel::types::Type as KType;
use zed_tests::scaling;
use zedc::check::ty::Ty;

use super::{Resolved, info, sig, sig_of, type_errors};

/// The units `text(m)` at `n` and `FACTOR * n`, read and resolved before the timing, so that a
/// test times the checker alone (COMPLEXITY.md F85).
pub(super) fn resolved(n: usize, text: impl Fn(usize) -> String) -> BTreeMap<usize, Resolved> {
    [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, Resolved::new(&text(m))))
        .collect()
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
    // sec:diagnostics, PRINT-tyvars, UNDERSCORE-print). The file binds `T` in the third row;
    // a message skips it and prints `U` (l01_29 `tyvars`), but a signature printed alone has no
    // program around it, so its names start at `T`.
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
            "g(positional a) = (T) -> (b) -> (c) -> a;\n",
            "T -> _ -> _ -> _ -> T",
        ),
        (
            "g(positional f) = (x) -> (y) -> f(x, y) + x;\n",
            "_ -> U -> _ -> U for U in int | f32 | f64 | rat",
        ),
        (
            "g(positional a, positional b) = ((c) -> (d) -> (c, d), a + b);\n",
            "(V, V) -> (T -> U -> (T, U), V) for V in int | f32 | f64 | rat",
        ),
        // The results of `h(x)` and `f(x)` are classes of `g`'s level that first appear
        // inside the lambdas, and are named in the order they appear there.
        (
            "g(positional f, positional h) = (x) -> (y) -> (h(y, x), f(x), y);\n",
            "(_, _) -> _ -> T -> (_, _, T)",
        ),
        (
            "g(positional f) = ((x) -> f(x), (y) -> (f(y), y));\n",
            "_ -> (_ -> _, T -> (_, T))",
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

/// Like [`overloads`], but each arrow of `q`'s function takes its atom or `#z`, so no arrow
/// of it equals the arrow of the slot it fits.
pub(super) fn wider_overloads(n: usize) -> String {
    let ov = |wide: &str| {
        (0..n)
            .map(|i| format!("((x: #a{i}{wide}) -> #b{i})"))
            .collect::<Vec<_>>()
            .join(" & ")
    };
    format!("p(f: {}) = 0;\nq(g: {}) = p(f: g);\n", ov(""), ov(" | #z"))
}

/// Like [`wider_overloads`], but every arrow of `q`'s function takes `#c` as well as its own
/// atom, and each arrow of the slot takes `#c` alone: every arrow of the function offers what
/// each arrow of the slot needs, and only the results tell them apart.
pub(super) fn shared_overloads(n: usize) -> String {
    let ov = |param: &dyn Fn(usize) -> String| {
        (0..n)
            .map(|i| format!("((x: {}) -> #b{i})", param(i)))
            .collect::<Vec<_>>()
            .join(" & ")
    };
    format!(
        "p(f: {}) = 0;\nq(g: {}) = p(f: g);\n",
        ov(&|_| "#c".into()),
        ov(&|i| format!("#c | #a{i}"))
    )
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
            }],
            own: [name(o)].into(),
            held: [name(h)].into(),
            params: Vec::new(),
            bounds: BTreeMap::new(),
            data: false,
            dense: false,
            word: None,
            needs: Vec::new(),
            named: 0,
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
        "type T1 = (0, (0, 1));\n(T1, (T1, 2))"
    );
    assert_eq!(
        sig(&shared_rows(2, false), "f"),
        "(T, U, V) -> ((T, (T, U)), ((T, (T, U)), V))"
    );
}

/// `r(positional line, bump = 1) = { a1 = (line else 0) + bump; a2 = (line else a1) + bump;
/// … an }`: each sum meets the parameter's class beside an int on one path and an int alone
/// on another, so each keeps two states where it kept one (ISSUE1-tvar-else).
pub(super) fn sums_of_a_line_or_a_count(n: usize) -> String {
    let steps: String = (1..=n)
        .map(|i| {
            format!(
                "a{i} = (line else {}) + bump; ",
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
    assert_eq!(s.to_string(), "_ -> U for U in int | f32 | f64 | rat");
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
    // `many_results_that_hold_a_variable_meet_in_linear_time_alone`.
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
    assert_eq!(
        sig(&sums_of_a_line_or_a_count(3), "r"),
        "(int | #_, bump: int) -> int"
    );
    assert_eq!(sig(&a_chain_of_tests(4), "f"), "int -> 0 | 2 | 5");
    assert_eq!(sig(&never_arguments(3), "f"), "Never -> Never");
}

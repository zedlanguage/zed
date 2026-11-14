//! A scope whose definitions form a cycle, a recursion that zedc does not compile before layer
//! L6: the checker rejects each cycle and still checks every other statement of the scope,
//! those that use a definition of the cycle among them. The checker gave up on the whole scope
//! at the first cycle, so `f` below got no signature and its errors went unreported, and the
//! checker itself reported nothing (SIG-lost-spin).

use super::{sig, type_errors};

/// The message for the cycle of the definitions `names`, as elaboration words it too, at the
/// statement written `at`.
fn recursion(names: &str, at: &str) -> String {
    let what = match names.contains(", ") {
        true => format!("{names} are defined in terms of each other"),
        false => format!("{names} is defined in terms of itself"),
    };
    format!("{what}, which is recursion: this version of zedc does not compile it yet. [{at}]")
}

/// The message for the definitions `names` of values that read each other's values, at the
/// statement written `at`.
fn values(names: &str, at: &str) -> String {
    let what = match names.contains(", ") {
        true => format!("{names} are defined in terms of each other's values"),
        false => format!("{names} is defined in terms of its own value"),
    };
    format!("{what}. [{at}]")
}

const F: &str = "f(positional c: int) = 1 + c;\n";

#[test]
fn a_function_beside_a_recursive_one_is_checked() {
    let text = format!("spin(positional n: int) = spin(n + 1);\n{F}");
    assert_eq!(sig(&text, "f"), "(int) -> int");
    assert_eq!(
        type_errors(&text),
        [recursion(
            "`spin`",
            "spin(positional n: int) = spin(n + 1);"
        )]
    );
}

/// Each shape of cycle, with `f` written before it and after it.
#[test]
fn every_shape_of_cycle_leaves_the_other_definitions_checked() {
    for (cycle, want) in [
        (
            "spin(positional n: int) = spin(n + 1);\n",
            recursion("`spin`", "spin(positional n: int) = spin(n + 1);"),
        ),
        // Mutual recursion.
        (
            "ping(positional n: int) = pong(n);\npong(positional n: int) = ping(n);\n",
            recursion("`ping`, `pong`", "ping(positional n: int) = pong(n);"),
        ),
        // Values defined in terms of each other.
        ("a = b + 1;\nb = a * 2;\n", values("`a`, `b`", "a = b + 1;")),
        // A value that holds itself.
        ("pair = (1, pair);\n", values("`pair`", "pair = (1, pair);")),
        // A function that reaches itself through a tuple.
        (
            "h(positional n: int) = { g, k = (h, n); g(k) };\n",
            recursion("`h`", "h(positional n: int) = { g, k = (h, n); g(k) };"),
        ),
        // A lambda that calls the name it is bound to.
        (
            "go = (x) -> go(x);\n",
            recursion("`go`", "go = (x) -> go(x);"),
        ),
        // A default that calls its own function.
        (
            "d(positional n: int = d(1)) = n;\n",
            recursion("`d`", "d(positional n: int = d(1)) = n;"),
        ),
    ] {
        for text in [format!("{cycle}{F}"), format!("{F}{cycle}")] {
            assert_eq!(sig(&text, "f"), "(int) -> int", "{text}");
            assert_eq!(type_errors(&text), std::slice::from_ref(&want), "{text}");
        }
    }
}

#[test]
fn a_cycle_inside_a_body_is_rejected_and_the_rest_of_the_body_checked() {
    // The block's other statements are checked: `f(true)` is rejected beside the cycle. In a
    // block a name is used only below its definition (DESIGN.md sec:lexical), so two bindings
    // that read each other are rejected before this check; a function that calls itself is
    // the cycle a block can hold.
    let text = format!(
        "g(positional n: int) = {{ x(positional k: int) = x(k); z = f(true); z + n }};\n{F}"
    );
    assert_eq!(
        type_errors(&text),
        [
            recursion("`x`", "x(positional k: int) = x(k);"),
            "`f` does not take (true): no arrow of `f` takes these types. [f(true)]".into(),
        ]
    );
    // A recursive function declared inside another.
    let text = format!(
        "outer(positional n: int) = {{ inner(positional k: int) = inner(k); m = f(n); inner(m) }};\n{F}"
    );
    assert_eq!(
        type_errors(&text),
        [recursion("`inner`", "inner(positional k: int) = inner(k);")]
    );
    assert_eq!(sig(&text, "f"), "(int) -> int");
}

#[test]
fn an_error_beside_a_cycle_is_reported() {
    let text = format!("spin(positional n: int) = spin(n + 1);\n{F}y = f(true);\n");
    assert_eq!(
        type_errors(&text),
        [
            recursion("`spin`", "spin(positional n: int) = spin(n + 1);"),
            "`f` does not take (true): no arrow of `f` takes these types. [f(true)]".into(),
        ]
    );
}

#[test]
fn a_function_that_calls_a_recursive_one_is_checked() {
    // `twice` uses `spin`, which has no signature: `twice` is checked with `spin(c)` of
    // unknown type, and its own errors are reported.
    let text = format!(
        "spin(positional n: int) = spin(n + 1);\n{F}twice(positional c: int) = f(spin(c)) + f(true);\n"
    );
    assert_eq!(
        type_errors(&text),
        [
            recursion("`spin`", "spin(positional n: int) = spin(n + 1);"),
            "`f` does not take (true): no arrow of `f` takes these types. [f(true)]".into(),
        ]
    );
    assert_eq!(sig(&text, "f"), "(int) -> int");
}

/// `n` cycles of two functions each, and a chain of `n` functions, each calling the one before
/// and a function of a cycle.
pub(super) fn cycles_beside_a_chain(n: usize) -> String {
    let mut text = String::from("g0(positional c: int) = 1 + c;\n");
    for i in 0..n {
        text.push_str(&format!(
            "p{i}(positional n: int) = q{i}(n);\nq{i}(positional n: int) = p{i}(n);\n"
        ));
        text.push_str(&format!(
            "g{}(positional c: int) = g{i}(c) + g0(p{i}(c));\n",
            i + 1
        ));
    }
    text
}

#[test]
fn cycles_beside_a_chain_of_functions_are_each_one_error() {
    // A small instance of the benchmark `bench::cycles::many_cycles_beside_many_functions_scale`.
    let (info, _) = super::info(&cycles_beside_a_chain(3));
    assert_eq!(info.errors.len(), 3);
    assert_eq!(info.sigs.len(), 4);
}

/// `3n` items: item `3i` and `3i + 1` form cycle `i`; item `3i + 2` depends on `3i - 1` and on
/// `3i`.
pub(super) fn deps_around_cycles(n: usize) -> Vec<Vec<usize>> {
    (0..3 * n)
        .map(|k| match k % 3 {
            0 => vec![k + 1],
            1 => vec![k - 1],
            _ => match k {
                2 => vec![0],
                _ => vec![k - 3, k - 2],
            },
        })
        .collect()
}

#[test]
fn the_order_around_cycles_lists_each_item_outside_them_and_each_cycle() {
    // A small instance of the benchmark `bench::cycles::the_order_around_many_cycles_scales`.
    use zedc::resolve::topo::topo_around_cycles;
    let deps = deps_around_cycles(3);
    let (order, cycles) = topo_around_cycles(&deps, deps.len());
    assert_eq!((order.len(), cycles.len()), (3, 3));
}

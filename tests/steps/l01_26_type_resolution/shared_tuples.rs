//! A tuple that holds one value twice holds one shared row twice, so `n` levels of it have
//! `2^n` paths through `n` rows. The checker reads each row once: the kernel type of a tuple
//! shape, which a call needs to compare its argument with the parameter, is made once per row
//! and kept in it, so `pair(pair(… pair(1) …))` and `t == t` cost `O(n)`, not `O(2^n)` at each
//! call (TUPLE-eq-dup: 33.8 s at `n = 24`, 1.26 s at `n = 18` before).

use super::type_errors;

const SCALE: &str = "scale(positional x) = x * 2;\n";

/// `leaf` doubled by `n` nested calls of `pair`, compared with itself.
pub(super) fn by_calls(n: usize, leaf: &str) -> String {
    format!(
        "{SCALE}pair(positional x) = (x, x);\nt = {}{leaf}{};\nsame = t == t;\n",
        "pair(".repeat(n),
        ")".repeat(n)
    )
}

/// `leaf` in a tuple, then `n - 1` bindings each holding the last twice, the last compared
/// with itself.
pub(super) fn by_bindings(n: usize, leaf: &str) -> String {
    let mut text = format!("{SCALE}t0 = ({leaf}, 1);\n");
    text.extend((1..n).map(|i| format!("t{i} = (t{0}, t{0});\n", i - 1)));
    text.push_str(&format!("same = t{0} == t{0};\n", n - 1));
    text
}

#[test]
fn a_value_held_twice_at_each_level_is_data() {
    assert_eq!(type_errors(&by_calls(3, "1")), Vec::<String>::new());
    assert_eq!(type_errors(&by_bindings(3, "1")), Vec::<String>::new());
}

#[test]
fn a_function_held_twice_at_each_level_is_one_error_per_compared_operand() {
    // A tuple may hold a function (DESIGN.md step L1.17), so no tuple is an error; `==` needs
    // data, and each of its operands holds the function, once each, however many paths reach it.
    // The value: `leaf` in `levels` levels of pairs.
    let value = |leaf: &str, levels: usize| {
        (0..levels).fold(leaf.to_string(), |v, _| format!("({v}, {v})"))
    };
    // `name` is the operand refused, `l == r` the comparison.
    let at = |name: &str, value: &str, l: &str, r: &str| {
        format!(
            "Cannot compare a value that may hold a function: `{name} : {value}` in `{l} == \
             {r}`. [{l} == {r}]"
        )
    };
    let f = "T -> T for T in int | f32 | f64 | rat";
    // One operand written twice, `t == t`, is one refusal: the second would be the same text
    // at the same span (TEST-harness-duplicate-eq-error).
    let by_calls_value = value(f, 3);
    let text = by_calls(3, "scale");
    assert_eq!(type_errors(&text), [at("t", &by_calls_value, "t", "t")]);
    // Two operands, `t == u` with `u = t`, are a refusal each.
    let two = text.replace("same = t == t;", "u = t;\nsame = t == u;");
    assert_eq!(
        type_errors(&two),
        [
            at("t", &by_calls_value, "t", "u"),
            at("u", &by_calls_value, "t", "u")
        ]
    );
    // The bindings start from `(scale, 1)`, then pair it twice.
    let by_bindings_value = value(&format!("({f}, 1)"), 2);
    assert_eq!(
        type_errors(&by_bindings(3, "scale")),
        [at("t2", &by_bindings_value, "t2", "t2")]
    );
}

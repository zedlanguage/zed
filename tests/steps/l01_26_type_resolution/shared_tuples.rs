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
fn a_function_held_twice_at_each_level_is_one_error() {
    // Reported once, at the tuple that first holds it; the levels above meet the same function.
    let at = |site: &str| {
        format!(
            "a tuple takes data, and this value may hold a function, `(T) -> T for T in int | f32 | f64 | rat`: data is a value that holds no function at any depth. [{site}]"
        )
    };
    assert_eq!(type_errors(&by_calls(3, "scale")), [at("pair(scale)")]);
    assert_eq!(type_errors(&by_bindings(3, "scale")), [at("scale")]);
}

//! The units the benchmarks of `bench/scaling.rs` format, and what formatting each must give,
//! checked here at small sizes (TEST-bench-move-rest, P170).

/// `f(c) = if c { if c { … { a = 1; a } … } else { 0 } } else { 0 };`, nested `depth` deep.
pub(super) fn nested(depth: usize) -> String {
    format!(
        "f(c) = {}{{ a = 1; a }}{};\n",
        "if c { ".repeat(depth) + "if c ",
        " else { 0 }".to_string() + &" } else { 0 }".repeat(depth),
    )
}

/// `n` statements, each with four comments on their own lines before it and one after it.
pub(super) fn commented(n: usize) -> String {
    (0..n)
        .map(|i| format!("// a\n// b\n// c\n// d\na{i} = {i}; // a{i}\n"))
        .collect()
}

/// `n` statements, each a call with a sort key and two comments inside, which move to its end,
/// then a blank line, a leading comment, another blank line and the next statement.
pub(super) fn moved(n: usize) -> String {
    (0..n)
        .map(|i| format!("a{i} = sort(xs, // by\n  desc x -> x, // key\n  {i});\n\n// next\n\n"))
        .collect()
}

/// `n` statements, each a display that holds a set element and a map entry, which the syntax
/// rejects with one step: the first entry.
pub(super) fn mixed(n: usize) -> String {
    (0..n)
        .map(|i| format!("y{i} = {{{i}, 2 -> 3}};\n"))
        .collect()
}

/// Formats `unit`, which must be accepted, and gives the text written.
pub(super) fn formats(unit: &str) -> String {
    zedc::format::format_source(unit.as_bytes()).unwrap()
}

/// Formats `unit`, which must be rejected, and gives the report of its syntax errors.
pub(super) fn rejects(unit: &str) -> String {
    zedc::format::format_source(unit.as_bytes()).unwrap_err()
}

/// Every unit of the benchmarks is formatted, or rejected, at small sizes, and the text written
/// at one size of each is the whole expected text; `bench/scaling.rs` holds the timing.
#[test]
fn each_benchmark_unit_is_formatted_at_small_sizes() {
    for n in [1, 2, 9] {
        formats(&nested(n));
        formats(&commented(n));
        formats(&moved(n));
        rejects(&mixed(n));
    }
    assert_eq!(
        formats(&nested(1)),
        "f(c) = if c {\n  if c {\n    a = 1;\n    a\n  } else { 0 }\n} else { 0 };\n"
    );
    assert_eq!(formats(&commented(2)), commented(2));
    assert_eq!(
        formats(&moved(1)),
        "a0 = sort(xs, desc x -> x, 0); // by\n// key\n\n// next\n"
    );
    assert_eq!(
        rejects(&mixed(2)),
        "1:10: a map entry `k -> v` stands in a display whose first entry is a set element, and \
         a display is a set or a map, not both. Write every entry as a set element, or write the \
         entries in two displays.\n  \
         [1] 1:7: the first entry, a set element\n      \
         1 | y0 = {0, 2 -> 3};\n        \
         |       ^\n\
         2:10: a map entry `k -> v` stands in a display whose first entry is a set element, and \
         a display is a set or a map, not both. Write every entry as a set element, or write the \
         entries in two displays.\n  \
         [1] 2:7: the first entry, a set element\n      \
         2 | y1 = {1, 2 -> 3};\n        \
         |       ^"
    );
}

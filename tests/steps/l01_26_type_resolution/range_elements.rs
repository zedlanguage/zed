//! Row RANGE-element-interval: the parameter of a lambda mapped over a range written in the
//! text, with `map`, `where`, `flatMap`, `foldl` or `foldr`, holds the ints between the range's ends, so
//! `(1..=5).map(i -> x mod i)` is accepted (`mod` takes `m` in int[1..], QUESTIONS A174). The
//! elements of `a ..= b` lie in `[lo a, hi b]` and those of `a ..< b` in `[lo a, hi b - 1]`,
//! from the intervals the checker has for the ends under the tests the walk is in, unbounded
//! where an end is. A range that reaches the word some other way, through a parameter or a
//! function's result, is read as any int. `for` is not covered: name resolution rejects every
//! `for` before the checker reads the program (walk.rs, the `for` frame).

use super::type_errors;
use zed_tests::step_helpers::l01_16_elaboration::value;

/// The refusal of `x mod i` inside the function given to `word`, at the call `at`.
fn refused(word: &str, at: &str) -> Vec<String> {
    vec![format!(
        "the function given to `{word}` takes `i` in int[1..]: `i : int`. [{at}]"
    )]
}

#[test]
fn a_range_from_one_gives_its_lambda_moduli_from_one() {
    let f = "f(positional x: int) = (1..=5).map(i -> x mod i);\n";
    assert_eq!(type_errors(f), Vec::<String>::new());
    assert_eq!(
        value(&format!("{f}y = f(7);\n"), "y"),
        // A range is the domain of its members, keyed by them (DESIGN.md sec:kernel, "Range"),
        // so `map` keeps the keys 1 through 5.
        "{1 -> 0, 2 -> 1, 3 -> 1, 4 -> 3, 5 -> 2}"
    );
}

#[test]
fn a_range_from_zero_is_still_refused() {
    let f = "f(positional x: int) = (0..=5).map(i -> x mod i);\n";
    assert_eq!(type_errors(f), refused("map", "(0..=5).map(i -> x mod i)"));
}

#[test]
fn half_open_open_and_empty_ranges_bound_their_elements() {
    for f in [
        "f(positional x: int) = (1..<6).map(i -> x mod i);\n",
        // Open: `3..` holds 3, 4, …, read by `first` only.
        "f(positional x: int) = (3..).map(i -> x mod i).first;\n",
        // Empty: no element, so the lambda never runs.
        "f(positional x: int) = (2..<2).map(i -> x mod i);\n",
        "f(positional x: int) = (5..=1).map(i -> x mod i);\n",
        "f(positional x: int) = (0..<0).map(i -> x mod i);\n",
        "f(positional x: int) = (-4..=-5).map(i -> x mod i);\n",
    ] {
        assert_eq!(type_errors(f), Vec::<String>::new(), "{f}");
    }
    assert_eq!(
        value(
            "f(positional x: int) = (5..=1).map(i -> x mod i);\ny = f(7);\n",
            "y"
        ),
        "{}"
    );
    for (f, at) in [
        ("(0..<6)", "(0..<6).map(i -> x mod i)"),
        ("(-1..=-1)", "(-1..=-1).map(i -> x mod i)"),
        ("(-3..=3)", "(-3..=3).map(i -> x mod i)"),
    ] {
        let f = format!("f(positional x: int) = {f}.map(i -> x mod i);\n");
        assert_eq!(type_errors(&f), refused("map", at), "{f}");
    }
    // `0..` holds 0, so its lambda is refused too (read by `first` only, as an open range must
    // be in this version).
    let open = "f(positional x: int) = (0..).map(i -> x mod i).first;\n";
    assert_eq!(
        type_errors(open),
        refused("map", "(0..).map(i -> x mod i)"),
        "{open}"
    );
}

#[test]
fn a_parameter_end_gives_the_interval_the_checker_has_for_it() {
    for f in [
        "f(positional x: int, n: int[1..]) = (n..=9).map(i -> x mod i);\n",
        "f(positional x: int, n: int) = (1..=n).map(i -> x mod i);\n",
        "f(positional x: int, n: int[2..=4]) = (n - 1..<n + 3).map(i -> x mod i);\n",
        // A test on the end narrows it where the lambda runs.
        "f(positional x: int, n: int) = if n >= 1 { (n..=9).map(i -> x mod i) } else { {} };\n",
    ] {
        assert_eq!(type_errors(f), Vec::<String>::new(), "{f}");
    }
    for f in [
        "f(positional x: int, n: int) = (n..=9).map(i -> x mod i);\n",
        "f(positional x: int, n: int[0..]) = (n..=9).map(i -> x mod i);\n",
        "f(positional x: int, n: int) = if n >= 0 { (n..=9).map(i -> x mod i) } else { {} };\n",
    ] {
        assert_eq!(
            type_errors(f),
            refused("map", "(n..=9).map(i -> x mod i)"),
            "{f}"
        );
    }
    assert_eq!(
        value(
            "f(positional x: int, n: int[1..]) = (n..=4).map(i -> x mod i);\ny = f(7, n: 2);\n",
            "y"
        ),
        "{2 -> 1, 3 -> 1, 4 -> 3}"
    );
}

#[test]
fn nested_maps_read_the_outer_lambdas_interval() {
    let f = "f(positional x: int) = (1..=3).map(j -> (j..=4).map(i -> x mod i));\n";
    assert_eq!(type_errors(f), Vec::<String>::new());
    assert_eq!(
        value(&format!("{f}y = f(7);\n"), "y"),
        "{1 -> {1 -> 0, 2 -> 1, 3 -> 1, 4 -> 3}, 2 -> {2 -> 1, 3 -> 1, 4 -> 3}, 3 -> {3 -> 1, 4 -> 3}}"
    );
    // The inner range starts at `j - 1`, which is 0 for the first `j`.
    let g = "f(positional x: int) = (1..=3).map(j -> (j - 1..=4).map(i -> x mod i));\n";
    assert_eq!(
        type_errors(g),
        refused("map", "(j - 1..=4).map(i -> x mod i)")
    );
}

#[test]
fn where_and_folds_read_the_interval_too() {
    for f in [
        "f(positional x: int) = (1..=5).where(i -> x mod i == 0);\n",
        "f(positional x: int) = (1..=5).foldl(0, (a, i) -> a + x mod i);\n",
        "f(positional x: int) = (1..=5).foldr((i, a) -> a + x mod i, 0);\n",
        "r = 1..=5;\nf(positional x: int) = r.map(i -> x mod i);\n",
    ] {
        assert_eq!(type_errors(f), Vec::<String>::new(), "{f}");
    }
    // 7 mod 1 + … + 7 mod 5 = 0 + 1 + 1 + 3 + 2.
    for f in [
        "f(positional x: int) = (1..=5).foldl(0, (a, i) -> a + x mod i);\ny = f(7);\n",
        "f(positional x: int) = (1..=5).foldr((i, a) -> a + x mod i, 0);\ny = f(7);\n",
    ] {
        assert_eq!(value(f, "y"), "7", "{f}");
    }
    assert_eq!(
        value(
            "f(positional x: int) = (1..=5).where(i -> 12 mod i == 0);\ny = f(7);\n",
            "y"
        ),
        // `where` keeps the members of the domain, a set.
        "{1, 2, 3, 4}"
    );
    for (word, f) in [
        ("where", "(0..=5).where(i -> x mod i == 0)"),
        ("foldl", "(0..=5).foldl(0, (a, i) -> a + x mod i)"),
        ("foldr", "(0..=5).foldr((i, a) -> a + x mod i, 0)"),
    ] {
        let text = format!("f(positional x: int) = {f};\n");
        assert_eq!(type_errors(&text), refused(word, f), "{text}");
    }
    let r = "r = 0..=5;\nf(positional x: int) = r.map(i -> x mod i);\n";
    assert_eq!(type_errors(r), refused("map", "r.map(i -> x mod i)"));
    // The accumulator of a fold is not an entry: it reads as any int.
    let acc = "f(positional x: int) = (1..=5).foldl(1, (a, i) -> x mod a);\n";
    assert_eq!(type_errors(acc).len(), 1, "{acc}");
}

#[test]
fn flat_map_reads_the_interval_too() {
    // Row NARROW-settle-spurious-warning, item 3: `flatMap` runs its function once for each
    // entry, with the entry, as `map` does (`Ck::range_param`).
    let f = "f(positional x: int) = (1..=5).flatMap(i -> [x mod i]);\n";
    assert_eq!(type_errors(f), Vec::<String>::new());
    // 7 mod 1, …, 7 mod 5, each emission under its entry's key (`{0}` is `{0 -> 0}`).
    assert_eq!(
        value(&format!("{f}y = f(7);\n"), "y"),
        "{1 -> {0}, 2 -> {0 -> 1}, 3 -> {0 -> 1}, 4 -> {0 -> 3}, 5 -> {0 -> 2}}"
    );
    let zero = "(0..=5).flatMap(i -> [x mod i])";
    let text = format!("f(positional x: int) = {zero};\n");
    assert_eq!(type_errors(&text), refused("flatMap", zero), "{text}");
}

#[test]
fn a_range_through_a_parameter_is_read_as_any_int() {
    // Complexity tradeoff at `Ck::entry_range`: only a range written in the text, or bound to
    // a name, is read.
    let f = "g(positional r: int ->? int, x: int) = r.map(i -> x mod i);\n";
    assert_eq!(type_errors(f), refused("map", "r.map(i -> x mod i)"));
}

/// `n` functions, each mapping `x mod i` over a range from 1, and `n` mapping it over a range
/// from 0, which are the `n` errors.
pub(super) fn range_moduli(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                // Not `f{i}`: `f32` and `f64` name types.
                "from1_{i}(positional x: int) = (1..={}).map(i -> x mod i);\n\
                 from0_{i}(positional x: int) = (0..={}).map(i -> x mod i);\n",
                i + 2,
                i + 2
            )
        })
        .collect()
}

#[test]
fn range_moduli_give_one_error_per_range_from_zero() {
    // A small instance of the benchmark `bench::range_elements::range_moduli_scale`.
    assert_eq!(type_errors(&range_moduli(3)).len(), 3);
}

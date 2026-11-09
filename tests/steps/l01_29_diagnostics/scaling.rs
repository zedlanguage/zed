//! Placing diagnostics at the rule of low complexity (DESIGN.md Part G). Each diagnostic and
//! each of its steps was placed by decoding the file from its first byte, so a file of `n`
//! lines with an error on each took `O(n²)`.

use zed_tests::scaling;

use super::rejected;

/// `n` definitions, each reading a name nothing declares.
fn unresolved(n: usize) -> String {
    (0..n).map(|i| format!("h{i} = missing{i};\n")).collect()
}

#[test]
fn placing_a_diagnostic_on_every_line_scales() {
    scaling::check("placing a diagnostic on each of n lines", 500, |n| {
        let out = rejected(&unresolved(n));
        // One diagnostic per line, the last at the last line, after `h{n-1} = `.
        let last = n - 1;
        let col = format!("h{last} = ").len() + 1;
        assert_eq!(out.lines().count(), n);
        let want = format!(
            "{n}:{col}: {}",
            zed_tests::undefined(&format!("missing{last}"))
        );
        assert_eq!(out.lines().last(), Some(want.as_str()));
    });
}

/// A chain of `n` bindings, each reading the one before twice, ending in an error.
fn doubled(n: usize) -> String {
    let mut src = String::from("main(stdin: Lines) -> (stdout: Lines) {\n  a0 = 1;\n");
    for i in 1..n {
        src += &format!("  a{i} = a{p} + a{p};\n", p = i - 1);
    }
    src + &format!("  stdout <- \"x\" ++ a{};\n}}\n", n - 1)
}

#[test]
fn deriving_through_values_read_twice_scales() {
    scaling::check(
        "the derivation of a chain read twice at each of n bindings",
        400,
        |n| {
            let out = rejected(&doubled(n));
            assert!(
                out.contains("`a0` is defined as this expression, 1"),
                "{out}"
            );
        },
    );
}

/// A function adding `n` untyped parameters and testing the sum as a condition: one class
/// with `n` reasons, shown in one diagnostic. Each parameter and each addition has a line of
/// its own, since each step of a diagnostic shows the whole line it is on.
fn summed_condition(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let ps: Vec<String> = xs.iter().map(|x| format!("positional {x}")).collect();
    format!(
        "f({}) = if {} {{ 1 }} else {{ 2 }};\n",
        ps.join(",\n"),
        xs.join("\n+ ")
    )
}

#[test]
fn the_reasons_of_a_class_narrowed_many_times_scale() {
    // Each reason was looked for among those shown before it (COMPLEXITY.md F29).
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            let out = rejected(&summed_condition(3));
            assert!(out.contains("not bool"), "{out}");
            assert_eq!(
                out.matches("gives these values one carrier").count(),
                2,
                "{out}"
            );
            scaling::check("the reasons of a class merged n times", 1000, |n| {
                let out = rejected(&summed_condition(n));
                assert_eq!(out.matches("gives these values one carrier").count(), n - 1);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

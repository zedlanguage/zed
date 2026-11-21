use zed_tests::scaling;

use super::super::sig_of;

/// A function whose parameter is narrowed `n` times in a chain, each `else` on an atom of its
/// own narrowing what the one before left: its result is `(T \ (#a0 | #a0(..) | …)) | 0 | …`.
fn chain(n: usize) -> String {
    let mut body = "r".to_string();
    for i in 0..n {
        body = format!("({body}) else #a{i} -> {i}");
    }
    format!("g(r) = {body};\n")
}

/// A function of `n` parameters, each narrowed once and standing again beside its difference.
fn wide(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("r{i}")).collect();
    let items: Vec<String> = (0..n)
        .map(|i| format!("r{i} else #a{i} -> {i}, r{i}"))
        .collect();
    format!("g({}) = ({});\n", params.join(", "), items.join(", "))
}

/// The chain of leftovers is walked once where the last is written ([`Scope::removed`] in
/// zedc-types), and its atoms joined in pairs, O(n log n). Small instance:
/// `else_difference::a_chain_of_elses_prints_one_difference_of_the_atoms_in_order`.
#[test]
fn a_chain_of_elses_prints_in_n_log_n() {
    let sigs = scaling::inputs(400, |n| sig_of(&chain(n), "g"));
    for (n, s) in &sigs {
        let text = s.to_string();
        assert!(text.starts_with("(r: T) -> (T \\ (#a0 | "), "{n}: {text}");
        assert!(text.contains(&format!("#a{} ", n - 1)), "{n}: {text}");
    }
    scaling::check("the signature of a chain of n elses printed", 400, |n| {
        assert!(!sigs[&n].to_string().is_empty());
    });
}

/// Each union's leftovers are looked at in ordered sets, O(v log v) for its v variables, so
/// the text is written in O(n log n). Small instance:
/// `else_difference::each_variable_prints_its_own_difference`.
#[test]
fn many_parameters_each_with_a_difference_print_in_n_log_n() {
    let sigs = scaling::inputs(300, |n| sig_of(&wide(n), "g"));
    for (n, s) in &sigs {
        let text = s.to_string();
        assert_eq!(text.matches(" \\ (#a").count(), *n, "{text}");
    }
    scaling::check(
        "a signature of n parameters each with a difference printed",
        300,
        |n| {
            assert!(!sigs[&n].to_string().is_empty());
        },
    );
}

//! A program with a recursion beside other definitions, as `zedc run` and `zedc check` load
//! it: the recursion is rejected, and every other definition is still checked, so an error in
//! one is reported with it, each once (SIG-lost-spin). Before, the checker stopped at the
//! cycle and only the recursion was reported.

use super::rejected;

#[test]
fn an_error_beside_a_recursion_is_reported_with_it() {
    let out = rejected(
        "spin(positional n: int) = spin(n + 1);\nf(positional c: int) = 1 + c;\nmain = f(true);\n",
    );
    let heads: Vec<&str> = out.lines().filter(|l| !l.starts_with(' ')).collect();
    assert_eq!(
        heads,
        [
            "1:1: `spin` is defined in terms of itself, which is recursion. Recursion is part of \
             the Zed language, and this version of zedc does not compile it yet. Write the \
             computation without a definition that uses itself.",
            "3:8: `f` does not take (true): these are the types of its arguments here, and `f` \
             has no arrow that takes them all",
        ],
        "{out}"
    );
    assert!(
        out.contains(
            "`f` is declared here with no type written for its result; the type the checker \
             found for `f` is `(int) -> int`"
        ),
        "{out}"
    );
}

/// A call of the recursive function gives no value and adds no error of its own: `f(spin(1))`
/// is not reported, `f(true)` is.
#[test]
fn a_call_of_a_recursion_adds_no_error() {
    let out = rejected(
        "spin(positional n: int) = spin(n + 1);\nf(positional c: int) = 1 + c;\n\
         main = f(spin(1)) + f(true);\n",
    );
    let heads: Vec<&str> = out.lines().filter(|l| !l.starts_with(' ')).collect();
    assert_eq!(heads.len(), 2, "{out}");
    assert!(
        heads[0].starts_with("1:1: `spin` is defined in terms of itself"),
        "{out}"
    );
    assert!(
        heads[1].starts_with("3:21: `f` does not take (true)"),
        "{out}"
    );
}

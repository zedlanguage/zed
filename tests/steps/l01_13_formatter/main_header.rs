//! `main`'s header is written as the program wrote it (DESIGN.md sec:ports, step L1.19: "The
//! parameter may be left out, `main() { … }`, and so may its type, `main(m) { … }`"), each
//! form with and without `-> int`.

use super::fmt;

#[test]
fn main_is_written_with_the_parameter_and_type_it_was_given() {
    for (text, want) in [
        (
            "main(m){m.stdout<-\"a\";}\n",
            "main(m) {\n  m.stdout <- \"a\";\n}\n",
        ),
        ("main()->int{0}\n", "main() -> int {\n  0\n}\n"),
        (
            "main(m:MainArgs)->int{0}\n",
            "main(m: MainArgs) -> int {\n  0\n}\n",
        ),
    ] {
        assert_eq!(fmt(text), want, "{text:?}");
    }
}

//! `e else d` replaces the loose atom members of `e`'s type; `e else #a -> d` only the
//! members its atom pattern matches. Chains read left to right.

use super::check;

#[test]
fn else_and_its_atom_pattern_form() {
    check(&[
        ("port else 8080", "(else port 8080)"),
        (
            "cache[k] else #notFound -> 0",
            "(else (index cache k) #notFound 0)",
        ),
        (
            "parse(s) else #syntaxError(pos:) -> pos",
            "(else (call parse s) #syntaxError(pos:) pos)",
        ),
        (
            "parse(s) else #syntaxError(pos: #start) -> 0",
            "(else (call parse s) #syntaxError(pos: #start) 0)",
        ),
        (
            "eval(e) else #add(#zero, #zero) -> 0",
            "(else (call eval e) #add(#zero, #zero) 0)",
        ),
        // DESIGN.md: `e else #a -> d1 else #b -> d2`
        (
            "e else #a -> d1 else #b -> d2",
            "(else (else e #a d1) #b d2)",
        ),
        ("a || b else c", "(else (|| a b) c)"),
        ("e else (x -> d)", "(else e (fn (x) d))"),
        ("e else { d }", "(else e (block (return d)))"),
    ]);
}

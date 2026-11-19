//! Name resolution refuses each form of layer L6, naming the step that compiles it, once, and
//! binds the names such a form declares, so that a use of one is not refused as well.

use zed_tests::step_helpers::l02_01_parser_structs::check_refused as check;

#[test]
fn each_form_names_the_step_that_compiles_it() {
    check(&[
        (
            "f(n) = loop t { while t < n; };",
            &[concat!(
                zed_tests::not_yet!("a `loop`"),
                " [loop t { while t < n; }]"
            )],
        ),
        (
            "f(xs) = for x in xs { if x > 0 { break; }; x };",
            // `break;` stands only in a loop's or a `for`'s body, refused here as well.
            &[
                concat!(
                    zed_tests::not_yet!("a `for`"),
                    " [for x in xs { if x > 0 { break; }; x }]"
                ),
                concat!(zed_tests::not_yet!("a `break`"), " [break;]"),
            ],
        ),
        (
            "f(x) = x*.h;",
            &[concat!(
                zed_tests::not_yet!("a call `*.` that writes its receiver"),
                " [x*.h]"
            )],
        ),
        (
            "f(x) = { while x; 0 };",
            &[concat!(
                zed_tests::not_yet!("a `while` guard"),
                " [while x;]"
            )],
        ),
        (
            "f(x) = { until x; 0 };",
            &[concat!(
                zed_tests::not_yet!("an `until` guard"),
                " [until x;]"
            )],
        ),
        (
            // A generation push outside a loop or a method is refused (row "Generation push
            // outside a loop"), and a loop's body is not walked, so the push stands in a method,
            // one whose receiver's fields are not known here (row "Generation push to a name
            // that is not a field of the receiver" refuses one for a known receiver).
            "T.f(x) { out' <- x; }",
            &[
                concat!(zed_tests::not_yet!("a method"), " [T.f(x) { out' <- x; }]"),
                concat!(
                    zed_tests::not_yet!("a generation push `x' <- e`"),
                    " [out' <- x;]"
                ),
            ],
        ),
        (
            "cdf[i] = cdf[i - 1] + 1;",
            &[concat!(
                zed_tests::not_yet!("an indexed definition"),
                " [cdf[i] = cdf[i - 1] + 1;]"
            )],
        ),
        (
            "cdf[i in 0..<4] = cdf[i - 1] + 1 with cdf[-1] = 0;",
            &[concat!(
                zed_tests::not_yet!("an indexed definition"),
                " [cdf[i in 0..<4] = cdf[i - 1] + 1 with cdf[-1] = 0;]"
            )],
        ),
        (
            "f(x) = x' + 1;",
            &[concat!(
                zed_tests::not_yet!("the primed name `x'`"),
                " [x']"
            )],
        ),
        (
            "x' = 1;",
            &[concat!(
                zed_tests::not_yet!("the primed name `x'`"),
                " [x' = 1;]"
            )],
        ),
        (
            "f(c) = c.y';",
            &[concat!(
                zed_tests::not_yet!("the primed field `y'`"),
                " [c.y']"
            )],
        ),
    ]);
}

/// The names an L6 form declares are bound, once per indexed family, so their uses resolve;
/// a primed name in a form refused whole is not reported again.
#[test]
fn declared_names_are_bound_and_refused_once() {
    check(&[
        (
            "x[i in 0..<4] = i;\nx[i in 4..<8] = 0;\ny = x;",
            &[
                concat!(
                    zed_tests::not_yet!("an indexed definition"),
                    " [x[i in 0..<4] = i;]"
                ),
                concat!(
                    zed_tests::not_yet!("an indexed definition"),
                    " [x[i in 4..<8] = 0;]"
                ),
            ],
        ),
        (
            "x[i in 0..<4] = x[i - 1] + 1 with x[-1] = 0;\ny = x;",
            &[concat!(
                zed_tests::not_yet!("an indexed definition"),
                " [x[i in 0..<4] = x[i - 1] + 1 with x[-1] = 0;]"
            )],
        ),
        (
            "x = 1;\nx[0] = 2;",
            &[
                "`x` is already bound in this scope [x[0] = 2;]",
                concat!(zed_tests::not_yet!("an indexed definition"), " [x[0] = 2;]"),
            ],
        ),
    ]);
}

#[test]
fn a_break_in_a_string_hole_is_refused_by_name_resolution() {
    // The syntax tree's builder accepts a `break;` in a string hole with no lambda or function
    // around it in the hole, since it cannot see whether a loop's body holds the string
    // (`Builder::break_placed`); name resolution walks the hole's statements and refuses it,
    // with or without a loop around the string (PROOF-sweep-front-end).
    check(&[
        (
            "f(x) = \"a${ { break; } }\";",
            &[concat!(zed_tests::not_yet!("a `break`"), " [break;]")],
        ),
        (
            "f(x) = \"a${ { y = x; break; } }b\";",
            &[concat!(zed_tests::not_yet!("a `break`"), " [break;]")],
        ),
    ]);
}

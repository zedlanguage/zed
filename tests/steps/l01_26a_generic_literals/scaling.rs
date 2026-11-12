//! Generic literals at the rule of low complexity (DESIGN.md Part G): each joins its class
//! once, and each takes its carrier at run time by one `match` on the other operand.
//!
//! Each test times elaboration alone, from the checker's findings made before timing: parsing
//! and checking cost about 430,000 to 460,000 instructions per term and elaboration about 4%
//! of the whole, so a quadratic in elaboration that allocates nothing passes a test that times
//! them all (COMPLEXITY.md F85, F86). The checker's own cost on these bodies is timed in
//! `l01_26_type_resolution::scaling`.

use zed_tests::scaling;

use zed_tests::step_helpers::l01_16_elaboration::{checked, elab};
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, sig, type_errors};

/// A function of `n` untyped parameters, each added with a generic literal: `n` class
/// merges and `n` generic literals, nested `2n` deep.
fn sum(n: usize) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("positional x{i}")).collect();
    let body: Vec<String> = (0..n).map(|i| format!("x{i} + {}", i + 1)).collect();
    format!("f({}) = {};\n", ps.join(", "), body.join(" + "))
}

#[test]
fn a_body_of_many_generic_literals_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(sig(&sum(2), "f"), "(T, T) -> T for T in int | f64 | rat");
            let n = 1000;
            let units = [checked(&sum(n)), checked(&sum(scaling::FACTOR * n))];
            for (u, m) in units.iter().zip([n, scaling::FACTOR * n]) {
                assert_eq!(u.info.follows.len(), m);
            }
            assert_eq!(units[0].elab(), elab(&sum(n)).unwrap());
            scaling::check("elaborating a body of n generic literals", n, |m| {
                units[usize::from(m != n)].elab();
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A function of one parameter multiplied by `n` decimal literals of 19 significant digits,
/// each its own number: each is read and fitted at `f64` and `rat` once (DESIGN.md L1.26b).
fn decimals(n: usize) -> String {
    let body: Vec<String> = (0..n)
        .map(|i| format!("x * 0.{:019}", 1_234_567_890_123_456_789u64 - i as u64))
        .collect();
    format!("f(positional x) = {};\n", body.join(" + "))
}

#[test]
fn a_body_of_many_decimal_literals_of_19_digits_checks_in_linear_time() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(type_errors(&decimals(2)), Vec::<String>::new());
            let n = 500;
            let srcs = [decimals(n), decimals(scaling::FACTOR * n)];
            scaling::check(
                "checking a body of n decimal literals of 19 digits",
                n,
                |m| {
                    checked(&srcs[usize::from(m != n)]);
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// One decimal literal of `n` digits at a parameter of type `f64`, read at `f64` alone
/// (DESIGN.md L1.26b). Read at `rat`, as in a class that holds `rat`, its digits cost
/// O(n^1.47) (COMPLEXITY.md K41).
fn long(n: usize) -> String {
    format!("id(positional v: f64) = v;\nx = id(0.{});\n", "3".repeat(n))
}

#[test]
fn one_decimal_literal_of_many_digits_checks_in_linear_time() {
    assert_eq!(type_errors(&long(40)), Vec::<String>::new());
    let n = 65_536;
    let srcs = [long(n), long(scaling::FACTOR * n)];
    scaling::check("checking one decimal literal of n digits", n, |m| {
        checked(&srcs[usize::from(m != n)]);
    });
}

/// A function that calls a generic `mul` `n` times, each with a generic literal argument:
/// `n` literals that each take the carrier of the caller's parameter.
fn calls(n: usize) -> String {
    let body: Vec<String> = (0..n).map(|i| format!("mul(x, {})", i + 1)).collect();
    format!(
        "mul(positional x, positional k) = x * k;\nf(positional x) = {};\n",
        body.join(" + ")
    )
}

#[test]
fn a_body_of_many_generic_literal_arguments_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(sig(&calls(2), "f"), "(T) -> T for T in int | f64 | rat");
            let n = 1000;
            let units = [checked(&calls(n)), checked(&calls(scaling::FACTOR * n))];
            for (u, m) in units.iter().zip([n, scaling::FACTOR * n]) {
                assert_eq!(u.info.witness.len(), m);
                assert_eq!(u.info.follows.len(), m);
            }
            assert_eq!(units[0].elab(), elab(&calls(n)).unwrap());
            scaling::check(
                "elaborating a body of n generic literal arguments",
                n,
                |m| {
                    units[usize::from(m != n)].elab();
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A value bound outside a function, `y = (1 + 0) /* … */ * (1 + 0) /* … */ * … * d`, of `n`
/// parenthesized sums of integer literals and the decimal `d`. Each sum is an operation on
/// literals alone, and so is their product, which takes the carrier of what it meets
/// (DESIGN.md sec:diagnostics, "A `/` of integer literals"). The comments make the line long
/// beside the checker's work on each sum.
fn product(n: usize, d: &str) -> String {
    format!(
        "y = {} * {d};\n",
        vec!["(1 + 0) /* a comment the fixes keep, which makes the line long */"; n].join(" * ")
    )
}

/// With `d = 0.5` nothing gives the literals a carrier, and each fix writes the decimal with
/// one, on one line of length of order n, and names the value of `y`, folded over the `2n`
/// operations (MSG-literal-fixes). Negative controls (each run once, not committed), at
/// n = 500 and 4,000, when each fix wrote the first literal of every sum: `Rewrite::line`
/// building a new line for each edit failed at 33.0 times the bytes; applying each edit in
/// place by `String::replace_range`, which moves the rest of the line each time, passed at 8.2
/// times the work, since `memmove` costs a small fraction of an instruction per byte against
/// the checker's work on each sum, so this test does not see that form.
#[test]
fn a_menu_of_a_long_line_scales() {
    scaling::on_a_thread(1 << 29, || {
        let c = "/* a comment the fixes keep, which makes the line long */";
        let one = format!(
            "  fixes, each checked here:\n    y = (1 + 0) {c} * 0.5f64;    y is 0.5\n    \
             y = (1 + 0) {c} * 0.5r;      y is 1r/2r"
        );
        let [m] = &type_errors(&product(1, "0.5"))[..] else {
            panic!("one rejection")
        };
        assert!(m.ends_with(&format!("{one} [0.5]")), "{m}");
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&product(m, "0.5")));
        for (m, u) in &units {
            let [e] = &u.type_errors()[..] else {
                panic!("one rejection")
            };
            assert_eq!(e.matches("(1 + 0)").count(), 3 * m, "{e}");
            assert!(e.contains("* 0.5f64;    y is 0.5\n"), "{e}");
        }
        scaling::check("rejecting a value of n sums with a menu", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

/// With `d = 0.5f64` the product of the `n` sums meets an `f64`, and each of its `2n`
/// literals takes it: each operation is recorded as one on literals alone from its operands'
/// entries, one lookup each, and the literals are walked once, where the product meets the
/// `f64` (`Ck::lit_op_meets`). Negative control (run once, not committed), at n = 500 and
/// 4,000: testing each operand by walking it, at each `*`, failed at 44.4 times the bytes, and
/// `a_menu_of_a_long_line_scales` with it at 42.6 times.
#[test]
fn an_operation_on_many_literals_takes_its_carrier_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        assert_eq!(type_errors(&product(3, "0.5f64")), Vec::<String>::new());
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&product(m, "0.5f64")));
        for u in units.values() {
            assert_eq!(u.type_errors(), Vec::<String>::new());
        }
        scaling::check("checking a value of n sums that meets an f64", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

/// `y = (1 / 1) * (1 / 1) * … * (1 / 1)`, of `n` divisions of integer literals: a `/` of
/// literals takes the carrier of what it meets, so each fix writes the first literal of the
/// value alone, and the `*` carry its carrier to every `/` (DESIGN.md sec:diagnostics, "A `/`
/// of integer literals": "the menu writes the carrier at the first literal of the value").
///
/// Each `/` of two literals is also rejected as it is walked, and those `n` rejections are
/// dropped for the binding's one (`Ck::rejects_unfixed`). Their menus are written only for the
/// errors kept at the end (`Ck::reject`): written as each was found, each fix the whole line of
/// length of order n, the check cost O(n²) (0.40 s, 1.30 s and 19.3 s at n = 500, 1,000 and
/// 4,000; COMPLEXITY.md F150).
#[test]
fn a_menu_that_writes_a_literal_in_each_of_many_divisions_scales() {
    let quotients = |n: usize| format!("y = {};\n", vec!["(1 / 1)"; n].join(" * "));
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&quotients(m)));
        for u in units.values() {
            let [e] = &u.type_errors()[..] else {
                panic!("one rejection")
            };
            // The first fix is also the headline's repair.
            for (fix, k) in [
                ("y = (1.0f64 / 1) * (1 / 1)", 2),
                ("y = (1r / 1) * (1 / 1)", 1),
            ] {
                assert_eq!(e.matches(fix).count(), k, "{e}");
            }
            assert!(e.contains(" * (1 / 1);") && e.contains(" y is 1r\n"), "{e}");
        }
        scaling::check("rejecting a value of n divisions with a menu", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

/// `y = 1 / 1 / … / 1`, `n` divisions nested to depth `n`: only the innermost divides two
/// literals, and each fix writes its first literal alone, whose carrier reaches each `/`.
/// The walk that finds the literals a fix writes follows the path to the written literal
/// alone (`unreached`), so it does not look into an operand again at the `/` around it.
#[test]
fn a_menu_of_divisions_nested_deep_scales() {
    let quotients = |n: usize| format!("y = 1{};\n", " / 1".repeat(n));
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&quotients(m)));
        for (m, u) in &units {
            let [e] = &u.type_errors()[..] else {
                panic!("one rejection")
            };
            let fix = format!("    y = 1r{};", " / 1".repeat(*m));
            assert!(e.contains(&fix), "{e}");
            assert_eq!(e.matches("1.0f64").count(), 2, "{e}");
        }
        scaling::check("rejecting n nested divisions with a menu", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

/// `y = (1 / 2 + 1 / 2 + … + 1 / 2) + 1.0f64`, a sum of `n` divisions of integer literals, each
/// on a line of its own, that meets an `f64`. Each `/` is rejected as it is walked, since it
/// divides two integer literals, and the sum's `2n` literals take the `f64` where the sum
/// meets it, walked once (`Ck::lit_takes`); the `n` rejections are dropped when the binding
/// ends, the errors after the binding's first split off once (`Ck::drop_met`). Each `/` is on
/// a line of its own so that the menu `Ck::reject` writes for each rejection, before it is
/// dropped, costs its own line and not the whole value.
///
/// Negative control (run once, not committed), at n = 500 and 4,000: `Ck::drop_met` testing
/// each error against every dropped range, which is quadratic with a small step, passed at
/// 9.3 times, below the limit of 11.74, so this test does not catch that form.
#[test]
fn a_sum_of_many_divisions_of_literals_takes_its_carrier_in_linear_time() {
    let sum = |n: usize| format!("y = ({}) + 1.0f64;\n", vec!["1 / 2"; n].join("\n  + "));
    scaling::on_a_thread(1 << 29, || {
        assert_eq!(type_errors(&sum(3)), Vec::<String>::new());
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&sum(m)));
        for u in units.values() {
            assert_eq!(u.type_errors(), Vec::<String>::new());
        }
        scaling::check("checking a sum of n divisions that meets an f64", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

/// `y = ((…((1 + 1) / 1 + 1) / 1 …) + 1) / 1 + 1.0f64`, `n` divisions of literals nested
/// `2n` deep, each level on a line of its own, that meets an `f64`. Each `/` holds operations
/// on literals alone that have no type until they meet a carrier, and records them as such
/// (`Ck::lit_open_within`), stopping at the operation below it, recorded already; the sum
/// takes the `f64` where it meets it, which removes them all at once (`Ck::lit_takes`).
///
/// Negative control (run once, not committed), at n = 500 and 4,000: walking all of each
/// operand at each `/`, without stopping at an operation recorded already, which is
/// quadratic, failed at 45.4 times the bytes, above the limit of 11.7.
#[test]
fn divisions_of_literals_nested_deep_record_their_operands_in_linear_time() {
    let nest = |n: usize| {
        format!(
            "y = {}1{} + 1.0f64;\n",
            "(".repeat(n),
            "\n  + 1) / 1".repeat(n)
        )
    };
    scaling::on_a_thread(1 << 29, || {
        assert_eq!(type_errors(&nest(3)), Vec::<String>::new());
        assert_eq!(
            zed_tests::step_helpers::l01_16_elaboration::value(&nest(3), "y"),
            "5.0"
        );
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&nest(m)));
        for u in units.values() {
            assert_eq!(u.type_errors(), Vec::<String>::new());
        }
        scaling::check(
            "checking n nested divisions of literals that meet an f64",
            n,
            |m| {
                std::hint::black_box(units[&m].type_errors());
            },
        );
    });
}

/// `y = (1 + 1, 1 + 1, …) == (2.0f64, 2.0f64, …)`, two tuples of `n` components: each `1 + 1`
/// takes the `f64` of the component it is compared with, one lookup of that component's type
/// each (`Ck::lit_pairs`), and the left tuple's type is made again once, bottom up
/// (`retyped`).
///
/// Negative control (run once, not committed), at n = 500 and 4,000: making the type again
/// at each component changed, which is quadratic, did not end within 60 s.
#[test]
fn a_comparison_of_tuples_of_many_operations_scales() {
    let pairs = |n: usize| {
        format!(
            "y = ({}) == ({});\n",
            vec!["1 + 1"; n].join(", "),
            vec!["2.0f64"; n].join(", ")
        )
    };
    scaling::on_a_thread(1 << 29, || {
        assert_eq!(type_errors(&pairs(3)), Vec::<String>::new());
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&pairs(m)));
        for u in units.values() {
            assert_eq!(u.type_errors(), Vec::<String>::new());
        }
        scaling::check(
            "checking a comparison of two tuples of n components",
            n,
            |m| {
                std::hint::black_box(units[&m].type_errors());
            },
        );
    });
}

/// `n` calls of `f(x: f64)`, each given a `/` of literals on a line of its own: each argument
/// takes the parameter's `f64` by one lookup of the parameter's carrier and one walk of the
/// argument (`Ck::lit_args_take`, DESIGN.md sec:domains: "A use fixes a literal's carrier [...]
/// at a declared type, that type's").
///
/// Negative control (run once, not committed), at n = 500 and 4,000: copying every operation
/// on literals alone recorded so far at each call, which is quadratic, failed at 13.9 times the
/// bytes, above the limit of 11.7, and so did the six other tests of literals here.
#[test]
fn many_calls_given_divisions_of_literals_take_their_carriers_in_linear_time() {
    let calls = |n: usize| {
        let ys: String = (0..n)
            .map(|i| format!("y{i} = f(x: ({i} + 1) / 2);\n"))
            .collect();
        format!("f(x: f64) = x;\n{ys}")
    };
    scaling::on_a_thread(1 << 29, || {
        assert_eq!(
            zed_tests::step_helpers::l01_16_elaboration::value(&calls(3), "y2"),
            "1.5"
        );
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&calls(m)));
        for u in units.values() {
            assert_eq!(u.type_errors(), Vec::<String>::new());
        }
        scaling::check_order(
            "checking n calls given a division of literals at an f64 parameter",
            n,
            1,
            |m| {
                std::hint::black_box(units[&m].type_errors());
            },
        );
    });
}

/// `y = f(x: ((…((1 + 1) / 1 + 1) / 1 …) + 1) / 1)` at `f(x: f64)`, `n` divisions of literals
/// nested `2n` deep, each level on a line of its own: the argument takes the parameter's `f64`
/// in one walk (`Ck::lit_takes`), which removes every operation in it from those with no type.
#[test]
fn an_argument_of_divisions_of_literals_nested_deep_takes_its_carrier_in_linear_time() {
    let nest = |n: usize| {
        format!(
            "f(x: f64) = x;\ny = f(x: {}1{});\n",
            "(".repeat(n),
            "\n  + 1) / 1".repeat(n)
        )
    };
    scaling::on_a_thread(1 << 29, || {
        assert_eq!(
            zed_tests::step_helpers::l01_16_elaboration::value(&nest(3), "y"),
            "4.0"
        );
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&nest(m)));
        for u in units.values() {
            assert_eq!(u.type_errors(), Vec::<String>::new());
        }
        scaling::check_order(
            "checking an argument of n nested divisions of literals at an f64 parameter",
            n,
            1,
            |m| {
                std::hint::black_box(units[&m].type_errors());
            },
        );
    });
}

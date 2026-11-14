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
            assert_eq!(
                sig(&sum(2), "f"),
                "(T, T) -> T for T in int | f32 | f64 | rat"
            );
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
            assert_eq!(
                sig(&calls(2), "f"),
                "(T) -> T for T in int | f32 | f64 | rat"
            );
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

/// `(…((3/2)^-1)^-1 …)^-1`, `n` powers of an operation on literals nested `n` deep, each
/// level on a line of its own: in a body beside `x: rat`, the same on the base `2`, at the top
/// level times `1r`, and `x / (2r/3r) * (2r/3r) …`, `n` divisors that are operations on
/// literals; one divisor `3r^(200 n) + 1r`, whose range is read without the power; and one
/// divisor of `n` nested squares of `3r`. Each base or divisor's value or range is a lookup of
/// the one kept for the operation inside it (`Ck::rat_folded`), so no `#divByZero` is added in
/// one step per operation, and the
/// integer exponents keep `int` (POW-rat-literal-ops). In a body each base is a class that may
/// still be an `int`, so each `^` records that its base takes no int, a need whose words are
/// made only if it fails.
///
/// Negative control (run once, not committed): the need's words made at each `^` allocated
/// 13.1 times the bytes at 8n on the body and 12.7 times on the base `2`, against the limit of
/// 11.7; COMPLEXITY.md row POW-rat-literal-ops.
#[test]
fn operations_on_literals_typed_by_their_value_check_in_linear_time() {
    let nest = |base: &str, n: usize| format!("{}({base}){}", "(".repeat(n), ")\n^-1".repeat(n));
    let body = |n: usize| format!("f(x: rat) = x + {};\ny = f(x: 0r);\n", nest("3/2", n));
    let two = |n: usize| format!("f(x: rat) = x + {};\ny = f(x: 0r);\n", nest("2", n));
    let top = |n: usize| format!("y = {} * 1r;\n", nest("3/2", n));
    let chain = |n: usize| {
        let ops: String = (0..n)
            .map(|i| match i % 2 {
                0 => "\n  / (2r/3r)",
                _ => "\n  * (2r/3r)",
            })
            .collect();
        format!("f(x: rat) = x{ops};\ny = f(x: 1r);\n")
    };
    // One divisor whose power has an exponent of 200 n: its range, at least `1r`, is read
    // from the base and the exponent, and the power, of about 95 n digits, is not computed, so
    // the check does not grow with n (order 0).
    let power = |n: usize| format!("f(x: rat) = x / (3r^{} + 1r);\n", 200 * n);
    // A divisor of n nested squares `((3r^2)^2 …)^2 + 1r`: the square is taken of the base
    // `3r`, a value of the text, and not of the range of a power, so the ends stay `9r` and
    // do not double in size at each level.
    let squares = |n: usize| {
        format!(
            "f(x: rat) = x / ({}3r{} + 1r);\n",
            "(".repeat(n),
            ")^2".repeat(n)
        )
    };
    let value = zed_tests::step_helpers::l01_16_elaboration::value;
    scaling::on_a_thread(1 << 29, || {
        assert_eq!(sig(&body(3), "f"), "(x: rat) -> rat");
        assert_eq!(value(&body(3), "y"), "2r/3r");
        assert_eq!(value(&body(4), "y"), "3r/2r");
        assert_eq!(sig(&two(3), "f"), "(x: rat) -> rat");
        assert_eq!(value(&two(3), "y"), "1r/2r");
        assert_eq!(value(&top(3), "y"), "2r/3r");
        assert_eq!(sig(&chain(3), "f"), "(x: rat) -> rat");
        assert_eq!(value(&chain(3), "y"), "3r/2r");
        assert_eq!(sig(&power(3), "f"), "(x: rat) -> rat");
        assert_eq!(sig(&squares(3), "f"), "(x: rat) -> rat");
        let n = 500;
        for (what, make, order) in [
            (
                "checking n nested powers of literals in a body at rat",
                &body as &dyn Fn(usize) -> String,
                1,
            ),
            (
                "checking n nested powers of the literal 2 in a body at rat",
                &two,
                1,
            ),
            (
                "checking n nested powers of literals at the top level",
                &top,
                1,
            ),
            (
                "checking n divisors that are operations on literals",
                &chain,
                1,
            ),
            (
                "checking a divisor that holds a power of 3 at 200 n",
                &power,
                0,
            ),
            ("checking a divisor of n nested squares of 3", &squares, 1),
        ] {
            let units = scaling::inputs(n, |m| Resolved::new(&make(m)));
            for u in units.values() {
                assert_eq!(u.type_errors(), Vec::<String>::new(), "{what}");
            }
            scaling::check_order(what, n, order, |m| {
                std::hint::black_box(units[&m].type_errors());
            });
        }
    });
}

/// The fixes of a rejected binding name the value a power of literals gives at `rat` by the
/// operation as the fix writes it, `x is 3r^200000 / 2`, and do not compute it: the power has
/// about 95 n digits at an exponent of 200 n, and the message, its fixes and the check cost the
/// text, which does not grow with n (order 0; DESIGN.md sec:diagnostics, "The value a fix
/// names"). The same holds where the binding compares tuples, whose fix names the comparison
/// where a pair at `int` or `rat` holds a `^`.
/// Before MSG-fixnote-huge-value each fix computed the power: at n = 500 the division took 19.7
/// times the bytes at 8n, and through `zedc run` at the exponents 200,000 and 1,600,000 the
/// comparisons took 4.9 times (`rat`) and 6.7 times (`int`) the instructions (COMPLEXITY.md row
/// MSG-fixnote-huge-value).
#[test]
fn a_fix_names_a_power_of_literals_without_computing_it() {
    let half = |n: usize| format!("x = 3^{} / 2;\n", 200 * n);
    let pair = |n: usize| format!("y = (3^{} + 0.5, 1) == (1, 2);\n", 200 * n);
    let int_pair = |n: usize| format!("y = (3^{} + 1, 0.5) == (2, 2);\n", 200 * n);
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        for (what, make) in [
            (
                "the fixes of a division of a power of 3 at 200 n",
                &half as &dyn Fn(usize) -> String,
            ),
            (
                "the fixes of a comparison holding a power of 3 at 200 n",
                &pair,
            ),
            (
                "the fixes of a comparison holding a power of 3 at 200 n at int",
                &int_pair,
            ),
        ] {
            let units = scaling::inputs(n, |m| Resolved::new(&make(m)));
            for u in units.values() {
                assert_eq!(u.type_errors().len(), 1, "{what}");
            }
            scaling::check_order(what, n, 0, |m| {
                std::hint::black_box(units[&m].type_errors());
            });
        }
    });
}

/// The type of an `if` whose branch is a power of literals keeps the power, held as its prime
/// exponents, and prints it as the program wrote it (DESIGN.md step L1.26a and sec:diagnostics,
/// "Types in a message"; LIT-power-values): the checking of `f(b: bool) = if b { 3^K } else
/// { 2 };`, and the rejection of `main() = f(b: true) > 1;` through `zedc run`, which writes
/// `(b: bool) -> 2 | 3^K`, cost the text, which does not grow with K = 200 n (order 0). A
/// branch that adds to the power, `3^K + 1`, is built as binary digits, O(n log n) by the
/// products of `num::fast`, and its type prints its decimal digits, O(n log^2 n) (radix
/// conversion; COMPLEXITY.md C31). Before MSG-literal-type-huge-power the power's type printed
/// its digits, 233M and about 2,500M instructions through `zedc run` at K = 200,000 and
/// 1,600,000; that item made the type `int` (COMPLEXITY.md row MSG-literal-type-huge-power).
#[test]
fn the_type_of_an_if_holding_a_power_of_literals_prints_the_power() {
    use zed_tests::step_helpers::l01_19_whole_file_ports::run;
    let def = |n: usize| format!("f(b: bool) = if b {{ 3^{} }} else {{ 2 }};\n", 200 * n);
    let main = |n: usize| format!("{}main() = f(b: true) > 1;\n", def(n));
    let sum = |n: usize| {
        format!(
            "f(b: bool) = if b {{ 3^{} + 1 }} else {{ 2 }};\nmain() = f(b: true) > 1;\n",
            200 * n
        )
    };
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&def(m)));
        for m in [n, scaling::FACTOR * n] {
            assert_eq!(sig(&def(m), "f"), format!("(b: bool) -> 2 | 3^{}", 200 * m));
        }
        scaling::check_order("the checking of an `if` of 3^(200 n)", n, 0, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
        let texts = scaling::inputs(n, main);
        scaling::check_order("zedc run of an `if` of 3^(200 n), rejected", n, 0, |m| {
            let out = run("l01_26a_power_scaling", &texts[&m], "", &[]);
            assert_eq!(out.status, 1);
            let ty = format!("`(b: bool) -> 2 | 3^{}`", 200 * m);
            assert!(out.stderr.contains(&ty), "{}", out.stderr);
        });
        // The decimal conversion runs on `num::fast` products at both sizes from n = 1000; at
        // n = 500 the smaller runs on num-bigint's Toom-3, of a lower constant, and the ratio
        // was 14.6 (2026-11-13). At n = 1000 it was over the limit of 10.5 (TESTS-scaling-limit-
        // 10_5). The larger size is held under the checker's fold bound (`FOLD_ASK_BITS` in
        // zedc-check, CONST-fold-machine): `3^K` asks 8 * 2 * K bits, so it is folded only up to
        // K = 2^23, and at n = 8000 the larger size, K = 12,800,000, was past it. So the sizes
        // are 5000 and 40,000, K = 1,000,000 and 8,000,000: 10.0 times the instructions for both
        // the checking and `zedc run` (2026-11-13), under the limit but over 9, as
        // O(n log^2 n) gives 8 * (log 8n / log n)^2, about 10.5 at 1.6M bits.
        let n = 5000;
        let units = scaling::inputs(n, |m| Resolved::new(&sum(m)));
        scaling::check("the checking of an `if` of 3^(200 n) + 1", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
        let texts = scaling::inputs(n, sum);
        scaling::check("zedc run of an `if` of 3^(200 n) + 1, rejected", n, |m| {
            let out = run("l01_26a_power_scaling", &texts[&m], "", &[]);
            assert_eq!(out.status, 1);
            assert!(out.stderr.contains("(b: bool) -> 2 | "), "{}", out.stderr);
        });
    });
}

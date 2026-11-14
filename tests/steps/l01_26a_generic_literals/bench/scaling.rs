//! Generic literals at the rule of low complexity (DESIGN.md Part G): each joins its class
//! once, and each takes its carrier at run time by one `match` on the other operand.
//!
//! Each test times elaboration alone, from the checker's findings made before timing: parsing
//! and checking cost about 430,000 to 460,000 instructions per term and elaboration about 4%
//! of the whole, so a quadratic in elaboration that allocates nothing passes a test that times
//! them all (COMPLEXITY.md F85, F86). The checker's own cost on these bodies is timed in
//! `l01_26_type_resolution::bench::scaling`. A small instance of each check these make besides
//! the ratio is among the correctness tests of `scaling.rs`.

use zed_tests::scaling;

use zed_tests::step_helpers::l01_16_elaboration::{checked, elab};
use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::scaling::{
    calls, calls_of_divisions, calls_with_divisor, decimals, deep_exponent, divisor_chain,
    flat_exponent, half_of_a_power, if_of_a_power, int_pair_of_a_power, long,
    main_of_an_if_of_a_power, main_of_an_if_of_a_sum, nested_argument, nested_divisions,
    nested_quotients, pair_of_a_power, pairs, power_divisor, powers_at_the_top, powers_in_a_body,
    powers_of_two, product, quotients, squares_divisor, sum, sum_of_divisions,
};

#[test]
fn a_body_of_many_generic_literals_scales() {
    scaling::on_a_thread(1 << 29, || {
        let n = 1000;
        let units = [checked(&sum(n)), checked(&sum(scaling::FACTOR * n))];
        for (u, m) in units.iter().zip([n, scaling::FACTOR * n]) {
            assert_eq!(u.info.follows.len(), m);
        }
        assert_eq!(units[0].elab(), elab(&sum(n)).unwrap());
        scaling::check("elaborating a body of n generic literals", n, |m| {
            units[usize::from(m != n)].elab();
        });
    });
}

#[test]
fn a_body_of_many_decimal_literals_of_19_digits_checks_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let srcs = [decimals(n), decimals(scaling::FACTOR * n)];
        scaling::check(
            "checking a body of n decimal literals of 19 digits",
            n,
            |m| {
                checked(&srcs[usize::from(m != n)]);
            },
        );
    });
}

#[test]
fn one_decimal_literal_of_many_digits_checks_in_linear_time() {
    let n = 65_536;
    let srcs = [long(n), long(scaling::FACTOR * n)];
    scaling::check("checking one decimal literal of n digits", n, |m| {
        checked(&srcs[usize::from(m != n)]);
    });
}

#[test]
fn a_body_of_many_generic_literal_arguments_scales() {
    scaling::on_a_thread(1 << 29, || {
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
    });
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
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&product(m, "0.5")));
        for (m, u) in &units {
            let [e] = &u.type_errors()[..] else {
                panic!("one rejection")
            };
            assert_eq!(e.matches("(1 + 0)").count(), 3 * m, "{e}");
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

/// Each `/` of two literals is also rejected as it is walked, and those `n` rejections are
/// dropped for the binding's one (`Ck::rejects_unfixed`). Their menus are written only for the
/// errors kept at the end (`Ck::reject`): written as each was found, each fix the whole line of
/// length of order n, the check cost O(n²) (0.40 s, 1.30 s and 19.3 s at n = 500, 1,000 and
/// 4,000; COMPLEXITY.md F150).
#[test]
fn a_menu_that_writes_a_literal_in_each_of_many_divisions_scales() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&quotients(m)));
        for u in units.values() {
            assert_eq!(u.type_errors().len(), 1);
        }
        scaling::check("rejecting a value of n divisions with a menu", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

/// The walk that finds the literals a fix writes follows the path to the written literal
/// alone (`unreached`), so it does not look into an operand again at the `/` around it.
#[test]
fn a_menu_of_divisions_nested_deep_scales() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&nested_quotients(m)));
        for (m, u) in &units {
            let [e] = &u.type_errors()[..] else {
                panic!("one rejection")
            };
            let fix = format!("    y = 1r{};", " / 1".repeat(*m));
            assert!(e.contains(&fix), "{e}");
        }
        scaling::check("rejecting n nested divisions with a menu", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

/// Each `/` is rejected as it is walked, since it divides two integer literals, and the sum's
/// `2n` literals take the `f64` where the sum meets it, walked once (`Ck::lit_takes`); the `n`
/// rejections are dropped when the binding ends, the errors after the binding's first split off
/// once (`Ck::drop_met`). Each `/` is on a line of its own so that the menu `Ck::reject` writes
/// for each rejection, before it is dropped, costs its own line and not the whole value.
///
/// Negative control (run once, not committed), at n = 500 and 4,000: `Ck::drop_met` testing
/// each error against every dropped range, which is quadratic with a small step, passed at
/// 9.3 times, below the limit of 11.74, so this test does not catch that form.
#[test]
fn a_sum_of_many_divisions_of_literals_takes_its_carrier_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&sum_of_divisions(m)));
        for u in units.values() {
            assert_eq!(u.type_errors(), Vec::<String>::new());
        }
        scaling::check("checking a sum of n divisions that meets an f64", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

/// Each `/` holds operations on literals alone that have no type until they meet a carrier,
/// and records them as such (`Ck::lit_open_within`), stopping at the operation below it,
/// recorded already; the sum takes the `f64` where it meets it, which removes them all at once
/// (`Ck::lit_takes`).
///
/// Negative control (run once, not committed), at n = 500 and 4,000: walking all of each
/// operand at each `/`, without stopping at an operation recorded already, which is
/// quadratic, failed at 45.4 times the bytes, above the limit of 11.7.
#[test]
fn divisions_of_literals_nested_deep_record_their_operands_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&nested_divisions(m)));
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

/// Each `1 + 1` takes the `f64` of the component it is compared with, one lookup of that
/// component's type each (`Ck::lit_pairs`), and the left tuple's type is made again once,
/// bottom up (`retyped`).
///
/// Negative control (run once, not committed), at n = 500 and 4,000: making the type again
/// at each component changed, which is quadratic, did not end within 60 s.
#[test]
fn a_comparison_of_tuples_of_many_operations_scales() {
    scaling::on_a_thread(1 << 29, || {
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

/// Each argument takes the parameter's `f64` by one lookup of the parameter's carrier and one
/// walk of the argument (`Ck::lit_args_take`, DESIGN.md sec:domains: "A use fixes a literal's
/// carrier [...] at a declared type, that type's").
///
/// Negative control (run once, not committed), at n = 500 and 4,000: copying every operation
/// on literals alone recorded so far at each call, which is quadratic, failed at 13.9 times the
/// bytes, above the limit of 11.7, and so did the six other tests of literals here.
#[test]
fn many_calls_given_divisions_of_literals_take_their_carriers_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&calls_of_divisions(m)));
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

/// The same `n` calls cost about as much as `n` calls whose divisor has a suffix,
/// `f(x: (i + 1) / 2.0f64)`, which no step rejects: the rejection of the `/` of integer
/// literals, which the call drops when the argument takes `f64`, is not built
/// (`Ck::lit_spared`). Built, with its repairs tried and its fixes checked, it made the bare
/// calls cost 4.8 times the work and 4.4 times the bytes of the fixed ones; without it they cost
/// 1.4 times both.
#[test]
fn a_division_of_literals_that_a_call_gives_a_carrier_costs_no_rejection() {
    scaling::on_a_thread(1 << 29, || {
        let n = 100;
        let (bare, fixed) = (
            Resolved::new(&calls_with_divisor(n, "2")),
            Resolved::new(&calls_with_divisor(n, "2.0f64")),
        );
        for u in [&bare, &fixed] {
            assert_eq!(u.type_errors(), Vec::<String>::new());
        }
        scaling::compare_costs(
            &format!(
                "checking n = {n} calls given `(i + 1) / 2.0f64`, then `(i + 1) / 2`, at an f64 \
                 parameter"
            ),
            "the two calls differ only in whether the walk types the `/` before the call gives \
             it `f64`: the bare one tries the `/` at `int` and refuses it, then takes the carrier, \
             1.4 times the work and the bytes when measured; building the rejection made it 4.8 \
             and 4.4",
            2.0,
            || {
                std::hint::black_box(fixed.type_errors());
            },
            || {
                std::hint::black_box(bare.type_errors());
            },
        );
    });
}

/// The argument takes the parameter's `f64` in one walk (`Ck::lit_takes`), which removes every
/// operation in it from those with no type.
#[test]
fn an_argument_of_divisions_of_literals_nested_deep_takes_its_carrier_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&nested_argument(m)));
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

/// Checks `make(m)` at `n` and `8n`, accepted with no error, as work of order `n^order`.
fn accepted_scales(what: &str, n: usize, order: u32, make: fn(usize) -> String) {
    scaling::on_a_thread(1 << 29, || {
        let units = scaling::inputs(n, |m| Resolved::new(&make(m)));
        for u in units.values() {
            assert_eq!(u.type_errors(), Vec::<String>::new(), "{what}");
        }
        scaling::check_order(what, n, order, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

// `(…((3/2)^-1)^-1 …)^-1`, `n` powers of an operation on literals nested `n` deep, each level
// on a line of its own: in a body beside `x: rat`, the same on the base `2`, at the top level
// times `1r`, and `x / (2r/3r) * (2r/3r) …`, `n` divisors that are operations on literals; one
// divisor `3r^(200 n) + 1r`, whose range is read without the power; and one divisor of `n`
// nested squares of `3r`. Each base or divisor's value or range is a lookup of the one kept for
// the operation inside it (`Ck::rat_folded`), so no `#divByZero` is added in one step per
// operation, and the integer exponents keep `int` (POW-rat-literal-ops). In a body each base is
// a class that may still be an `int`, so each `^` records that its base takes no int, a need
// whose words are made only if it fails.
//
// Negative control (run once, not committed): the need's words made at each `^` allocated
// 13.1 times the bytes at 8n on the body and 12.7 times on the base `2`, against the limit of
// 11.7; COMPLEXITY.md row POW-rat-literal-ops.

#[test]
fn operations_on_literals_typed_by_their_value_check_in_linear_time_in_a_body() {
    accepted_scales(
        "checking n nested powers of literals in a body at rat",
        500,
        1,
        powers_in_a_body,
    );
}

#[test]
fn operations_on_literals_typed_by_their_value_check_in_linear_time_powers_of_two() {
    accepted_scales(
        "checking n nested powers of the literal 2 in a body at rat",
        500,
        1,
        powers_of_two,
    );
}

#[test]
fn operations_on_literals_typed_by_their_value_check_in_linear_time_at_the_top_level() {
    accepted_scales(
        "checking n nested powers of literals at the top level",
        500,
        1,
        powers_at_the_top,
    );
}

#[test]
fn operations_on_literals_typed_by_their_value_check_in_linear_time_divisors() {
    accepted_scales(
        "checking n divisors that are operations on literals",
        500,
        1,
        divisor_chain,
    );
}

/// The power, of about 95 n digits, is not computed, so the check does not grow with n
/// (order 0).
#[test]
fn operations_on_literals_typed_by_their_value_check_in_linear_time_a_power_divisor() {
    accepted_scales(
        "checking a divisor that holds a power of 3 at 200 n",
        500,
        0,
        power_divisor,
    );
}

#[test]
fn operations_on_literals_typed_by_their_value_check_in_linear_time_squares() {
    accepted_scales(
        "checking a divisor of n nested squares of 3",
        500,
        1,
        squares_divisor,
    );
}

/// Checks `make(m)` at `n` and `8n`, rejected once each, as work of order 0.
fn one_rejection_does_not_grow(what: &str, n: usize, make: fn(usize) -> String) {
    scaling::on_a_thread(1 << 29, || {
        let units = scaling::inputs(n, |m| Resolved::new(&make(m)));
        for u in units.values() {
            assert_eq!(u.type_errors().len(), 1, "{what}");
        }
        scaling::check_order(what, n, 0, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

// The fixes of a rejected binding name the value a power of literals gives at `rat` by the
// operation as the fix writes it, `x is 3r^200000 / 2`, and do not compute it: the power has
// about 95 n digits at an exponent of 200 n, and the message, its fixes and the check cost the
// text, which does not grow with n (order 0; DESIGN.md sec:diagnostics, "The value a fix
// names"). The same holds where the binding compares tuples, whose fix names the comparison
// where a pair at `int` or `rat` holds a `^`. Before MSG-fixnote-huge-value each fix computed
// the power: at n = 500 the division took 19.7 times the bytes at 8n, and through `zedc run` at
// the exponents 200,000 and 1,600,000 the comparisons took 4.9 times (`rat`) and 6.7 times
// (`int`) the instructions (COMPLEXITY.md row MSG-fixnote-huge-value).

#[test]
fn a_fix_names_a_power_of_literals_without_computing_it_in_a_division() {
    one_rejection_does_not_grow(
        "the fixes of a division of a power of 3 at 200 n",
        500,
        half_of_a_power,
    );
}

#[test]
fn a_fix_names_a_power_of_literals_without_computing_it_in_a_comparison() {
    one_rejection_does_not_grow(
        "the fixes of a comparison holding a power of 3 at 200 n",
        500,
        pair_of_a_power,
    );
}

#[test]
fn a_fix_names_a_power_of_literals_without_computing_it_in_a_comparison_at_int() {
    one_rejection_does_not_grow(
        "the fixes of a comparison holding a power of 3 at 200 n at int",
        500,
        int_pair_of_a_power,
    );
}

// The type of an `if` whose branch is a power of literals keeps the power, held as its prime
// exponents, and prints it as the program wrote it (DESIGN.md step L1.26a and sec:diagnostics,
// "Types in a message"; LIT-power-values): the checking of `f(b: bool) = if b { 3^K } else
// { 2 };`, and the rejection of `main() = f(b: true) > 1;` through `zedc run`, which writes
// `(b: bool) -> 2 | 3^K`, cost the text, which does not grow with K = 200 n (order 0). A
// branch that adds to the power, `3^K + 1`, is built as binary digits, O(n log n) by the
// products of `num::fast`, and its type prints its decimal digits, O(n log^2 n) (radix
// conversion; COMPLEXITY.md C31). Before MSG-literal-type-huge-power the power's type printed
// its digits, 233M and about 2,500M instructions through `zedc run` at K = 200,000 and
// 1,600,000; that item made the type `int` (COMPLEXITY.md row MSG-literal-type-huge-power).

#[test]
fn the_type_of_an_if_holding_a_power_of_literals_prints_the_power_when_checked() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&if_of_a_power(m)));
        for (m, u) in &units {
            assert_eq!(
                zed_tests::step_helpers::l01_26_type_resolution::sig(&if_of_a_power(*m), "f"),
                format!("(b: bool) -> 2 | 3^{}", 200 * m)
            );
            assert_eq!(u.type_errors(), Vec::<String>::new());
        }
        scaling::check_order("the checking of an `if` of 3^(200 n)", n, 0, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

#[test]
fn the_type_of_an_if_holding_a_power_of_literals_prints_the_power_when_run() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let texts = scaling::inputs(n, main_of_an_if_of_a_power);
        scaling::check_order("zedc run of an `if` of 3^(200 n), rejected", n, 0, |m| {
            let out = run("l01_26a_power_scaling", &texts[&m], "", &[]);
            assert_eq!(out.status, 1);
            let ty = format!("`(b: bool) -> 2 | 3^{}`", 200 * m);
            assert!(out.stderr.contains(&ty), "{}", out.stderr);
        });
    });
}

// The decimal conversion runs on `num::fast` products at both sizes from n = 1000; at n = 500
// the smaller runs on num-bigint's Toom-3, of a lower constant, and the ratio was 14.6
// (2026-11-13). At n = 1000 it was over the limit of 10.5 (TESTS-scaling-limit-10_5). The larger
// size is held under the checker's fold bound (`FOLD_ASK_BITS` in zedc-check,
// CONST-fold-machine): `3^K` asks 8 * 2 * K bits, so it is folded only up to K = 2^23, and at
// n = 8000 the larger size, K = 12,800,000, was past it. So the sizes are 5000 and 40,000,
// K = 1,000,000 and 8,000,000: 10.0 times the instructions for both the checking and `zedc run`
// (2026-11-13), under the limit but over 9, as O(n log^2 n) gives 8 * (log 8n / log n)^2, about
// 10.5 at 1.6M bits.

#[test]
fn the_type_of_an_if_holding_a_power_of_literals_prints_the_power_plus_one_when_checked() {
    scaling::on_a_thread(1 << 29, || {
        let n = 5000;
        let units = scaling::inputs(n, |m| Resolved::new(&main_of_an_if_of_a_sum(m)));
        scaling::check("the checking of an `if` of 3^(200 n) + 1", n, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

#[test]
fn the_type_of_an_if_holding_a_power_of_literals_prints_the_power_plus_one_when_run() {
    scaling::on_a_thread(1 << 29, || {
        let n = 5000;
        let texts = scaling::inputs(n, main_of_an_if_of_a_sum);
        scaling::check("zedc run of an `if` of 3^(200 n) + 1, rejected", n, |m| {
            let out = run("l01_26a_power_scaling", &texts[&m], "", &[]);
            assert_eq!(out.status, 1);
            assert!(out.stderr.contains("(b: bool) -> 2 | "), "{}", out.stderr);
        });
    });
}

/// `y = 2r * 2^(…e)` of shape `shape` at `n` and `8n`, rejected for `e = 0.5` and accepted for
/// `e = 2`: at `rat` the text of each exponent is read once and the exponent folded once at
/// `int` (`int_exponent`, `Ck::lit_fit`; plan row LIT-rat-decimal-exponent), not once per `^` it
/// holds.
fn exponent_scales(what: &str, shape: fn(usize, &str) -> String, e: &str, ok: bool) {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&shape(m, e)));
        for u in units.values() {
            assert_eq!(u.type_errors().is_empty(), ok);
        }
        scaling::check(
            &format!("checking 2r * 2^(…{e}), an exponent of n terms, {what}"),
            n,
            |m| {
                std::hint::black_box(units[&m].type_errors());
            },
        );
    });
}

#[test]
fn a_power_at_rat_with_a_long_or_deep_exponent_checks_in_linear_time_long_rejected() {
    exponent_scales("long", flat_exponent, "0.5", false);
}

#[test]
fn a_power_at_rat_with_a_long_or_deep_exponent_checks_in_linear_time_long_accepted() {
    exponent_scales("long", flat_exponent, "2", true);
}

#[test]
fn a_power_at_rat_with_a_long_or_deep_exponent_checks_in_linear_time_deep_rejected() {
    exponent_scales("deep", deep_exponent, "0.5", false);
}

#[test]
fn a_power_at_rat_with_a_long_or_deep_exponent_checks_in_linear_time_deep_accepted() {
    exponent_scales("deep", deep_exponent, "2", true);
}

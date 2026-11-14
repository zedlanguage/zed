//! The formatter keeps the parentheses a construct needs in each position: a block, `for` or
//! `loop` reached as the first operand of an operator, a call, an index, a member read or a
//! tail (sec:grammar, "The head flag", and the `!HEAD` guard of `Primary`); a lambda body or an
//! `else` default that starts with a brace; an index key that starts with `in`; and each case
//! of the head flag of step L1.8. Each unit formats to text that builds to the same statements
//! and formats to itself (`fmt`); a dropped parenthesis would change the statements or fail to
//! parse.

use zed_tests::is_not_yet;

use super::head_cases::HEAD_CASES;
use super::{build, fmt};

/// Units whose expressions hold a parenthesis the formatter must keep.
const UNITS: &[&str] = &[
    // A block, `for` or `loop` as the first operand.
    "f(y, b) = if (y else { 1 }) == 0 { 2 } else { 3 };",
    "f(b) = if ({ a = 1; a }) == b { 1 } else { 2 };",
    "f(b) = ({ a = 1; a }) + b;",
    "f(b) = -({ a = b; a });",
    "f(b) = ({ a = b; a })(1);",
    "f(b) = ({ a = b; a })[0];",
    "f(b) = ({ a = b; a }).c;",
    "f(b) = ({ a = b; a }) with { c = 2 };",
    "f(b) = ({ a = b; a })*.c;",
    "f(b) = ({ a = b; a }) is int;",
    "f(b) = ({ a = b; a }) >< max;",
    "f(b) = ({ a = b; a })..<5;",
    "f(b) = ({ a = b; a }) in b;",
    "f(b) = ({ a = b; a }) else 0;",
    "f(xs) = (for x in xs { x }) + 1;",
    "f(n) = (loop { a', b' = (b, a + 1); until a > n; }) + 1;",
    "f(ys, zs) = for y in (ys else { zs }) { y };",
    "f(v, p, q) = match v { x where (p else { q }) -> 1, _ -> 0 };",
    "f(y) = match (y else { 1 }) { _ -> 0 };",
    // A lambda body or an `else` default that starts with a brace.
    "f = y -> ({1, 2}::card..<5);",
    "f = y -> ({1, 2} >< max);",
    "f = y -> ({ a: 1 } with { a = 2 });",
    "f = y -> ({ a: 1 }*.g);",
    "f = y -> ({ a: 1 }.a);",
    "f(y) = y else ({1, 2} >< max);",
    "f(y) = y else ({ a = 1; a } + 1);",
    // An index key that starts with `in`.
    "f(x, i, s) = x[(i in s)..<5];",
    "f(x, i, s) = x[(i in s) >< max];",
    "f(x, i, s) = x[(i in s)(1)];",
    "f(x, i, s) = x[(i in s)[0]];",
    "f(x, i, s) = x[(i in s).a];",
    "f(x, i, s) = x[(i in s) is bool];",
    "f(x, i, s) = x[(i in s) with { a = 1 }];",
    "f(x, i, s) = x[(i in s)*.a];",
    // A call that curries the named parameters left out (`Args` puts `...` after one argument
    // at least).
    "g(a) = f(a, ...);",
    "g(a) = f(x: a, ...);",
];

/// Each unit that builds formats to a fixed point that builds to its statements; one refused
/// as not compiled yet is counted. Every other refusal is wrong: the unit is valid Zed.
#[test]
fn each_parenthesis_a_position_needs_is_kept() {
    let mut units: Vec<String> = UNITS.iter().map(|s| s.to_string()).collect();
    units.extend(
        HEAD_CASES
            .iter()
            .filter(|(_, tree)| *tree != "ERROR")
            .map(|(text, _)| format!("h(x, y, xs, ys, a, b, c, p, v, s) = {text};")),
    );
    let (mut wrong, mut built, mut refused) = (Vec::new(), 0, 0);
    for unit in &units {
        match build(unit) {
            Ok(_) => {
                built += 1;
                if let Err(e) = std::panic::catch_unwind(|| fmt(unit)) {
                    let why = e
                        .downcast_ref::<String>()
                        .cloned()
                        .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                        .unwrap_or_default();
                    wrong.push(format!("{unit}\n  {why}"));
                }
            }
            Err(e) if is_not_yet(&e) => refused += 1,
            Err(e) => wrong.push(format!("{unit}\n  does not build: {e}")),
        }
    }
    println!(
        "{} units: {built} built and formatted, {refused} refused as not compiled yet",
        units.len()
    );
    assert!(
        wrong.is_empty(),
        "{} of {} wrong:\n{}",
        wrong.len(),
        units.len(),
        wrong.join("\n")
    );
}

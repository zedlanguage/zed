//! Postfix chains read left to right, and bind tighter than every operator.

use super::ast;

#[track_caller]
fn check(cases: &[(&str, &str)]) {
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(text, want)| {
            let got = ast(text).map_or_else(|e| format!("error: {e}"), |e| e.to_string());
            (got != want).then(|| format!("{text}\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_digit_then_a_letter_is_member_access() {
    check(&[
        // DESIGN.md: `y = 5.double.clamp(0, 8);  // ≡ clamp(double(5), 0, 8)`
        ("5.double.clamp(0, 8)", "(call (. (. 5 double) clamp) 0 8)"),
        ("2.5.floor", "(. 2.5 floor)"),
        ("0x1F.bits", "(. 0x1F bits)"),
        ("1.0e3.round()", "(call (. 1.0e3 round))"),
    ]);
}

#[test]
fn suffixes_apply_left_to_right() {
    check(&[
        ("grid[r][c]", "(index (index grid r) c)"),
        ("orders[id].total", "(. (index orders id) total)"),
        ("pos'.x", "(. pos' x)"),
        ("user?.address?.city", "(?. (?. user address) city)"),
        ("make()(3)", "(call (call make) 3)"),
        ("pair[0]", "(index pair 0)"),
        ("add[1]", "(index add 1)"),
        (
            "lines.map(trim).filter(nonEmpty)",
            "(call (. (call (. lines map) trim) filter) nonEmpty)",
        ),
        ("#parseError(at: 3)", "(call #parseError (at: 3))"),
    ]);
}

#[test]
fn a_chain_is_an_operand_of_the_operators_around_it() {
    check(&[
        // DESIGN.md: `accel(pos[i-1]) * dt ** 2`
        (
            "accel(pos[i - 1]) * dt ** 2",
            "(* (call accel (index pos (- i 1))) (** dt 2))",
        ),
        ("-x.abs", "(- (. x abs))"),
        ("-x ** 2", "(- (** x 2))"),
        ("2 ** -1", "(** 2 (- 1))"),
        ("!done && xs.len > 0", "(&& (! done) (> (. xs len) 0))"),
        ("a - b - c", "(- (- a b) c)"),
        ("(a - b).abs", "(. (- a b) abs)"),
        ("total div n mod 7", "(mod (div total n) 7)"),
        ("x == y || p.ok", "(|| (== x y) (. p ok))"),
        (
            "\"${user.name} has ${cart.items.len} items\"",
            "(str (. user name) \" has \" (. (. cart items) len) \" items\")",
        ),
        (
            "label(\"${row.id}\", \"${row.qty * row.price}\")",
            "(call label (str (. row id)) (str (* (. row qty) (. row price))))",
        ),
    ]);
}

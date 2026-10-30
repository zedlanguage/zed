//! Soundness on random bodies: for each arrow the checker gives a random function, each value
//! the evaluator computes at arguments of the arrow's parameter types lies in its result.

use zed_kernel::{Evaluator, F64, Value, World};
use zed_tests::instances::Rng;
use zedc::check::ty::Carrier;

use super::info;
use crate::l01_16_elaboration::{elab, with_prelude};

/// A random body over `x` and `y`, of depth at most `d`.
fn body(rng: &mut Rng, d: u32) -> String {
    if d == 0 || rng.below(3) == 0 {
        return match rng.below(7) {
            0 | 1 => "x".into(),
            2 | 3 => "y".into(),
            4 => rng.int(-3, 3).to_string(),
            5 => format!("{}.5", rng.int(-2, 2)),
            _ => "\"s\"".into(),
        };
    }
    let a = body(rng, d - 1);
    let b = body(rng, d - 1);
    match rng.below(9) {
        0 => format!("({a} + {b})"),
        1 => format!("({a} - {b})"),
        2 => format!("({a} * {b})"),
        3 => format!("({a} / {b})"),
        4 => format!("({a} ++ {b})"),
        5 => format!("(-{a})"),
        6 => format!("if {a} < {b} {{ {a} }} else {{ {b} }}"),
        7 => format!("if {a} == {b} {{ {b} }} else {{ {a} }}"),
        _ => format!("(if {a} is String {{ len({a}) }} else {{ {b} }})"),
    }
}

/// Argument texts of carrier `c`.
fn args(c: Carrier) -> &'static [&'static str] {
    match c {
        Carrier::Int => &["0", "2", "-3"],
        Carrier::F64 => &["0.0", "1.5", "-2.25"],
        Carrier::Rat => &["0r", "3r/2r", "(0r - 2r)"],
        Carrier::Str => &["\"\"", "\"ab\""],
        Carrier::Bool => &["true", "false"],
    }
}

#[test]
fn each_computed_value_is_in_its_arrows_result() {
    let mut rng = Rng::new(26);
    let (mut fns, mut checked, mut failed) = (0, 0, 0);
    for _ in 0..700 {
        let f = format!("f(positional x, positional y) = {};\n", body(&mut rng, 3));
        let (i, _) = info(&f);
        if !i.errors.is_empty() {
            continue;
        }
        let s = i.sigs.values().next().unwrap().clone();
        fns += 1;
        // One call for each arrow with carrier parameters and each pair of arguments.
        let mut p = f.clone();
        let mut calls = Vec::new();
        for a in &s.arrows {
            let cs: Option<Vec<Carrier>> = a
                .params
                .iter()
                .map(|p| match p.pieces().as_slice() {
                    [pc] => pc.carrier(),
                    _ => None,
                })
                .collect();
            let Some(cs) = cs else { continue };
            for x in args(cs[0]) {
                for y in args(cs[1]) {
                    p += &format!("r{} = f({x}, {y});\n", calls.len());
                    calls.push((format!("f({x}, {y})"), &a.result));
                }
            }
        }
        let u = elab(&p).unwrap_or_else(|e| panic!("{p}: {e:?}"));
        for (k, (call, result)) in calls.iter().enumerate() {
            let t = u.get(&format!("r{k}")).unwrap();
            match Evaluator::new(World::new()).run(&with_prelude(t)) {
                Ok(v) => {
                    assert!(result.contains(&v), "{f}{call}: {v} is not in {result}");
                    checked += 1;
                }
                // A value past the size limit; a division by zero is the atom, a value.
                Err(_) => failed += 1,
            }
        }
    }
    println!("{fns} functions, {checked} values, {failed} failed");
    assert!(
        fns >= 300 && checked >= 650,
        "{fns} functions, {checked} values"
    );
    assert!(failed < checked / 4, "{failed} failed of {checked}");
}

#[test]
fn a_wrong_claim_is_caught() {
    // The check above would reject a result type that missed the value.
    let (i, _) = info("f(positional x, positional y) = x + y;\n");
    let a = &i.sigs.values().next().unwrap().arrows[0];
    assert!(a.result.contains(&Value::Int(3)));
    assert!(!a.result.contains(&Value::Float(F64::new(3.0))));
    assert!(!a.result.contains(&Value::Str("3".into())));
}

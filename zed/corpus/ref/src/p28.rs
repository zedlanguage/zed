//! 28 precedence climbing (shunting-yard with the same pop rule) modulo 65536. Zed rule used: mod
//! is Euclidean.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::ToPrimitive;

use crate::zedrt::parse_int;

const M: u64 = 65536;

fn prec(tok: &str) -> Option<u32> {
    match tok {
        "+" | "-" => Some(1),
        "*" => Some(2),
        "^" => Some(3),
        _ => None,
    }
}

fn apply(o: &str, a: u64, b: u64) -> u64 {
    match o {
        "+" => (a + b) % M,
        "-" => (a + M - b) % M,
        "*" => (a * b) % M,
        _ => {
            let (mut result, mut base, mut e) = (1, a % M, b);
            while e > 0 {
                if e & 1 == 1 {
                    result = result * base % M;
                }
                base = base * base % M;
                e >>= 1;
            }
            result % M
        }
    }
}

fn red(vals: &mut Vec<u64>, ops: &mut Vec<&str>) -> Result<(), String> {
    let short = || "too few operands".to_string();
    let b = vals.pop().ok_or_else(short)?;
    let a = vals.pop().ok_or_else(short)?;
    let o = ops.pop().expect("reduced only with an operator waiting");
    vals.push(apply(o, a, b));
    Ok(())
}

fn ev(l: &str) -> Result<u64, String> {
    let (mut vals, mut ops): (Vec<u64>, Vec<&str>) = (Vec::new(), Vec::new());
    let m = BigInt::from(M);
    for tok in l.split(' ') {
        if let Some(p) = prec(tok) {
            while let Some(top) = ops.last().copied().and_then(prec) {
                if top > p || (top == p && tok != "^") {
                    red(&mut vals, &mut ops)?;
                } else {
                    break;
                }
            }
            ops.push(tok);
        } else {
            let v = parse_int(tok)?.mod_floor(&m);
            vals.push(v.to_u64().expect("below the modulus"));
        }
    }
    while !ops.is_empty() {
        red(&mut vals, &mut ops)?;
    }
    vals.first().copied().ok_or("no value".into())
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    for l in lines {
        say!(out, "{l} = {}", ev(l)?);
    }
    Ok(())
}

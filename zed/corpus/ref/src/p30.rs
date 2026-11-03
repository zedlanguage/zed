//! 30 client/server, run as one process. The struct grammars are phrase level: whitespace between
//! elements is skipped. A parse failure reports the farthest position any alternative reached
//! (the same assumption as 07). serialize writes the elements with no whitespace. Positions are
//! code-point offsets; item names are ASCII letters and quantities ASCII digits.

use num_bigint::BigInt;

use crate::zedrt::parse_int;

fn price(item: &str) -> Option<u32> {
    match item {
        "apple" => Some(3),
        "pear" => Some(5),
        "plum" => Some(2),
        _ => None,
    }
}

struct Request {
    kind: String,
    item: String,
    qty: Option<String>,
}

fn ws(s: &[char], mut i: usize) -> usize {
    while matches!(s.get(i), Some(' ' | '\t')) {
        i += 1;
    }
    i
}

/// After whitespace from `i`: the start and end of the longest run of `ok` characters.
fn word(s: &[char], i: usize, ok: fn(&char) -> bool) -> (usize, usize) {
    let start = ws(s, i);
    let n = s[start..].iter().take_while(|c| ok(c)).count();
    (start, start + n)
}

/// The request on `line`, or the farthest failure position.
fn parse(line: &str) -> Result<Request, usize> {
    let s: Vec<char> = line.chars().collect();
    let text = |i: usize, j: usize| s[i..j].iter().collect::<String>();
    let mut far = 0;
    let at0 = ws(&s, 0);
    for kind in ["get", "buy"] {
        if at0 + 3 > s.len() || text(at0, at0 + 3) != kind {
            far = far.max(at0);
            continue;
        }
        let (item_at, item_end) = word(&s, at0 + 3, char::is_ascii_alphabetic);
        if item_end == item_at {
            far = far.max(item_at);
            continue;
        }
        let mut j = item_end;
        let mut qty = None;
        if kind == "buy" {
            let (qty_at, qty_end) = word(&s, j, char::is_ascii_digit);
            if qty_end == qty_at {
                far = far.max(qty_at);
                continue;
            }
            qty = Some(text(qty_at, qty_end));
            j = qty_end;
        }
        j = ws(&s, j);
        if j != s.len() {
            far = far.max(j);
            continue;
        }
        return Ok(Request {
            kind: kind.into(),
            item: text(item_at, item_end),
            qty,
        });
    }
    Err(far)
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    for l in lines {
        match parse(l) {
            Ok(Request { kind, item, qty }) => {
                let q = match qty.filter(|_| kind != "get") {
                    Some(qty) => parse_int(&qty)?,
                    None => BigInt::from(1),
                };
                match price(&item) {
                    Some(p) => say!(out, "{item}={}", BigInt::from(p) * q),
                    None => say!(out, "missing:{item}"),
                }
            }
            Err(far) => say!(out, "bad request at {far}"),
        }
    }
    Ok(())
}

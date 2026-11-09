//! Number literals (steps L1.3 and L1.4):
//!
//! ```peg
//! Number   = (Rational | Generic | Float | Integer) !XID_CONTINUE
//! Rational = (Float | Decimal) 'r'
//! Generic  = Integer 'n'
//! Float    = Decimal '.' Decimal Exponent? | Decimal Exponent
//! Exponent = [eE] [+\-]? Decimal
//! Integer  = '0x' Hex ('_'? Hex)* | '0o' [0-7] ('_'? [0-7])* | '0b' [01] ('_'? [01])* | Decimal
//! Decimal  = [0-9] ('_'? [0-9])*
//! ```
//!
//! A literal keeps its digits, with the `_` removed, and its base: its width is chosen later
//! from its use (sec:domains), so the lexer never rounds or overflows. A float or a rational
//! keeps its decimal text, and a rational is exact (`0.1r` is one tenth). A digit must follow
//! the `.`, so `5.double` and `1..10` begin with the integer. A number that runs into a
//! character that continues a name is one error over the number and that run, since no other
//! rule reads a token starting with a digit: `200ms`, `1__000`, `1_000_`, `0b102`, `0x`.
//!
//! An integer followed by `n` is generic (step L1.26a): `1n` is the integer 1 in whichever
//! numeric carrier its use needs. Only an integer takes the `n`, since it has the same value in
//! every carrier, and a decimal does not (`0.1` in f64 is not one tenth), so `1.5n` and
//! `1e3n` are errors that name `1.5` and `1.5r`.

use std::sync::Arc;

use num_bigint::BigUint;
use unicode_ident::is_xid_continue;
use zed_kernel::num::TooLarge;

use super::token::{Error, ErrorKind, Span, Tok};

/// The end and token of the number starting at byte `pos` of `text`, if one starts there.
pub(super) fn number(text: &str, pos: usize) -> Option<Result<(usize, Tok), Error>> {
    let b = text.as_bytes();
    if !b.get(pos)?.is_ascii_digit() {
        return None;
    }
    let prefixed = |p: u8| b.get(pos) == Some(&b'0') && b.get(pos + 1) == Some(&p);
    let radix = [(b'x', 16), (b'o', 8), (b'b', 2)]
        .into_iter()
        .find(|&(p, r)| prefixed(p) && b.get(pos + 2).is_some_and(|&d| digit(d, r)))
        .map_or(10, |(_, r)| r);
    let start = if radix == 10 { pos } else { pos + 2 };
    let mut end = digits(b, start, radix);
    let int_end = end;
    if radix == 10 {
        if b.get(end) == Some(&b'.') && b.get(end + 1).is_some_and(u8::is_ascii_digit) {
            end = digits(b, end + 1, 10);
        }
        if matches!(b.get(end), Some(b'e' | b'E')) {
            let sign = usize::from(matches!(b.get(end + 1), Some(b'+' | b'-')));
            if b.get(end + 1 + sign).is_some_and(u8::is_ascii_digit) {
                end = digits(b, end + 1 + sign, 10);
            }
        }
    }
    let rational = radix == 10 && b.get(end) == Some(&b'r');
    let generic = end == int_end && b.get(end) == Some(&b'n');
    let after = end + usize::from(rational || generic);
    if text[after..].chars().next().is_some_and(is_xid_continue) {
        return Some(Err(run_on(text, pos, after, radix)));
    }
    let digits = match without_separators(&text[start..end]) {
        Ok(d) => Arc::new(d),
        Err(r) => {
            return Some(Err(Error {
                kind: ErrorKind::Unread(r),
                span: Span {
                    start: pos,
                    end: after,
                },
            }));
        }
    };
    let tok = if rational {
        Tok::Rat(digits)
    } else if generic {
        Tok::Generic { radix, digits }
    } else if end > int_end {
        Tok::Float(digits)
    } else {
        Tok::Int { radix, digits }
    };
    Some(Ok((after, tok)))
}

/// `s` without its `_`, in memory the system gives first for all of `s`; [`TooLarge`] when it
/// refuses, naming that memory, so a literal too long to copy is an error and not an abort.
fn without_separators(s: &str) -> Result<String, TooLarge> {
    let mut out = String::new();
    out.try_reserve_exact(s.len()).map_err(|_| TooLarge {
        bits: BigUint::from(s.len()) << 3u32,
    })?;
    s.split('_').for_each(|part| out.push_str(part));
    Ok(out)
}

fn digit(d: u8, radix: u32) -> bool {
    (d as char).is_digit(radix)
}

/// The end of the digits of base `radix` starting at `pos`, a digit, with single `_` between.
fn digits(b: &[u8], pos: usize, radix: u32) -> usize {
    let mut end = pos + 1;
    loop {
        match b.get(end) {
            Some(&d) if digit(d, radix) => end += 1,
            Some(b'_') if b.get(end + 1).is_some_and(|&d| digit(d, radix)) => end += 2,
            _ => return end,
        }
    }
}

/// The error for a number from `pos` to `end` followed by a character continuing a name.
fn run_on(text: &str, pos: usize, end: usize, radix: u32) -> Error {
    let run = text[end..]
        .char_indices()
        .find(|&(_, c)| !is_xid_continue(c))
        .map_or(text.len(), |(i, _)| end + i);
    let next = text[end..].chars().next().expect("a character follows");
    let d = &text[pos..end];
    let why = if matches!(next, 'e' | 'E') && radix == 10 && !d.contains(['e', 'E']) {
        format!(
            "the number `{d}{next}` has an exponent mark `{next}` with no digits after it, and an \
             exponent needs digits, as in `1e3` or `1e-3`. Write the exponent's digits after \
             `{next}`, or remove the `{next}`."
        )
    } else if next == 'r' && radix != 10 {
        format!(
            "the number `{d}r` is a rational written in another base, and a rational is written \
             in decimal, as `16r` for the value of `0x10`. Write its value in decimal digits \
             before the `r`."
        )
    } else if next == 'n' && radix == 10 && !d.ends_with('r') && d.contains(['.', 'e', 'E']) {
        format!(
            "the number `{d}n` puts the suffix `n` on a decimal, and only an integer takes `n`: \
             an integer has the same value in every number type, while a decimal has one value \
             in f64 and another in rat. Write `{d}` for a float or `{d}r` for an exact rational."
        )
    } else if next == '_' {
        let whole = &text[pos..run];
        format!(
            "the number `{whole}` has a `_` that does not stand between two digits, and `_` may \
             stand only between two digits, as in `1_000_000`. Remove that `_`."
        )
    } else if radix == 10 && d == "0" && "XOB".contains(next) {
        let lower = next.to_ascii_lowercase();
        format!(
            "`0{next}` is written with a capital `{next}`, and a number's base is marked with a \
             small letter: `0x`, `0o` or `0b`. Write `0{lower}`."
        )
    } else if radix == 10 && d == "0" && "xob".contains(next) {
        let (base, example) = match next {
            'x' => ("16", "0x1F"),
            'o' => ("8", "0o17"),
            _ => ("2", "0b101"),
        };
        format!(
            "`0{next}` starts a number in base {base}, and no digit of base {base} follows it. \
             Write the digits after `0{next}`, as in `{example}`."
        )
    } else if radix < 10 && next.is_ascii_digit() {
        let whole = &text[pos..run];
        let (prefix, digits) = if radix == 2 {
            ("0b", "0 and 1")
        } else {
            ("0o", "0 to 7")
        };
        format!(
            "the number `{whole}` starts with `{prefix}`, whose digits are {digits}, and `{next}` \
             is not one of them. Write the number with those digits, or in decimal without \
             `{prefix}`."
        )
    } else {
        let name = &text[end..run];
        format!(
            "the number `{d}` runs into the name `{name}` with nothing between them, and a number \
             must not run into a name. Put an operator or a space between them, as in \
             `{d} * {name}`."
        )
    };
    Error {
        kind: ErrorKind::BadNumber(why),
        span: Span {
            start: pos,
            end: run,
        },
    }
}

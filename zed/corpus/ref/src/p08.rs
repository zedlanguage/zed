//! 08 percent-decoding fused with UTF-8 decoding: the two recurrences of the program, run in
//! order. hexVal of a character that is not a hex digit is 0 (indexOf gives #none, `else 0`).
//! A byte sequence cut short by a #char or by the end of the line is dropped; a stray
//! continuation byte is dropped, and so is a byte from 0xF8 up, which starts no UTF-8 sequence;
//! a byte expected as a continuation is taken as one whatever its high bits are. Characters are
//! code points. A decoded value above U+10FFFF, a surrogate, or an overlong form (a value that a
//! shorter sequence writes, such as C0 80 for U+0000) is not a character and is dropped, as the
//! program's header says of malformed UTF-8.

/// The value of hex digit `c` (either case), else 0, also for no character.
fn hex_val(c: Option<&char>) -> u32 {
    c.and_then(|c| c.to_digit(16)).unwrap_or(0)
}

enum Token {
    Byte(u32),
    Char(char),
}

fn decode(line: &str) -> String {
    let s: Vec<char> = line.chars().collect();
    let mut skip = Vec::with_capacity(s.len());
    let mut prev = 0;
    for &c in &s {
        prev = if c == '%' && prev == 0 {
            2
        } else {
            prev.max(1) - 1
        };
        skip.push(prev);
    }
    let mut toks = Vec::new();
    for (i, &c) in s.iter().enumerate() {
        if i > 0 && skip[i - 1] != 0 {
            continue;
        }
        toks.push(if c == '%' {
            Token::Byte(hex_val(s.get(i + 1)) * 16 + hex_val(s.get(i + 2)))
        } else {
            Token::Char(c)
        });
    }
    // A value that is no Unicode scalar value (a surrogate, or above U+10FFFF) writes nothing.
    let emit = |c: u32, out: &mut String| {
        if let Some(c) = char::from_u32(c) {
            out.push(c);
        }
    };
    let mut out = String::new();
    // `min` is the smallest value a sequence of the current length writes; below it the form is
    // overlong.
    let (mut need, mut cp, mut min) = (0, 0, 0);
    for tok in toks {
        match tok {
            Token::Char(code) => {
                (need, cp) = (0, 0);
                out.push(code);
            }
            Token::Byte(b) if need == 0 => match b {
                0..128 => emit(b, &mut out),
                128..192 => {} // a stray continuation byte
                192..224 => (need, cp, min) = (1, b % 32, 0x80),
                224..240 => (need, cp, min) = (2, b % 16, 0x800),
                240..248 => (need, cp, min) = (3, b % 8, 0x1_0000),
                _ => {} // starts no sequence
            },
            Token::Byte(v) => {
                cp = cp * 64 + v % 64;
                if need == 1 {
                    if cp >= min {
                        emit(cp, &mut out);
                    }
                    (need, cp) = (0, 0);
                } else {
                    need -= 1;
                }
            }
        }
    }
    out
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    for line in lines {
        say!(out, "{}", decode(line));
    }
    Ok(())
}

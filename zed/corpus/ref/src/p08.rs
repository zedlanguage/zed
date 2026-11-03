//! 08 percent-decoding fused with UTF-8 decoding: the two recurrences of the program, run in
//! order. hexVal of a character that is not a hex digit is 0 (indexOf gives #none, `else 0`).
//! A byte sequence cut short by a #char or by the end of the line is dropped; a stray
//! continuation byte is dropped; a byte expected as a continuation is taken as one whatever its
//! high bits are. Characters are code points. A decoded value above U+10FFFF, or a surrogate, is
//! not a character: the line fails.

/// The value of hex digit `c` (either case), else 0, also for no character.
fn hex_val(c: Option<&char>) -> u32 {
    c.and_then(|c| c.to_digit(16)).unwrap_or(0)
}

enum Token {
    Byte(u32),
    Char(char),
}

fn decode(line: &str) -> Result<String, String> {
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
    let emit = |c: u32, out: &mut String| match char::from_u32(c) {
        Some(c) => {
            out.push(c);
            Ok(())
        }
        None => Err(format!("not a printable character: U+{c:x}")),
    };
    let mut out = String::new();
    let (mut need, mut cp) = (0, 0);
    for tok in toks {
        match tok {
            Token::Char(code) => {
                (need, cp) = (0, 0);
                out.push(code);
            }
            Token::Byte(b) if need == 0 => match b {
                0..128 => emit(b, &mut out)?,
                128..192 => {} // a stray continuation byte
                192..224 => (need, cp) = (1, b % 32),
                224..240 => (need, cp) = (2, b % 16),
                _ => (need, cp) = (3, b % 8),
            },
            Token::Byte(v) => {
                cp = cp * 64 + v % 64;
                if need == 1 {
                    emit(cp, &mut out)?;
                    (need, cp) = (0, 0);
                } else {
                    need -= 1;
                }
            }
        }
    }
    Ok(out)
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    for line in lines {
        say!(out, "{}", decode(line)?);
    }
    Ok(())
}

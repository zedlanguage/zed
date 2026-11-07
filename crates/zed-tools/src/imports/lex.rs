//! The tokens of Rust text, as far as the import graph needs them, and the matching brackets.

/// A token of Rust text. Comments make no token.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Tok<'a> {
    Ident(&'a str),
    /// A number, `0` or `1.5`.
    Num(&'a str),
    /// A string, byte string or character literal, whose text is not kept.
    Str,
    /// `::`
    Sep,
    /// `{`
    Open,
    /// `}`
    Close,
    LParen,
    RParen,
    LBrack,
    RBrack,
    Lt,
    Gt,
    Semi,
    Comma,
    Star,
    Bang,
    Dot,
    Amp,
    Question,
    Colon,
    Eq,
    Pipe,
    Hash,
    /// `->`
    Arrow,
    /// `=>`
    FatArrow,
    /// A lifetime or a label, `'a`.
    Life,
    Other,
}

fn is_ident(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_' || c >= 0x80
}

/// The tokens of `text`, each with its line. Comments are skipped and a string or character
/// literal is one token, so a path written in them is not read as one.
pub(super) fn lex(text: &str) -> Vec<(Tok<'_>, usize)> {
    let b = text.as_bytes();
    let (mut i, mut line) = (0, 1);
    let mut toks = Vec::new();
    while let Some(&c) = b.get(i) {
        match c {
            b'\n' => {
                line += 1;
                i += 1;
            }
            b' ' | b'\t' | b'\r' => i += 1,
            b'/' if b.get(i + 1) == Some(&b'/') => {
                while b.get(i).is_some_and(|&c| c != b'\n') {
                    i += 1;
                }
            }
            b'/' if b.get(i + 1) == Some(&b'*') => {
                let mut depth = 0usize;
                while i < b.len() {
                    if b[i..].starts_with(b"/*") {
                        depth += 1;
                        i += 2;
                    } else if b[i..].starts_with(b"*/") {
                        depth -= 1;
                        i += 2;
                        if depth == 0 {
                            break;
                        }
                    } else {
                        line += usize::from(b[i] == b'\n');
                        i += 1;
                    }
                }
            }
            b'"' => {
                toks.push((Tok::Str, line));
                i = string(b, i, None, &mut line);
            }
            b'\'' => i = quote(b, i, &mut line, &mut toks),
            b'0'..=b'9' => {
                let start = i;
                i += 1;
                while b.get(i).is_some_and(|&c| {
                    is_ident(c) || (c == b'.' && b.get(i + 1).is_some_and(u8::is_ascii_digit))
                }) {
                    i += 1;
                }
                toks.push((Tok::Num(&text[start..i]), line));
            }
            c if is_ident(c) => {
                let start = i;
                while b.get(i).copied().is_some_and(is_ident) {
                    i += 1;
                }
                let word = &text[start..i];
                match (word, b.get(i)) {
                    ("r" | "br" | "cr", Some(b'#' | b'"')) => {
                        let hashes = b[i..].iter().take_while(|&&c| c == b'#').count();
                        if b.get(i + hashes) == Some(&b'"') {
                            toks.push((Tok::Str, line));
                            i = string(b, i + hashes, Some(hashes), &mut line);
                        } else {
                            // A raw identifier, `r#type`: a name, not the keyword.
                            i += hashes;
                            while b.get(i).copied().is_some_and(is_ident) {
                                i += 1;
                            }
                            toks.push((Tok::Ident(&text[start..i]), line));
                        }
                    }
                    ("b" | "c", Some(b'"')) => {
                        toks.push((Tok::Str, line));
                        i = string(b, i, None, &mut line);
                    }
                    // A byte literal `b'x'`: the quote that follows is read as a character.
                    ("b", Some(b'\'')) => {}
                    _ => toks.push((Tok::Ident(word), line)),
                }
            }
            _ => {
                let two = |d: u8| b.get(i + 1) == Some(&d);
                let tok = match c {
                    b':' if two(b':') => {
                        i += 1;
                        Tok::Sep
                    }
                    b'-' if two(b'>') => {
                        i += 1;
                        Tok::Arrow
                    }
                    b'=' if two(b'>') => {
                        i += 1;
                        Tok::FatArrow
                    }
                    b'{' => Tok::Open,
                    b'}' => Tok::Close,
                    b'(' => Tok::LParen,
                    b')' => Tok::RParen,
                    b'[' => Tok::LBrack,
                    b']' => Tok::RBrack,
                    b'<' => Tok::Lt,
                    b'>' => Tok::Gt,
                    b';' => Tok::Semi,
                    b',' => Tok::Comma,
                    b'*' => Tok::Star,
                    b'!' => Tok::Bang,
                    b'.' => Tok::Dot,
                    b'&' => Tok::Amp,
                    b'?' => Tok::Question,
                    b':' => Tok::Colon,
                    b'=' => Tok::Eq,
                    b'|' => Tok::Pipe,
                    b'#' => Tok::Hash,
                    _ => Tok::Other,
                };
                toks.push((tok, line));
                i += 1;
            }
        }
    }
    toks
}

/// Skips the string literal whose opening quote is at `i`, raw with `hashes` when given, and
/// gives the position after it.
fn string(b: &[u8], mut i: usize, hashes: Option<usize>, line: &mut usize) -> usize {
    i += 1;
    while let Some(&c) = b.get(i) {
        *line += usize::from(c == b'\n');
        match (c, hashes) {
            (b'\\', None) => {
                *line += usize::from(b.get(i + 1) == Some(&b'\n'));
                i += 2;
            }
            (b'"', None) => return i + 1,
            (b'"', Some(h)) if b[i + 1..].iter().take(h).filter(|&&c| c == b'#').count() == h => {
                return i + 1 + h;
            }
            _ => i += 1,
        }
    }
    i
}

/// Reads the character literal or lifetime whose quote is at `i` as a token, and gives the
/// position after it. A lifetime is a token of its own, so `'static` is not read as the word
/// `static`.
fn quote<'a>(b: &[u8], i: usize, line: &mut usize, toks: &mut Vec<(Tok<'a>, usize)>) -> usize {
    if b.get(i + 1) == Some(&b'\\') {
        toks.push((Tok::Str, *line));
        let mut j = i + 3;
        while b.get(j).is_some_and(|&c| c != b'\'') {
            j += 1;
        }
        return j + 1;
    }
    let width = match b.get(i + 1) {
        Some(&c) if c < 0x80 => 1,
        Some(&c) if c < 0xE0 => 2,
        Some(&c) if c < 0xF0 => 3,
        Some(_) => 4,
        None => return i + 1,
    };
    if b.get(i + 1 + width) == Some(&b'\'') {
        toks.push((Tok::Str, *line));
        *line += usize::from(b[i + 1] == b'\n');
        return i + 2 + width;
    }
    let mut j = i + 1;
    while b.get(j).copied().is_some_and(is_ident) {
        j += 1;
    }
    toks.push((Tok::Life, *line));
    j
}

/// For each bracket of `toks` (`{}`, `()`, `[]`), the position of the one that matches it; for
/// every other token, and a bracket without a match, its own position. One pass with a stack.
pub(super) fn mates(toks: &[(Tok<'_>, usize)]) -> Vec<usize> {
    let mut mate: Vec<usize> = (0..toks.len()).collect();
    let mut open: Vec<usize> = Vec::new();
    for (i, &(tok, _)) in toks.iter().enumerate() {
        let opener = match tok {
            Tok::Open | Tok::LParen | Tok::LBrack => {
                open.push(i);
                continue;
            }
            Tok::Close => Tok::Open,
            Tok::RParen => Tok::LParen,
            Tok::RBrack => Tok::LBrack,
            _ => continue,
        };
        // A close that does not match the innermost open (in a macro's text) is left alone.
        if open.last().is_some_and(|&o| toks[o].0 == opener) {
            let o = open.pop().expect("just seen");
            mate[o] = i;
            mate[i] = o;
        }
    }
    mate
}

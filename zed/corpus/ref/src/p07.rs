//! 07 JSON parser. Implements the grammar of 07-json-parser/json.zed with the Zed rules this
//! output depends on:
//! - struct grammars skip whitespace (space, tab) between elements; token types (JsonStr,
//!   JsonNum, JsonLit) are exact; nothing is skipped before the first element or after the
//!   document's end, which must be the end of the line;
//! - union alternatives are tried in declared order (they are disjoint by their first
//!   character, so the choice rule picks the only match);
//! - X* sep "," is zero or more X separated by ",", no trailing separator;
//! - serialize writes the matched text of every token and the literal scaffolding, with no
//!   whitespace;
//! - the #syntaxError position is the farthest code-point offset at which the parse failed,
//!   after skipping whitespace (an assumption; see LEDGER.md).
//!
//! A JsonNum digit is any character with a Numeric_Type of Decimal or Digit (`is_digit`); a
//! JsonStr character is an ASCII letter or digit, or a space.
//!
//! Lists nest as deeply as the input says, so the parse keeps its own stack of open lists and
//! writes the serialized text into one buffer as it goes.

use crate::zedrt::is_digit;

/// A list being parsed.
#[derive(Clone, Copy)]
enum List {
    Object,
    Array,
}

impl List {
    fn close(self) -> &'static str {
        match self {
            List::Object => "}",
            List::Array => "]",
        }
    }
}

struct Parser {
    s: Vec<char>,
    far: usize,
}

impl Parser {
    /// Records a failure at `i`.
    fn fail<T>(&mut self, i: usize) -> Option<T> {
        self.far = self.far.max(i);
        None
    }

    fn ws(&self, mut i: usize) -> usize {
        while matches!(self.s.get(i), Some(' ' | '\t')) {
            i += 1;
        }
        i
    }

    fn starts_with(&self, t: &str, i: usize) -> bool {
        (i..)
            .zip(t.chars())
            .all(|(at, c)| self.s.get(at) == Some(&c))
    }

    fn lit(&mut self, i: usize, t: &str) -> Option<usize> {
        if self.starts_with(t, i) {
            Some(i + t.len())
        } else {
            self.fail(i)
        }
    }

    /// Writes the text `i..j` of the line.
    fn copy(&self, i: usize, j: usize, out: &mut String) {
        out.extend(&self.s[i..j]);
    }

    /// The value at `i`. A list only opens here, with `after` the offset after its bracket; a
    /// failure anywhere fails the document, since the alternatives are disjoint by their first
    /// character, and every position tried while unwinding is below the failure.
    fn value(&mut self, i: usize, open: &mut Vec<List>, out: &mut String) -> Option<Step> {
        if let Some(after) = self.lit(i, "{") {
            out.push('{');
            open.push(List::Object);
            return Some(Step::Opened(after));
        }
        if let Some(after) = self.lit(i, "[") {
            out.push('[');
            open.push(List::Array);
            return Some(Step::Opened(after));
        }
        let end = self
            .str(i)
            .or_else(|| self.num(i))
            .or_else(|| self.kw(i))
            .or_else(|| self.fail(i))?;
        self.copy(i, end, out);
        Some(Step::Done(end))
    }

    /// The next element of the list on top of `open`, starting at `i`.
    fn item(&mut self, i: usize, open: &mut Vec<List>, out: &mut String) -> Option<Step> {
        if matches!(open.last(), Some(List::Object)) {
            let j = self.str(i)?;
            self.copy(i, j, out);
            let at = self.ws(j);
            let colon = self.lit(at, ":")?;
            out.push(':');
            let at = self.ws(colon);
            self.value(at, open, out)
        } else {
            self.value(i, open, out)
        }
    }

    /// Parses the document at the start of the line, writing it to `out`, and gives the offset
    /// after it.
    fn document(&mut self, out: &mut String) -> Option<usize> {
        let mut open = Vec::new();
        let mut step = self.value(0, &mut open, out)?;
        loop {
            step = match step {
                Step::Opened(after) => {
                    let first = self.ws(after);
                    let close = open.last().expect("a list just opened").close();
                    if self.starts_with(close, first) {
                        self.fail::<()>(first); // no element here
                        open.pop();
                        out.push_str(close);
                        Step::Done(first + 1)
                    } else {
                        self.item(first, &mut open, out)?
                    }
                }
                Step::Done(end) => {
                    let Some(&list) = open.last() else {
                        return Some(end);
                    };
                    let before = self.ws(end);
                    if let Some(comma) = self.lit(before, ",") {
                        out.push(',');
                        let after = self.ws(comma);
                        self.item(after, &mut open, out)?
                    } else {
                        let done = self.lit(before, list.close())?;
                        open.pop();
                        out.push_str(list.close());
                        Step::Done(done)
                    }
                }
            };
        }
    }

    fn str(&mut self, i: usize) -> Option<usize> {
        let mut j = self.lit(i, "\"")?;
        while self
            .s
            .get(j)
            .is_some_and(|c| c.is_ascii_alphanumeric() || *c == ' ')
        {
            j += 1;
        }
        self.lit(j, "\"")
    }

    fn digits(&self, mut k: usize) -> usize {
        while self.s.get(k).is_some_and(|c| is_digit(*c)) {
            k += 1;
        }
        k
    }

    fn num(&mut self, i: usize) -> Option<usize> {
        let j = i + usize::from(self.starts_with("-", i));
        let mut k = self.digits(j);
        if k == j {
            return self.fail(k);
        }
        if self.starts_with(".", k) {
            let m = self.digits(k + 1);
            if m > k + 1 {
                k = m;
            } else {
                self.far = self.far.max(k + 1);
            }
        }
        Some(k)
    }

    fn kw(&mut self, i: usize) -> Option<usize> {
        for w in ["true", "false", "null"] {
            if self.starts_with(w, i) {
                return Some(i + w.len());
            }
        }
        self.fail(i)
    }
}

/// What the document parse does next.
enum Step {
    /// A list opened; its elements or its end come after this offset.
    Opened(usize),
    /// A value ended at this offset.
    Done(usize),
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    for line in lines {
        let mut p = Parser {
            s: line.chars().collect(),
            far: 0,
        };
        let start = out.len();
        match p.document(out) {
            Some(end) if end == p.s.len() => out.push('\n'),
            Some(end) => {
                out.truncate(start);
                p.far = p.far.max(end);
                say!(out, "error at {}", p.far);
            }
            None => {
                out.truncate(start);
                say!(out, "error at {}", p.far);
            }
        }
    }
    Ok(())
}

//! The line ends of text read as lines (DESIGN.md sec:codecs, the layer `lines()`, and step
//! L1.19): a line ends at `\n`, at `\r\n` or at a lone `\r`, the line breaks of source text
//! (sec:lexical), and its line end is not part of it; a last line needs no line end, and an
//! input that ends with a line end has no empty line after it (author, 2026-11-13, QUESTIONS
//! A90). The text comes in reads of any size, and a line is given as soon as its `\n` or `\r`
//! is read: after a `\r` the reader drops a `\n` that comes next, in the same read or the next,
//! so no read waits on the character after a `\r`.
//!
//! The reader works on bytes. In UTF-8 the bytes `\r` and `\n` occur only as those characters,
//! never inside the encoding of another, so splitting the bytes splits the characters, and a
//! line's bytes are checked as UTF-8 by the caller.

/// Splits text, given in reads, into lines. A line that lies inside one read is given as a
/// slice of that read; one that straddles reads is joined in a buffer that grows by doubling,
/// so each byte is copied at most once (amortized) and only when its line crosses a read
/// (sec:codecs, Cost). Memory is bounded by the longest line.
///
/// Complexity tradeoff: the scan tests each byte against `\n` and `\r` one at a time, O(n) for
/// n bytes with a small constant. DESIGN sec:codecs asks the layer `lines()` to find line ends
/// sixteen or thirty-two bytes per step with vector registers; that scan belongs to step L7.3i,
/// which builds the layer, and gives the same lines.
#[derive(Debug, Default)]
pub struct LineReader {
    /// The start of a line not yet ended, joined from earlier reads; empty when no line is open,
    /// since a line is open only once a byte of it that is no line end has been read.
    held: Vec<u8>,
    /// Whether the last byte read was a `\r`, so that a `\n` at the start of the next read is
    /// the second half of `\r\n` and ends no line.
    after_cr: bool,
}

impl LineReader {
    /// A reader at the start of its input.
    pub fn new() -> LineReader {
        LineReader::default()
    }

    /// Reads `bytes`, the next part of the input, and gives `line` each line that ends in it, in
    /// order, without its line end. O(b + h) for b bytes and h bytes held from earlier reads.
    pub fn read(&mut self, bytes: &[u8], mut line: impl FnMut(&[u8])) {
        let mut rest = bytes;
        if self.after_cr && !rest.is_empty() {
            self.after_cr = false;
            if let [b'\n', after @ ..] = rest {
                rest = after;
            }
        }
        while let Some(i) = rest.iter().position(|&b| b == b'\n' || b == b'\r') {
            if self.held.is_empty() {
                line(&rest[..i]);
            } else {
                self.held.extend_from_slice(&rest[..i]);
                line(&self.held);
                self.held.clear();
            }
            let cr = rest[i] == b'\r';
            rest = &rest[i + 1..];
            if cr {
                match rest {
                    [b'\n', after @ ..] => rest = after,
                    [] => self.after_cr = true,
                    _ => {}
                }
            }
        }
        self.held.extend_from_slice(rest);
    }

    /// Ends the input, giving `line` the last line if it has no line end.
    pub fn finish(self, mut line: impl FnMut(&[u8])) {
        if !self.held.is_empty() {
            line(&self.held);
        }
    }

    /// The lines of `bytes`, a whole input read at once, each a slice of it.
    pub fn whole(bytes: &[u8], mut line: impl FnMut(&[u8])) {
        let mut reader = LineReader::new();
        reader.read(bytes, &mut line);
        reader.finish(line);
    }
}

#[cfg(test)]
mod tests {
    use super::LineReader;

    /// The lines of `reads`, read one after another.
    fn lines(reads: &[&[u8]]) -> Vec<String> {
        let mut out = Vec::new();
        let mut reader = LineReader::new();
        let mut give = |l: &[u8]| out.push(String::from_utf8(l.to_vec()).unwrap());
        for r in reads {
            reader.read(r, &mut give);
        }
        reader.finish(give);
        out
    }

    #[test]
    fn each_line_end_ends_one_line() {
        assert_eq!(lines(&[b""]), Vec::<String>::new());
        assert_eq!(lines(&[b"\n"]), [""]);
        assert_eq!(lines(&[b"\r"]), [""]);
        assert_eq!(lines(&[b"\r\n"]), [""]);
        for whole in [&b"a"[..], b"a\n", b"a\r\n", b"a\r"] {
            assert_eq!(lines(&[whole]), ["a"], "{whole:?}");
        }
        assert_eq!(lines(&[b"a\rb"]), ["a", "b"]);
        assert_eq!(lines(&[b"a\r\nb"]), ["a", "b"]);
        assert_eq!(lines(&[b"a\n\rb"]), ["a", "", "b"]);
        assert_eq!(lines(&[b"a\r\r\n"]), ["a", ""]);
        assert_eq!(lines(&[b"a\n\nb\n"]), ["a", "", "b"]);
    }

    #[test]
    fn a_line_is_given_when_its_cr_is_read() {
        let mut out = Vec::new();
        let mut reader = LineReader::new();
        reader.read(b"a\r", |l| out.push(l.to_vec()));
        // Given at once, before the next read is in.
        assert_eq!(out, [b"a".to_vec()]);
        reader.read(b"\nb", |l| out.push(l.to_vec()));
        assert_eq!(out, [b"a".to_vec()]);
        reader.finish(|l| out.push(l.to_vec()));
        assert_eq!(out, [b"a".to_vec(), b"b".to_vec()]);
    }

    #[test]
    fn every_cut_of_the_input_gives_the_same_lines() {
        let input = b"one\r\ntwo\rthree\n\r\nfour\r\rfive\r";
        let whole = lines(&[input]);
        assert_eq!(whole, ["one", "two", "three", "", "four", "", "five"]);
        for cut in 0..=input.len() {
            let (a, b) = input.split_at(cut);
            assert_eq!(lines(&[a, b]), whole, "cut at {cut}");
            // An empty read between the two keeps a `\r` at the end of the first.
            assert_eq!(
                lines(&[a, b"", b]),
                whole,
                "cut at {cut} with an empty read"
            );
        }
        let bytes: Vec<&[u8]> = input.chunks(1).collect();
        assert_eq!(lines(&bytes), whole, "one byte per read");
    }
}

//! The line and column of an offset, from the line starts found once (`source::Lines`), agree
//! with decoding the text from its first byte up to the offset.

use zed_tests::instances::Rng;
use zedc::source::{Lines, line_col};

/// The line and column of `offset` by decoding `text[..offset]`: the definition.
fn decoded(text: &str, offset: usize) -> (usize, usize) {
    let (mut line, mut col) = (1, 1);
    let mut chars = text[..offset].chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\r' if chars.peek() == Some(&'\n') => {}
            '\r' | '\n' => (line, col) = (line + 1, 1),
            _ => col += 1,
        }
    }
    (line, col)
}

#[test]
fn every_offset_is_placed_as_decoding_places_it() {
    let mut rng = Rng::new(0x11c0);
    let pieces = ["a", "é", "€", "\n", "\r", "\r\n", "\n\r", "\r\r\n", "𝄞"];
    for _ in 0..200 {
        let text: String = (0..rng.below(30)).map(|_| rng.pick(&pieces)).collect();
        let lines = Lines::new(text.as_bytes());
        for offset in (0..=text.len()).filter(|&i| text.is_char_boundary(i)) {
            let want = decoded(&text, offset);
            assert_eq!(
                lines.line_col(text.as_bytes(), offset),
                want,
                "{text:?} at {offset}"
            );
            assert_eq!(
                line_col(text.as_bytes(), offset),
                want,
                "{text:?} at {offset}"
            );
        }
    }
}

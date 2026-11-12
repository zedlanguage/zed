//! The checker marks the parts a message's types share with the Unicode noncharacters U+FDD4 to
//! U+FDD8 until it names them or writes them in full (steps MSG-type-defs-layout,
//! MSG-derive-type-size), and the variables of a type it names in a message with U+FDD9 to U+FDDE
//! (UNDERSCORE-print). User text with those characters must never be read as a mark: a string
//! writes them escaped, as `\u{fdd5}`, which reads back, and a name or an atom cannot hold them.

use super::rejected;

/// `ap` takes a pair of two `int | #x`, so its messages define `T1`; `h` passes it `arg`.
fn passing(arg: &str) -> String {
    format!("ap(positional g: (int | #x, int | #x)) = 0;\nh() = ap({arg});\nmain() = 0;\n")
}

#[test]
fn a_string_with_the_marks_is_written_escaped_beside_the_definitions() {
    for code in 0xFDD4..=0xFDDEu32 {
        let c = char::from_u32(code).unwrap();
        let esc = format!("\\u{{{code:X}}}");
        // The character itself, a reference's whole form around it, and its escape in the source.
        for (arg, shown) in [
            (format!("\"a{c}b\""), format!("\"a{esc}b\"")),
            (
                format!("\"{c}0\u{FDD6}{c}\""),
                format!("\"{esc}0\\u{{FDD6}}{esc}\""),
            ),
            (format!("\"a\\u{{{code:X}}}b\""), format!("\"a{esc}b\"")),
        ] {
            let out = rejected(&passing(&arg));
            let mut lines = out.lines();
            assert_eq!(
                lines.next(),
                Some(
                    format!(
                        "2:7: `ap` does not take ({shown}): no arrow of `ap` takes these types."
                    )
                    .as_str()
                ),
                "{out}"
            );
            assert_eq!(
                lines.next(),
                Some("  T1 stands for a part written more than once:")
            );
            assert_eq!(lines.next(), Some("    type T1 = int | #x;"));
            assert!(out.contains("`ap` takes ((T1, T1)) -> 0"), "{out}");
            // Only the source lines quoted under a step hold the character as written.
            for line in out.lines().filter(|l| !l.contains(" | ")) {
                assert!(!line.contains(c), "{line:?} in {out}");
            }
        }
    }
}

#[test]
fn a_name_or_an_atom_cannot_hold_the_marks() {
    for code in 0xFDD4..=0xFDDEu32 {
        let c = char::from_u32(code).unwrap();
        for src in [
            passing(&format!("#a{c}")),
            passing("1").replace("h()", &format!("h{c}()")),
        ] {
            let out = rejected(&src);
            assert!(
                out.contains(&format!("(U+{code:X}) starts no name, number, operator")),
                "{out}"
            );
        }
    }
}

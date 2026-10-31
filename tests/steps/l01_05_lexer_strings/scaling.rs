//! The lexing of strings at the rule of low complexity (DESIGN.md Part G).

use zed_tests::scaling;

use super::parts;

/// A `"""` string of `n` indented lines, each holding a hole.
fn lines(n: usize) -> String {
    let body: String = (0..n).map(|i| format!("    line ${{{i}}}\n")).collect();
    format!("\"\"\"\n{body}    \"\"\"")
}

#[test]
fn a_long_indented_string_scales() {
    // Each character was tested against every line's cut of indentation.
    scaling::check("a \"\"\" string of n lines", 1000, |n| {
        assert_eq!(parts(&lines(n)).len(), 2 * n);
    });
    let p = parts(&lines(2));
    assert_eq!([&p[0][..], &p[2][..]], ["line ", "\nline "]);
    assert!(
        p[1].starts_with("${Int") && p[3].starts_with("${Int"),
        "{p:?}"
    );
}

/// A string whose holes nest `d` deep: `"${"${…"${0}"…}"}"`.
fn nested(d: usize) -> String {
    let mut s = "0".to_string();
    for _ in 0..d {
        s = format!("\"${{{s}}}\"");
    }
    s
}

#[test]
fn nested_holes_scale() {
    // Each hole was scanned for its `}` once for each hole around it, and its text searched
    // for a line break as many times.
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            scaling::check("a string with holes nested d deep", 500, |d| {
                assert_eq!(parts(&nested(d)).len(), 1);
            });
        })
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(
        parts(&nested(2)),
        [
            "${Str([Hole { tokens: [Token { tok: Int { radix: 10, digits: \"0\" }, span: Span { start: 6, end: 7 } }], span: Span { start: 4, end: 8 } }])}"
        ]
    );
}

//! The documentation's fences (step L1.7): DESIGN.md and EXAMPLES.md are the first test suite
//! (DESIGN.md Part G, "The document is the first test suite").
//!
//! A fence is the text between a line ```` ```zed ```` and the next line ```` ``` ````, as
//! written, indentation included. A ✗ on a line marks the line the checker must reject; a ✗
//! on a line that is wholly a `//` comment marks a rejected variant instead, which is left out
//! of the fence's marks and is checked as its own fixture.

/// A fence and where it starts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fence {
    /// The line of its ```` ```zed ````, counted from 1.
    pub line: usize,
    /// The line just before that one, which a fixture file uses for the fence's header.
    pub before: String,
    /// The lines between the delimiters, joined by `\n`.
    pub text: String,
}

/// The fences tagged `zed` in `markdown`, in order. A fence that is never closed runs to the
/// end of the text.
pub fn extract(markdown: &str) -> Vec<Fence> {
    let lines: Vec<&str> = markdown.split('\n').collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        if lines[i].trim() == "```zed" {
            let body = lines[i + 1..]
                .iter()
                .take_while(|l| l.trim() != "```")
                .count();
            out.push(Fence {
                line: i + 1,
                before: if i > 0 {
                    lines[i - 1].into()
                } else {
                    String::new()
                },
                text: lines[i + 1..i + 1 + body].join("\n"),
            });
            i += body + 1;
        }
        i += 1;
    }
    out
}

/// The ✗ marks of a fence, by line within it, counted from 1.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Marks {
    /// The lines the checker must reject.
    pub lines: Vec<usize>,
    /// The lines that are wholly a comment: rejected variants, each with its own fixture.
    pub variants: Vec<usize>,
}

/// The ✗ marks of the fence `text`.
pub fn marks(text: &str) -> Marks {
    let mut m = Marks::default();
    for (k, line) in text.split('\n').enumerate() {
        if line.contains('✗') {
            if line.trim_start().starts_with("//") {
                m.variants.push(k + 1);
            } else {
                m.lines.push(k + 1);
            }
        }
    }
    m
}

/// The layer a `// layer Lk` comment line in `text` names, the highest if it names several.
pub fn label(text: &str) -> Option<u32> {
    text.split('\n')
        .filter_map(|l| {
            let rest = l.trim().strip_prefix("// layer L")?;
            let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
            let after = rest[digits.len()..].chars().next();
            if after.is_some_and(|c| c.is_alphanumeric() || c == '_') {
                return None;
            }
            digits.parse().ok()
        })
        .max()
}

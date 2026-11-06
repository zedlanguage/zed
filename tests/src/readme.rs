//! The results README.md states for its `zed` fences (item README-fences), and the table of
//! expected results the tests compare them with.
//!
//! The page states a fence's results in three forms: a trailing comment on a line of the fence
//! (`a = 5.double.clamp(0, 8);        // 8`), a ```` ```text ```` block after it, and an HTML
//! table after it under a bold caption line (`**`revenue`**`). A fence's results are those
//! between its closing line and the next `zed` fence or heading. A table with no caption line
//! compares the language with others or lists repairs, and states no result.
//!
//! Each result is written as lines, one form per kind:
//!
//! ```text
//! comment a = 5.double.clamp(0, 8); // 8
//! text
//! > a = 8, because 5.double is 10 and clamp(0, 8) caps it
//! table `revenue`
//! | region | day | sku | revenue |
//! | East | 0 | ink | 14 |
//! ```
//!
//! A table row has its cells' text with the tags removed and each `rowspan` cell repeated in the
//! rows it covers, so a row reads as one keypath and its value.
//!
//! The table of expected results holds one entry per fence, under the line `== KEY`, where KEY
//! is the fence's key in the copy (`README.md [Numbers] 1`). An entry lists the fence's results
//! in the lines above, in page order, each followed by the checks that compare it with the run:
//!
//! - `check EXPR`: a Zed expression of type `bool` that holds when the fence's run gives the
//!   stated result;
//! - `no check: REASON`: the result states nothing the run gives, such as a comment that only
//!   explains.
//!
//! Before its results an entry may have:
//!
//! - `input SOURCE`: a Zed statement added to the fence when it runs, for a value the page
//!   states as an input (`input:` in a caption or a text line);
//! - `runs from Lk: REASON`: the fence runs from layer `k` and not its own, because an input or
//!   the value of an earlier fence it names needs that layer.

/// One entry of the table of expected results.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Entry {
    /// The fence's key.
    pub key: String,
    /// The layer it runs from, if the entry raises it above the fence's own.
    pub runs_from: Option<u32>,
    /// The statements added to the fence when it runs.
    pub inputs: Vec<String>,
    /// Its results, each as its lines, with the checks that follow it.
    pub results: Vec<Stated>,
}

/// One stated result of an [`Entry`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Stated {
    /// The result as the page states it, in the lines of the module documentation.
    pub lines: Vec<String>,
    /// The Zed expressions that must hold.
    pub checks: Vec<String>,
    /// Why it has no check, if it has none.
    pub no_check: Option<String>,
}

/// The table of expected results `text`, in order; an error names the line that is not one of
/// the forms the module documentation lists.
pub fn entries(text: &str) -> Result<Vec<Entry>, String> {
    let mut out: Vec<Entry> = Vec::new();
    for (k, line) in text.split('\n').enumerate() {
        let at = k + 1;
        if line.is_empty() {
            continue;
        }
        if let Some(key) = line.strip_prefix("== ") {
            out.push(Entry {
                key: key.into(),
                ..Entry::default()
            });
            continue;
        }
        let entry = out
            .last_mut()
            .ok_or_else(|| format!("line {at}: a line before the first `== KEY` line"))?;
        let starts_result =
            line.starts_with("comment ") || line == "text" || line.starts_with("table ");
        if let Some(rest) = line.strip_prefix("runs from L") {
            let (k, _reason) = rest
                .split_once(": ")
                .ok_or_else(|| format!("line {at}: `runs from Lk` has no `: REASON`"))?;
            let k = k
                .parse()
                .map_err(|_| format!("line {at}: `runs from L{k}` names no layer"))?;
            entry.runs_from = Some(k);
        } else if let Some(source) = line.strip_prefix("input ") {
            if !entry.results.is_empty() {
                return Err(format!("line {at}: an `input` line after a result"));
            }
            entry.inputs.push(source.into());
        } else if starts_result {
            entry.results.push(Stated {
                lines: vec![line.into()],
                ..Stated::default()
            });
        } else {
            let result = entry
                .results
                .last_mut()
                .ok_or_else(|| format!("line {at}: `{line}` comes before any result"))?;
            if let Some(expr) = line.strip_prefix("check ") {
                result.checks.push(expr.into());
            } else if let Some(reason) = line.strip_prefix("no check: ") {
                result.no_check = Some(reason.into());
            } else if line.starts_with("| ") || line == ">" || line.starts_with("> ") {
                if !result.checks.is_empty() || result.no_check.is_some() {
                    return Err(format!("line {at}: a line of a result after its checks"));
                }
                result.lines.push(line.into());
            } else {
                return Err(format!(
                    "line {at}: `{line}` is none of the forms of an entry"
                ));
            }
        }
    }
    Ok(out)
}

/// The results `page` states for each of its `zed` fences, in fence order, each as its lines.
/// Time linear in the length of the page.
pub fn stated(page: &str) -> Vec<Vec<Vec<String>>> {
    let lines: Vec<&str> = page.split('\n').collect();
    let mut out: Vec<Vec<Vec<String>>> = Vec::new();
    // Whether the lines read now follow a `zed` fence, before the next fence or heading.
    let mut after_fence = false;
    let mut caption: Option<&str> = None;
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        let trimmed = line.trim();
        if let Some(kind) = trimmed.strip_prefix("```") {
            let end = lines[i + 1..]
                .iter()
                .position(|l| l.trim() == "```")
                .map_or(lines.len(), |p| i + 1 + p);
            let body = &lines[(i + 1).min(end)..end];
            if kind == "zed" {
                out.push(
                    body.iter()
                        .filter_map(|l| comment(l))
                        .map(|c| vec![c])
                        .collect(),
                );
                after_fence = true;
            } else if kind == "text" && after_fence {
                let mut result = vec!["text".to_string()];
                result.extend(body.iter().map(|l| quoted(l)));
                out.last_mut().expect("a fence before").push(result);
            }
            caption = None;
            i = end + 1;
            continue;
        }
        if line.starts_with('#') {
            after_fence = false;
        } else if trimmed.starts_with("<table") {
            let end = lines[i..]
                .iter()
                .position(|l| l.contains("</table>"))
                .map_or(lines.len() - 1, |p| i + p);
            if let (true, Some(c)) = (after_fence, caption) {
                let mut result = vec![format!("table {c}")];
                result.extend(rows(&lines[i..=end].join("\n")));
                out.last_mut().expect("a fence before").push(result);
            }
            caption = None;
            i = end + 1;
            continue;
        } else if !trimmed.is_empty() {
            caption = trimmed
                .strip_prefix("**")
                .and_then(|c| c.strip_suffix("**"))
                .filter(|c| !c.is_empty());
        }
        i += 1;
    }
    out
}

/// A line of a ```` ```text ```` block as a line of a result.
fn quoted(line: &str) -> String {
    if line.is_empty() {
        ">".into()
    } else {
        format!("> {line}")
    }
}

/// The `comment` line of a fence line that has code and a trailing `//` comment, with the
/// spaces between them reduced to one.
fn comment(line: &str) -> Option<String> {
    let code_start = line.trim_start();
    if code_start.is_empty() || code_start.starts_with("//") {
        return None;
    }
    let mut in_string = false;
    let bytes = line.as_bytes();
    for (k, &b) in bytes.iter().enumerate() {
        match b {
            b'"' => in_string = !in_string,
            b'/' if !in_string && bytes.get(k + 1) == Some(&b'/') => {
                let code = line[..k].trim();
                let text = line[k + 2..].trim();
                return Some(format!("comment {code} // {text}"));
            }
            _ => {}
        }
    }
    None
}

/// The rows of the HTML table `html`, each as `| cell | cell |`, with each cell that spans
/// several rows repeated in each of them.
fn rows(html: &str) -> Vec<String> {
    // The cells still spanning down: the column, the text, and the rows left to cover.
    let mut spans: Vec<(usize, String, usize)> = Vec::new();
    let mut out = Vec::new();
    for row in html.split("<tr").skip(1) {
        let row = row.split("</tr>").next().unwrap_or_default();
        let mut given = cells(row).into_iter();
        let mut cells_out: Vec<String> = Vec::new();
        let mut next_spans = Vec::new();
        loop {
            let col = cells_out.len();
            if let Some(k) = spans.iter().position(|(c, _, _)| *c == col) {
                let (c, text, left) = spans.swap_remove(k);
                if left > 1 {
                    next_spans.push((c, text.clone(), left - 1));
                }
                cells_out.push(text);
                continue;
            }
            let Some((text, span)) = given.next() else {
                break;
            };
            if span > 1 {
                next_spans.push((col, text.clone(), span - 1));
            }
            cells_out.push(text);
        }
        // A span reaching past the row's last cell is kept for the rows below.
        next_spans.append(&mut spans);
        spans = next_spans;
        out.push(format!("| {} |", cells_out.join(" | ")));
    }
    out
}

/// The cells of the inside of one `<tr>`: each one's text and the rows it spans.
fn cells(row: &str) -> Vec<(String, usize)> {
    let mut out = Vec::new();
    let mut rest = row;
    while let Some(open) = rest.find("<t") {
        let after = &rest[open..];
        let Some(tag_end) = after.find('>') else {
            break;
        };
        let tag = &after[..tag_end];
        if !(tag.starts_with("<td") || tag.starts_with("<th")) {
            rest = &after[tag_end + 1..];
            continue;
        }
        let span = tag
            .split_once("rowspan=\"")
            .and_then(|(_, r)| r.split('"').next()?.parse().ok())
            .unwrap_or(1);
        let body = &after[tag_end + 1..];
        let close = body
            .find("</td>")
            .into_iter()
            .chain(body.find("</th>"))
            .min()
            .unwrap_or(body.len());
        out.push((text_of(&body[..close]), span));
        rest = &body[close..];
    }
    out
}

/// The text of an HTML fragment: its tags removed, its entities decoded, its runs of white space
/// reduced to one space. A `<` starts a tag only before a letter or `/`, since the page writes
/// Zed's `><` in a cell as it is.
fn text_of(html: &str) -> String {
    let mut plain = String::with_capacity(html.len());
    let mut in_tag = false;
    let mut chars = html.chars().peekable();
    while let Some(c) = chars.next() {
        let opens = chars
            .peek()
            .is_some_and(|n| n.is_ascii_alphabetic() || *n == '/');
        match c {
            '<' if !in_tag && opens => in_tag = true,
            '>' if in_tag => in_tag = false,
            _ if !in_tag => plain.push(c),
            _ => {}
        }
    }
    let decoded = plain
        .replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", "\"")
        .replace("&#39;", "'")
        .replace("&amp;", "&");
    decoded.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The lines of the entries of `keys`, each with the results `stated` gives it and no checks:
/// what a new table of expected results starts from, and what a failure shows.
pub fn render(keys: &[String], stated: &[Vec<Vec<String>>]) -> String {
    let mut out = String::new();
    for (key, results) in keys.iter().zip(stated) {
        out.push_str(&format!("== {key}\n"));
        for r in results {
            for l in r {
                out.push_str(l);
                out.push('\n');
            }
        }
        out.push('\n');
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{entries, rows, stated};

    #[test]
    fn a_rowspan_cell_repeats_in_the_rows_it_covers() {
        let html = "<table>\n<tr><th>a</th><th>b</th><th>v</th></tr>\n\
                    <tr><td rowspan=\"2\"><code>x</code></td><td>0</td><td>1</td></tr>\n\
                    <tr><td>1</td><td>2 &lt; 3</td></tr>\n</table>";
        assert_eq!(
            rows(html),
            ["| a | b | v |", "| x | 0 | 1 |", "| x | 1 | 2 < 3 |"]
        );
        let merge = "<tr><td><code>(k >< (+) -> r)</code></td></tr>";
        assert_eq!(rows(merge), ["| (k >< (+) -> r) |"]);
    }

    #[test]
    fn results_are_comments_text_blocks_and_captioned_tables() {
        let page = "# A\n```zed\na = 1;   // 1\n// b = 2;  // ✗ rejected\n```\n\n```text\na = 1\n\nz\n```\n\
                    **`a`**\n\n<table>\n<tr><td>1</td></tr>\n</table>\n\n<table>\n<tr><td>no caption</td></tr>\n</table>\n\
                    # B\n```text\nnot after a fence\n```\n```zed\nc = \"//\";\n```\n";
        let want = vec![
            vec![
                vec!["comment a = 1; // 1".to_string()],
                vec!["text".into(), "> a = 1".into(), ">".into(), "> z".into()],
                vec!["table `a`".into(), "| 1 |".into()],
            ],
            vec![],
        ];
        assert_eq!(stated(page), want);
    }

    #[test]
    fn an_entry_reads_its_inputs_results_and_checks() {
        let text = "== K 1\nruns from L7: needs m\ninput m = 1;\ntable `a`\n| 1 |\ncheck a == 1\n\
                    comment x; // y\nno check: explains\n";
        let e = entries(text).expect("well formed");
        assert_eq!(e.len(), 1);
        assert_eq!(e[0].runs_from, Some(7));
        assert_eq!(e[0].inputs, ["m = 1;"]);
        assert_eq!(e[0].results[0].lines, ["table `a`", "| 1 |"]);
        assert_eq!(e[0].results[0].checks, ["a == 1"]);
        assert_eq!(e[0].results[1].no_check.as_deref(), Some("explains"));
    }

    #[test]
    fn each_malformed_entry_has_its_own_message() {
        for (text, want) in [
            ("check a\n", "before the first `== KEY`"),
            ("== K\ncheck a\n", "comes before any result"),
            ("== K\nruns from L7\n", "has no `: REASON`"),
            ("== K\nruns from Lx: r\n", "names no layer"),
            (
                "== K\ntext\ninput a = 1;\n",
                "an `input` line after a result",
            ),
            ("== K\ntext\ncheck a\n> b\n", "after its checks"),
            ("== K\ntext\nwhat\n", "none of the forms"),
        ] {
            let e = entries(text).expect_err(text);
            assert!(e.contains(want), "{text:?}: {e}");
        }
    }
}

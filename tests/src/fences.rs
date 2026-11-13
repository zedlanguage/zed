//! The documentation's fences, each with its layer: those of DESIGN.md and EXAMPLES.md, read
//! from the spec in place (`crate::spec`), and those of this repository's README.md, laid out
//! against the spec's grammar (`zed_tools::fence_layers`); and the variants of their commented ✗
//! lines, built from the spec's fences at test time by the table `zed/fences/variants.txt`. No
//! copy of the spec is kept in this repository.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use zed_tools::fence_layers::{self, LaidFence};
use zed_tools::spec::Spec;
use zedc::fence;

/// A fence of DESIGN.md, EXAMPLES.md or README.md, with its layer.
#[derive(Clone, Debug)]
pub struct DocFence {
    /// Its document, section and place among the fences of that section: `DESIGN.md
    /// [sec:remap_law] 1`. Expected outputs are keyed by it, so that an edit in one section of
    /// the document changes no other section's keys.
    pub key: String,
    /// The document and line of its ```` ```zed ````, for messages: `DESIGN.md:196`.
    pub at: String,
    /// The layer from which it is parsed, checked and run.
    pub layer: u32,
    /// The lowest ring of sec:grammar at which it parses.
    pub ring: u32,
    /// Whether it parses only under the documentation notation of sec:grammar.
    pub notation: bool,
    /// Its text.
    pub text: String,
}

impl From<LaidFence> for DocFence {
    fn from(l: LaidFence) -> DocFence {
        let f = l.fence;
        DocFence {
            key: format!("{} [{}] {}", f.file, f.section, f.index),
            at: format!("{}:{}", f.file, f.line),
            layer: l.layer,
            ring: l.ring,
            notation: l.notation,
            text: f.text,
        }
    }
}

/// A rejected variant: a fence with one commented ✗ line made live.
#[derive(Clone, Debug)]
pub struct Variant {
    /// Its name in the table.
    pub name: String,
    /// The commented line of the fence it is a variant of, trimmed.
    pub of: String,
    /// Its text, built from its fence: the line `// variant: ` and its commented line, then the
    /// fence with that line made live.
    pub text: String,
}

/// The directory `zed/fences/`, which holds the table of the variants and the predictions.
pub fn dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../zed/fences")
}

/// The fences of the document at `path`, laid out against `spec`, in order.
pub fn of_document(path: &Path, spec: &Spec) -> Vec<DocFence> {
    let path = path.to_str().expect("a UTF-8 path");
    fence_layers::of_document(path, spec)
        .unwrap_or_else(|e| panic!("{e}"))
        .into_iter()
        .map(DocFence::from)
        .collect()
}

/// The spec's grammars and its directory, read once per test binary. Panics where the spec is
/// not found, or where `ZED_SPEC_DIR=none` says not to read it.
pub fn spec() -> &'static Spec {
    static SPEC: OnceLock<Spec> = OnceLock::new();
    SPEC.get_or_init(|| {
        let root = crate::spec::dir("the documentation's fences").unwrap_or_else(|| {
            panic!(
                "the fences of DESIGN.md and EXAMPLES.md and the grammar are read from the spec \
                 repository, and {}={} says not to read it",
                crate::spec::VAR,
                crate::spec::NONE
            )
        });
        Spec::open(root.to_str().expect("a UTF-8 path")).unwrap_or_else(|e| panic!("{e}"))
    })
}

/// The fences of `doc` under the directory `under`, laid out once per test binary in `cell`.
/// Laying out a fence parses it at up to every ring, which over a whole document takes about a
/// second, so each document is laid out once.
fn laid(cell: &'static OnceLock<Vec<DocFence>>, under: &str, doc: &str) -> Vec<DocFence> {
    cell.get_or_init(|| of_document(&Path::new(under).join(doc), spec()))
        .clone()
}

/// The fences of DESIGN.md, in order.
pub fn design() -> Vec<DocFence> {
    static CELL: OnceLock<Vec<DocFence>> = OnceLock::new();
    laid(&CELL, &spec().root, "DESIGN.md")
}

/// The fences of EXAMPLES.md, in order.
pub fn examples() -> Vec<DocFence> {
    static CELL: OnceLock<Vec<DocFence>> = OnceLock::new();
    laid(&CELL, &spec().root, "EXAMPLES.md")
}

/// Every fence: DESIGN.md's, then EXAMPLES.md's.
pub fn all() -> Vec<DocFence> {
    let mut out = design();
    out.extend(examples());
    out
}

/// The passage of DESIGN.md that starts at the one line whose text, without its indentation,
/// starts with `first`: that line and the lines after it up to a blank line, a line that ends
/// a fence, or a line indented less, each without the first line's indentation and each
/// ending in `\n`. A test compares the output of the compiler with the passage that documents
/// it, read from the spec at test time, so that this repository keeps no copy of the passage
/// (item SPEC-no-verbatim). Panics, naming `first`, where no line or more than one starts with
/// it.
///
/// Complexity tradeoff: one scan of DESIGN.md's lines, O(D) for D bytes, on each call; a test
/// reads a few passages, so an index of the lines by their start, O(D) to build once, would
/// save nothing.
pub fn passage(first: &str) -> String {
    let path = &spec().design;
    let design = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let lines: Vec<&str> = design.lines().collect();
    let starts: Vec<usize> = (0..lines.len())
        .filter(|&i| lines[i].trim_start().starts_with(first))
        .collect();
    let [start] = starts[..] else {
        panic!(
            "DESIGN.md has {} lines that start with `{first}`, and the test reads the passage \
             that starts at exactly one",
            starts.len()
        );
    };
    let indent = lines[start].len() - lines[start].trim_start().len();
    let mut out = String::new();
    for line in &lines[start..] {
        let body = line.trim_start();
        if body.is_empty() || body == "```" || line.len() - body.len() < indent {
            break;
        }
        out.push_str(&line[indent..]);
        out.push('\n');
    }
    out
}

/// The fences of this repository's README.md (item README-fences), in order, laid out against
/// the spec's grammar. They are not among [`all`]: the page states its own results, and its
/// tests compare them with the run.
pub fn readme() -> Vec<DocFence> {
    static CELL: OnceLock<Vec<DocFence>> = OnceLock::new();
    laid(
        &CELL,
        concat!(env!("CARGO_MANIFEST_DIR"), "/.."),
        "README.md",
    )
}

/// The table of the variants, `zed/fences/variants.txt`.
pub fn table() -> PathBuf {
    dir().join("variants.txt")
}

/// Every variant, by name, each built from its fence in the spec by [`build`]. Panics with a
/// message for each entry of the table that cannot be built, naming its fence's key.
pub fn variants() -> Vec<Variant> {
    let path = table();
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let mut out = build(&text, &all()).unwrap_or_else(|errors| {
        panic!(
            "the variants of {} cannot be built from the spec:\n{}",
            path.display(),
            errors.join("\n")
        )
    });
    out.sort_by(|a, b| a.name.cmp(&b.name));
    out
}

/// One change an entry of the table makes to its fence. Each names a line of the fence by a
/// piece of text that exactly one line holds (for `live`, exactly one commented ✗ line).
#[derive(Clone, Copy, Debug)]
enum Op<'t> {
    /// `live: TEXT`: the commented ✗ line made live; its `//` is removed.
    Live(&'t str),
    /// `omit: TEXT`: the line left out.
    Omit(&'t str),
    /// `keep: TEXT`: the line kept; where an entry keeps any line, it leaves out every line it
    /// does not keep but the live one.
    Keep(&'t str),
    /// `edit: OLD => NEW`: OLD replaced by NEW in the line that holds OLD.
    Edit(&'t str, &'t str),
    /// `stands: OLD => NEW`: the live line stands for this edit of another line. The line that
    /// holds OLD gets NEW in its place and the live line's `// ✗` comment at its end, and the
    /// commented ✗ line stays commented.
    Stands(&'t str, &'t str),
}

/// An entry of the table: from its `variant:` line, at line `at` of the table, to the next.
struct Entry<'t> {
    name: &'t str,
    at: usize,
    fence: Option<&'t str>,
    ops: Vec<Op<'t>>,
}

/// The variants that the table `table` names, built from `fences`, in the table's order; or a
/// message for each entry that cannot be built.
///
/// The table is a list of entries, one line per word, `#` lines and blank lines ignored:
///
/// ```text
/// variant: two-writers-of-one-generation
/// fence: DESIGN.md [sec:generations] 4
/// live: _ = c*.bump(1);
/// omit: prev = c*.bump(3);
/// edit: until prev => until c.n
/// ```
///
/// Each text after a word is a short piece of the line it names, never the line itself, so the
/// table quotes no passage of the spec; the program is built in memory each time the tests run.
/// The variant's text is `// variant: ` and its commented ✗ line, then the fence's lines with
/// the changes made, so its lines are numbered as the fence's are, one higher.
///
/// Complexity tradeoff: the fences are found by key in a hash map, O(F) to build and O(1) per
/// entry, where scanning the fences for each entry would be O(V·F) for V entries and F fences.
/// Each change is found by one scan of its fence's lines, O(L) for L bytes of the fence, and
/// the variant is written in one more pass, so an entry costs O(L·(1 + C)) for C changes, about
/// the size of the text it writes.
pub fn build(table: &str, fences: &[DocFence]) -> Result<Vec<Variant>, Vec<String>> {
    let mut errors = Vec::new();
    let entries = parse(table, &mut errors);
    let by_key: HashMap<&str, &DocFence> = fences.iter().map(|f| (f.key.as_str(), f)).collect();
    let mut names = HashSet::new();
    let mut out = Vec::new();
    for e in &entries {
        let at = format!("variants.txt:{}: the variant `{}`", e.at, e.name);
        if !names.insert(e.name) {
            errors.push(format!("{at} is named twice"));
            continue;
        }
        let Some(key) = e.fence else {
            errors.push(format!("{at} has no `fence:` line"));
            continue;
        };
        let Some(fence) = by_key.get(key) else {
            errors.push(format!(
                "{at} is built from the fence `{key}`, and the spec has no fence with that key; \
                 find the fence that now holds its ✗ line and write that fence's key"
            ));
            continue;
        };
        match build_one(e, fence) {
            Ok(v) => out.push(v),
            Err(m) => errors.push(format!("{at}, of the fence `{key}` at {}: {m}", fence.at)),
        }
    }
    if errors.is_empty() {
        Ok(out)
    } else {
        Err(errors)
    }
}

/// The entries of `table`, with a message in `errors` for each line that is not one.
fn parse<'t>(table: &'t str, errors: &mut Vec<String>) -> Vec<Entry<'t>> {
    let mut entries: Vec<Entry> = Vec::new();
    for (k, raw) in table.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let at = k + 1;
        let Some((word, rest)) = line.split_once(':').map(|(w, r)| (w, r.trim())) else {
            errors.push(format!("variants.txt:{at}: `{line}` has no `word:`"));
            continue;
        };
        if word == "variant" {
            entries.push(Entry {
                name: rest,
                at,
                fence: None,
                ops: Vec::new(),
            });
            continue;
        }
        let Some(e) = entries.last_mut() else {
            errors.push(format!(
                "variants.txt:{at}: `{word}:` comes before any `variant:` line"
            ));
            continue;
        };
        let pair = || rest.split_once(" => ").map(|(a, b)| (a.trim(), b.trim()));
        let op = match (word, pair()) {
            ("fence", _) if e.fence.is_none() => {
                e.fence = Some(rest);
                continue;
            }
            ("fence", _) => {
                errors.push(format!("variants.txt:{at}: a second `fence:` line"));
                continue;
            }
            ("live", _) => Op::Live(rest),
            ("omit", _) => Op::Omit(rest),
            ("keep", _) => Op::Keep(rest),
            ("edit", Some((old, new))) => Op::Edit(old, new),
            ("stands", Some((old, new))) => Op::Stands(old, new),
            ("edit" | "stands", None) => {
                errors.push(format!("variants.txt:{at}: `{word}:` needs `OLD => NEW`"));
                continue;
            }
            _ => {
                errors.push(format!(
                    "variants.txt:{at}: `{word}:` is not a word of the table; the words are \
                     variant, fence, live, omit, keep, edit and stands"
                ));
                continue;
            }
        };
        if rest.is_empty() {
            errors.push(format!("variants.txt:{at}: `{word}:` names no text"));
            continue;
        }
        e.ops.push(op);
    }
    entries
}

/// The one line, of the fence lines `lines` at the places `among` (from 0), that holds `text`.
fn the_line(lines: &[&str], among: &[usize], what: &str, text: &str) -> Result<usize, String> {
    let hits: Vec<usize> = among
        .iter()
        .copied()
        .filter(|&i| lines[i].contains(text))
        .collect();
    match hits[..] {
        [i] => Ok(i),
        [] => Err(format!("no {what} of the fence holds `{text}`")),
        _ => Err(format!(
            "{} {what}s of the fence hold `{text}`, its lines {}; write a longer piece of one",
            hits.len(),
            hits.iter()
                .map(|i| (i + 1).to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}

/// The variant entry `e` names, built from `fence`, or what stops it.
fn build_one(e: &Entry, fence: &DocFence) -> Result<Variant, String> {
    let lines: Vec<&str> = fence.text.split('\n').collect();
    let every: Vec<usize> = (0..lines.len()).collect();
    let commented: Vec<usize> = fence::marks(&fence.text)
        .variants
        .iter()
        .map(|k| k - 1)
        .collect();
    let mut live = None;
    let mut omitted = vec![false; lines.len()];
    let mut kept: Option<Vec<bool>> = None;
    let mut edits: Vec<(usize, &str, &str)> = Vec::new();
    let mut stands = None;
    for &op in &e.ops {
        match op {
            Op::Live(t) if live.is_none() => {
                live = Some(the_line(&lines, &commented, "commented ✗ line", t)?);
            }
            Op::Live(_) => return Err("it has two `live:` lines".into()),
            Op::Omit(t) => omitted[the_line(&lines, &every, "line", t)?] = true,
            Op::Keep(t) => {
                let i = the_line(&lines, &every, "line", t)?;
                kept.get_or_insert_with(|| vec![false; lines.len()])[i] = true;
            }
            Op::Edit(old, new) => edits.push((the_line(&lines, &every, "line", old)?, old, new)),
            Op::Stands(old, new) if stands.is_none() => {
                stands = Some((the_line(&lines, &every, "line", old)?, old, new));
            }
            Op::Stands(..) => return Err("it has two `stands:` lines".into()),
        }
    }
    let live = live.ok_or("it has no `live:` line")?;
    let gone = |i: usize| omitted[i] || kept.as_ref().is_some_and(|k| !k[i] && i != live);
    let changed = edits
        .iter()
        .map(|&(i, ..)| i)
        .chain(stands.map(|(i, ..)| i));
    if let Some(i) = std::iter::once(live).chain(changed).find(|&i| gone(i)) {
        return Err(format!("its line {} is both left out and changed", i + 1));
    }
    if stands.is_some_and(|(i, ..)| i == live) {
        return Err("its `stands:` line is its live line".into());
    }
    edits.sort_by_key(|&(i, ..)| i);
    let of = lines[live].trim();
    // Reserved once: the variant is about the fence's size, and growing by doubling would
    // allocate about twice that in all.
    let mut text = String::with_capacity(fence.text.len() + 2 * of.len() + 16);
    text.push_str("// variant: ");
    text.push_str(of);
    text.push('\n');
    let mut next = edits.iter().peekable();
    for (i, &line) in lines.iter().enumerate() {
        let mut l = if i == live && stands.is_none() {
            uncomment(line)
        } else {
            line.to_string()
        };
        while let Some(&(_, old, new)) = next.next_if(|&&(j, ..)| j == i) {
            l = l.replacen(old, new, 1);
        }
        if gone(i) {
            continue;
        }
        if let Some((_, old, new)) = stands.filter(|&(j, ..)| j == i) {
            l = format!("{}   {}", l.replacen(old, new, 1), mark(lines[live]));
        }
        text.push_str(&l);
        text.push('\n');
    }
    Ok(Variant {
        name: e.name.into(),
        of: of.into(),
        text,
    })
}

/// The commented line `line` made live: its first `//` and the space after it removed, its
/// indentation kept, so its code stands at the column the fence writes it at.
fn uncomment(line: &str) -> String {
    let body = line.trim_start();
    let indent = &line[..line.len() - body.len()];
    let rest = body.strip_prefix("//").unwrap_or(body);
    format!("{indent}{}", rest.strip_prefix(' ').unwrap_or(rest))
}

/// The `// ✗ …` comment that ends the commented ✗ line `line`.
fn mark(line: &str) -> &str {
    let x = line.find('✗').expect("a ✗ line");
    line[..x].rfind("//").map_or(&line[x..], |s| &line[s..])
}

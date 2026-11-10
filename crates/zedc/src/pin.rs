//! Pins (step L2.8, DESIGN.md sec:units): the content address a build writes beside the source
//! and checks on every later build, so that the same source builds the same program on any
//! machine.
//!
//! An import is pinned in its own statement, `import geometry.shapes @hash("…");`: the build
//! writes the address of the unit it names when the statement has none, and checks the one it
//! has, never resolving the import again. Every other pin is a line of the pin file
//! [`PIN_FILE`] at the package root, which the toolchain alone writes: `<kind> <address> <key>`,
//! the kind first, then the address as 64 hex digits, then the key, the rest of the line, so
//! that a key may hold spaces. The kind `prelude` pins the package's prelude unit, its key the
//! unit's path, so the prelude is pinned as an ordinary unit is. The same file holds the pins
//! later steps add under kinds of their own (a package's bytes, step L2.8c; proof pins, step
//! L15.7; measured plan pins, step L24.7; files read at the compile-time stage, step L21.1a): a
//! pin of a kind this build does not know is kept as it is written.
//!
//! A unit's address is that of its exported declarations ([`canon::unit_address`], step M0.11),
//! each addressed by the canonicalizer from its elaborated value ([`address`]). It is a function
//! of the unit's text, so the database keeps it under the text
//! ([`Query::Address`](crate::query::Query::Address)).
//!
//! Where DESIGN.md does not say: every build tier writes and checks pins alike, since a pin is a
//! fact of the source and not of a tier; a unit that does not compile alone (until step L2.4
//! links units, one that imports another or reads the package's prelude unit) has no address
//! yet, so an import of it is neither pinned nor checked; and a pin that does not match is a
//! rejection whose repairs are to remove the pin, which the next build writes again, or to
//! restore the unit.

use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::sync::Arc;

use zed_kernel::num::TooLarge;

use crate::address::ContentAddress;
use crate::ast::{Error, Note};
use crate::canon;
use crate::elab::Unit;
use crate::lex::{self, Span, Tok};
use crate::resolve::Exports;
use crate::source;

/// The pin file, under the package root.
pub const PIN_FILE: &str = "zed.pins";

/// The kind of the prelude unit's pin in the pin file.
pub const PRELUDE: &str = "prelude";

/// The first line of the pin file the toolchain writes.
const HEADER: &str = "// Pins written by zedc: each line is `<kind> <address> <key>`, and each \
                      build checks it. Delete a line, and the next build writes it again.\n";

/// How a pin stands against the address its unit has now.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Check {
    /// Nothing is pinned: the build writes the address.
    Unpinned,
    /// The pin is the address.
    Fresh,
    /// The pin is this other address: the build stops.
    Stale(ContentAddress),
}

/// How the pin `pinned` stands against the address `now`.
pub fn check(pinned: Option<ContentAddress>, now: ContentAddress) -> Check {
    match pinned {
        None => Check::Unpinned,
        Some(p) if p == now => Check::Fresh,
        Some(p) => Check::Stale(p),
    }
}

/// The address of a unit and of each of its exports.
#[derive(Debug)]
pub struct Addressed {
    /// The unit's address.
    pub unit: ContentAddress,
    /// The elaborated unit the exports are definitions of.
    defs: Arc<Unit>,
    /// Each exported definition, by its index in `defs`, with its address, in the unit's
    /// order: what the re-pin report compares (step L2.8a).
    exports: Vec<(usize, ContentAddress)>,
}

impl Addressed {
    /// Each exported definition's name and address, in the unit's order; an overloaded name
    /// once for each of its arrows.
    pub fn exports(&self) -> impl Iterator<Item = (&str, ContentAddress)> {
        self.exports
            .iter()
            .map(|&(i, a)| (self.defs.defs[i].name.as_str(), a))
    }
}

/// A unit's address, or why it has none: `None` when the unit does not compile alone, and
/// [`TooLarge`] when the system refused the memory to write out one of its constants.
pub type Address = Option<Result<Addressed, TooLarge>>;

/// The address of the elaborated unit `unit`, whose top level defines `exports`: each
/// definition, in dependency order, addressed with each name it uses of an earlier definition
/// read as that definition's address, and the unit addressed by those it exports. O(t log t)
/// for definitions of size t in all, the canonicalizer's cost, and O(e log e) for e exports.
pub fn address(unit: &Arc<Unit>, exports: &Exports) -> Result<Addressed, TooLarge> {
    let mut known: HashMap<&str, ContentAddress> = HashMap::with_capacity(unit.defs.len());
    let mut out = Vec::new();
    for (i, d) in unit.defs.iter().enumerate() {
        let a = canon::address_of_body(&d.name, &d.term, &|x| known.get(x).copied())?;
        known.insert(&d.kernel, a);
        if exports.get(&d.name).is_some_and(|e| !e.local) {
            out.push((i, a));
        }
    }
    let named: Vec<(&str, ContentAddress)> = out
        .iter()
        .map(|&(i, a)| (unit.defs[i].name.as_str(), a))
        .collect();
    Ok(Addressed {
        unit: canon::unit_address(&named),
        defs: unit.clone(),
        exports: out,
    })
}

/// Text to insert into a file's text, at a byte offset of the text as loaded (its line
/// endings normalized, [`source::load`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edit {
    /// Where.
    pub at: usize,
    /// What.
    pub text: String,
}

/// The pin `@hash("…")` of `address`, as the formatter writes it, with the space before it.
fn hash_text(address: ContentAddress) -> String {
    format!(" @hash(\"{address}\")")
}

/// The tokens of the import statement `stmt`, its `;` included, and the index of its last
/// token before the `;`. `None` when it does not lex to a statement ending in `;`, which a
/// parsed import always does.
fn import_tokens(stmt: &str) -> Option<(Vec<lex::Token>, usize)> {
    let tokens = lex::lex(stmt).ok()?;
    match &tokens[..] {
        [.., _, last] if matches!(last.tok, Tok::Op(";")) => {
            let before = tokens.len() - 2;
            Some((tokens, before))
        }
        _ => None,
    }
}

/// The edit that pins the import statement at `span` of `text` to `address`: the pin written
/// after the statement's last token before its `;`, so a comment there stays after it. O(s) for
/// a statement of s bytes.
pub fn pin_import(text: &str, span: Span, address: ContentAddress) -> Option<Edit> {
    let (tokens, last) = import_tokens(&text[span.start..span.end])?;
    Some(Edit {
        at: span.start + tokens[last].span.end,
        text: hash_text(address),
    })
}

/// The import statement at `span` of `text` with its pin removed: the repair that takes the
/// unit's new address, which the build then writes. O(s) for a statement of s bytes.
pub fn unpinned(text: &str, span: Span) -> Option<String> {
    let stmt = &text[span.start..span.end];
    let (tokens, last) = import_tokens(stmt)?;
    let at = tokens
        .iter()
        .position(|t| matches!(&t.tok, Tok::Annot(a) if a == "hash"))?;
    let from = at.checked_sub(1).map_or(0, |b| tokens[b].span.end);
    Some(format!(
        "{}{}",
        &stmt[..from],
        &stmt[tokens[last].span.end..]
    ))
}

/// `edits` in order of their offsets, those at one offset in the order given, and the bytes
/// they insert. O(k log k) for k edits.
fn sorted<'a>(edits: impl IntoIterator<Item = &'a Edit>) -> (Vec<&'a Edit>, usize) {
    let mut order: Vec<&Edit> = edits.into_iter().collect();
    order.sort_by_key(|e| e.at);
    let added = order.iter().map(|e| e.text.len()).sum();
    (order, added)
}

/// `text` with `edits` made, each at its offset, those at one offset in the order given.
/// O(t + k log k) for t bytes and k edits.
pub fn apply<'a>(text: &str, edits: impl IntoIterator<Item = &'a Edit>) -> String {
    let (order, added) = sorted(edits);
    let mut out = String::with_capacity(text.len() + added);
    let mut from = 0;
    for e in order {
        out.push_str(&text[from..e.at]);
        out.push_str(&e.text);
        from = e.at;
    }
    out.push_str(&text[from..]);
    out
}

/// The offsets in the file's bytes `raw` of the offsets `at`, ascending, of its text as loaded:
/// [`source::load`] reads `\r\n`, and a lone `\r`, as `\n`. O(r + k) for r bytes and k offsets.
fn raw_offsets(raw: &[u8], at: &[usize]) -> Vec<usize> {
    let mut out = Vec::with_capacity(at.len());
    let (mut i, mut j) = (0, 0);
    for &a in at {
        while j < a {
            i += if raw[i] == b'\r' && raw.get(i + 1) == Some(&b'\n') {
                2
            } else {
                1
            };
            j += 1;
        }
        out.push(i);
    }
    out
}

/// The bytes of the file `path`, `None` when there is none, or why it cannot be read, or that
/// it changed: unless its text as loaded is `read`, or it is missing and `read` is `None`.
fn unchanged(path: &Path, read: Option<&str>) -> Result<Option<Vec<u8>>, String> {
    let raw = match std::fs::read(path) {
        Ok(raw) => Some(raw),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
        Err(e) => return Err(source::io_reason(&e)),
    };
    let now = raw.as_deref().map(|r| source::load(r).ok());
    match (now, read) {
        (None, None) => Ok(raw),
        (Some(Some(now)), Some(read)) if now == read => Ok(raw),
        _ => Err("the file changed while zedc was reading it; build again".into()),
    }
}

/// Writes `edits` into the file `path`, which was read as `read`: the file's own bytes are
/// read again and kept as they are around each edit, line endings included, and the result
/// replaces the file at once ([`replace`]). Why it could not, as a clause, when the file cannot
/// be read or written, or changed after it was read. O(r + k log k) for r bytes and k edits.
pub fn write_edits<'a>(
    path: &Path,
    read: &str,
    edits: impl IntoIterator<Item = &'a Edit>,
) -> Result<(), String> {
    let raw = unchanged(path, Some(read))?.unwrap_or_default();
    let (order, added) = sorted(edits);
    let at: Vec<usize> = order.iter().map(|e| e.at).collect();
    let mut out = Vec::with_capacity(raw.len() + added);
    let mut from = 0;
    for (e, r) in order.iter().zip(raw_offsets(&raw, &at)) {
        out.extend_from_slice(&raw[from..r]);
        out.extend_from_slice(e.text.as_bytes());
        from = r;
    }
    out.extend_from_slice(&raw[from..]);
    replace(path, &out).map_err(|e| source::io_reason(&e))
}

/// Writes `text` as the file `path`, which was read as `read`, or was missing when `read` is
/// `None`. Why it could not, as a clause, as [`write_edits`] gives it. O(r + t) for a file of r
/// bytes and a text of t.
pub fn write_file(path: &Path, read: Option<&str>, text: &str) -> Result<(), String> {
    unchanged(path, read)?;
    replace(path, text.as_bytes()).map_err(|e| source::io_reason(&e))
}

/// Replaces the file `path`, or makes it, with `bytes`: written to a new file beside it, given
/// the old file's permissions, and renamed over it, so that no reader sees it half written. A
/// link is followed, so the file it names is replaced and the link kept.
pub fn replace(path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    let path = match std::fs::canonicalize(path) {
        Ok(p) => p,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => path.to_path_buf(),
        Err(e) => return Err(e),
    };
    let name = path
        .file_name()
        .map_or_else(Default::default, |n| n.to_string_lossy());
    let new = path.with_file_name(format!(".{name}.zedc-new"));
    let written = std::fs::write(&new, bytes)
        .and_then(|()| match std::fs::metadata(&path) {
            Ok(m) => std::fs::set_permissions(&new, m.permissions()),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
            Err(e) => Err(e),
        })
        .and_then(|()| std::fs::rename(&new, &path));
    if written.is_err() {
        // The new file is this function's own; a failure to remove it hides nothing more.
        let _ = std::fs::remove_file(&new);
    }
    written
}

/// The pins of the pin file, by kind and key.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Pins {
    // Complexity tradeoff: an ordered map, O(log p) per lookup where a hash map is O(1), so that
    // the file is written in one order fixed by its pins, with no sort at each write.
    entries: BTreeMap<(String, String), ContentAddress>,
}

impl Pins {
    /// The pins of the pin file `text`, or an error at each line that is not a pin or repeats
    /// one's kind and key. A line that is empty or starts with `//` is no pin. O(t + p log p)
    /// for t bytes and p pins.
    pub fn parse(text: &str) -> Result<Pins, Vec<Error>> {
        let mut pins = Pins::default();
        let mut errors = Vec::new();
        let mut first: HashMap<(&str, &str), Span> = HashMap::new();
        let mut start = 0;
        for line in text.split_inclusive('\n') {
            let span = Span {
                start,
                end: start + line.trim_end_matches('\n').len(),
            };
            start += line.len();
            let line = &text[span.start..span.end];
            if line.is_empty() || line.starts_with("//") {
                continue;
            }
            let Some((kind, address, key)) = pin_line(line) else {
                errors.push(Error {
                    row: None,
                    menu: String::new(),
                    span,
                    message: format!(
                        "this line of the pin file `{PIN_FILE}` is not a pin. A pin is written \
                         as its kind, its content address of 64 lowercase hex digits and its \
                         key, with one space between them, as `{PRELUDE} {} std.prelude`. zedc \
                         writes this file: delete the line, and the next build writes the pin \
                         again.",
                        "0".repeat(64)
                    ),
                    notes: Vec::new(),
                });
                continue;
            };
            if let Some(&at) = first.get(&(kind, key)) {
                errors.push(Error {
                    row: None,
                    menu: String::new(),
                    span,
                    message: format!(
                        "the pin file `{PIN_FILE}` pins the {kind} `{key}` twice, and it holds \
                         one pin for each. Delete both lines, and the next build writes the pin \
                         again."
                    ),
                    notes: vec![Note {
                        span: at,
                        text: format!("the {kind} `{key}` is first pinned here"),
                    }],
                });
                continue;
            }
            first.insert((kind, key), span);
            pins.entries.insert((kind.into(), key.into()), address);
        }
        if errors.is_empty() {
            Ok(pins)
        } else {
            Err(errors)
        }
    }

    /// The pin of the `kind` `key`, if there is one. O(log p).
    pub fn get(&self, kind: &str, key: &str) -> Option<ContentAddress> {
        self.entries.get(&(kind.into(), key.into())).copied()
    }

    /// Pins the `kind` `key` to `address`, if it is not, and drops every other pin of `kind`
    /// when `only` holds: the kind has one pin. Whether the pins changed. O(m log p) for m pins
    /// dropped.
    pub fn set(&mut self, kind: &str, key: &str, address: ContentAddress, only: bool) -> bool {
        let dropped = only && self.drop_kind(kind, Some(key));
        let old = self.entries.insert((kind.into(), key.into()), address);
        dropped || old != Some(address)
    }

    /// Drops every pin of `kind` but that of `keep`. Whether one was dropped. O(m log p) for m
    /// pins dropped.
    pub fn drop_kind(&mut self, kind: &str, keep: Option<&str>) -> bool {
        let gone: Vec<(String, String)> = self
            .entries
            .range((kind.to_string(), String::new())..)
            .take_while(|((k, _), _)| k == kind)
            .filter(|((_, key), _)| Some(key.as_str()) != keep)
            .map(|(k, _)| k.clone())
            .collect();
        for k in &gone {
            self.entries.remove(k);
        }
        !gone.is_empty()
    }

    /// How many pins there are.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether there is no pin.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The pin file of these pins, as the toolchain writes it: its first line says what the file
    /// is, then one line for each pin, in order of kind and then key, so that the same pins
    /// give the same bytes. O(p) for p pins.
    pub fn text(&self) -> String {
        let mut out = String::from(HEADER);
        for ((kind, key), address) in &self.entries {
            out.push_str(&format!("{kind} {address} {key}\n"));
        }
        out
    }
}

/// The kind, address and key of the pin line `line`, if it is one: a kind of lowercase ASCII
/// letters, an address and a key that is not empty, with one space between them.
fn pin_line(line: &str) -> Option<(&str, ContentAddress, &str)> {
    let (kind, rest) = line.split_once(' ')?;
    let (address, key) = rest.split_once(' ')?;
    let kind_ok = !kind.is_empty() && kind.bytes().all(|b| b.is_ascii_lowercase());
    let key_ok = !key.is_empty() && key.trim() == key;
    match (kind_ok, key_ok) {
        (true, true) => Some((kind, ContentAddress::parse(address)?, key)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a(b: u8) -> ContentAddress {
        ContentAddress([b; 32])
    }

    #[test]
    fn pins_round_trip_in_a_fixed_order() {
        let mut p = Pins::default();
        assert!(p.set("proof", "z law", a(2), false));
        assert!(p.set(PRELUDE, "std.prelude", a(1), true));
        assert!(!p.set(PRELUDE, "std.prelude", a(1), true));
        let text = p.text();
        assert!(text.starts_with("//"));
        assert_eq!(Pins::parse(&text), Ok(p.clone()));
        assert_eq!(p.get("proof", "z law"), Some(a(2)));
        // A new prelude path drops the old one's pin.
        assert!(p.set(PRELUDE, "lib.base", a(3), true));
        assert_eq!(p.get(PRELUDE, "std.prelude"), None);
        assert_eq!(p.len(), 2);
    }

    #[test]
    fn a_line_that_is_no_pin_and_a_repeated_pin_are_errors() {
        let good = format!("{PRELUDE} {} std.prelude", a(1));
        let text = format!("{good}\nprelude 12 x\n{good}\n");
        let errors = Pins::parse(&text).unwrap_err();
        assert_eq!(errors.len(), 2);
        assert_eq!(
            &text[errors[0].span.start..errors[0].span.end],
            "prelude 12 x"
        );
        assert!(errors[1].message.contains("twice"));
        assert_eq!(errors[1].notes[0].span.start, 0);
    }

    #[test]
    fn edits_land_at_their_offsets_in_the_files_own_line_endings() {
        let raw = b"a\r\nb\rc\n";
        let read = source::load(raw).unwrap();
        assert_eq!(read, "a\nb\nc\n");
        assert_eq!(
            raw_offsets(raw, &[0, 1, 2, 3, 4, 6]),
            vec![0, 1, 3, 4, 5, 7]
        );
        let e = |at, t: &str| Edit { at, text: t.into() };
        assert_eq!(apply(&read, &[e(3, "!"), e(1, "?")]), "a?\nb!\nc\n");
    }

    #[test]
    fn an_import_is_pinned_after_its_last_token_and_unpinned_back() {
        let text = "x = 1;\nimport geometry.shapes as g // the shapes\n  ;\n";
        let span = Span {
            start: 7,
            end: text.len() - 1,
        };
        let edit = pin_import(text, span, a(9)).unwrap();
        let pinned = apply(text, &[edit]);
        assert_eq!(
            pinned,
            format!(
                "x = 1;\nimport geometry.shapes as g @hash(\"{}\") // the shapes\n  ;\n",
                a(9)
            )
        );
        let span = Span {
            start: 7,
            end: pinned.len() - 1,
        };
        assert_eq!(
            unpinned(&pinned, span).unwrap(),
            "import geometry.shapes as g // the shapes\n  ;"
        );
    }
}

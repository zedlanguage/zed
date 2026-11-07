//! The catalog of routines the compiler's Rust calls (row PORT-catalog of `docs/plan_dag.md`):
//! every function, method and macro of the standard library or of a dependency that the code of
//! `zedc`, `zed-kernel` and `zed-native` calls, outside their unit tests, each with what stands
//! for it in Zed. Row S reads it, and the standard library (rows STD-seq, STD-text, STD-num)
//! starts from its missing entries.
//!
//! `catalog SPEC_DIR CATALOG.md [--index INDEX.scip] [--write]`
//!
//! The calls come from a SCIP index of this repository, which `rust-analyzer scip` writes with
//! every name resolved, methods and operators included; without `--index` the tool runs it,
//! into `build/ra`, with `cfg(test)` off so unit tests are not counted. A use is an occurrence
//! that neither defines nor imports the name. A routine is a symbol whose last descriptor is a
//! method (`name().`) or a macro (`name!`), in a package that is not a member of this workspace.
//!
//! The catalog's table has one row per routine: its path, its uses, the files that use it, its
//! first use, and the Zed column, which is written by hand and is one of
//!
//! - `missing`: nothing in Zed or in the plan provides it yet;
//! - `row ID`, or several separated by commas: plan rows of `docs/plan_dag.md` that provide it;
//! - one or more Zed texts in backticks, separated by commas, each an expression of the grammar
//!   of `SPEC_DIR/DESIGN.md` whose defined words lie in Zed₀ (layer 24 or below, the bound of
//!   `zed/compiler/ZED0.md`); a name the words table does not list stands for a value.
//!
//! With `--write` the tool rewrites the table from the index, keeping each routine's Zed column
//! and giving a new routine `missing`. Without it the tool checks the catalog: the routines the
//! index finds and the rows of the table must be the same set. Both check every Zed column, and
//! the tool fails on any problem, one line each.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

use zedc::parse::{Node, TOP};

use crate::layer::WordTable;
use crate::plan::row_ids;
use crate::spec::Spec;
use crate::syntax::{Tokens, lex, then_end};
use crate::text::{read_text, repr};
use crate::{Outcome, arg, impl_root, say};

/// The source directories whose calls the catalog lists, as path prefixes: `crates/zedc` covers
/// the compiler `zedc` and each crate `zedc-*` it is split into.
pub const SOURCES: [&str; 3] = [
    "crates/zedc",
    "crates/zed-kernel/src/",
    "crates/zed-native/src/",
];

/// The highest layer of Zed₀ (`zed/compiler/ZED0.md`: the language parts of L19–L24).
pub const ZED0_LAYER: u32 = 24;

/// The header of the catalog's table.
const HEADER: &str = "| Routine | Uses | Files | First use | Zed |";

/// The line that starts the counts the tool writes above the table.
const COUNTS: &str = "Counts: ";

/// A protocol buffer field's value.
enum Field<'a> {
    Varint(u64),
    Bytes(&'a [u8]),
    Fixed,
}

/// The fields of one protocol buffer message, in order.
struct Wire<'a> {
    buf: &'a [u8],
    at: usize,
}

impl<'a> Wire<'a> {
    fn new(buf: &'a [u8]) -> Wire<'a> {
        Wire { buf, at: 0 }
    }

    fn varint(&mut self) -> Result<u64, String> {
        let mut v = 0u64;
        for shift in (0..64).step_by(7) {
            let b = *self
                .buf
                .get(self.at)
                .ok_or("the index ends inside a number")?;
            self.at += 1;
            v |= u64::from(b & 0x7f) << shift;
            if b & 0x80 == 0 {
                return Ok(v);
            }
        }
        Err("a number in the index is longer than ten bytes".into())
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
        let end = self
            .at
            .checked_add(n)
            .filter(|&e| e <= self.buf.len())
            .ok_or("a field of the index runs past its end")?;
        let out = &self.buf[self.at..end];
        self.at = end;
        Ok(out)
    }

    fn field(&mut self) -> Result<(u64, Field<'a>), String> {
        let key = self.varint()?;
        let value = match key & 7 {
            0 => Field::Varint(self.varint()?),
            1 => {
                self.take(8)?;
                Field::Fixed
            }
            2 => {
                let n = usize::try_from(self.varint()?).map_err(|_| "a field length overflows")?;
                Field::Bytes(self.take(n)?)
            }
            5 => {
                self.take(4)?;
                Field::Fixed
            }
            w => return Err(format!("the index has a field of wire type {w}")),
        };
        Ok((key >> 3, value))
    }
}

impl<'a> Iterator for Wire<'a> {
    type Item = Result<(u64, Field<'a>), String>;

    fn next(&mut self) -> Option<Self::Item> {
        (self.at < self.buf.len()).then(|| self.field())
    }
}

/// The SCIP role bits of an occurrence that are not uses.
const DEFINITION: u64 = 1;
const IMPORT: u64 = 2;

/// One occurrence of a SCIP document: its symbol, its line from 0, and its roles.
fn occurrence(bytes: &[u8]) -> Result<(&str, u64, u64), String> {
    let (mut symbol, mut line, mut roles) = ("", None, 0);
    for f in Wire::new(bytes) {
        match f? {
            (1, Field::Bytes(packed)) => {
                if line.is_none() {
                    line = Some(Wire::new(packed).varint()?);
                }
            }
            (1, Field::Varint(v)) => {
                line.get_or_insert(v);
            }
            (2, Field::Bytes(s)) => {
                symbol = std::str::from_utf8(s).map_err(|_| "a symbol is not UTF-8")?;
            }
            (3, Field::Varint(v)) => roles = v,
            _ => {}
        }
    }
    Ok((symbol, line.ok_or("an occurrence with no range")?, roles))
}

/// Reads one descriptor name of a SCIP symbol: a backticked name, with doubled backticks for
/// one, or a run of identifier characters.
fn name(cs: &mut std::iter::Peekable<std::str::Chars<'_>>) -> String {
    let mut out = String::new();
    if cs.peek() == Some(&'`') {
        cs.next();
        while let Some(c) = cs.next() {
            if c == '`' {
                if cs.peek() != Some(&'`') {
                    break;
                }
                cs.next();
            }
            out.push(c);
        }
    } else {
        while let Some(&c) = cs.peek() {
            if !(c.is_alphanumeric() || matches!(c, '_' | '+' | '-' | '$')) {
                break;
            }
            out.push(c);
            cs.next();
        }
    }
    out
}

/// The readable path of the routine a SCIP symbol names, `package::module::Type::name`, or
/// `None` when the symbol is local, of a package in `ours`, or not a function, method or macro.
/// An impl block's self type `T` and trait `Tr` are written `T` or `<T as Tr>`.
pub fn routine(symbol: &str, ours: &HashSet<String>) -> Option<String> {
    let mut parts = symbol.splitn(5, ' ');
    let (scheme, _manager, package, _version, descriptors) = (
        parts.next()?,
        parts.next()?,
        parts.next()?,
        parts.next()?,
        parts.next()?,
    );
    if scheme == "local" || ours.contains(package) {
        return None;
    }
    if !(descriptors.ends_with(").") || descriptors.ends_with('!')) {
        return None;
    }
    let mut segs = vec![package.replace('-', "_")];
    let mut cs = descriptors.chars().peekable();
    let mut impl_of: Option<Vec<String>> = None;
    while cs.peek().is_some() {
        if cs.peek() == Some(&'[') {
            cs.next();
            let n = name(&mut cs);
            (cs.next() == Some(']')).then_some(())?;
            impl_of.get_or_insert_with(Vec::new).push(n);
            continue;
        }
        if let Some(parts) = impl_of.take() {
            segs.push(match &parts[..] {
                [t] => t.clone(),
                [t, tr] => format!("<{t} as {tr}>"),
                _ => return None,
            });
        }
        let n = name(&mut cs);
        match cs.next()? {
            '#' if n == "impl" => impl_of = Some(Vec::new()),
            '/' | '#' | '.' | ':' => segs.push(n),
            '!' => segs.push(format!("{n}!")),
            '(' => {
                for c in cs.by_ref() {
                    if c == ')' {
                        break;
                    }
                }
                (cs.next() == Some('.')).then_some(())?;
                segs.push(n);
            }
            _ => return None,
        }
    }
    (segs.len() > 1).then(|| segs.join("::"))
}

/// The uses of one routine.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Uses {
    /// How many occurrences use it.
    pub count: usize,
    /// The files that use it.
    pub files: BTreeSet<String>,
    /// The first use, by path and then line (from 1).
    pub first: Option<(String, u64)>,
}

/// The routines that the documents of `index` under `sources` use, by path. Each symbol is
/// read once, through a hash map, so the cost is O(occurrences + routines × log routines).
pub fn scan(
    index: &[u8],
    sources: &[&str],
    ours: &HashSet<String>,
) -> Result<BTreeMap<String, Uses>, String> {
    let mut out: BTreeMap<String, Uses> = BTreeMap::new();
    let mut seen: HashMap<&str, Option<String>> = HashMap::new();
    for f in Wire::new(index) {
        let (2, Field::Bytes(doc)) = f? else {
            continue;
        };
        let (mut path, mut occs) = ("", Vec::new());
        for g in Wire::new(doc) {
            match g? {
                (1, Field::Bytes(p)) => {
                    path = std::str::from_utf8(p).map_err(|_| "a document path is not UTF-8")?;
                }
                (2, Field::Bytes(o)) => occs.push(o),
                _ => {}
            }
        }
        if !sources.iter().any(|s| path.starts_with(s)) {
            continue;
        }
        for o in occs {
            let (symbol, line, roles) = occurrence(o)?;
            if roles & (DEFINITION | IMPORT) != 0 {
                continue;
            }
            let Some(r) = seen.entry(symbol).or_insert_with(|| routine(symbol, ours)) else {
                continue;
            };
            // The name is copied once per routine, not once per use.
            if !out.contains_key(r) {
                out.insert(r.clone(), Uses::default());
            }
            let u = out.get_mut(r).expect("inserted above");
            u.count += 1;
            if !u.files.contains(path) {
                u.files.insert(path.into());
            }
            let site = (path, line + 1);
            if u.first.as_ref().is_none_or(|f| site < (f.0.as_str(), f.1)) {
                u.first = Some((path.into(), line + 1));
            }
        }
    }
    Ok(out)
}

/// The package names of the workspace at `root`: the `name` of each member's manifest.
pub fn workspace_packages(root: &str) -> Result<HashSet<String>, String> {
    let manifest = read_text(&format!("{root}/Cargo.toml"))?;
    let list = manifest
        .split_once("members = [")
        .and_then(|(_, rest)| rest.split_once(']'))
        .ok_or("the workspace manifest has no members list")?
        .0;
    let mut out = HashSet::new();
    for member in list.split(',').map(|m| m.trim().trim_matches('"')) {
        if member.is_empty() {
            continue;
        }
        let text = read_text(&format!("{root}/{member}/Cargo.toml"))?;
        let name = text
            .lines()
            .find_map(|l| l.strip_prefix("name = \""))
            .and_then(|l| l.strip_suffix('"'))
            .ok_or_else(|| format!("{member}/Cargo.toml names no package"))?;
        out.insert(name.into());
    }
    Ok(out)
}

/// One row of the catalog's table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row {
    /// The routine's path, as [`routine`] writes it.
    pub routine: String,
    /// The Zed column.
    pub zed: String,
}

/// A table cell's text with `\|` read as `|`.
fn unescape(cell: &str) -> String {
    cell.replace("\\|", "|")
}

/// The cells of a table line, split at the `|` that `\` does not escape.
fn cells(line: &str) -> Vec<&str> {
    let inner = line.trim().trim_start_matches('|');
    let mut out = Vec::new();
    let (mut start, mut prev) = (0, ' ');
    for (i, c) in inner.char_indices() {
        if c == '|' && prev != '\\' {
            out.push(inner[start..i].trim());
            start = i + 1;
        }
        prev = c;
    }
    out
}

/// The catalog's text split around its table: the text before the counts line, the rows, and
/// the text after the table.
pub fn read_catalog(text: &str) -> Result<(String, Vec<Row>, String), String> {
    let at = text
        .find(&format!("\n{HEADER}\n"))
        .ok_or_else(|| format!("the catalog has no table headed {HEADER}"))?;
    let mut before = &text[..at + 1];
    if let Some(c) = before.rfind(&format!("\n{COUNTS}")) {
        before = &before[..c + 1];
    }
    let mut lines = text[at + 1..].split_inclusive('\n');
    lines.next();
    lines.next();
    let mut rows = Vec::new();
    let mut after = String::new();
    for l in lines.by_ref() {
        if !l.starts_with('|') {
            after.push_str(l);
            break;
        }
        let c = cells(l);
        let [routine, _, _, _, zed] = c[..] else {
            return Err(format!(
                "a catalog row without five cells: {}",
                l.trim_end()
            ));
        };
        let routine = unescape(routine.trim_matches('`'));
        rows.push(Row {
            routine,
            zed: zed.into(),
        });
    }
    after.extend(lines);
    Ok((before.to_owned(), rows, after))
}

/// The catalog's text: `before`, the counts, the table of `found` with each routine's Zed column
/// from `zed` (`missing` when it has none), and `after`.
pub fn write_catalog(
    before: &str,
    found: &BTreeMap<String, Uses>,
    zed: &HashMap<&str, &str>,
    after: &str,
) -> String {
    let uses: usize = found.values().map(|u| u.count).sum();
    let mut out = format!(
        "{before}{COUNTS}{} routines, {uses} uses.\n\n{HEADER}\n|---|--:|--:|---|---|\n",
        found.len()
    );
    for (r, u) in found {
        let (path, line) = u.first.as_ref().map_or(("", 0), |(p, l)| (p.as_str(), *l));
        writeln!(
            out,
            "| `{}` | {} | {} | `{path}:{line}` | {} |",
            r.replace('|', "\\|"),
            u.count,
            u.files.len(),
            zed.get(r.as_str()).copied().unwrap_or("missing")
        )
        .expect("writing to a String");
    }
    if !after.is_empty() {
        out.push('\n');
        out.push_str(after.trim_start_matches('\n'));
    }
    out
}

/// The backticked spans of a Zed column and the text outside them, or `None` when a backtick is
/// unclosed.
fn spans(cell: &str) -> Option<(Vec<&str>, String)> {
    let (mut spans, mut outside) = (Vec::new(), String::new());
    let mut rest = cell;
    while let Some(a) = rest.find('`') {
        outside.push_str(&rest[..a]);
        let b = rest[a + 1..].find('`')?;
        spans.push(&rest[a + 1..a + 1 + b]);
        rest = &rest[a + 2 + b..];
    }
    outside.push_str(rest);
    Some((spans, outside))
}

/// The problem with one Zed column, if any: `missing`, plan rows of `rows`, or Zed texts that
/// parse as expressions of `spec`, use no defined word above Zed₀, and call each word with the
/// arguments it takes (`check_words`). `cell` is as the table holds it, so `\|` is read as `|`.
pub fn check_zed(
    cell: &str,
    spec: &Spec,
    words: &WordTable,
    rows: &HashSet<&str>,
) -> Option<String> {
    let cell = &unescape(cell);
    if cell == "missing" {
        return None;
    }
    if let Some(list) = cell.strip_prefix("row ") {
        let bad: Vec<&str> = list
            .split(',')
            .map(|r| r.trim().trim_start_matches("row ").trim())
            .filter(|r| !rows.contains(r))
            .collect();
        return (!bad.is_empty()).then(|| format!("no plan row {}", bad.join(", ")));
    }
    let Some((texts, outside)) = spans(cell) else {
        return Some("an unclosed backtick".into());
    };
    if texts.is_empty() || outside.split(',').any(|s| !s.trim().is_empty()) {
        return Some("neither `missing`, `row ID` nor Zed texts in backticks".into());
    }
    for t in texts {
        let toks = match lex(&spec.lexical, t) {
            Ok(toks) => toks,
            Err(e) => return Some(format!("{} does not lex: {e}", repr(t))),
        };
        let mut p = zedc::parse::Parser::new(&spec.syntactic, TOP, &toks);
        let Some((_, root)) = then_end(&spec.syntactic, &mut p, &toks, "Expr") else {
            return Some(format!("{} is not an expression of the grammar", repr(t)));
        };
        for tok in &toks.0 {
            if let Some(l) = words.layer_of(&tok.text).filter(|&l| l > ZED0_LAYER) {
                return Some(format!(
                    "{} uses `{}` of L{l}, above Zed₀ (L{ZED0_LAYER})",
                    repr(t),
                    tok.text
                ));
            }
        }
        if let Some(problem) = check_words(spec, words, t, &toks, &p.nodes, root) {
            return Some(problem);
        }
    }
    None
}

/// The index of the repository at `root`: the file `index`, or a new one that `rust-analyzer
/// scip` writes into `build/ra`.
fn index_of(root: &str, index: Option<&str>) -> Result<Vec<u8>, String> {
    let path = match index {
        Some(p) => p.to_owned(),
        None => {
            let dir = format!("{root}/build/ra");
            std::fs::create_dir_all(&dir).map_err(|e| format!("{dir}: {e}"))?;
            let config = format!("{dir}/config.json");
            std::fs::write(&config, "{\"cfg\":{\"setTest\":false}}\n")
                .map_err(|e| format!("{config}: {e}"))?;
            let out = format!("{dir}/index.scip");
            let status = std::process::Command::new("rust-analyzer")
                .args(["scip", root, "--config-path", &config, "--output", &out])
                .env("CARGO_TARGET_DIR", &dir)
                .stderr(std::process::Stdio::null())
                .status()
                .map_err(|e| format!("rust-analyzer: {e}"))?;
            if !status.success() {
                return Err(format!("rust-analyzer scip failed: {status}"));
            }
            out
        }
    };
    std::fs::read(&path).map_err(|e| format!("{path}: {e}"))
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let usage = "catalog SPEC_DIR CATALOG.md [--index INDEX.scip] [--write]";
    let spec = Spec::open(arg(args, 0, usage)?)?;
    let path = arg(args, 1, usage)?;
    let (mut index, mut write) = (None, false);
    let mut rest = args[2..].iter();
    while let Some(a) = rest.next() {
        match a.as_str() {
            "--index" => index = Some(rest.next().ok_or_else(|| format!("usage: {usage}"))?),
            "--write" => write = true,
            _ => return Err(format!("usage: {usage}")),
        }
    }
    let root = impl_root();
    let ours = workspace_packages(&root)?;
    let found = scan(
        &index_of(&root, index.map(String::as_str))?,
        &SOURCES,
        &ours,
    )?;
    let (before, rows, after) = read_catalog(&read_text(path)?)?;
    let words = WordTable::read(&spec.design)?;
    let plan = read_text(&format!("{root}/docs/plan_dag.md"))?;
    let plan_rows: HashSet<&str> = row_ids(&plan)?.into_iter().collect();

    let mut bad = 0;
    let mut listed = HashSet::with_capacity(rows.len());
    for r in &rows {
        if !listed.insert(r.routine.as_str()) {
            say!(out, "listed twice: `{}`", r.routine);
            bad += 1;
        }
        if let Some(p) = check_zed(&r.zed, &spec, &words, &plan_rows) {
            say!(out, "`{}`: {p}", r.routine);
            bad += 1;
        }
    }
    if write {
        let zed: HashMap<&str, &str> = rows
            .iter()
            .map(|r| (r.routine.as_str(), r.zed.as_str()))
            .collect();
        let text = write_catalog(&before, &found, &zed, &after);
        std::fs::write(path, text).map_err(|e| format!("{path}: {e}"))?;
        let gone = listed.iter().filter(|r| !found.contains_key(**r)).count();
        say!(
            out,
            "wrote {} routines; {} new, {gone} no longer called",
            found.len(),
            found
                .keys()
                .filter(|r| !listed.contains(r.as_str()))
                .count()
        );
    } else {
        for r in found.keys().filter(|r| !listed.contains(r.as_str())) {
            say!(out, "called, not in the catalog: `{r}`");
            bad += 1;
        }
        for r in rows.iter().filter(|r| !found.contains_key(&r.routine)) {
            say!(out, "in the catalog, not called: `{}`", r.routine);
            bad += 1;
        }
    }
    let missing = rows.iter().filter(|r| r.zed == "missing").count();
    say!(
        out,
        "catalog: {} routines, {missing} missing in Zed, {bad} problems",
        found.len()
    );
    Ok(bad == 0)
}

/// How many positional arguments a word takes, the receiver of `x.f(a)` counted.
#[derive(Clone, Copy, Debug)]
enum Count {
    Exactly(usize),
    AtLeast(usize),
}

impl Count {
    fn admits(self, n: usize) -> bool {
        match self {
            Count::Exactly(k) => n == k,
            Count::AtLeast(k) => n >= k,
        }
    }
}

/// A word a Zed text of the catalog may call, with the arguments DESIGN.md gives it.
struct Sig {
    word: &'static str,
    /// The positional arguments. The receiver of `x.f(a)` fills `f`'s first parameter, and a
    /// member read `x.f` with no parentheses is `f(x)` (DESIGN.md, "Application is indexing").
    positional: Count,
    /// The named arguments it must be given.
    required: &'static [&'static str],
    /// The named arguments it may be given.
    optional: &'static [&'static str],
}

const fn sig(word: &'static str, positional: Count) -> Sig {
    Sig {
        word,
        positional,
        required: &[],
        optional: &[],
    }
}

/// The words a catalog Zed text may call, each a prelude word of `zedc::resolve::WORDS`, with
/// its arguments: the casts and the L1 string and number words take one (L1.14); `min` and
/// `max` two or more (`min(d[i-1][j] + 1, …)`, sec:power); the bit words as step L1.39a
/// gives them and the integer machine operations as step L1.39f does, with `width:` on the
/// words whose result depends on a width; the views of a string one (L1.39c); the family
/// operations their receiver and the operands of the kernel table (sec:kernel): `foldl(init,
/// op)`, `foldr(op, init)`, `.sort(asc f, …)` or `.sort(by: le)`, and one operand for the
/// others.
const SIGS: &[Sig] = &[
    sig("String", Count::Exactly(1)),
    sig("int", Count::Exactly(1)),
    sig("rat", Count::Exactly(1)),
    sig("f64", Count::Exactly(1)),
    sig("abs", Count::Exactly(1)),
    sig("min", Count::AtLeast(2)),
    sig("max", Count::AtLeast(2)),
    sig("len", Count::Exactly(1)),
    sig("lower", Count::Exactly(1)),
    sig("upper", Count::Exactly(1)),
    sig("trim", Count::Exactly(1)),
    sig("sum", Count::Exactly(1)),
    sig("bitAnd", Count::Exactly(2)),
    sig("bitOr", Count::Exactly(2)),
    sig("bitXor", Count::Exactly(2)),
    Sig {
        required: &["width"],
        ..sig("bitNot", Count::Exactly(1))
    },
    sig("shl", Count::Exactly(2)),
    sig("shr", Count::Exactly(2)),
    sig("popCount", Count::Exactly(1)),
    Sig {
        required: &["width"],
        ..sig("leadingZeros", Count::Exactly(1))
    },
    Sig {
        required: &["width"],
        ..sig("trailingZeros", Count::Exactly(1))
    },
    Sig {
        required: &["width"],
        ..sig("rotl", Count::Exactly(2))
    },
    Sig {
        required: &["width"],
        ..sig("rotr", Count::Exactly(2))
    },
    sig("f64Bits", Count::Exactly(1)),
    Sig {
        required: &["width"],
        ..sig("mulHi", Count::Exactly(2))
    },
    Sig {
        required: &["width"],
        ..sig("bitReverse", Count::Exactly(1))
    },
    Sig {
        required: &["width"],
        ..sig("byteSwap", Count::Exactly(1))
    },
    sig("pdep", Count::Exactly(2)),
    sig("pext", Count::Exactly(2)),
    Sig {
        required: &["width"],
        ..sig("funnelShl", Count::Exactly(3))
    },
    Sig {
        required: &["width"],
        ..sig("funnelShr", Count::Exactly(3))
    },
    sig("codePoint", Count::Exactly(1)),
    sig("scalar", Count::Exactly(1)),
    sig("utf8", Count::Exactly(1)),
    sig("fromUtf8", Count::Exactly(1)),
    sig("count", Count::Exactly(1)),
    sig("map", Count::Exactly(2)),
    sig("where", Count::Exactly(2)),
    sig("foldl", Count::Exactly(3)),
    sig("foldr", Count::Exactly(3)),
    sig("reduce", Count::Exactly(2)),
    sig("any", Count::Exactly(2)),
    sig("all", Count::Exactly(2)),
    sig("find", Count::Exactly(2)),
    sig("split", Count::Exactly(2)),
    sig("lines", Count::Exactly(1)),
    sig("group", Count::Exactly(2)),
    sig("flatMap", Count::Exactly(2)),
    Sig {
        optional: &["by"],
        ..sig("sort", Count::AtLeast(1))
    },
    sig("zip", Count::Exactly(2)),
    sig("first", Count::Exactly(1)),
    sig("last", Count::Exactly(1)),
    sig("minBy", Count::Exactly(2)),
    sig("maxBy", Count::Exactly(2)),
    sig("slice", Count::Exactly(2)),
    sig("take", Count::Exactly(2)),
    sig("drop", Count::Exactly(2)),
    sig("takeWhile", Count::Exactly(2)),
    sig("chunkBy", Count::Exactly(2)),
];

/// The names that stand for operands in a Zed text of the catalog.
const OPERANDS: [&str; 14] = [
    "a", "b", "n", "x", "xs", "s", "m", "k", "f", "p", "z", "i", "t", "ys",
];

/// One call in a Zed text: the word, its positional arguments (the receiver counted), the
/// names of its named arguments, and whether any positional argument is a sort key.
struct Call<'t> {
    word: &'t str,
    positional: usize,
    named: Vec<&'t str>,
    keys: bool,
}

/// The arguments of the call suffix `call`: positional, named, and whether a sort key is
/// among them.
fn args<'t>(
    call: usize,
    nodes: &[Node],
    rule_of: &dyn Fn(usize) -> &'t str,
    name_of: &dyn Fn(usize) -> &'t str,
) -> (usize, Vec<&'t str>, bool) {
    let (mut positional, mut named, mut keys) = (0, Vec::new(), false);
    for &a in &nodes[call].kids {
        if rule_of(a) != "Args" {
            continue;
        }
        for &arg in &nodes[a].kids {
            match rule_of(arg) {
                "NamedArg" => named.push(name_of(nodes[arg].kids[0])),
                "SortArg" => {
                    positional += 1;
                    keys = true;
                }
                _ => positional += 1,
            }
        }
    }
    (positional, named, keys)
}

/// The problem with the words of the Zed text `t`, parsed as `nodes` from `toks` with root
/// `root`, if any: every name it reads is an operand, a parameter of a lambda the name lies
/// in, or a word that `words` or the prelude defines, and every word it calls or reads as a member is
/// one of [`SIGS`], given the arguments listed there.
// Complexity tradeoff: linear in the text; one walk binds each lambda parameter on entering
// its lambda and unbinds it on leaving, so a name is checked against the parameters in scope
// by one hash lookup, with no walk up its ancestors, and against the fixed tables `SIGS` and
// `zedc::resolve::WORDS`, whose sizes do not depend on the catalog.
fn check_words(
    spec: &Spec,
    words: &WordTable,
    t: &str,
    toks: &Tokens,
    nodes: &[Node],
    root: usize,
) -> Option<String> {
    let rule_of = |n: usize| spec.syntactic.rules[nodes[n].rule].name.as_str();
    let name_of = |n: usize| toks.0[nodes[n].start].text.as_str();
    let mut parent = vec![usize::MAX; nodes.len()];
    for (n, node) in nodes.iter().enumerate() {
        for &k in &node.kids {
            parent[k] = n;
        }
    }
    let defined = |w: &str| {
        zedc::resolve::prelude_layer(w).is_some()
            || words.layer_of(w).is_some()
            || words.layer_of(&format!(".{w}")).is_some()
    };
    // The name `n` binds a parameter: one written before a lambda's arrow (every child of
    // the lambda but its body, the last), or the name of a parameter or tuple target in a
    // parameter list, not its type or default.
    let binds = |n: usize| {
        let q = parent[n];
        q != usize::MAX
            && match rule_of(q) {
                "Lambda" => nodes[q].kids.last() != Some(&n),
                "Param" | "PositionalParam" => nodes[q].kids.first() == Some(&n),
                "Target" => true,
                _ => false,
            }
    };
    // The node `n` heads the postfix `parent[n]` whose suffix is a call: that call's suffix.
    let called = |n: usize| {
        let q = *parent.get(n)?;
        (q != usize::MAX && rule_of(q) == "Postfix" && nodes[q].kids.first() == Some(&n))
            .then(|| nodes[q].kids.get(1).copied())
            .flatten()
            .filter(|&c| rule_of(c) == "CallSuffix")
    };
    let mut calls = Vec::new();
    // A depth-first walk in text order. `scope` counts the parameters of the lambdas open at
    // the node, `bound` lists them in the order they were bound, and `marks` holds the length
    // of `bound` when each open lambda was entered, so leaving a lambda unbinds its own.
    let mut scope: HashMap<&str, usize> = HashMap::new();
    let (mut bound, mut marks) = (Vec::new(), Vec::new());
    let mut stack = vec![(root, false)];
    while let Some((n, leaving)) = stack.pop() {
        if leaving {
            let mark = marks.pop().unwrap_or(0);
            for w in bound.drain(mark..) {
                if let Some(c) = scope.get_mut(w) {
                    *c -= 1;
                }
            }
            continue;
        }
        if rule_of(n) == "Lambda" {
            marks.push(bound.len());
            stack.push((n, true));
        }
        stack.extend(nodes[n].kids.iter().rev().map(|&k| (k, false)));
        if rule_of(n) != "Name" || parent[n] == usize::MAX {
            continue;
        }
        let (q, w) = (parent[n], name_of(n));
        if binds(n) {
            *scope.entry(w).or_insert(0) += 1;
            bound.push(w);
            continue;
        }
        match rule_of(q) {
            "NamedArg" => {}
            "MemberSuffix" => {
                // `recv.w(…)` or the member read `recv.w`.
                let post = parent[q];
                let (positional, named, keys) = match called(post) {
                    Some(c) => {
                        let (p, named, keys) = args(c, nodes, &rule_of, &name_of);
                        (p + 1, named, keys)
                    }
                    None => (1, Vec::new(), false),
                };
                if !defined(w) {
                    return Some(format!("{} reads `.{w}`, which is no word", repr(t)));
                }
                calls.push(Call {
                    word: w,
                    positional,
                    named,
                    keys,
                });
            }
            _ if OPERANDS.contains(&w) || scope.get(w).is_some_and(|&c| c > 0) => {}
            _ if !defined(w) => {
                return Some(format!(
                    "{} names `{w}`, which is no operand, parameter or word",
                    repr(t)
                ));
            }
            _ => {
                if let Some(c) = called(n) {
                    let (positional, named, keys) = args(c, nodes, &rule_of, &name_of);
                    calls.push(Call {
                        word: w,
                        positional,
                        named,
                        keys,
                    });
                }
            }
        }
    }
    for c in calls {
        let Some(s) = SIGS.iter().find(|s| s.word == c.word) else {
            return Some(format!(
                "{} calls `{}`, whose arguments the check does not know",
                repr(t),
                c.word
            ));
        };
        let missing: Vec<&str> = s
            .required
            .iter()
            .copied()
            .filter(|r| !c.named.contains(r))
            .collect();
        let extra: Vec<&str> = c
            .named
            .iter()
            .copied()
            .filter(|n| !s.required.contains(n) && !s.optional.contains(n))
            .collect();
        // `.sort` takes sort keys or one comparator `by:`, not both and not neither.
        let sort_wrong = c.word == "sort" && (c.keys == c.named.contains(&"by"));
        let keys_wrong = c.keys && c.word != "sort";
        if !s.positional.admits(c.positional)
            || !missing.is_empty()
            || !extra.is_empty()
            || sort_wrong
            || keys_wrong
        {
            let want = match (s.word, s.positional) {
                ("sort", _) => "its receiver and sort keys, or its receiver and `by:`".to_owned(),
                (_, Count::Exactly(k)) => format!("{k} positional"),
                (_, Count::AtLeast(k)) => format!("{k} or more positional"),
            };
            let req: String = s.required.iter().map(|r| format!(" and `{r}:`")).collect();
            let named = if c.named.is_empty() {
                String::new()
            } else {
                format!(" and `{}:`", c.named.join(":`, `"))
            };
            return Some(format!(
                "{} calls `{}` with {} positional{named}; it takes {want}{req}",
                repr(t),
                c.word,
                c.positional
            ));
        }
    }
    None
}

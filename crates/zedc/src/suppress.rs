//! The address of a diagnostic and its suppression (DESIGN.md sec:diagnostics, item
//! DIAG-suppress). Each diagnostic has an address, printed under it as `address: <hex>`, that
//! is the same on every run of the same source; `--suppress <address>` on `zedc run`,
//! `replay`, `build` and `test` leaves the warning at that address unprinted. The program is
//! the same with or without it: suppression changes only what is printed. A rejection cannot
//! be suppressed, and an address that names nothing is reported.

use std::collections::HashMap;

use crate::address::ContentAddress;
use crate::ast::{self, Stmt, StmtKind, Target};
use crate::lex::Span;
use crate::run::Diagnostic;

/// Whether a diagnostic is advisory or rejects the unit.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Severity {
    /// A warning: the unit is accepted.
    Warning,
    /// A rejection: the unit is not accepted.
    Rejection,
}

/// The addresses of `errors`, diagnostics of `severity` of the unit `text` whose top-level
/// statements are `stmts` (empty when the unit was rejected before resolution), in order.
///
/// An address is the BLAKE3-256 hash of the severity, the rejection row, the name of the
/// top-level declaration the diagnostic lies in, the text of the node it is at with its
/// white space dropped, and its message; and of its occurrence among the diagnostics with all
/// of these the same, counted in order, so that no two diagnostics of a unit share an address.
/// Line and column are not part of it, so an edit elsewhere in the unit, a line added above
/// for instance, leaves it as it was. The full 256 bits are kept even under zed-kernel's
/// feature `short-addresses`, which shortens content addresses only.
pub(crate) fn addresses(
    text: &str,
    stmts: &[Stmt],
    severity: Severity,
    errors: &[ast::Error],
) -> Vec<ContentAddress> {
    if errors.is_empty() {
        return Vec::new();
    }
    let content = Content::new(text.as_bytes());
    let mut seen: HashMap<[u8; 32], u64> = HashMap::with_capacity(errors.len());
    errors
        .iter()
        .map(|e| {
            let mut h = blake3::Hasher::new();
            h.update(b"zed diagnostic\0");
            h.update(match severity {
                Severity::Warning => &b"warning\0"[..],
                Severity::Rejection => b"rejection\0",
            });
            h.update(e.row.map_or("", |r| r.name()).as_bytes());
            h.update(b"\0");
            h.update(enclosing(stmts, e.span.start).unwrap_or("").as_bytes());
            h.update(b"\0");
            h.update(&content.hash(e.span).to_le_bytes());
            h.update(e.message.as_bytes());
            h.update(b"\0");
            let n = seen.entry(*h.finalize().as_bytes()).or_insert(0);
            h.update(&n.to_le_bytes());
            *n += 1;
            ContentAddress(*h.finalize().as_bytes())
        })
        .collect()
}

/// The name of the top-level declaration of `stmts`, which are in source order, whose text
/// holds the byte `at`; `None` when no declaration does or the statement declares no name.
fn enclosing(stmts: &[Stmt], at: usize) -> Option<&str> {
    let i = stmts
        .partition_point(|s| s.span.start <= at)
        .checked_sub(1)?;
    let s = &stmts[i];
    (at < s.span.end).then(|| declared(s)).flatten()
}

/// The name the statement `s` declares, if it declares one.
fn declared(s: &Stmt) -> Option<&str> {
    match &s.kind {
        StmtKind::Function(f) => Some(&f.name),
        StmtKind::Method(m) => Some(&m.function.name),
        StmtKind::Struct(d) => Some(&d.name),
        StmtKind::Type(d) => Some(&d.name),
        StmtKind::Bind { targets, .. } => targets.iter().find_map(|t| match t {
            Target::Name(name, _) => Some(name.as_str()),
            _ => None,
        }),
        StmtKind::Mutable(d) | StmtKind::Local(d) | StmtKind::Annotated { decl: d, .. } => {
            declared(d)
        }
        _ => None,
    }
}

/// The modulus of the polynomial hash of a node's text, the prime 2^61 - 1.
const MODULUS: u64 = (1 << 61) - 1;
/// The base of the polynomial hash, below `MODULUS`.
const BASE: u64 = 1_000_003;

/// The polynomial hash of each prefix of a text with its white space dropped, so that the hash
/// of any span is found in O(1).
///
/// Complexity tradeoff: two nodes whose texts differ but hash alike modulo 2^61 - 1 are not
/// told apart by this part of the address, which then rests on the declaration, the message
/// and the occurrence count, so the two still get distinct addresses. Why: hashing each
/// node's text whole costs the sum of the nodes' lengths, O(n · depth) for diagnostics at
/// nested nodes; the prefix hashes cost O(n) once and O(1) per node. Test:
/// `l01_29_diagnostics::suppress::addresses_scale`. A complete solution would hash each
/// node's text with BLAKE3, at that cost.
struct Content {
    /// The hash of the first `i` bytes that are not white space, at `i` for each byte offset.
    prefix: Vec<u64>,
    /// The count of bytes that are not white space before each byte offset.
    count: Vec<usize>,
    /// `BASE` to each power up to the count of bytes that are not white space.
    power: Vec<u64>,
}

impl Content {
    fn new(text: &[u8]) -> Content {
        let mul = |a: u64, b: u64| (u128::from(a) * u128::from(b) % u128::from(MODULUS)) as u64;
        let mut content = Content {
            prefix: Vec::with_capacity(text.len() + 1),
            count: Vec::with_capacity(text.len() + 1),
            power: vec![1],
        };
        let (mut hash, mut count) = (0u64, 0usize);
        for &b in text {
            content.prefix.push(hash);
            content.count.push(count);
            if !b.is_ascii_whitespace() {
                hash = (mul(hash, BASE) + u64::from(b) + 1) % MODULUS;
                count += 1;
                content.power.push(mul(content.power[count - 1], BASE));
            }
        }
        content.prefix.push(hash);
        content.count.push(count);
        content
    }

    /// The hash of the text of `span`, clamped to the text, with its white space dropped.
    fn hash(&self, span: Span) -> u64 {
        let last = self.prefix.len() - 1;
        let (start, end) = (
            span.start.min(last),
            span.end.clamp(span.start.min(last), last),
        );
        let n = self.count[end] - self.count[start];
        let shifted = (u128::from(self.prefix[start]) * u128::from(self.power[n])
            % u128::from(MODULUS)) as u64;
        (self.prefix[end] + MODULUS - shifted) % MODULUS
    }
}

/// The addresses `--suppress` names on a command line, each with whether a diagnostic had it.
#[derive(Default, Debug)]
pub struct Suppress {
    named: Vec<ContentAddress>,
    matched: HashMap<ContentAddress, bool>,
}

impl Suppress {
    /// The words of `words` other than each `--suppress <address>`, and the addresses those
    /// name; or why a word after `--suppress` is not an address, or is missing.
    pub fn take<'a>(words: &[&'a str]) -> Result<(Suppress, Vec<&'a str>), String> {
        let mut suppress = Suppress::default();
        let mut rest = Vec::with_capacity(words.len());
        let mut words = words.iter();
        while let Some(&w) = words.next() {
            if w != "--suppress" {
                rest.push(w);
                continue;
            }
            let hex = words
                .next()
                .ok_or("`--suppress` needs an address, 64 lowercase hex digits")?;
            let a = ContentAddress::parse(hex).ok_or_else(|| {
                format!("`--suppress {hex}`: an address is 64 lowercase hex digits")
            })?;
            if suppress.matched.insert(a, false).is_none() {
                suppress.named.push(a);
            }
        }
        Ok((suppress, rest))
    }

    /// Whether the warning `w` is suppressed; its address is then counted as matched.
    pub fn hides(&mut self, w: &Diagnostic) -> bool {
        self.matched.get_mut(&w.address).is_some_and(|m| {
            *m = true;
            true
        })
    }

    /// A line for each rejection of `rejections`, of the unit read from `file`, whose
    /// address is named: a rejection cannot be suppressed. The address counts as matched.
    pub fn refused(&mut self, file: &str, rejections: &[Diagnostic]) -> Vec<String> {
        let mut out = Vec::new();
        for d in rejections {
            if let Some(m) = self.matched.get_mut(&d.address) {
                *m = true;
                out.push(format!(
                    "{file}:{}:{}: `--suppress {}` names a rejection, which cannot be suppressed",
                    d.line, d.col, d.address
                ));
            }
        }
        out
    }

    /// A line for each address named that no diagnostic had, in the order named.
    pub fn unmatched(&self) -> Vec<String> {
        self.named
            .iter()
            .filter(|a| !self.matched[*a])
            .map(|a| format!("`--suppress {a}`: no diagnostic has this address"))
            .collect()
    }
}

//! The address of a diagnostic (DESIGN.md sec:diagnostics, item DIAG-suppress): a hash of what
//! the diagnostic is and where in the unit's declarations it lies, the same on every run of the
//! same source; `super::InFile` adds the file. A file of its own so that the front end
//! (`crate::front`), which gives each diagnostic its address, imports it without importing the
//! suppression, which reads diagnostics.

use std::collections::HashMap;

use crate::address::ContentAddress;
use crate::ast::{self, Stmt, StmtKind, Target};
use crate::lex::Span;

/// Whether a diagnostic is advisory or rejects the unit.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Severity {
    /// A warning: the unit is accepted.
    Warning,
    /// A rejection: the unit is not accepted.
    Rejection,
}

/// The part of the address that the text decides ([`super::InFile`] joins it with the file's)
/// of each of `errors`, diagnostics of `severity` of the unit `text` whose top-level
/// statements are `stmts` (empty when the unit was rejected before resolution), in order.
///
/// That part is the BLAKE3-256 hash of the severity, the rejection row, the name of the
/// top-level declaration the diagnostic lies in, the text of the node it is at with its
/// white space dropped, and its message; and of its occurrence among the diagnostics with all
/// of these the same, counted in order, so that no two diagnostics of a unit share it.
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
/// `l01_29_diagnostics::suppress::suppressing_every_warning_scales`. A complete solution would
/// hash each node's text with BLAKE3, at that cost.
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

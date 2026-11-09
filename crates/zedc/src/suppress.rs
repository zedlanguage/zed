//! The address of a diagnostic and its suppression (DESIGN.md sec:diagnostics, items
//! DIAG-suppress, DIAG-suppress-rest and DIAG-addr-root). Each diagnostic has an address,
//! printed under it as `address: <hex>` only with `--addresses`, that is the same on every run of
//! the same file, from any directory; `--suppress <address>` on `zedc run`, `replay`, `build` and `test` leaves the
//! warning at that address unprinted. The program is the same with or without it: suppression changes
//! only what is printed. A rejection cannot be suppressed, and an address that names nothing
//! is reported.
//!
//! The address has two parts. The front end gives each diagnostic the part its unit's text
//! decides ([`Diagnostic::address`]), so one text read from two files is compiled once
//! (`crate::query`); [`InFile::address`] joins that part with the file's, so the same warning
//! in two files has two addresses, unless they are one unit of two copies of a package.

mod addresses;

use std::collections::HashMap;
use std::path::Path;

use crate::address::ContentAddress;
use crate::front::Diagnostic;
use crate::place::Place;

pub use addresses::Severity;
pub(crate) use addresses::addresses;

/// The part of a diagnostic's address that names its file, which does not depend on the
/// directory `zedc` runs in (DESIGN.md sec:diagnostics): for a unit under a manifest, a hash of
/// its path from the package root, its unit name ([`Place::Unit`]); for a file with no manifest
/// above it, a hash of its absolute path ([`Place::Loose`]); each found after every symbolic
/// link and every `.` and `..` step is resolved. Two paths to one file therefore give one
/// `InFile` (two hard links to one file are two paths and give two), and two files give two,
/// whatever their texts, except the same unit of two copies of one package: a package moved or
/// checked out elsewhere prints the same addresses. The two kinds are hashed under two tags, so a
/// unit name never gives the part of a file with no manifest.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct InFile([u8; 32]);

impl InFile {
    /// The file `file` as its diagnostics' addresses name it ([`Place::of`]); or why it cannot
    /// be resolved, or its path under its package root is not UTF-8.
    pub fn of(file: &Path) -> Result<InFile, String> {
        Place::of(file).map(|p| InFile::at(&p))
    }

    /// The file at `place` as its diagnostics' addresses name it. O(parts of its path).
    pub fn at(place: &Place) -> InFile {
        match place {
            Place::Unit { name, .. } => InFile::named(name),
            Place::Loose(full) => InFile::hashed(
                b"zed diagnostic file with no package\0",
                full.components().map(|c| c.as_os_str().as_encoded_bytes()),
            ),
        }
    }

    /// The file `name`, a path under its package root with `/` between its parts, as its
    /// diagnostics' addresses name it, whether or not the file exists (a unit a package names
    /// and has no file). O(length of `name`).
    pub fn named(name: &str) -> InFile {
        InFile::hashed(
            b"zed diagnostic unit file\0",
            name.split('/').map(str::as_bytes),
        )
    }

    /// The hash of `tag` and of each of `parts` ended by a zero byte, which no part holds.
    /// O(total length).
    fn hashed<'a>(tag: &[u8], parts: impl Iterator<Item = &'a [u8]>) -> InFile {
        let mut h = blake3::Hasher::new();
        h.update(tag);
        for part in parts {
            h.update(part);
            h.update(b"\0");
        }
        InFile(*h.finalize().as_bytes())
    }

    /// The address of the diagnostic `d` of this file, as printed and as `--suppress` names it:
    /// the BLAKE3-256 hash of the file's part and `d`'s own. O(1).
    pub fn address(self, d: &Diagnostic) -> ContentAddress {
        self.join(d.address)
    }

    /// The address of the diagnostic of this file whose part the text decides is `part`
    /// ([`Diagnostic::address`]): the BLAKE3-256 hash of the file's part and `part`. O(1).
    pub fn join(self, part: ContentAddress) -> ContentAddress {
        let mut h = blake3::Hasher::new();
        h.update(b"zed diagnostic in a file\0");
        h.update(&self.0);
        h.update(&part.0);
        ContentAddress(*h.finalize().as_bytes())
    }
}

/// What a command line says about addresses: the addresses `--suppress` names, each with
/// whether a diagnostic had it, and whether `--addresses` asks for each diagnostic's address to
/// be printed under it (DESIGN.md sec:diagnostics: the default text holds no address).
#[derive(Default, Debug)]
pub struct Suppress {
    named: Vec<ContentAddress>,
    matched: HashMap<ContentAddress, bool>,
    print: bool,
}

/// How a diagnostic's address is written, for the messages about `--suppress`.
const ADDRESS_FORM: &str = "an address is the 64 lowercase hexadecimal digits that `zedc` prints \
     under a warning when run with `--addresses`";

impl Suppress {
    /// The words of `words` other than each `--suppress <address>` and each `--addresses`, and
    /// what those say; or why a word after `--suppress` is not an address, or is missing.
    pub fn take<'a>(words: &[&'a str]) -> Result<(Suppress, Vec<&'a str>), String> {
        let mut suppress = Suppress::default();
        let mut rest = Vec::with_capacity(words.len());
        let mut words = words.iter();
        while let Some(&w) = words.next() {
            if w == "--addresses" {
                suppress.print = true;
                continue;
            }
            if w != "--suppress" {
                rest.push(w);
                continue;
            }
            let hex = words.next().ok_or_else(|| {
                format!(
                    "`--suppress` is the last word of the command line, and it needs the \
                     address of the warning to leave unprinted after it; {ADDRESS_FORM}. \
                     Write `--suppress <address>`, or remove `--suppress`."
                )
            })?;
            let a = ContentAddress::parse(hex).ok_or_else(|| {
                format!(
                    "`--suppress {hex}`: `{hex}` is not an address; {ADDRESS_FORM}. Copy the \
                     address from that line whole, or remove `--suppress {hex}`."
                )
            })?;
            if suppress.matched.insert(a, false).is_none() {
                suppress.named.push(a);
            }
        }
        Ok((suppress, rest))
    }

    /// The line a diagnostic whose address is `address` prints under it: `\n  address: <hex>`
    /// when `--addresses` was given, and nothing otherwise.
    pub fn address_line(&self, address: ContentAddress) -> String {
        match self.print {
            true => format!("\n  address: {address}"),
            false => String::new(),
        }
    }

    /// Whether the warning whose address ([`InFile::address`]) is `address` is suppressed;
    /// the address is then counted as matched.
    pub fn hides(&mut self, address: ContentAddress) -> bool {
        self.matched.get_mut(&address).is_some_and(|m| {
            *m = true;
            true
        })
    }

    /// A line for each rejection of `rejections`, of the unit read from `file`, which is
    /// `at`, whose address is named: a rejection cannot be suppressed. The address counts as
    /// matched.
    pub fn refused(&mut self, file: &str, at: InFile, rejections: &[Diagnostic]) -> Vec<String> {
        let mut out = Vec::new();
        for d in rejections {
            let address = at.address(d);
            if self.matched.contains_key(&address) {
                out.extend(self.refused_at(&format!("{file}:{}:{}", d.line, d.col), address));
            }
        }
        out
    }

    /// The line, placed at `place` (`file:line:col`, or `file` for a rejection with no place
    /// in its file), that says `--suppress` names the rejection whose address is `address`,
    /// if it does: a rejection cannot be suppressed. The address counts as matched.
    pub fn refused_at(&mut self, place: &str, address: ContentAddress) -> Option<String> {
        let m = self.matched.get_mut(&address)?;
        *m = true;
        Some(format!(
            "{place}: `--suppress {address}` names the error printed above at this place, and \
             an error cannot be suppressed, since the program it rejects cannot be built; \
             only a warning can be. Correct the program as that error describes, or remove \
             `--suppress {address}`."
        ))
    }

    /// A line for each address named that no diagnostic had, in the order named.
    pub fn unmatched(&self) -> Vec<String> {
        self.named
            .iter()
            .filter(|a| !self.matched[*a])
            .map(|a| {
                format!(
                    "`--suppress {a}`: no warning or error of this run has this address, so it \
                     suppresses nothing. An address changes when the warning's text, the \
                     declaration it lies in or the file's path from its package root changes. \
                     Run with `--addresses` to see each warning's address now, and remove or \
                     replace `--suppress {a}`."
                )
            })
            .collect()
    }
}

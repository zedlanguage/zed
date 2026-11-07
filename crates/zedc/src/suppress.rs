//! The address of a diagnostic and its suppression (DESIGN.md sec:diagnostics, items
//! DIAG-suppress and DIAG-suppress-rest). Each diagnostic has an address, printed under it as
//! `address: <hex>`, that is the same on every run of the same file from the same directory;
//! `--suppress <address>` on `zedc run`, `replay`, `build` and `test` leaves the warning at
//! that address unprinted. The program is the same with or without it: suppression changes
//! only what is printed. A rejection cannot be suppressed, and an address that names nothing
//! is reported.
//!
//! The address has two parts. The front end gives each diagnostic the part its unit's text
//! decides ([`Diagnostic::address`]), so one text read from two files is compiled once
//! (`crate::query`); [`InFile::address`] joins that part with the file's, so the same warning
//! in two files has two addresses.

mod addresses;

use std::collections::HashMap;
use std::path::Path;

use crate::address::ContentAddress;
use crate::front::Diagnostic;

pub use addresses::Severity;
pub(crate) use addresses::addresses;

/// The part of a diagnostic's address that names its file: a hash of the path from the
/// current directory to the file, taken after every symbolic link and every `.` and `..` step
/// of both is resolved. Two paths to one file therefore give one `InFile` (two hard links to
/// one file are two paths and give two), and two files give two, whatever their texts. The
/// path is relative, so a tree moved or checked out elsewhere and run from the same place in it
/// prints the same addresses.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct InFile([u8; 32]);

impl InFile {
    /// The file `file` as its diagnostics' addresses name it; or why it, or the current
    /// directory, cannot be resolved.
    pub fn of(file: &Path) -> Result<InFile, String> {
        let full = std::fs::canonicalize(file).map_err(|e| format!("{}: {e}", file.display()))?;
        Ok(InFile::from_resolved(&full, &here()?))
    }

    /// The file `name`, a path under the package root `root` with `/` between its parts, as
    /// its diagnostics' addresses name it: [`InFile::of`] when the file exists; when it does
    /// not (a unit a package names and has no file), the resolved root followed by the parts
    /// of `name`. Or why the root or the current directory cannot be resolved.
    pub fn under(root: &Path, name: &str) -> Result<InFile, String> {
        let file = root.join(name);
        // The empty path, which a file in the current directory has as its directory, is `.`.
        let root = if root.as_os_str().is_empty() {
            Path::new(".")
        } else {
            root
        };
        let full = match std::fs::canonicalize(&file) {
            Ok(full) => full,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => std::fs::canonicalize(root)
                .map_err(|e| format!("{}: {e}", root.display()))?
                .join(name),
            Err(e) => return Err(format!("{}: {e}", file.display())),
        };
        Ok(InFile::from_resolved(&full, &here()?))
    }

    /// The file at `full` seen from the directory `here`, both absolute with no link and no
    /// `.` or `..` step: one `..` for each part of `here` below the parts they share, then
    /// each part of `full` below them, each part ended by a zero byte, which no part holds.
    /// O(parts of the two paths).
    fn from_resolved(full: &Path, here: &Path) -> InFile {
        let shared = full
            .components()
            .zip(here.components())
            .take_while(|(a, b)| a == b)
            .count();
        let mut h = blake3::Hasher::new();
        h.update(b"zed diagnostic file\0");
        for _ in here.components().skip(shared) {
            h.update(b"..\0");
        }
        for part in full.components().skip(shared) {
            h.update(part.as_os_str().as_encoded_bytes());
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

/// The current directory, resolved as [`InFile`] resolves a file; or why it cannot be.
fn here() -> Result<std::path::PathBuf, String> {
    std::env::current_dir()
        .and_then(std::fs::canonicalize)
        .map_err(|e| format!("the current directory: {e}"))
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
            "{place}: `--suppress {address}` names a rejection, which cannot be suppressed"
        ))
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

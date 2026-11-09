//! Where a file lies on disk: the package root above it and its path from that root, or none
//! (DESIGN.md sec:units, sec:diagnostics; items DIAG-addr-rest and DIAG-addr-root). Both
//! [`crate::unit`], which loads a package, and [`crate::suppress`], which names a file in each
//! printed address, use it, so it imports neither.

use std::path::{Path, PathBuf};

use rustix::fs::{AtFlags, CWD, FileType, Mode, OFlags, openat, statat};

/// The name of the manifest file, which marks the package root.
pub const MANIFEST: &str = "zed.manifest";

/// Where a file lies, after every symbolic link and every `.` and `..` step of its path is
/// resolved: which package it is a unit of, if any. Its diagnostics' addresses name it by this
/// ([`crate::suppress::InFile::at`]), so by nothing that depends on the directory `zedc` runs in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Place {
    /// A file under a manifest: its package root, the nearest directory above it that holds a
    /// manifest, and its path under that root with `/` between its parts.
    Unit {
        /// The package root, resolved.
        root: PathBuf,
        /// The file's path under the root, which names its unit (DESIGN.md sec:units).
        name: String,
    },
    /// A file with no manifest in any directory above it: its absolute path, resolved.
    Loose(PathBuf),
}

impl Place {
    /// Where the file `file` lies; or why it, or a directory above it, cannot be resolved, or
    /// its path under its package root is not UTF-8. O(parts of the path): the directories
    /// above the file are walked by opening each one's `..` from the one below, so each probe
    /// for a manifest names one part, and neither this process nor the kernel goes over the
    /// whole path again per directory.
    pub fn of(file: &Path) -> Result<Place, String> {
        let full = std::fs::canonicalize(file).map_err(|e| {
            format!(
                "zedc cannot follow the path `{}` to the file it names, to find the package the \
                 file belongs to: {e}. Name a file that exists, on a path whose directories zedc \
                 may enter.",
                file.display()
            )
        })?;
        let Some(parent) = full.parent() else {
            return Ok(Place::Loose(full));
        };
        // Opened for its place only (`O_PATH`), so a directory that may be passed through and
        // not read still is.
        let flags = OFlags::PATH | OFlags::DIRECTORY | OFlags::CLOEXEC;
        let cannot = |e| {
            format!(
                "zedc cannot open a directory above `{}` to look there for the manifest \
                 `zed.manifest` that marks a package: {e}. Let zedc enter the directories above \
                 the file.",
                file.display()
            )
        };
        let mut dir = openat(CWD, parent, flags, Mode::empty()).map_err(cannot)?;
        let above = parent.components().count() - 1;
        let mut up = 0;
        loop {
            // As `Path::is_file`: a regular file once links are followed, and no error.
            let manifest = statat(&dir, MANIFEST, AtFlags::empty())
                .is_ok_and(|s| FileType::from_raw_mode(s.st_mode) == FileType::RegularFile);
            if manifest {
                let root = parent.ancestors().nth(up).expect("one ancestor per level");
                let rel = full.strip_prefix(root).expect("the root is above the file");
                let name: Vec<&str> = rel
                    .components()
                    .map(|c| c.as_os_str().to_str())
                    .collect::<Option<_>>()
                    .ok_or_else(|| {
                        format!(
                            "the path of `{}` under its package root `{}` is not UTF-8 text, and \
                             a unit is named by that path. Rename the file and the directories \
                             between it and the package root with UTF-8 names.",
                            file.display(),
                            root.display()
                        )
                    })?;
                return Ok(Place::Unit {
                    root: root.to_path_buf(),
                    name: name.join("/"),
                });
            }
            if up == above {
                return Ok(Place::Loose(full));
            }
            dir = openat(&dir, "..", flags, Mode::empty()).map_err(cannot)?;
            up += 1;
        }
    }
}

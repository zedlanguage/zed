//! The bytes of a named section of an object file or executable. A file of its own so that
//! `link` (the build's own section) and `exe` (the program's section, `zedc check-exe`) both
//! read sections without `exe` importing `link`, which imports the crate root, which re-exports
//! `exe`: an import cycle (step S.1f).

use std::path::Path;

/// The bytes of the section `name` in the executable or object file `exe`, if it has that
/// section.
pub(crate) fn section_of(exe: &Path, name: &str) -> Result<Option<Vec<u8>>, String> {
    let file = std::fs::File::open(exe).map_err(|e| format!("{}: {e}", exe.display()))?;
    section(&object::ReadCache::new(file), exe, name)
}

/// The bytes of the section `name` in the object file or executable `data` read from `file`,
/// if it has that section.
pub(crate) fn section<'a, R: object::ReadRef<'a>>(
    data: R,
    file: &Path,
    name: &str,
) -> Result<Option<Vec<u8>>, String> {
    use object::{Object as _, ObjectSection as _};
    let at = |e: &dyn std::fmt::Display| format!("{}: {e}", file.display());
    let object = object::File::parse(data).map_err(|e| at(&e))?;
    object
        .section_by_name(name)
        .map(|s| s.data().map(<[u8]>::to_vec).map_err(|e| at(&e)))
        .transpose()
}

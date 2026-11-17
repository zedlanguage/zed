//! The spec checkout, for the tests that read DESIGN.md and EXAMPLES.md in place. Those tests
//! are compiled only with the feature `spec` of this crate, so a clone of this repository
//! without the spec builds and tests without them; tools/run_tests.sh always turns the feature
//! on, so the local suite never leaves them out. This module itself is always compiled, so that
//! its own unit tests run in every build of the crate's library.
//!
//! The checkout is the directory named by [`VAR`] when that is set, and otherwise the first
//! directory `zed` holding DESIGN.md beside this repository or beside one of its ancestors, so
//! that the spec beside the main checkout is found from that checkout, from a worktree under
//! `wt/`, and from the build root zrun mounts a worktree at. A test never passes without
//! reading the spec: where it is not found, the test fails and names the paths tried.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// The environment variable that names the spec checkout.
pub const VAR: &str = "ZED_SPEC_DIR";

/// The spec checkout, found once per test binary ([`locate`]). Panics, naming the paths tried,
/// where there is none.
pub fn dir() -> &'static Path {
    static DIR: OnceLock<PathBuf> = OnceLock::new();
    DIR.get_or_init(|| {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("the test crate is inside the repository");
        locate(std::env::var_os(VAR).as_deref(), repo).unwrap_or_else(|e| panic!("{e}"))
    })
}

/// The spec checkout as a string, as the tools of `zed_tools` take it.
pub fn root() -> String {
    dir().display().to_string()
}

/// The path of the spec's DESIGN.md.
pub fn design_path() -> String {
    format!("{}/DESIGN.md", root())
}

/// The path of the spec's EXAMPLES.md.
pub fn examples_path() -> String {
    format!("{}/EXAMPLES.md", root())
}

/// The text of the spec's DESIGN.md, read once per test binary.
pub fn design() -> &'static str {
    static TEXT: OnceLock<String> = OnceLock::new();
    TEXT.get_or_init(|| read(&design_path()))
}

/// The text of the file at `path`; panics naming it when it cannot be read.
pub fn read(path: &str) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"))
}

/// The spec checkout for the repository at `repo`, given `var`, the value of [`VAR`]: that
/// directory where it is set, and otherwise the first `zed` directory holding DESIGN.md in the
/// parent of `repo` or in an ancestor of it. The repository's own `zed/` folder is not looked
/// at. An error naming every path tried where no DESIGN.md is found.
pub fn locate(var: Option<&OsStr>, repo: &Path) -> Result<PathBuf, String> {
    if let Some(var) = var {
        let dir = PathBuf::from(var);
        return if dir.join("DESIGN.md").is_file() {
            Ok(dir)
        } else {
            Err(format!(
                "{VAR}={var:?}, but {} is not a file",
                dir.join("DESIGN.md").display()
            ))
        };
    }
    let mut tried = Vec::new();
    for up in repo.ancestors().skip(1) {
        let design = up.join("zed").join("DESIGN.md");
        if design.is_file() {
            return Ok(up.join("zed"));
        }
        tried.push(design.display().to_string());
    }
    Err(format!(
        "no spec checkout: {VAR} is not set, and none of {} is a file; set {VAR} to the spec \
         checkout, or build the tests without the feature `spec`",
        tried.join(", ")
    ))
}

#[cfg(test)]
mod tests {
    use super::{VAR, locate};
    use std::ffi::OsStr;
    use std::fs;
    use std::path::{Path, PathBuf};

    /// The directory `rel` under `root`, made.
    fn dir(root: &Path, rel: &str) -> PathBuf {
        let path = root.join(rel);
        fs::create_dir_all(&path).expect("making a test directory");
        path
    }

    /// The directory `rel` under `root`, made, with a DESIGN.md in it.
    fn spec(root: &Path, rel: &str) -> PathBuf {
        let path = dir(root, rel);
        fs::write(path.join("DESIGN.md"), "# Zed\n").expect("writing a test file");
        path
    }

    #[test]
    fn finds_the_spec_beside_the_main_checkout_and_beside_a_worktree() {
        let t = crate::scratch::scratch("spec-walk");
        let spec = spec(&t, "Work/zed");
        assert_eq!(locate(None, &dir(&t, "Work/zed-impl")), Ok(spec.clone()));
        assert_eq!(locate(None, &dir(&t, "Work/wt/trees/item")), Ok(spec));
    }

    #[test]
    fn the_nearest_spec_wins() {
        let t = crate::scratch::scratch("spec-nearest");
        spec(&t, "Work/zed");
        let near = spec(&t, "Work/wt/zed");
        assert_eq!(locate(None, &dir(&t, "Work/wt/item")), Ok(near));
    }

    #[test]
    fn the_repositorys_own_zed_folder_is_not_the_spec() {
        // The scratch directory is under this repository's build, beside no spec; a spec
        // beside one of the build's ancestors would be found, so the walk is checked to name
        // the paths that are not the repository's own.
        let t = crate::scratch::scratch("spec-own");
        let repo = dir(&t, "Work/zed-impl");
        spec(&t, "Work/zed-impl/zed");
        match locate(None, &repo) {
            Ok(found) => assert!(!found.starts_with(&repo), "{}", found.display()),
            Err(e) => {
                let tried = t.join("Work/zed/DESIGN.md");
                assert!(e.contains(&tried.display().to_string()), "{e}");
                assert!(e.contains(VAR), "{e}");
                assert!(!e.contains("zed-impl/zed/DESIGN.md"), "{e}");
            }
        }
    }

    #[test]
    fn the_variable_overrides_the_walk() {
        let t = crate::scratch::scratch("spec-var");
        spec(&t, "Work/zed");
        let other = spec(&t, "elsewhere/spec");
        let repo = dir(&t, "Work/zed-impl");
        assert_eq!(locate(Some(other.as_os_str()), &repo), Ok(other));
    }

    #[test]
    fn a_variable_naming_no_spec_is_an_error_that_names_the_path() {
        let t = crate::scratch::scratch("spec-empty");
        spec(&t, "Work/zed");
        let empty = dir(&t, "empty");
        let repo = dir(&t, "Work/zed-impl");
        let err = locate(Some(empty.as_os_str()), &repo).unwrap_err();
        assert!(err.contains(VAR), "{err}");
        assert!(
            err.contains(&empty.join("DESIGN.md").display().to_string()),
            "{err}"
        );
        assert!(locate(Some(OsStr::new("")), &repo).is_err());
    }
}

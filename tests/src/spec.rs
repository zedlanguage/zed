//! The spec repository, for the tests that compare this repository with it (DESIGN.md,
//! EXAMPLES.md).
//!
//! It is the directory named by [`VAR`] when that is set, and otherwise the first directory
//! `zed` holding DESIGN.md beside this repository or beside one of its ancestors, so that the
//! spec checkout beside the main checkout is found from that checkout and from a worktree
//! under `wt/`. A test never passes without reading the spec: where it is not found, the test
//! fails and names the paths tried. The one exception is `ZED_SPEC_DIR=none`, which CI sets,
//! since CI does not read the spec repository (the author's instruction, 2026-10-29); each
//! test then says on standard error that it did not check.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};

/// The environment variable that names the spec repository.
pub const VAR: &str = "ZED_SPEC_DIR";

/// The value of [`VAR`] under which the spec is not read.
pub const NONE: &str = "none";

/// The spec repository, or `None` where [`VAR`] is [`NONE`], with a line on standard error
/// naming `what`, the check left undone. Panics where the spec is not found.
pub fn dir(what: &str) -> Option<PathBuf> {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the test crate is inside the repository");
    match locate(std::env::var_os(VAR).as_deref(), repo) {
        Ok(Some(dir)) => Some(dir),
        Ok(None) => {
            eprintln!("{VAR}={NONE}: the spec repository is not read, so {what} is not checked");
            None
        }
        Err(message) => panic!("{message}"),
    }
}

/// The spec repository for the repository at `repo`, given `var`, the value of [`VAR`]: that
/// directory where it is set, and otherwise the first `zed` directory holding DESIGN.md in the
/// parent of `repo` or in an ancestor of it. The repository's own `zed/` folder of copies is
/// not looked at. `Ok(None)` where `var` is [`NONE`]; an error naming every path tried where
/// no DESIGN.md is found.
pub fn locate(var: Option<&OsStr>, repo: &Path) -> Result<Option<PathBuf>, String> {
    if let Some(var) = var {
        if var == NONE {
            return Ok(None);
        }
        let dir = PathBuf::from(var);
        return if dir.join("DESIGN.md").is_file() {
            Ok(Some(dir))
        } else {
            Err(format!(
                "{VAR}={var:?}, but {} is not a file",
                dir.join("DESIGN.md").display()
            ))
        };
    }
    let mut tried = Vec::new();
    for up in repo.ancestors().skip(1) {
        let dir = up.join("zed");
        let design = dir.join("DESIGN.md");
        if design.is_file() {
            return Ok(Some(dir));
        }
        tried.push(design);
    }
    let tried: Vec<String> = tried.iter().map(|p| p.display().to_string()).collect();
    Err(format!(
        "no spec repository: {VAR} is not set, and none of {} is a file; set {VAR} to the spec \
         checkout, or to `{NONE}` where the spec is not to be read",
        tried.join(", ")
    ))
}

#[cfg(test)]
mod tests {
    use super::{NONE, VAR, locate};
    use std::ffi::OsStr;
    use std::fs;
    use std::path::PathBuf;

    /// A directory under the system's temporary directory, removed at the end of the test.
    /// Its ancestors hold no `zed/DESIGN.md`, unlike those of this repository.
    struct Tmp(PathBuf);

    impl Tmp {
        fn new(name: &str) -> Tmp {
            let path =
                std::env::temp_dir().join(format!("zed-spec-locate-{}-{name}", std::process::id()));
            let _ = fs::remove_dir_all(&path);
            fs::create_dir_all(&path).expect("creating a test directory");
            Tmp(path)
        }

        /// Creates the directory `rel` and gives its path.
        fn dir(&self, rel: &str) -> PathBuf {
            let path = self.0.join(rel);
            fs::create_dir_all(&path).expect("creating a test directory");
            path
        }

        /// Writes a DESIGN.md into the directory `rel` and gives that directory.
        fn spec(&self, rel: &str) -> PathBuf {
            let path = self.dir(rel);
            fs::write(path.join("DESIGN.md"), "# Zed\n").expect("writing a test file");
            path
        }
    }

    impl Drop for Tmp {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn finds_the_spec_beside_the_main_checkout_and_beside_a_worktree() {
        let t = Tmp::new("walk");
        let spec = t.spec("Work/zed");
        let main = t.dir("Work/zed-impl");
        let worktree = t.dir("Work/wt/item");
        assert_eq!(locate(None, &main), Ok(Some(spec.clone())));
        assert_eq!(locate(None, &worktree), Ok(Some(spec)));
    }

    #[test]
    fn the_nearest_spec_wins() {
        let t = Tmp::new("nearest");
        t.spec("Work/zed");
        let near = t.spec("Work/wt/zed");
        assert_eq!(locate(None, &t.dir("Work/wt/item")), Ok(Some(near)));
    }

    #[test]
    fn the_repositorys_own_zed_folder_is_not_the_spec() {
        let t = Tmp::new("own");
        let repo = t.dir("Work/zed-impl");
        t.spec("Work/zed-impl/zed");
        t.dir("Work/zed");
        let err = locate(None, &repo).unwrap_err();
        let tried = t.0.join("Work/zed/DESIGN.md");
        assert!(err.contains(&tried.display().to_string()), "{err}");
        assert!(err.contains(VAR), "{err}");
        assert!(!err.contains("zed-impl/zed/DESIGN.md"), "{err}");
    }

    #[test]
    fn the_variable_overrides_the_walk() {
        let t = Tmp::new("var");
        t.spec("Work/zed");
        let other = t.spec("elsewhere/spec");
        let repo = t.dir("Work/zed-impl");
        assert_eq!(locate(Some(other.as_os_str()), &repo), Ok(Some(other)));
    }

    #[test]
    fn a_variable_naming_no_spec_is_an_error() {
        let t = Tmp::new("empty");
        t.spec("Work/zed");
        let empty = t.dir("empty");
        let repo = t.dir("Work/zed-impl");
        let err = locate(Some(empty.as_os_str()), &repo).unwrap_err();
        assert!(err.contains(VAR), "{err}");
        assert!(
            err.contains(&empty.join("DESIGN.md").display().to_string()),
            "{err}"
        );
        assert!(locate(Some(OsStr::new("")), &repo).is_err());
    }

    #[test]
    fn none_reads_no_spec() {
        let t = Tmp::new("none");
        t.spec("Work/zed");
        let repo = t.dir("Work/zed-impl");
        assert_eq!(locate(Some(OsStr::new(NONE)), &repo), Ok(None));
    }
}

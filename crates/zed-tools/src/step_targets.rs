//! `step_targets [--check] [ROOT]` keeps the test targets of `tests/Cargo.toml` equal to the step
//! folders of `tests/steps`: one `[[test]]` per folder, named after it, with the folder's `mod.rs`
//! as its crate root, so that a change to one folder rebuilds that folder's test binary alone.
//! The targets lie between the lines [`BEGIN`] and [`END`]. With no flag the tool writes them
//! there; with `--check` it writes nothing and prints one line per folder without a target and
//! per target without a folder, and fails if there is any. `ROOT` is the repository, this one
//! when none is given.

use std::collections::{BTreeSet, HashSet};
use std::ops::Range;
use std::path::Path;

use crate::text::read_text;
use crate::{Outcome, impl_root, say};

/// The line before the targets.
pub const BEGIN: &str = "# BEGIN step targets: written by `cargo run -p zed-tools --bin step_targets`; do not edit by hand.";

/// The line after the targets.
pub const END: &str = "# END step targets";

/// The step folders in the directory `steps`: its subdirectories, in byte order.
pub fn folders(steps: &Path) -> Result<BTreeSet<String>, String> {
    let entries = std::fs::read_dir(steps).map_err(|e| format!("{}: {e}", steps.display()))?;
    let mut names = BTreeSet::new();
    for e in entries {
        let e = e.map_err(|e| format!("{}: {e}", steps.display()))?;
        if e.file_type().map_err(|e| format!("{e}"))?.is_dir() {
            let name = e.file_name().into_string();
            names.insert(name.map_err(|n| format!("folder name not UTF-8: {n:?}"))?);
        }
    }
    Ok(names)
}

/// The path of folder `name`'s crate root, relative to `tests/`.
fn root_of(name: &str) -> String {
    format!("steps/{name}/mod.rs")
}

/// The lines between [`BEGIN`] and [`END`] for `folders`, in their order.
pub fn block(folders: &BTreeSet<String>) -> String {
    folders
        .iter()
        .map(|f| format!("[[test]]\nname = \"{f}\"\npath = \"{}\"\n", root_of(f)))
        .collect()
}

/// The bytes of `toml` between the line [`BEGIN`] and the line [`END`].
fn body(toml: &str) -> Result<Range<usize>, String> {
    let begin = format!("{BEGIN}\n");
    let start = toml
        .find(&begin)
        .ok_or_else(|| format!("tests/Cargo.toml has no line `{BEGIN}`"))?
        + begin.len();
    let end = toml[start..]
        .find(&format!("{END}\n"))
        .ok_or_else(|| format!("tests/Cargo.toml has no line `{END}` after `{BEGIN}`"))?;
    Ok(start..start + end)
}

/// `toml` with the lines between [`BEGIN`] and [`END`] replaced by `block`.
pub fn splice(toml: &str, block: &str) -> Result<String, String> {
    let r = body(toml)?;
    Ok(format!("{}{block}{}", &toml[..r.start], &toml[r.end..]))
}

/// The targets between [`BEGIN`] and [`END`] in `toml`, each its name and its path, in order.
pub fn targets(toml: &str) -> Result<Vec<(String, String)>, String> {
    let mut found = Vec::new();
    let mut name: Option<String> = None;
    for line in toml[body(toml)?].lines() {
        let quoted = |key: &str| {
            line.strip_prefix(key)
                .and_then(|v| v.trim().strip_prefix('='))
                .and_then(|v| v.trim().strip_prefix('"')?.strip_suffix('"'))
                .map(str::to_string)
        };
        if let Some(n) = quoted("name") {
            name = Some(n);
        } else if let Some(p) = quoted("path") {
            let n = name
                .take()
                .ok_or_else(|| format!("tests/Cargo.toml: path {p} has no name before it"))?;
            found.push((n, p));
        }
    }
    match name {
        Some(n) => Err(format!("tests/Cargo.toml: target {n} has no path")),
        None => Ok(found),
    }
}

/// One line per difference between the step folders `folders` and the targets `targets`: a
/// folder without a target, a target without a folder, a target listed twice, and a target whose
/// path is not its folder's `mod.rs`.
pub fn drift(folders: &BTreeSet<String>, targets: &[(String, String)]) -> Vec<String> {
    let mut problems = Vec::new();
    let mut seen: HashSet<&str> = HashSet::new();
    for (name, path) in targets {
        if !seen.insert(name) {
            problems.push(format!("target {name} is listed twice in tests/Cargo.toml"));
        }
        if !folders.contains(name) {
            problems.push(format!(
                "target {name} in tests/Cargo.toml has no folder tests/steps/{name}"
            ));
        }
        if *path != root_of(name) {
            problems.push(format!(
                "target {name} has the path {path}, not {}",
                root_of(name)
            ));
        }
    }
    for f in folders {
        if !seen.contains(f.as_str()) {
            problems.push(format!(
                "folder tests/steps/{f} has no [[test]] target in tests/Cargo.toml: run step_targets"
            ));
        }
    }
    problems
}

/// The tool: see the module documentation.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let check = args.first().is_some_and(|a| a == "--check");
    let root = match &args[usize::from(check)..] {
        [] => impl_root(),
        [root] => root.clone(),
        _ => return Err("usage: step_targets [--check] [ROOT]".into()),
    };
    let manifest = format!("{root}/tests/Cargo.toml");
    let toml = read_text(&manifest)?;
    let folders = folders(&Path::new(&root).join("tests/steps"))?;
    if check {
        let problems = drift(&folders, &targets(&toml)?);
        for p in &problems {
            say!(out, "{p}");
        }
        return Ok(problems.is_empty());
    }
    let written = splice(&toml, &block(&folders))?;
    if written == toml {
        say!(out, "{manifest}: {} step targets, unchanged", folders.len());
    } else {
        std::fs::write(&manifest, &written).map_err(|e| format!("{manifest}: {e}"))?;
        say!(out, "{manifest}: wrote {} step targets", folders.len());
    }
    Ok(true)
}

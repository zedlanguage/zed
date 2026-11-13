//! The sources a build of a workspace crate is made from, and their BLAKE3 hash
//! (RUNTIME-build-src). `build.rs` compiles this file as a module of its own and writes the hash
//! into [`link::BUILD`](crate::link::BUILD), so that two builds of `zed-native` from different
//! sources hold different builds in the section `.zed_native.build`. Cargo's hash of the crate,
//! which the rest of that section holds, names the crate's features and its dependencies'
//! builds but none of the source files' contents, so before this a runtime library built from
//! older sources passed `zedc build`'s check (L1.36a) and gave the same key of a link (L1.36b).
//!
//! The sources of a crate are its `Cargo.toml`, its `build.rs` if it has one, every file under
//! its `src` directory, and every file a Rust file among these names by a string literal in
//! `include!`, `include_str!`, `include_bytes!` or `#[path = ...]`, read the same way in turn.
//! The sources of a build are those of the crate and of every crate of the workspace it depends
//! on, directly or not, through `[dependencies]` or `[build-dependencies]`, of any target, but
//! not `[dev-dependencies]`, which do not enter the library. A file counts once, however many
//! crates name it.
//!
//! This reads more than the compiler does: a file under `src` that no module names, and a file a
//! `#[cfg(test)]` module includes, change the hash but not the build. Two builds of one tree
//! still agree, and a file the compiler reads is never left out, which is what the check needs.
//! A literal with an escape in it, and a path built by a macro, are not followed; the only such
//! paths in the workspace are under `OUT_DIR`, the output of a build script, which is hashed.
//! One build script reads a file outside the workspace: `zedc-syntax`'s reads the compiler's
//! grammar from the spec's DESIGN.md (`crates/zedc-syntax/spec_grammar.rs`), which this
//! repository does not hold, so `build.rs` reads that grammar too and adds it to the hash with
//! [`with_grammar`].

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read as _;
use std::path::{Component, Path, PathBuf};

/// The sources of one build: their hash and the files and directories read to find them.
pub struct Sources {
    /// BLAKE3 over every source file in the order of its path: for each, the length and bytes
    /// of the path from the workspace's root, then the length and bytes of its contents.
    pub hash: [u8; 32],
    /// Every file hashed, every `Cargo.toml` read, and every directory listed, which a build
    /// script names to Cargo with `cargo::rerun-if-changed`, so that it runs again exactly when
    /// one of them changes, or a file is added to a directory.
    pub read: Vec<PathBuf>,
}

/// The sources of a build of the crate in directory `krate`, which lies in a workspace.
///
/// Cost: O(B + M + F log F) for B bytes of source files, M bytes of manifests and F files; each
/// crate and each file is read once, kept by a visited set.
pub fn of(krate: &Path) -> Result<Sources, String> {
    let krate = normal(krate);
    let root = krate
        .ancestors()
        .find(|d| {
            std::fs::read_to_string(d.join("Cargo.toml"))
                .is_ok_and(|m| m.lines().any(|l| l.trim() == "[workspace]"))
        })
        .ok_or_else(|| {
            format!(
                "{}: no directory above it holds a Cargo.toml with a [workspace] table",
                krate.display()
            )
        })?
        .to_path_buf();
    let root_manifest = root.join("Cargo.toml");
    let members: BTreeMap<String, PathBuf> =
        table(&read(&root_manifest)?, |h| h == "workspace.dependencies")
            .into_iter()
            .filter_map(|(name, dep)| match dep {
                Dep::Path(p) => Some((name, normal(&root.join(p)))),
                Dep::Workspace | Dep::Other => None,
            })
            .collect();

    let mut read_dirs = vec![root_manifest];
    let mut files = BTreeSet::new();
    let mut rust = Vec::new();
    // The crates of the dependency closure, by an explicit work list and a visited set.
    let mut crates = BTreeSet::from([krate.clone()]);
    let mut work = vec![krate];
    while let Some(dir) = work.pop() {
        let manifest = dir.join("Cargo.toml");
        for (name, dep) in table(&read(&manifest)?, is_dependencies) {
            let dep = match dep {
                Dep::Path(p) => normal(&dir.join(p)),
                Dep::Workspace => match members.get(&name) {
                    Some(d) => d.clone(),
                    None => continue,
                },
                Dep::Other => continue,
            };
            if crates.insert(dep.clone()) {
                work.push(dep);
            }
        }
        file(manifest, &mut files, &mut rust);
        let script = dir.join("build.rs");
        if script.is_file() {
            file(script, &mut files, &mut rust);
        }
        // The files under `src`, by an explicit stack; a directory reached twice through a
        // symbolic link is listed once.
        let mut listed = BTreeSet::new();
        let mut dirs = vec![dir.join("src")];
        while let Some(d) = dirs.pop() {
            let real = std::fs::canonicalize(&d).map_err(|e| format!("{}: {e}", d.display()))?;
            if !listed.insert(real) {
                continue;
            }
            let entries = std::fs::read_dir(&d).map_err(|e| format!("{}: {e}", d.display()))?;
            for entry in entries {
                let path = entry.map_err(|e| format!("{}: {e}", d.display()))?.path();
                if path.is_dir() {
                    dirs.push(path);
                } else {
                    file(path, &mut files, &mut rust);
                }
            }
            read_dirs.push(d);
        }
    }

    // The files Rust files name by a literal, and those they name in turn.
    let mut bytes = Vec::new();
    while let Some(path) = rust.pop() {
        load(&path, &mut bytes)?;
        let at = path.parent().unwrap_or(Path::new(""));
        for named in named_files(&bytes) {
            let target = normal(&at.join(named));
            // A literal naming no file is not an include the compiler reads (it lies in a
            // comment or a string), since an include of a missing file does not compile.
            if target.is_file() {
                file(target, &mut files, &mut rust);
            }
        }
    }

    let mut hasher = blake3::Hasher::new();
    for path in &files {
        load(path, &mut bytes)?;
        let name = path.strip_prefix(&root).unwrap_or(path).as_os_str();
        hasher.update(&(name.len() as u64).to_le_bytes());
        hasher.update(name.as_encoded_bytes());
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
    }
    let mut read = read_dirs;
    read.extend(files);
    Ok(Sources {
        hash: *hasher.finalize().as_bytes(),
        read,
    })
}

/// The hash of a build whose sources hash to `sources` and whose compiler embeds the grammar
/// texts `grammar`, read from the spec when `zedc-syntax` is built: BLAKE3 over `sources`, then
/// the length and bytes of each text. O(the length of the texts).
pub fn with_grammar(sources: [u8; 32], grammar: &[&str]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&sources);
    for text in grammar {
        hasher.update(&(text.len() as u64).to_le_bytes());
        hasher.update(text.as_bytes());
    }
    *hasher.finalize().as_bytes()
}

/// Adds `path` to `files`, and to `rust` to be searched for the files it names if it is a Rust
/// file seen for the first time.
fn file(path: PathBuf, files: &mut BTreeSet<PathBuf>, rust: &mut Vec<PathBuf>) {
    if files.insert(path.clone()) && path.extension().is_some_and(|e| e == "rs") {
        rust.push(path);
    }
}

/// Reads the file at `path` into `bytes`, replacing what it held.
fn load(path: &Path, bytes: &mut Vec<u8>) -> Result<(), String> {
    bytes.clear();
    std::fs::File::open(path)
        .and_then(|mut f| f.read_to_end(bytes))
        .map(drop)
        .map_err(|e| format!("{}: {e}", path.display()))
}

/// Reads the text file at `path`.
fn read(path: &Path) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))
}

/// `path` with `.` and `..` resolved by its text, as the compiler and Cargo join relative paths.
fn normal(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for c in path.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                out.pop();
            }
            Component::Prefix(_) | Component::RootDir | Component::Normal(_) => out.push(c),
        }
    }
    out
}

/// The paths named by a string literal right after `include!(`, `include_str!(`,
/// `include_bytes!(` or `#[path =` in the Rust source `text`. One pass over `text`.
fn named_files(text: &[u8]) -> Vec<&str> {
    const OPENERS: [&[u8]; 4] = [
        b"include!(",
        b"include_str!(",
        b"include_bytes!(",
        b"#[path",
    ];
    let mut out = Vec::new();
    for i in 0..text.len() {
        if text[i] != b'i' && text[i] != b'#' {
            continue;
        }
        let Some(opener) = OPENERS.iter().find(|o| text[i..].starts_with(o)) else {
            continue;
        };
        let mut k = i + opener.len();
        while k < text.len() && (text[k].is_ascii_whitespace() || text[k] == b'=') {
            k += 1;
        }
        if text.get(k) != Some(&b'"') {
            continue;
        }
        let rest = &text[k + 1..];
        let Some(end) = rest.iter().position(|&b| b == b'"' || b == b'\\') else {
            continue;
        };
        if rest[end] == b'"'
            && let Ok(s) = std::str::from_utf8(&rest[..end])
        {
            out.push(s);
        }
    }
    out
}

/// How a manifest names a dependency.
enum Dep {
    /// `workspace = true`: the entry of that name in the root's `[workspace.dependencies]`.
    Workspace,
    /// `path = "..."`, relative to the manifest's directory.
    Path(String),
    /// A crate from a registry or a repository, outside the workspace.
    Other,
}

/// Whether the table with header `h` lists dependencies that enter a build of the crate.
fn is_dependencies(h: &str) -> bool {
    h == "dependencies"
        || h == "build-dependencies"
        || (h.starts_with("target.")
            && (h.ends_with(".dependencies") || h.ends_with(".build-dependencies")))
}

/// The entries of the tables of `manifest` whose header `wanted` accepts, by name: a line
/// `name = ...` or `name.workspace = true` in the table, or a table `[<header>.name]` of its
/// own. Inline tables are on one line, as TOML requires.
fn table(manifest: &str, wanted: impl Fn(&str) -> bool) -> Vec<(String, Dep)> {
    // The table being read: `None` outside a wanted one; `Some(None)` in a wanted table;
    // `Some(Some(k))` in the table of the dependency at index `k` of `out`.
    let mut current: Option<Option<usize>> = None;
    let mut out: Vec<(String, Dep)> = Vec::new();
    for line in manifest.lines() {
        let line = line.trim();
        if line.starts_with('#') || line.is_empty() {
            continue;
        }
        if let Some(header) = line.strip_prefix('[') {
            let header = header.trim_end_matches(']').trim();
            current = if wanted(header) {
                Some(None)
            } else {
                header.rsplit_once('.').and_then(|(h, name)| {
                    wanted(h).then(|| {
                        out.push((name.trim().to_string(), Dep::Other));
                        Some(out.len() - 1)
                    })
                })
            };
            continue;
        }
        let (Some(within), Some((key, value))) = (current, line.split_once('=')) else {
            continue;
        };
        let (key, value) = (key.trim(), value.trim());
        match within {
            Some(k) => {
                if let Some(dep) = field(key, value) {
                    out[k].1 = dep;
                }
            }
            None => {
                if let Some(name) = key.strip_suffix(".workspace") {
                    if value.starts_with("true") {
                        out.push((name.trim().to_string(), Dep::Workspace));
                    }
                } else if let Some(name) = key.strip_suffix(".path") {
                    out.push((
                        name.trim().to_string(),
                        Dep::Path(literal(value).to_string()),
                    ));
                } else {
                    let inline = value.strip_prefix('{').unwrap_or("");
                    let dep = inline
                        .split(',')
                        .filter_map(|pair| pair.split_once('='))
                        .find_map(|(k, v)| field(k.trim(), v.trim()))
                        .unwrap_or(Dep::Other);
                    out.push((key.to_string(), dep));
                }
            }
        }
    }
    out
}

/// What the field `key = value` of a dependency says of where it is, if anything.
fn field(key: &str, value: &str) -> Option<Dep> {
    match key {
        "workspace" if value.starts_with("true") => Some(Dep::Workspace),
        "path" => Some(Dep::Path(literal(value).to_string())),
        _ => None,
    }
}

/// The text of the first string literal in `value`, or `value` itself if it has none.
fn literal(value: &str) -> &str {
    value
        .split_once('"')
        .and_then(|(_, rest)| rest.split_once('"'))
        .map_or(value, |(s, _)| s)
}

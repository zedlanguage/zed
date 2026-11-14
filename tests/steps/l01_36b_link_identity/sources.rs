//! The build of zed-native names its sources (RUNTIME-build-src): the section
//! `.zed_native.build` of the runtime library ends with the BLAKE3 hash of the sources of
//! zed-native and of the workspace crates it depends on (`zed_native::sources`), so a runtime
//! library built from older sources is not taken for this build's, and gives another key of a
//! link. The hash is tested on a small workspace of a shop's till: the crate `till` depends on
//! `prices` by the workspace and on `receipt` by its path, and includes a tax table from
//! outside every crate; `stock`, a crate of the workspace, is only `till`'s dev-dependency.

use std::path::{Path, PathBuf};

use zed_native::link::build_id;
use zed_native::sources;

use super::dir;

/// Writes `text` at `path`, making its directory.
fn put(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

/// The till's workspace, written in `d` over what an earlier run left, with `n` modules in `prices`; returns the
/// directory of the crate `till`.
pub(super) fn till(d: &Path, n: usize) -> PathBuf {
    put(
        &d.join("Cargo.toml"),
        "[workspace]\nmembers = [\"till\", \"prices\", \"receipt\", \"stock\"]\n\n\
         [workspace.dependencies]\nprices = { path = \"prices\" }\n\
         stock = { path = \"stock\" }\nlibc = \"0.2\"\n",
    );
    put(
        &d.join("till/Cargo.toml"),
        "[package]\nname = \"till\"\n\n[dependencies]\nprices.workspace = true\n\
         libc.workspace = true\n\n[target.'cfg(unix)'.dependencies]\n\
         receipt = { version = \"0.1\", path = \"../receipt\" } # printed on paper\n\n\
         [dev-dependencies]\nstock.workspace = true\n",
    );
    put(
        &d.join("till/src/lib.rs"),
        "pub mod total;\npub const TAX: &str = include_str!(\"../../tax/table.txt\");\n",
    );
    put(
        &d.join("till/src/total.rs"),
        "pub fn total(a: u64, b: u64) -> u64 { a + b }\n",
    );
    put(
        &d.join("till/tests/till.rs"),
        "#[test]\nfn adds() { assert_eq!(till::total::total(1, 2), 3); }\n",
    );
    put(&d.join("tax/table.txt"), "food 5%\nother 20%\n");
    put(
        &d.join("prices/Cargo.toml"),
        "[package]\nname = \"prices\"\n",
    );
    let mut lib = String::new();
    for k in 0..n {
        lib += &format!("pub mod item{k};\n");
        put(
            &d.join(format!("prices/src/item{k}.rs")),
            &format!(
                "/// The price of item {k}, in cents.\npub const PRICE: u64 = {};\n",
                100 + k
            )
            .repeat(16),
        );
    }
    put(&d.join("prices/src/lib.rs"), &lib);
    put(
        &d.join("receipt/Cargo.toml"),
        "[package]\nname = \"receipt\"\n",
    );
    put(
        &d.join("receipt/src/lib.rs"),
        "pub const HEADER: &str = \"Till 1\";\n",
    );
    put(&d.join("stock/Cargo.toml"), "[package]\nname = \"stock\"\n");
    put(&d.join("stock/src/lib.rs"), "pub const COUNT: u64 = 12;\n");
    d.join("till")
}

/// The hash of the sources of the crate in `krate`.
pub(super) fn hash(krate: &Path) -> [u8; 32] {
    sources::of(krate).unwrap().hash
}

#[test]
fn the_runtime_library_names_the_sources_it_was_built_from() {
    let native = Path::new(env!("CARGO_MANIFEST_DIR")).join("../crates/zed-native");
    let id = build_id(&std::env::current_exe().unwrap()).unwrap();
    assert!(
        id.ends_with(&hash(&native)),
        "the section of this test's zed-native ends with the hash of its sources as they are now"
    );
    // zedc's sources, through which zed-native depends on them, and a file zedc includes
    // from outside every crate, are among them; a test's sources are not.
    let read = sources::of(&native).unwrap().read;
    let root = native.join("../..").canonicalize().unwrap();
    for wanted in [
        "crates/zed-native/src/link.rs",
        "crates/zed-native/build.rs",
        "crates/zedc/src/lib.rs",
        "crates/zed-kernel/src/lib.rs",
        "crates/zed-rt/src/lib.rs",
        "zed/grammar/syntax.peg",
    ] {
        assert!(
            read.iter()
                .any(|p| p.canonicalize().ok() == Some(root.join(wanted))),
            "{wanted} is read"
        );
    }
    for not in [
        "crates/zed-tools/src/lib.rs",
        "tests/steps/l01_36b_link_identity/sources.rs",
    ] {
        assert!(
            !read
                .iter()
                .any(|p| p.canonicalize().ok() == Some(root.join(not))),
            "{not} is not read"
        );
    }
}

#[test]
fn an_edit_in_the_crate_or_a_crate_it_depends_on_changes_the_hash() {
    let d = dir("sources-edit");
    let krate = till(&d, 3);
    // A file kept beside `src`, moved into it below; the run before left it in `src`, since
    // the test deletes nothing.
    let added = d.join("till/src/discount.rs");
    let aside = d.join("till/discount.rs");
    if added.exists() {
        std::fs::rename(&added, &aside).unwrap();
    } else if !aside.exists() {
        put(&aside, "pub const OFF: u64 = 10;\n");
    }
    let first = hash(&krate);
    assert_eq!(hash(&krate), first, "two reads of one tree give one hash");
    for edited in [
        "till/src/total.rs",
        "till/Cargo.toml",
        "prices/src/item1.rs",
        "receipt/src/lib.rs",
        "tax/table.txt",
    ] {
        let path = d.join(edited);
        let text = std::fs::read_to_string(&path).unwrap();
        std::fs::write(&path, format!("{text}// edited\n")).unwrap();
        assert_ne!(hash(&krate), first, "an edit of {edited} changes the hash");
        std::fs::write(&path, text).unwrap();
        assert_eq!(
            hash(&krate),
            first,
            "undoing the edit of {edited} gives the hash back"
        );
    }
    // A file added to `src` changes it too, since Cargo runs the build script again for it.
    std::fs::rename(&aside, &added).unwrap();
    assert_ne!(
        hash(&krate),
        first,
        "a file added to till/src changes the hash"
    );
}

#[test]
fn an_edit_outside_the_crate_and_its_dependencies_leaves_the_hash() {
    let d = dir("sources-outside");
    let krate = till(&d, 3);
    let first = hash(&krate);
    for (edited, text) in [
        ("stock/src/lib.rs", "pub const COUNT: u64 = 13;\n"),
        ("till/tests/till.rs", "#[test]\nfn adds() {}\n"),
        (
            "Cargo.toml",
            "[workspace]\nmembers = [\"till\", \"prices\", \"receipt\", \"stock\"]\n\n[workspace.dependencies]\nprices = { path = \"prices\" }\nstock = { path = \"stock\" }\nlibc = \"0.2.1\"\n",
        ),
        ("notes.txt", "count the drawer at six\n"),
    ] {
        put(&d.join(edited), text);
        assert_eq!(hash(&krate), first, "an edit of {edited} leaves the hash");
    }
}

#[test]
fn one_tree_in_two_directories_gives_one_hash() {
    let a = till(&dir("sources-here"), 3);
    let b = till(&dir("sources-there"), 3);
    assert_eq!(hash(&a), hash(&b));
}

#[test]
fn a_missing_source_directory_is_named() {
    let d = dir("sources-missing");
    let krate = till(&d, 1);
    // `receipt` moved to `register`, whose sources were never written.
    put(
        &d.join("register/Cargo.toml"),
        "[package]\nname = \"receipt\"\n",
    );
    let manifest = d.join("till/Cargo.toml");
    let text = std::fs::read_to_string(&manifest).unwrap();
    put(&manifest, &text.replace("../receipt", "../register"));
    let Err(why) = sources::of(&krate) else {
        panic!("a crate with no src directory has no sources to hash");
    };
    assert!(
        why.starts_with(&format!("{}: ", d.join("register/src").display())),
        "{why}"
    );
}

/// Whether an edit of `edited`, under `d`, changes the hash of the crate in `krate`; the edit
/// is undone after.
fn followed(d: &Path, krate: &Path, edited: &str) -> bool {
    let path = d.join(edited);
    let text = std::fs::read_to_string(&path).unwrap();
    let before = hash(krate);
    std::fs::write(&path, format!("{text}// edited\n")).unwrap();
    let after = hash(krate);
    std::fs::write(&path, text).unwrap();
    before != after
}

#[test]
fn each_way_a_manifest_names_a_dependency_is_read() {
    let receipt = "receipt/src/lib.rs";
    let prices = "prices/src/item0.rs";
    // The text after `till`'s `[package]` table, the file of a crate it may depend on, and
    // whether that crate is among its sources.
    let cases: [(&str, &str, &str, bool); 16] = [
        (
            "an inline table with a path",
            "[dependencies]\nreceipt = { path = \"../receipt\" }\n",
            receipt,
            true,
        ),
        (
            "a dotted key `.path`",
            "[dependencies]\nreceipt.path = \"../receipt\"\n",
            receipt,
            true,
        ),
        (
            "a table of its own with a path",
            "[dependencies.receipt]\npath = \"../receipt\"\n",
            receipt,
            true,
        ),
        (
            "a table of its own with a version and a path",
            "[dependencies.receipt]\nversion = \"0.1\"\npath = \"../receipt\"\n",
            receipt,
            true,
        ),
        (
            "a table of its own with a version only",
            "[dependencies.receipt]\nversion = \"0.1\"\n",
            receipt,
            false,
        ),
        (
            "a build dependency",
            "[build-dependencies]\nreceipt = { path = \"../receipt\" }\n",
            receipt,
            true,
        ),
        (
            "a build dependency of a target",
            "[target.'cfg(unix)'.build-dependencies]\nreceipt = { path = \"../receipt\" }\n",
            receipt,
            true,
        ),
        (
            "a dev-dependency",
            "[dev-dependencies]\nreceipt = { path = \"../receipt\" }\n",
            receipt,
            false,
        ),
        (
            "a dev-dependency in a table of its own",
            "[dev-dependencies.receipt]\npath = \"../receipt\"\n",
            receipt,
            false,
        ),
        (
            "a path through `.`",
            "[dependencies]\nreceipt = { path = \"./../receipt\" }\n",
            receipt,
            true,
        ),
        (
            "a registry version",
            "[dependencies]\nreceipt = \"0.1\"\n",
            receipt,
            false,
        ),
        (
            "lines commented out",
            "# [dependencies]\n# receipt = { path = \"../receipt\" }\n",
            receipt,
            false,
        ),
        (
            "the workspace's, in a table of its own",
            "[dependencies.prices]\nworkspace = true\n",
            prices,
            true,
        ),
        (
            "the workspace's, in an inline table",
            "[dependencies]\nprices = { workspace = true }\n",
            prices,
            true,
        ),
        (
            "the workspace's, by a name the workspace does not list",
            "[dependencies]\nregister.workspace = true\n",
            prices,
            false,
        ),
        (
            "another table",
            "[features]\nreceipt = []\n",
            receipt,
            false,
        ),
    ];
    for (k, (case, deps, edited, want)) in cases.into_iter().enumerate() {
        let d = dir(&format!("sources-form-{k}"));
        let krate = till(&d, 1);
        put(
            &krate.join("Cargo.toml"),
            &format!("[package]\nname = \"till\"\n\n{deps}"),
        );
        assert_eq!(followed(&d, &krate, edited), want, "{case}");
    }
}

#[test]
fn a_directory_reached_again_through_a_symbolic_link_is_read_once() {
    let plain = till(&dir("sources-plain"), 1);
    let linked = till(&dir("sources-linked"), 1);
    let again = linked.join("src/again");
    if again.symlink_metadata().is_err() {
        std::os::unix::fs::symlink(".", &again).unwrap();
    }
    assert_eq!(hash(&linked), hash(&plain));
}

#[test]
fn an_include_the_scan_does_not_follow_leaves_those_after_it() {
    let d = dir("sources-includes");
    let krate = till(&d, 1);
    // A literal naming no file, a path built by a macro, a literal with an escape, the include
    // of the tax table, and a literal that never ends, last in the file.
    put(
        &krate.join("src/lib.rs"),
        "pub mod total;\n\
         // include_str!(\"no-such-file.txt\") names no file.\n\
         pub const BUILT: &str = include_str!(concat!(env!(\"OUT_DIR\"), \"/built.txt\"));\n\
         pub const ESCAPED: &str = include_str!(\"..\\u{2f}notes.txt\");\n\
         pub const TAX: &str = include_str!(\"../../tax/table.txt\");\n\
         // include_str!(\"never ends",
    );
    assert!(followed(&d, &krate, "tax/table.txt"));
}

#[test]
fn a_crate_outside_every_workspace_is_named() {
    let krate = Path::new("/no-such-directory/crate");
    assert_eq!(
        sources::of(krate).err(),
        Some(
            "/no-such-directory/crate: no directory above it holds a Cargo.toml with a \
             [workspace] table"
                .to_string()
        )
    );
}

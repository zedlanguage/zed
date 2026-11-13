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
use zed_tests::scaling::{self, FACTOR};

use super::dir;

/// Writes `text` at `path`, making its directory.
fn put(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

/// The till's workspace, written in `d` over what an earlier run left, with `n` modules in `prices`; returns the
/// directory of the crate `till`.
fn till(d: &Path, n: usize) -> PathBuf {
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
fn hash(krate: &Path) -> [u8; 32] {
    sources::of(krate).unwrap().hash
}

#[test]
fn the_runtime_library_names_the_sources_it_was_built_from() {
    let native = Path::new(env!("CARGO_MANIFEST_DIR")).join("../crates/zed-native");
    let id = build_id(&std::env::current_exe().unwrap()).unwrap();
    // The grammar zedc embeds is read from the spec by its build script, and added to the hash.
    let spec = zed_tests::fences::spec();
    let grammar = [spec.syn_text.clone() + "\n", spec.doc_text.clone() + "\n"];
    let built = sources::with_grammar(hash(&native), &[&grammar[0], &grammar[1]]);
    assert!(
        id.ends_with(&built),
        "the section of this test's zed-native ends with the hash of its sources and the \
         spec's grammar as they are now"
    );
    // zedc's sources, through which zed-native depends on them, and the module the build
    // scripts read the grammar with, are among them; a test's sources are not.
    let read = sources::of(&native).unwrap().read;
    let root = native.join("../..").canonicalize().unwrap();
    for wanted in [
        "crates/zed-native/src/link.rs",
        "crates/zed-native/build.rs",
        "crates/zedc/src/lib.rs",
        "crates/zed-kernel/src/lib.rs",
        "crates/zed-rt/src/lib.rs",
        "crates/zedc-syntax/build.rs",
        "crates/zedc-syntax/spec_grammar.rs",
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

/// The grammar added to the hash changes it with each edit of a part, and with text moved from
/// one part to the other; the same grammar gives the same hash.
#[test]
fn an_edit_of_the_grammar_changes_the_hash() {
    let base = [7u8; 32];
    let first = sources::with_grammar(base, &["Unit <- A\n", "Doc <- B\n"]);
    assert_eq!(
        sources::with_grammar(base, &["Unit <- A\n", "Doc <- B\n"]),
        first
    );
    for other in [
        ["Unit <- A B\n", "Doc <- B\n"],
        ["Unit <- A\n", "Doc <- C\n"],
        ["Unit <- A\nDoc <- B\n", ""],
    ] {
        assert_ne!(sources::with_grammar(base, &other), first, "{other:?}");
    }
    assert_ne!(
        sources::with_grammar([8u8; 32], &["Unit <- A\n", "Doc <- B\n"]),
        first
    );
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

#[test]
fn the_hash_of_the_sources_scales() {
    let n = 40;
    let trees = scaling::inputs(n, |m| till(&dir(&format!("sources-scaling-{m}")), m));
    assert_eq!(trees.len(), 2, "sizes {n} and {}", FACTOR * n);
    scaling::check(&format!("the sources of a crate of {n} modules"), n, |m| {
        std::hint::black_box(hash(&trees[&m]));
    });
}

/// Adding the grammar to the hash reads each byte of it once. It allocates nothing, so its bytes
/// are not measured.
#[test]
fn adding_the_grammar_scales() {
    let n = 20_000;
    let texts = scaling::inputs(n, |m| "Rule <- A / B\n".repeat(m));
    let what = format!("the hash of a grammar of {n} rules");
    scaling::check_instructions_only(&what, n, 1, |m| {
        std::hint::black_box(sources::with_grammar([0; 32], &[&texts[&m], "Doc <- B\n"]));
    });
}

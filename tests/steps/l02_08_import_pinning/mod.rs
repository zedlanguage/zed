//! Step L2.8: import pinning. The build writes into each import that has no pin the content
//! address of the unit it names, `import pricing @hash("…");`, checks every pin it finds and
//! stops at one that no longer matches, and pins the package's prelude unit, as it pins any
//! unit, in the pin file `zed.pins` at the package root, the one file every later pin goes in.

mod bench;
mod combinations;
mod command;
mod imports;
mod pin_file;
mod prelude;
mod scaling;

use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

use zedc::query::Db;
use zedc::unit::{Memory, Package, load};

/// The files `files`, each a name under the root and its text.
fn files(files: &[(&str, &str)]) -> Memory {
    Memory(
        files
            .iter()
            .map(|&(name, text)| (name.to_string(), Arc::from(text)))
            .collect::<HashMap<_, _>>(),
    )
}

/// The package of `fs` that the unit `main` reaches.
fn package(fs: &[(&str, &str)]) -> Package {
    load(&mut Db::new(), &files(fs), &["main"])
}

/// The problems of the package `p` as `zedc` prints them, but for the forms of later steps.
fn mistakes(p: &Package) -> Vec<String> {
    p.report(Path::new(""))
        .into_iter()
        .filter(|m| !zed_tests::is_not_yet(m))
        .collect()
}

/// The address the pin `@hash("…")` in `text` names, the `n`-th (from 0) in the text.
fn pin_in(text: &str, n: usize) -> String {
    let at = text
        .match_indices("@hash(\"")
        .nth(n)
        .unwrap_or_else(|| panic!("no pin {n} in\n{text}"))
        .0
        + "@hash(\"".len();
    let hex = &text[at..at + 64];
    assert!(
        hex.bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase()),
        "{hex}"
    );
    assert_eq!(&text[at + 64..at + 66], "\")", "{text}");
    hex.to_string()
}

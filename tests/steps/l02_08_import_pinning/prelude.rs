//! The prelude unit is pinned as an ordinary unit is: its address, in the pin file under the
//! kind `prelude` and the unit's path, written when the file has none and checked when it has.

use zedc::pin::PIN_FILE;

use super::{mistakes, package};

/// The package's prelude unit, which the manifest names.
const STD: &str = "double(x: f64) = x * 2.0;\nhalf(x: f64) = x / 2.0;\n";

/// A unit that runs and reads nothing of the prelude.
const MAIN: &str = "main() -> (stdout: Lines) {}\n";

/// The first line of every pin file zedc writes.
const HEADER: &str = "// Pins written by zedc: each line is `<kind> <address> <key>`, and each \
                      build checks it. Delete a line, and the next build writes it again.\n";

/// The pin file a build of the package with prelude `std` as `std` writes.
fn written(std: &str) -> String {
    let p = package(&[
        ("zed.manifest", "prelude = \"std\";\n"),
        ("main.zed", MAIN),
        ("std.zed", std),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    p.writes.pin_file.clone().expect("the prelude is pinned")
}

/// The address in the prelude line of the pin file `text`.
fn address(text: &str) -> &str {
    let line = text.lines().find(|l| l.starts_with("prelude ")).unwrap();
    &line["prelude ".len().."prelude ".len() + 64]
}

#[test]
fn the_build_writes_the_prelude_pin_into_the_pin_file() {
    let text = written(STD);
    let h = address(&text);
    assert_eq!(text, format!("{HEADER}prelude {h} std\n"));
    // The address is the one an import of the same unit is pinned to.
    let p = package(&[
        ("main.zed", "import std;\nmain() -> (stdout: Lines) {}\n"),
        ("std.zed", STD),
    ]);
    assert_eq!(super::pin_in(&p.pinned("main").unwrap(), 0), h);
}

#[test]
fn a_matching_prelude_pin_is_checked_and_the_file_is_not_written() {
    let pins = written(STD);
    let p = package(&[
        ("zed.manifest", "prelude = \"std\";\n"),
        (PIN_FILE, &pins),
        ("main.zed", MAIN),
        ("std.zed", &format!("// the shop's prelude\n{STD}")),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert_eq!(p.writes.pin_file, None);
}

#[test]
fn a_changed_prelude_makes_its_pin_stale_at_the_manifest() {
    let pins = written(STD);
    let old = address(&pins).to_string();
    let changed = "double(x: f64) = x + x + 0.0;\nhalf(x: f64) = x / 2.0;\n";
    let new = address(&written(changed)).to_string();
    assert_ne!(old, new);
    let p = package(&[
        ("zed.manifest", "// the shop\nprelude = \"std\";\n"),
        (PIN_FILE, &pins),
        ("main.zed", MAIN),
        ("std.zed", changed),
    ]);
    assert_eq!(
        mistakes(&p),
        vec![format!(
            "zed.manifest:2:11: the prelude unit `std` is pinned in the pin file `zed.pins` to \
             the content address {old}, and it now has the address {new}: its exports, or a \
             declaration they use, changed in `std.zed` after the pin was written. A pinned \
             unit is checked and never read afresh, so the build stops here. Repairs: to build \
             with the prelude as it is now, delete the line `prelude {old} std` from \
             `zed.pins`, and the next build writes the new address; or, to build with the \
             prelude as it was pinned, restore `std.zed` to that version."
        )]
    );
    assert_eq!(p.writes.pin_file, None);
}

#[test]
fn a_new_prelude_path_replaces_the_old_pin_and_no_prelude_drops_it() {
    let pins = written(STD);
    let p = package(&[
        ("zed.manifest", "prelude = \"base\";\n"),
        (PIN_FILE, &pins),
        ("main.zed", MAIN),
        ("base.zed", STD),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    let h = address(&pins);
    assert_eq!(
        p.writes.pin_file.as_deref(),
        Some(format!("{HEADER}prelude {h} base\n").as_str())
    );
    let p = package(&[
        ("zed.manifest", "// no prelude\n"),
        (PIN_FILE, &pins),
        ("main.zed", "import std;\nmain() -> (stdout: Lines) {}\n"),
        ("std.zed", STD),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert_eq!(p.writes.pin_file.as_deref(), Some(HEADER));
}

#[test]
fn pins_of_kinds_a_later_step_writes_are_kept_as_they_are() {
    let proof = format!("proof {} sorted(xs) == xs\n", "ab".repeat(32));
    let p = package(&[
        ("zed.manifest", "prelude = \"std\";\n"),
        (PIN_FILE, &format!("{HEADER}{proof}")),
        ("main.zed", MAIN),
        ("std.zed", STD),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    let text = p.writes.pin_file.clone().unwrap();
    let h = address(&text);
    assert_eq!(text, format!("{HEADER}prelude {h} std\n{proof}"));
}

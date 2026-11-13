//! An imported unit, a root and the manifest are loaded as source (DESIGN.md sec:lexical):
//! "Source is UTF-8 in Unicode Normalization Form C; a file that is not NFC is rejected rather
//! than normalized ... a leading byte order mark is rejected for the same reason." A file so
//! rejected cannot be read, and the error names it with the line and column of the rejection, as
//! `pricing.zed:2:7:`.

use std::path::PathBuf;

use zedc::query::Db;
use zedc::unit::{Dir, Files, load};

/// A package directory of its own for test `name`, holding `files` as bytes, under the test
/// target's scratch directory; files in it are overwritten by each run, never deleted.
fn package_dir(name: &str, files: &[(&str, &[u8])]) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("l02_03_source")
        .join(name);
    for (file, bytes) in files {
        let path = d.join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, bytes).unwrap();
    }
    d
}

/// The lines of `zedc run app/main.zed` in a package whose unit `pricing` is `pricing`, that
/// say why an import is refused.
fn refused_import(name: &str, pricing: &[u8]) -> Vec<String> {
    let d = package_dir(
        name,
        &[
            ("zed.manifest", b"// the shop\n"),
            (
                "app/main.zed",
                b"import pricing.{net};\nmain(m: MainArgs) {}\n",
            ),
            ("pricing.zed", pricing),
        ],
    );
    let main = d.join("app/main.zed");
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(
        &["run", main.to_str().unwrap()],
        &mut "".as_bytes(),
        &mut out,
        &mut err,
    );
    let err = String::from_utf8(err).unwrap();
    assert_eq!(status, 1, "{err}");
    let root = d.display();
    err.lines()
        .filter(|l| l.contains("cannot be imported"))
        .map(|l| l.replace(&format!("{root}/"), ""))
        .collect()
}

#[test]
fn an_imported_unit_that_is_not_utf8_is_refused_at_its_line_and_column() {
    // Latin-1 `é` in a comment, as an editor set to Windows-1252 saves it.
    assert_eq!(
        refused_import("utf8", b"net(g: f64) = g / 1.2;\n// caf\xE9 prices\n"),
        [
            "app/main.zed:1:1: the unit `pricing` cannot be imported: pricing.zed:2:7: a Zed \
             file is UTF-8 text, and the bytes here, E9 in hexadecimal, are not a UTF-8 \
             character, so the file cannot be read. Save the file as UTF-8 in your editor, or \
             replace these bytes with the character they were meant to be."
        ]
    );
}

#[test]
fn an_imported_unit_with_a_byte_order_mark_is_refused() {
    // Notepad's UTF-8 with a byte order mark.
    assert_eq!(
        refused_import("bom", b"\xEF\xBB\xBFnet(g: f64) = g / 1.2;\n"),
        [
            "app/main.zed:1:1: the unit `pricing` cannot be imported: pricing.zed:1:1: the \
             file starts with a byte order mark (the bytes EF BB BF), and a Zed file may not, \
             since the same program would then be stored in two ways. Save the file as UTF-8 \
             without a byte order mark (in many editors this is \"UTF-8\" rather than \"UTF-8 \
             with BOM\")."
        ]
    );
}

#[test]
fn an_imported_unit_not_in_nfc_is_refused_at_the_first_sequence_nfc_changes() {
    // `é` written as `e` and a combining acute accent, as macOS file names give it.
    assert_eq!(
        refused_import(
            "nfc",
            "net(g: f64) = g / 1.2;\n// cafe\u{301} prices\n".as_bytes()
        ),
        [
            "app/main.zed:1:1: the unit `pricing` cannot be imported: pricing.zed:2:7: these \
             characters are not in Unicode Normalization Form C (NFC), which spells them as \
             U+00E9. A Zed file must be in NFC, so that two names that look the same are the \
             same name. Retype the characters, or have your editor save the file in NFC."
        ]
    );
}

#[test]
fn a_root_and_a_manifest_that_do_not_load_are_reported_with_their_position() {
    let d = package_dir(
        "root",
        &[
            ("zed.manifest", b"// the shop\n"),
            ("main.zed", b"x = 1;\ny = \"\xFF\";\n"),
        ],
    );
    let p = load(&mut Db::new(), &Dir(d.clone()), &["main"]);
    assert_eq!(
        p.report(std::path::Path::new("")),
        [
            "main.zed:2:6: a Zed file is UTF-8 text, and the bytes here, FF in hexadecimal, are not a \
          UTF-8 character, so the file cannot be read. Save the file as UTF-8 in your editor, or \
          replace these bytes with the character they were meant to be."
        ]
    );
    let d = package_dir(
        "manifest",
        &[
            ("zed.manifest", b"\xEF\xBB\xBF// the shop\n"),
            ("main.zed", b"x = 1;\n"),
        ],
    );
    let p = load(&mut Db::new(), &Dir(d), &["main"]);
    assert_eq!(
        p.report(std::path::Path::new("")),
        [
            "zed.manifest:1:1: the file starts with a byte order mark (the bytes EF BB BF), and \
             a Zed file may not, since the same program would then be stored in two ways. Save \
             the file as UTF-8 without a byte order mark (in many editors this is \"UTF-8\" \
             rather than \"UTF-8 with BOM\")."
        ]
    );
}

#[test]
fn an_imported_unit_with_crlf_line_ends_loads() {
    // A file saved on Windows: `\r\n` is one line break, and the import resolves.
    let d = package_dir(
        "crlf",
        &[
            ("zed.manifest", b"// the shop\r\n"),
            ("pricing.zed", b"// prices\r\nnet(g: f64) = g / 1.2;\r\n"),
            ("main.zed", b"import pricing.{net};\r\nx = net(1.2);\r\n"),
        ],
    );
    let p = load(&mut Db::new(), &Dir(d), &["main"]);
    let pricing = p.unit("pricing").unwrap();
    assert_eq!(
        pricing.text.as_ref().unwrap().as_deref().unwrap(),
        "// prices\nnet(g: f64) = g / 1.2;\n"
    );
    assert!(pricing.resolved.is_some());
}

#[test]
fn reading_a_unit_as_source_is_linear_in_its_bytes() {
    // A unit of `k` lines in NFC with `\r\n` line ends and accented strings, so that the UTF-8,
    // NFC and line-end passes each read every byte; the files are written before timing.
    let n = 4000;
    let unit = |k: usize| -> Vec<u8> {
        (0..k)
            .flat_map(|i| format!("cafe{i} = \"crème brûlée\";\r\n").into_bytes())
            .collect()
    };
    let dirs: Vec<(usize, Dir)> = [n, 8 * n]
        .into_iter()
        .map(|k| {
            let d = package_dir(&format!("scaling{k}"), &[("pricing.zed", &unit(k))]);
            (k, Dir(d))
        })
        .collect();
    let dir = |k: usize| &dirs.iter().find(|(m, _)| *m == k).unwrap().1;
    for &(k, ref d) in &dirs {
        let text = d.read("pricing.zed").unwrap().unwrap();
        assert_eq!(text.lines().count(), k);
        assert!(!text.contains('\r'));
    }
    zed_tests::scaling::check_order("Dir::read of a unit of n lines", n, 1, |k| {
        std::hint::black_box(dir(k).read("pricing.zed"));
    });
}

//! `--option <name>` on the command line turns on an option the manifest declares; one it does
//! not declare is a usage error naming those it does; and the options a build turns on leave
//! the pins as they are.

use std::path::{Path, PathBuf};

/// A package directory of its own for test `name`, holding `files`, under the test target's
/// scratch directory; files in it are overwritten by each run, never deleted.
fn package_dir(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("l02_08d")
        .join(name);
    for (file, text) in files {
        let path = d.join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    d
}

/// Runs `zedc <words>` and gives its status, standard output and standard error.
fn zedc(words: &[&str]) -> (u8, String, String) {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(words, &mut "".as_bytes(), &mut out, &mut err);
    (
        status,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

/// The lines of `err` that are not about forms of later steps.
fn mistakes(err: &str) -> Vec<&str> {
    err.lines().filter(|l| !zed_tests::is_not_yet(l)).collect()
}

/// A package whose unit `speed` reads the option `fast`, imported by `app/main.zed`.
fn package(name: &str) -> PathBuf {
    package_dir(
        name,
        &[
            ("zed.manifest", "options = \"fast, counting\";\n"),
            (
                "app/main.zed",
                "import speed.{label};\nmain(m: MainArgs) { m.stdout <- label() ++ \"\\n\"; }\n",
            ),
            (
                "speed.zed",
                "label() = if build.options.fast { \"fast\" } else { \"slow\" };\n",
            ),
            (
                "app/solo.zed",
                "main(m: MainArgs) {\n  m.stdout <- if build.options.fast { \"fast\" } \
                 else { \"slow\" };\n}\n",
            ),
        ],
    )
}

/// The text of `file`.
fn read(file: &Path) -> String {
    String::from_utf8(std::fs::read(file).unwrap()).unwrap()
}

#[test]
fn an_option_turned_on_is_read() {
    let d = package("read");
    let solo = d.join("app/solo.zed");
    let solo = solo.to_str().unwrap();
    for (words, said) in [
        (&["run", solo][..], "slow\n"),
        (&["run", solo, "--option", "fast"][..], "fast\n"),
        (
            &["run", solo, "--option", "counting", "--option", "fast"][..],
            "fast\n",
        ),
        (&["run", solo, "--option", "counting"][..], "slow\n"),
    ] {
        let (status, out, err) = zedc(words);
        assert_eq!((status, out.as_str()), (0, said), "{words:?}: {err}");
    }
}

#[test]
fn an_option_turned_on_leaves_the_pins_as_they_are() {
    let d = package("pins");
    let main = d.join("app/main.zed");
    let main = main.to_str().unwrap();
    // The run stops at the import, which this step does not yet link (step L2.4), after
    // writing the pins.
    let (_, _, err) = zedc(&["run", main]);
    assert_eq!(mistakes(&err), Vec::<&str>::new(), "{err}");
    let pinned = read(Path::new(main));
    assert!(pinned.contains("@hash(\""), "{pinned}");
    let (_, _, err) = zedc(&["run", main, "--option", "fast"]);
    assert_eq!(mistakes(&err), Vec::<&str>::new(), "{err}");
    // The unit reading the option has the address it has with every option off.
    assert_eq!(read(Path::new(main)), pinned);
}

#[test]
fn an_option_the_manifest_does_not_declare_is_a_usage_error() {
    let d = package("undeclared");
    let main = d.join("app/main.zed");
    let (status, out, err) = zedc(&["run", main.to_str().unwrap(), "--option", "quick"]);
    assert_eq!((status, out.as_str()), (2, ""));
    assert_eq!(
        err,
        "`--option quick`: the package declares the options `fast` and `counting`. Declare it \
         in the manifest, as `options = \"fast, counting, quick\";`, or remove \
         `--option quick`.\n"
    );
    // A loose file declares no option.
    let loose = package_dir("loose", &[("one.zed", "main(m: MainArgs) {}\n")]).join("one.zed");
    let (status, _, err) = zedc(&["run", loose.to_str().unwrap(), "--option", "fast"]);
    assert_eq!(status, 2, "{err}");
    assert!(err.contains("the package declares no option"), "{err}");
}

#[test]
fn option_needs_a_name_after_it() {
    let d = package("last");
    let main = d.join("app/main.zed");
    let (status, _, err) = zedc(&["run", main.to_str().unwrap(), "--option"]);
    assert_eq!(status, 2, "{err}");
    assert!(
        err.starts_with("`--option` is the last word of the command line"),
        "{err}"
    );
}

#[test]
fn the_manifest_lists_each_option_once_by_name() {
    use zedc::unit::manifest;
    assert_eq!(
        manifest("options = \"fast, counting\";\n").unwrap().options,
        ["fast", "counting"]
    );
    assert_eq!(
        manifest("options = \"\";\n").unwrap().options,
        Vec::<String>::new()
    );
    for (text, why) in [
        (
            "options = \"fast, fast\";\n",
            "the entry `options` lists `fast` twice",
        ),
        (
            "options = \"fast,\";\n",
            "the entry `options` holds an empty name",
        ),
        (
            "options = \"fast, short.addresses\";\n",
            "the option `short.addresses` is not a name",
        ),
        ("options = \"if\";\n", "the option `if` is not a name"),
    ] {
        let errors = manifest(text).unwrap_err();
        assert_eq!(errors.len(), 1, "{text}");
        assert!(
            errors[0].message.starts_with(why),
            "{text}: {}",
            errors[0].message
        );
    }
}

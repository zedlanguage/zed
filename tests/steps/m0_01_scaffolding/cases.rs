//! Completeness cases for the step folders and their targets (TEST-complete-m0, author P189):
//! each way `is_step_name`, `folders`, `block`, `splice`, `targets`, `drift` and the
//! `step_targets` tool can be called, at its smallest form. The case list is `COMPLETENESS.md`.

use std::collections::BTreeSet;
use std::fs;
use std::os::unix::ffi::OsStrExt;
use std::path::{Path, PathBuf};

use zed_tests::is_step_name;
use zed_tools::step_targets::{BEGIN, END, block, drift, folders, run, splice, targets};

/// The set of `names`.
fn set(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(|n| n.to_string()).collect()
}

/// `name`'s target as `block` writes it.
fn target(name: &str) -> (String, String) {
    (name.to_string(), format!("steps/{name}/mod.rs"))
}

/// A manifest whose block of targets is `body`.
fn manifest(body: &str) -> String {
    format!("[package]\nname = \"t\"\n{BEGIN}\n{body}{END}\n[dev-dependencies]\n")
}

#[test]
fn step_names_by_stage_step_letter_and_description() {
    let good = [
        ("stage m0", "m0_01_scaffolding"),
        ("stage s", "s_01_port_catalog"),
        ("lowest layer", "l01_01_source_loading"),
        ("layer 29", "l29_01_lowering"),
        ("layer 30", "l30_01_editor"),
        ("the last layer, 40", "l40_01_layout"),
        ("a step's letter", "l01_39a_bit_words"),
        ("a letter on stage s", "s_01f_import_graph"),
        ("a letter on stage m0", "m0_10a_laws"),
        ("step 99", "l02_99_x"),
        ("digits in the description", "l01_36a_x86_64"),
        (
            "an underscore inside the description",
            "l01_10_lambdas_types_else_tuples",
        ),
        ("two underscores inside the description", "l01_10_a__b"),
        ("a description of one letter", "m0_01_a"),
    ];
    for (case, name) in good {
        assert!(is_step_name(name), "{case}: {name} is well named");
    }
    let bad = [
        ("empty", ""),
        ("no description", "m0_01"),
        ("empty description", "m0_01_"),
        ("description begins with an underscore", "m0_01__a"),
        ("description ends with an underscore", "m0_01_a_"),
        ("upper case in the description", "m0_01_Scaffolding"),
        ("a hyphen in the description", "m0_01_a-b"),
        (
            "a letter beyond ASCII in the description",
            "m0_01_caf\u{e9}",
        ),
        ("upper case stage", "M0_01_a"),
        ("unknown stage", "x1_01_a"),
        ("stage m1", "m1_01_a"),
        ("layer 0", "l00_01_a"),
        ("layer 41, past the last", "l41_01_a"),
        ("layer of one digit", "l1_01_a"),
        ("layer of three digits", "l001_01_a"),
        ("step 00", "m0_00_a"),
        ("step of one digit", "m0_1_a"),
        ("step of three digits", "m0_001_a"),
        ("step with a sign", "m0_+1_a"),
        ("step with two letters", "m0_01ab_a"),
        ("step with an upper case letter", "m0_01A_a"),
        ("step that is only a letter", "m0_a_b"),
        (
            "a letter beyond ASCII after the layer letter",
            "l\u{e9}1_01_a",
        ),
    ];
    for (case, name) in bad {
        assert!(!is_step_name(name), "{case}: {name} is badly named");
    }
}

/// A fresh, empty directory for test `name` in the test target's scratch directory.
fn scratch(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("m0_01_cases_{name}"));
    if dir.exists() {
        fs::remove_dir_all(&dir).expect("clearing an old test directory");
    }
    fs::create_dir_all(&dir).expect("making a test directory");
    dir
}

#[test]
fn folders_lists_subdirectories_only_in_byte_order() {
    let dir = scratch("folders");
    assert_eq!(folders(&dir), Ok(BTreeSet::new()), "an empty directory");
    for d in ["l01_02_b", "L_upper", "m0_01_a", "l01_01_a"] {
        fs::create_dir(dir.join(d)).unwrap();
    }
    fs::write(dir.join("l01_03_file"), "a file is not a step folder").unwrap();
    let found: Vec<String> = folders(&dir).unwrap().into_iter().collect();
    assert_eq!(found, ["L_upper", "l01_01_a", "l01_02_b", "m0_01_a"]);
    let missing = dir.join("no_such_dir");
    let err = folders(&missing).unwrap_err();
    assert!(err.starts_with(&missing.display().to_string()), "{err}");
    let file = dir.join("l01_03_file");
    assert!(folders(&file).is_err(), "a file is not a directory");
    // A folder whose name is not UTF-8 is refused with its name, not skipped.
    let raw = std::ffi::OsStr::from_bytes(b"l01_04_\xff");
    fs::create_dir(dir.join(raw)).unwrap();
    assert_eq!(
        folders(&dir).unwrap_err(),
        "folder name not UTF-8: \"l01_04_\\xFF\""
    );
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn block_writes_one_target_per_folder_in_set_order() {
    assert_eq!(block(&BTreeSet::new()), "", "no folders");
    assert_eq!(
        block(&set(&["m0_01_a"])),
        "[[test]]\nname = \"m0_01_a\"\npath = \"steps/m0_01_a/mod.rs\"\n"
    );
    let two = block(&set(&["m0_01_a", "l01_01_a"]));
    assert!(two.find("l01_01_a").unwrap() < two.find("m0_01_a").unwrap());
}

#[test]
fn splice_replaces_only_the_lines_between_the_markers() {
    let toml = manifest("old lines\n");
    assert_eq!(splice(&toml, ""), Ok(manifest("")), "an empty block");
    assert_eq!(splice(&toml, "new\n"), Ok(manifest("new\n")));
    // A second pair of markers after the first is left as it is.
    let twice = format!("{}{}", manifest("a\n"), manifest("b\n"));
    assert_eq!(
        splice(&twice, "c\n").unwrap(),
        format!("{}{}", manifest("c\n"), manifest("b\n"))
    );
    // The markers must be whole lines: `END` before `BEGIN`, or a marker with no line break, is
    // not found.
    let reversed = format!("{END}\n{BEGIN}\n");
    assert!(splice(&reversed, "").unwrap_err().contains("after"));
    let no_break = format!("{BEGIN}\n{END}");
    assert!(splice(&no_break, "").unwrap_err().contains(END));
    let begin_no_break = BEGIN.to_string();
    assert!(
        splice(&begin_no_break, "")
            .unwrap_err()
            .contains("has no line")
    );
}

#[test]
fn targets_reads_names_and_paths_and_skips_every_other_line() {
    assert_eq!(targets(&manifest("")), Ok(vec![]), "an empty block");
    let spaced = "# a comment\n[[test]]\nname=\"a\"\n\npath   =   \"p\"  \nharness = false\n";
    assert_eq!(
        targets(&manifest(spaced)),
        Ok(vec![("a".to_string(), "p".to_string())]),
        "no spaces, many spaces, a comment, a blank line and another key"
    );
    // A key that only begins with `name` or `path` is another key.
    let longer = "names = \"x\"\nname = \"a\"\npaths = \"y\"\npath = \"p\"\n";
    assert_eq!(
        targets(&manifest(longer)).unwrap(),
        [("a".to_string(), "p".to_string())]
    );
    // Text outside the markers is not read.
    let outside = format!("name = \"z\"\n{}path = \"q\"\n", manifest(""));
    assert_eq!(targets(&outside), Ok(vec![]));
    assert_eq!(
        targets(&manifest("path = \"p\"\n")).unwrap_err(),
        "tests/Cargo.toml: path p has no name before it"
    );
    assert_eq!(
        targets(&manifest("name = \"a\"\n")).unwrap_err(),
        "tests/Cargo.toml: target a has no path"
    );
    // A second name before a path replaces the first.
    assert_eq!(
        targets(&manifest("name = \"a\"\nname = \"b\"\npath = \"p\"\n")).unwrap(),
        [("b".to_string(), "p".to_string())]
    );
    // A value that is not a quoted string is not read as a name or a path.
    assert_eq!(
        targets(&manifest("name = a\npath = 'p'\nname = \"\npath = \"\"\n")).unwrap_err(),
        "tests/Cargo.toml: path  has no name before it"
    );
}

#[test]
fn drift_of_matching_and_empty_lists_is_empty() {
    assert!(drift(&BTreeSet::new(), &[]).is_empty(), "nothing at all");
    assert!(drift(&set(&["a"]), &[target("a")]).is_empty(), "one");
    assert!(
        drift(&set(&["a", "b"]), &[target("b"), target("a")]).is_empty(),
        "targets in another order than the folders"
    );
    assert_eq!(
        drift(&BTreeSet::new(), &[target("a")]),
        ["target a in tests/Cargo.toml has no folder tests/steps/a"],
        "no folders"
    );
    assert_eq!(
        drift(&set(&["a"]), &[]),
        ["folder tests/steps/a has no [[test]] target in tests/Cargo.toml: run step_targets"],
        "no targets"
    );
}

#[test]
fn drift_reports_each_problem_of_one_target_together() {
    // Listed three times, the second time with another path and the third with no folder: one
    // line for each repeat, and the path line where it applies.
    let t = [
        target("a"),
        ("a".to_string(), "steps/b/mod.rs".to_string()),
        target("a"),
    ];
    assert_eq!(
        drift(&set(&["a"]), &t),
        [
            "target a is listed twice in tests/Cargo.toml",
            "target a has the path steps/b/mod.rs, not steps/a/mod.rs",
            "target a is listed twice in tests/Cargo.toml",
        ]
    );
    // No folder and the wrong path at once.
    assert_eq!(
        drift(&BTreeSet::new(), &[("z".to_string(), "x".to_string())]),
        [
            "target z in tests/Cargo.toml has no folder tests/steps/z",
            "target z has the path x, not steps/z/mod.rs",
        ]
    );
}

/// A repository root holding `tests/Cargo.toml` with `body` between the markers and the step
/// folders `steps`.
fn repo(name: &str, body: &str, steps: &[&str]) -> PathBuf {
    let root = scratch(name);
    fs::create_dir_all(root.join("tests/steps")).unwrap();
    for s in steps {
        fs::create_dir(root.join("tests/steps").join(s)).unwrap();
    }
    fs::write(root.join("tests/Cargo.toml"), manifest(body)).unwrap();
    root
}

/// `step_targets` run with `args`, then `root` appended unless `root` is `None`.
fn tool(args: &[&str], root: Option<&Path>) -> (Result<bool, String>, String) {
    let mut all: Vec<String> = args.iter().map(|a| a.to_string()).collect();
    all.extend(root.map(|r| r.display().to_string()));
    let mut out = String::new();
    (run(&all, &mut out), out)
}

#[test]
fn the_tool_checks_writes_and_refuses_bad_arguments() {
    let root = repo("tool", "", &["m0_01_a", "l01_01_a"]);
    let manifest_path = root.join("tests/Cargo.toml");
    let shown = manifest_path.display().to_string();
    // --check before writing: one line per folder, and failure.
    let (r, out) = tool(&["--check"], Some(&root));
    assert_eq!(r, Ok(false));
    assert_eq!(out.lines().count(), 2, "{out}");
    // Writing, then writing again, then checking.
    let (r, out) = tool(&[], Some(&root));
    assert_eq!(
        (r, out),
        (Ok(true), format!("{shown}: wrote 2 step targets\n"))
    );
    let written = fs::read_to_string(&manifest_path).unwrap();
    assert_eq!(written, manifest(&block(&set(&["m0_01_a", "l01_01_a"]))));
    let (r, out) = tool(&[], Some(&root));
    assert_eq!(
        (r, out),
        (Ok(true), format!("{shown}: 2 step targets, unchanged\n"))
    );
    assert_eq!(tool(&["--check"], Some(&root)), (Ok(true), String::new()));
    // A folder removed: --check names its target and fails.
    fs::remove_dir(root.join("tests/steps/l01_01_a")).unwrap();
    let (r, out) = tool(&["--check"], Some(&root));
    assert_eq!(r, Ok(false));
    assert_eq!(
        out,
        "target l01_01_a in tests/Cargo.toml has no folder tests/steps/l01_01_a\n"
    );
    // With no root the tool reads this repository; --check writes nothing there.
    assert_eq!(tool(&["--check"], None), (Ok(true), String::new()));
    // Arguments: two roots, or a flag that is not --check read as a root, are refused.
    let usage = Err("usage: step_targets [--check] [ROOT]".to_string());
    assert_eq!(tool(&["a", "b"], None).0, usage);
    assert_eq!(tool(&["--check", "a", "b"], None).0, usage);
    let (r, _) = tool(&["--write"], None);
    assert!(r.unwrap_err().starts_with("--write/tests/Cargo.toml"));
    // A root with no manifest, or a manifest with no markers, is an error and writes nothing.
    let bare = scratch("tool_bare");
    assert!(tool(&[], Some(&bare)).0.unwrap_err().contains("Cargo.toml"));
    fs::create_dir_all(bare.join("tests")).unwrap();
    fs::write(bare.join("tests/Cargo.toml"), manifest("")).unwrap();
    let no_steps = tool(&[], Some(&bare)).0.unwrap_err();
    assert!(no_steps.contains("tests/steps"), "{no_steps}");
    fs::create_dir(bare.join("tests/steps")).unwrap();
    fs::write(bare.join("tests/Cargo.toml"), "[package]\n").unwrap();
    assert!(
        tool(&[], Some(&bare))
            .0
            .unwrap_err()
            .contains("has no line")
    );
    assert!(
        tool(&["--check"], Some(&bare))
            .0
            .unwrap_err()
            .contains("has no line")
    );
    assert_eq!(
        fs::read_to_string(bare.join("tests/Cargo.toml")).unwrap(),
        "[package]\n"
    );
    fs::remove_dir_all(&root).unwrap();
    fs::remove_dir_all(&bare).unwrap();
}

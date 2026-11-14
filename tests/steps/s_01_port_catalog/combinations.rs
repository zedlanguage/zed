//! Completeness of plan row PORT-catalog (plan row TEST-complete-ports, COMPLETENESS.md beside
//! this file): the catalog's table read and written at its edges, and the tool's arguments.

use std::collections::{BTreeMap, HashMap};

use zed_tools::catalog::{self, Uses, read_catalog, scan, write_catalog};

use super::{index, ours, spec_dir};
use zed_tests::step_helpers::m0_03_grammar_tools::tool;

const HEAD: &str = "| Routine | Uses | Files | First use | Zed |\n|---|--:|--:|---|---|\n";

#[test]
fn a_catalog_with_no_table_or_a_short_row_is_refused() {
    let e = read_catalog("# C\n\nno table here\n").expect_err("no table");
    assert!(e.contains("has no table headed"), "{e}");
    let e = read_catalog(&format!("# C\n{HEAD}| `a::f` | 1 | 1 | `x:1` |\n")).expect_err("short");
    assert!(e.contains("a catalog row without five cells"), "{e}");
}

#[test]
fn the_table_reads_back_at_the_end_of_the_file_with_no_counts_and_with_no_rows() {
    // A table at the very end, with no counts line and no text after it.
    let (before, rows, after) = read_catalog(&format!(
        "# C\n{HEAD}| `a::f` | 1 | 1 | `x:1` | missing |\n"
    ))
    .unwrap();
    assert_eq!(
        (before.as_str(), rows.len(), after.as_str()),
        ("# C\n", 1, "")
    );
    // A table with no rows.
    let (_, rows, after) = read_catalog(&format!("# C\n{HEAD}\nAfter.\n")).unwrap();
    assert_eq!((rows.len(), after.as_str()), (0, "\nAfter.\n"));
}

#[test]
fn a_bar_in_a_routine_or_a_zed_text_survives_a_rewrite() {
    let routine = "core::ops::<bool as BitOr>::bitor|x";
    let mut found = BTreeMap::new();
    found.insert(routine.to_string(), Uses::default());
    let zed: HashMap<&str, &str> = [(routine, "`a \\|\\| b`")].into();
    let text = write_catalog("# C\n", &found, &zed, "");
    let (_, rows, _) = read_catalog(&text).unwrap();
    assert_eq!(rows.len(), 1, "{text}");
    assert_eq!(rows[0].routine, routine, "{text}");
    assert_eq!(rows[0].zed, "`a \\|\\| b`", "{text}");
}

#[test]
fn an_empty_index_finds_no_routine() {
    assert!(
        scan(&index(&[]), &catalog::SOURCES, &ours())
            .unwrap()
            .is_empty()
    );
    assert!(scan(&[], &catalog::SOURCES, &ours()).unwrap().is_empty());
}

#[test]
fn every_wrong_command_line_is_refused_with_the_usage() {
    let dir = spec_dir("catalog_usage");
    let usage = "usage: catalog SPEC_DIR CATALOG.md [--index INDEX.scip] [--write]";
    let cat = dir.write("CATALOG.md", &format!("# C\n{HEAD}"));
    for args in [
        vec![],
        vec![dir.root()],
        vec![dir.root(), cat.clone(), "--index".into()],
    ] {
        let args: Vec<&str> = args.iter().map(String::as_str).collect();
        let (outcome, out) = tool(catalog::run, &args);
        let e = outcome.expect_err("a wrong command line");
        assert!(e.contains(usage), "{args:?}: {e}\n{out}");
    }
}

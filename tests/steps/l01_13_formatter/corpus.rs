//! Every corpus program in `zed/corpus/` parses: its main file, the units in its folder
//! `NN-name/`, and its other spellings in `variants/`, and what parses formats to a fixed point.
//! The one error allowed is the refusal of a form a later layer builds, as one this zedc does
//! not compile yet; any other error is a defect in the program or in the parser. The
//! checker controls in `controls/` are left out, since some of them are meant not to parse.
//! 19-bank-ledger wrote `#bad -> {}`, an empty block after a match arm's arrow, which exports
//! nothing; the empty family there is `({})` (sec:lexical).

use std::path::{Path, PathBuf};
use zedc::format::format_source;

/// The `.zed` files of directory `dir`, sorted.
fn zed_files(dir: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "zed"))
        .collect();
    files.sort();
    files
}

#[test]
fn every_corpus_program_parses_or_is_refused_by_layer() {
    let corpus = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../zed/corpus");
    let mut files = zed_files(&corpus);
    for program in zed_files(&corpus) {
        let units = program.with_extension("");
        if units.is_dir() {
            files.extend(zed_files(&units));
        }
    }
    files.extend(zed_files(&corpus.join("variants")));
    let mut parsed = 0;
    let mut refused = Vec::new();
    let mut failed = Vec::new();
    for path in &files {
        let name = path.strip_prefix(&corpus).unwrap().display().to_string();
        match format_source(&std::fs::read(path).unwrap()) {
            Ok(out) => {
                parsed += 1;
                let text = String::from_utf8(std::fs::read(path).unwrap()).unwrap();
                match std::panic::catch_unwind(|| super::fmt(&text)) {
                    Ok(same) if same == out => {}
                    Ok(_) => failed.push(format!("{name}: zedc fmt and the test differ")),
                    Err(_) => failed.push(format!("{name}: no fixed point (see the panic above)")),
                }
            }
            Err(e) if zed_tests::is_not_yet(&e) => refused.push(name),
            Err(e) => failed.push(format!("{name}:{e}")),
        }
    }
    assert!(failed.is_empty(), "{}", failed.join("\n"));
    assert_eq!(
        refused,
        [
            "14-clustering.zed",
            "16-game-tick.zed",
            "18-socket-wordfreq.zed",
            "20-taint.zed",
            "29-late-dedup.zed",
            "07-json-parser/json.zed",
            "30-client-server/api.zed",
            "variants/02-histogram-push.zed",
            "variants/06-matrix-multiply-remap.zed",
            "variants/20-taint-error.zed",
            "variants/23-join-zoo-remap.zed",
        ],
        "the programs refused by layer"
    );
    // 31 programs, 8 units in folders and 5 variants.
    assert_eq!((files.len(), parsed), (44, 33));
}

//! Batch and single-file checking give the same answers (T6, SYNTHESIS Q2/Q3 item 4). A unit
//! checked alone, on a thread of its own with nothing cached, gives the same diagnostics as
//! when it is checked after every other unit on one thread, in either order: no answer
//! depends on what was asked before.

use std::path::PathBuf;

use zedc::run::load;

/// Every `.zed` unit of the corpus and of the steps' tests, and three rejected programs.
fn units() -> Vec<(String, Vec<u8>)> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut dirs = vec![root.join("../zed/corpus")];
    for step in std::fs::read_dir(root.join("steps")).unwrap() {
        dirs.push(step.unwrap().path().join("zed"));
    }
    let mut out = Vec::new();
    for dir in dirs {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in entries {
            let path = e.unwrap().path();
            if path.extension().is_some_and(|x| x == "zed") {
                out.push((path.display().to_string(), std::fs::read(&path).unwrap()));
            }
        }
    }
    out.sort();
    out.push((
        "concatenates a number".into(),
        b"main(stdin: Lines) -> (stdout: Lines) {\n  n = int(stdin[1]) else 0;\n  stdout <- \"n: \" ++ n;\n}\n".to_vec(),
    ));
    out.push((
        "a negative exponent".into(),
        b"f(x: int, n: int[-2..3]) -> int = x ** n;\n".to_vec(),
    ));
    out.push((
        "a parameter's morphism type outside its bound".into(),
        b"f(x: #a .. #b -> int) = 0;\nmain() = 0;\n".to_vec(),
    ));
    out
}

/// The diagnostics of `src`, or `None` when it is accepted.
fn answer(src: &[u8]) -> Option<String> {
    load(src).err()
}

#[test]
fn batch_and_single_file_checking_agree() {
    let units = units();
    assert!(units.len() > 30, "{} units", units.len());
    let alone: Vec<Option<String>> = units
        .iter()
        .map(|(_, src)| {
            let src = src.clone();
            std::thread::spawn(move || answer(&src)).join().unwrap()
        })
        .collect();
    assert!(alone.iter().filter(|a| a.is_some()).count() >= 3);
    let batch: Vec<Option<String>> = units.iter().map(|(_, src)| answer(src)).collect();
    let mut reversed: Vec<Option<String>> =
        units.iter().rev().map(|(_, src)| answer(src)).collect();
    reversed.reverse();
    for (i, (name, _)) in units.iter().enumerate() {
        assert_eq!(alone[i], batch[i], "{name}: alone, then in a batch");
        assert_eq!(
            alone[i], reversed[i],
            "{name}: alone, then in a reversed batch"
        );
    }
    // The bound check of a parameter's morphism type runs on this path too.
    let at = units
        .iter()
        .position(|(name, _)| name == "a parameter's morphism type outside its bound")
        .expect("the unit");
    assert_eq!(
        batch[at].as_deref(),
        Some(
            "1:6: the guarantee (left of `..`) of this morphism type is not within its \
             permission (right of `..`)"
        )
    );
}

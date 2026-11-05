//! Batch and single-file checking give the same answers (T6, SYNTHESIS Q2/Q3 item 4). A unit
//! checked alone, on a thread of its own with nothing cached, gives the same diagnostics as
//! when it is checked after every other unit on one thread, in either order: no answer
//! depends on what was asked before.

use std::path::PathBuf;

use zedc::run::load;

/// Every `.zed` unit of the corpus and of the steps' tests, four rejected programs and one
/// accepted one.
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
    out.push((
        "a generic literal at a union of two carriers it can adopt".into(),
        b"f(positional x: f64 | rat) = x;\nmain() = f(1n);\n".to_vec(),
    ));
    out.push((
        "a plain literal at a union of two carriers".into(),
        b"f(positional x: f64 | rat) = x;\nmain() = f(1);\n".to_vec(),
    ));
    out.push((
        "generic literals in a tuple at a union of tuple shapes".into(),
        b"tu(positional p: (f64, f64) | (String, f64)) = p;\nmain() = tu((1n, 2n));\n".to_vec(),
    ));
    out.push((
        "a generic literal compared with a union of two carriers it can adopt".into(),
        b"f(positional x: f64 | rat) = x == 1n;\nmain() = f(1.0);\n".to_vec(),
    ));
    out.push((
        "literals in a tuple compared with a union of tuple shapes".into(),
        b"isAt(positional p: (f64, f64) | (String, f64)) = p == (1, 2);\nmain() = isAt((1.0, 2.0));\n".to_vec(),
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
    // A literal at a type that names no one carrier is rejected the same way on both paths.
    let at = units
        .iter()
        .position(|(name, _)| name == "a generic literal at a union of two carriers it can adopt")
        .expect("the unit");
    assert_eq!(
        batch[at].as_deref(),
        Some(
            "2:12: `1n` at `rat | f64` adopts no one carrier: the type holds numbers of rat and \
             f64; write the one meant, as `1r` or `1.0`\n  \
             [1] 1:1: `f` is declared here, `(rat | f64) -> rat | f64`\n      \
             1 | f(positional x: f64 | rat) = x;\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"
        )
    );
    // So is one compared by `==` with a value of such a union.
    let at = units
        .iter()
        .position(|(name, _)| {
            name == "a generic literal compared with a union of two carriers it can adopt"
        })
        .expect("the unit");
    let answer = batch[at].as_deref().expect("a rejection");
    assert!(
        answer.starts_with("1:35: `1n` at `rat | f64` adopts no one carrier"),
        "{answer}"
    );
}

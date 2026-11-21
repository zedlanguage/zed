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
    let mut dirs = Vec::new();
    for step in std::fs::read_dir(root.join("steps")).unwrap() {
        dirs.push(step.unwrap().path().join("zed"));
    }
    // The corpus programs, those with units as `NN-name/main.zed` in their package roots.
    let mut out: Vec<(String, Vec<u8>)> = zed_tests::oracle::corpus()
        .into_iter()
        .map(|(path, _)| (path.display().to_string(), std::fs::read(&path).unwrap()))
        .collect();
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
        b"main(m: MainArgs) {\n  n = int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0;\n  m.stdout <- \"n: \" ++ n;\n}\n"
            .to_vec(),
    ));
    out.push((
        "a negative exponent".into(),
        b"f(x: int, n: int[-2..3]) -> int = x^n;\n".to_vec(),
    ));
    out.push((
        "a parameter's morphism type outside its bound".into(),
        b"f(x: #a .. #b -> int) = 0;\nmain() = 0;\n".to_vec(),
    ));
    out.push((
        "a generic literal at a union of two carriers it can adopt".into(),
        b"f(positional x: f64 | rat) = x;\nr = f(1);\nmain() {\n}\n".to_vec(),
    ));
    out.push((
        "a plain literal at a union of two carriers".into(),
        b"f(positional x: f64 | rat) = x;\nr = f(1);\nmain() {\n}\n".to_vec(),
    ));
    out.push((
        "generic literals in a tuple at a union of tuple shapes".into(),
        b"tu(positional p: (f64, f64) | (String, f64)) = p;\nr = tu((1, 2));\nmain() {\n}\n"
            .to_vec(),
    ));
    out.push((
        "a generic literal compared with a union of two carriers it can adopt".into(),
        b"f(positional x: f64 | rat) = x == 1;\nr = f(1.0);\nmain() {\n}\n".to_vec(),
    ));
    out.push((
        "readings related to a hub, settled where read".into(),
        b"f(positional n: int, positional a0: int, positional a1: int) =\n  if a0 >= n { if n >= -2 { if a1 >= n { if n >= -1 { popCount(a0) + popCount(a1) } else { 0 } } else { 0 } } else { 0 } } else { 0 };\nmain() = 0;\n".to_vec(),
    ));
    out.push((
        "literals in a tuple compared with a union of tuple shapes".into(),
        b"isAt(positional p: (f64, f64) | (String, f64)) = p == (1, 2);\nr = isAt((1.0, 2.0));\nmain() {\n}\n".to_vec(),
    ));
    // A family of functions, which each use that needs data rejects, and a family of
    // families of them (row FAIL-check-family-of-functions-as-data).
    out.push((
        "a family of functions shown and compared".into(),
        b"b = { \"a\" -> (y -> y + 1), \"b\" -> (y -> y * 2) };\nc = { 1 -> b };\nmain(m: MainArgs) {\n  m.stdout <- \"${c}\";\n  m.stdout <- if b == #x { \"s\" } else { \"d\" };\n}\n".to_vec(),
    ));
    out.push((
        "a family of functions read and applied".into(),
        b"b = { \"a\" -> (y -> y + 1) };\nmain(m: MainArgs) {\n  m.stdout <- \"${b[\"a\"](2)}\";\n}\n".to_vec(),
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
            "1:6: in a function type `L .. U -> V`, every function the guarantee `L`, left of \
             `..`, describes must also be allowed by the permission `U`, right of `..`, and in \
             this one the guarantee allows functions the permission does not. To repair it, \
             narrow the type left of `..`, or widen the type right of it."
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
            "2:7: Nothing chooses one carrier of `f64 | rat` for the literal `1`. Try `r = \
             f(1r)` instead.\n  \
             Part1 stands for a part written more than once:\n    \
             type Part1 = f64 | rat;\n  \
             [1] 1:1: `f` is declared here with no type written for its result; the type the \
             checker found for `f` is `Part1 -> Part1`\n      \
             1 | f(positional x: f64 | rat) = x;\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n  \
             fixes, each checked here:\n    \
             r = f(1r);        the literal is then exactly 1, a rat\n    \
             r = f(1.0f64);    the literal is then the f64 1.0"
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
        answer.starts_with("1:35: Nothing chooses one carrier of `f64 | rat` for the literal `1`"),
        "{answer}"
    );
    // A family of functions is rejected where it is shown, and accepted where it is applied.
    let at = |want: &str| units.iter().position(|(n, _)| n == want).expect("the unit");
    let answer = batch[at("a family of functions shown and compared")]
        .as_deref()
        .expect("a rejection");
    assert!(
        answer.starts_with(
            "4:18: Cannot show a value that may hold a function: `c : 1 -> (\"a\" | \"b\") -> \
             (T -> T for T in int | f32 | f64 | rat) | (T -> T for T in int | f32 | f64 | rat)` \
             in `\"${c}\"`."
        ),
        "{answer}"
    );
    assert_eq!(batch[at("a family of functions read and applied")], None);
}

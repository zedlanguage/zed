//! Step L1.19b: a record names its program's content address, and `zedc replay` refuses a
//! record of another program or of none. The address is that of the term a wave runs and the
//! ports, so a change of local names or layout keeps it and a change of meaning does not.

mod scaling;

use std::path::PathBuf;

use zedc::address::ContentAddress;
use zedc::run::{Record, load};

/// A directory of its own for test `name`, under the test target's scratch directory; files
/// in it are overwritten by each run, never deleted.
fn dir(name: &str) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("l01_19b")
        .join(name);
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// The status, standard output and standard error of `zedc <args>` with `stdin` as standard
/// input.
fn zedc(args: &[&str], stdin: &str) -> (u8, String, String) {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(args, &mut stdin.as_bytes(), &mut out, &mut err);
    (
        status,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

/// Writes `src` as `file` in test directory `name` and gives its path.
fn write(name: &str, file: &str, src: &str) -> String {
    let path = dir(name).join(file);
    std::fs::write(&path, src).unwrap();
    path.to_str().unwrap().to_string()
}

/// Doubles the number on its first line.
const DOUBLE: &str = "main(stdin: Lines) -> (stdout: Lines) {\n  n = int(stdin[1]) else 0;\n  stdout <- \"${n * 2}\";\n}\n";

/// [`DOUBLE`] with another local name and another layout.
const DOUBLE_AGAIN: &str = "main(stdin: Lines) -> (stdout: Lines) {\n\n    count = int(stdin[1])   else 0;\n    stdout <- \"${count * 2}\";\n}\n";

/// Triples it: the same ports, another meaning.
const TRIPLE: &str = "main(stdin: Lines) -> (stdout: Lines) {\n  n = int(stdin[1]) else 0;\n  stdout <- \"${n * 3}\";\n}\n";

/// Records a run of `src` on standard input `7` in test directory `name`, and gives the
/// paths of the program and of the record.
fn recorded(name: &str, src: &str) -> (String, String) {
    let prog = write(name, "prog.zed", src);
    let rec = dir(name).join("wave.rec").to_str().unwrap().to_string();
    let (status, out, err) = zedc(&["run", &prog, "--record", &rec], "7\n");
    assert_eq!((status, out.as_str(), err.as_str()), (0, "14\n", ""));
    (prog, rec)
}

#[test]
fn a_record_replays_against_its_own_program() {
    let (prog, rec) = recorded("same", DOUBLE);
    let bytes = std::fs::read(&rec).unwrap();
    let record = Record::from_bytes(&bytes).unwrap();
    let p = load(DOUBLE.as_bytes()).unwrap();
    assert_eq!(record.program, Some(p.address()));
    assert!(
        bytes.starts_with(format!("zed record 1\nprogram 64\n{}\n", p.address()).as_bytes()),
        "the address is the first entry"
    );
    assert_eq!(
        zedc(&["replay", &prog, &rec], "999\n"),
        (0, "14\n".to_string(), String::new())
    );
}

#[test]
fn local_names_and_layout_keep_the_address() {
    let (_, rec) = recorded("renamed", DOUBLE);
    let again = write("renamed", "again.zed", DOUBLE_AGAIN);
    assert_eq!(
        load(DOUBLE.as_bytes()).unwrap().address(),
        load(DOUBLE_AGAIN.as_bytes()).unwrap().address()
    );
    assert_eq!(
        zedc(&["replay", &again, &rec], ""),
        (0, "14\n".to_string(), String::new())
    );
}

#[test]
fn a_record_of_another_program_is_refused() {
    let (_, rec) = recorded("other", DOUBLE);
    let other = write("other", "triple.zed", TRIPLE);
    let (ours, theirs) = (
        load(DOUBLE.as_bytes()).unwrap().address(),
        load(TRIPLE.as_bytes()).unwrap().address(),
    );
    assert_ne!(ours, theirs);
    let (status, out, err) = zedc(&["replay", &other, &rec], "");
    assert_eq!((status, out.as_str()), (2, ""));
    assert_eq!(
        err,
        format!(
            "{rec}: the record is of the program with content address {ours}, not of this \
             program, {theirs}\n"
        )
    );
    // The library refuses it as the command does.
    let record = Record::from_bytes(&std::fs::read(&rec).unwrap()).unwrap();
    let triple = load(TRIPLE.as_bytes()).unwrap();
    assert!(triple.replay(&record).is_err());
}

#[test]
fn a_record_that_names_no_program_is_refused() {
    let (prog, rec) = recorded("none", DOUBLE);
    // The record as one written before step L1.19b: no `program` entry.
    let mut record = Record::from_bytes(&std::fs::read(&rec).unwrap()).unwrap();
    record.program = None;
    let old = dir("none").join("old.rec").to_str().unwrap().to_string();
    std::fs::write(&old, record.to_bytes()).unwrap();
    assert!(
        !std::fs::read(&old)
            .unwrap()
            .windows(7)
            .any(|w| w == b"program")
    );
    let (status, out, err) = zedc(&["replay", &prog, &old], "");
    assert_eq!((status, out.as_str()), (2, ""));
    assert_eq!(
        err,
        format!(
            "{old}: the record names no program, as records written before programs were \
             named in them do; run the program again with `--record`\n"
        )
    );
    assert_eq!(
        load(DOUBLE.as_bytes())
            .unwrap()
            .replay(&record)
            .err()
            .as_deref(),
        Some(
            "the record names no program, as records written before programs were named in \
             them do; run the program again with `--record`"
        )
    );
}

#[test]
fn the_kind_of_a_port_is_part_of_the_address() {
    // The term reads the input by its name alone; the ports tell a `Lines` from `Files`.
    let lines = "main(x: Lines) -> (stdout: Lines) {\n  stdout <- \"a\";\n}\n";
    let files = "main(x: Files) -> (stdout: Lines) {\n  stdout <- \"a\";\n}\n";
    let (a, b) = (
        load(lines.as_bytes()).unwrap(),
        load(files.as_bytes()).unwrap(),
    );
    assert_ne!(a.address(), b.address());
}

#[test]
fn a_program_entry_must_be_first_and_well_formed() {
    let a = load(DOUBLE.as_bytes()).unwrap().address();
    let hex = a.to_string();
    let record = Record {
        program: Some(a),
        args: vec!["x".into()],
        ..Record::default()
    };
    assert_eq!(Record::from_bytes(&record.to_bytes()), Ok(record));
    let bad = Err("not a Zed record".to_string());
    for text in [
        // After another entry.
        format!("zed record 1\narg 1\nx\nprogram 64\n{hex}\n"),
        // Twice.
        format!("zed record 1\nprogram 64\n{hex}\nprogram 64\n{hex}\n"),
        // Not 64 hexadecimal digits.
        format!("zed record 1\nprogram 63\n{}\n", &hex[1..]),
        format!(
            "zed record 1\nprogram 64\n{}\n",
            hex.replace(|c: char| c.is_ascii_digit(), "g")
        ),
        // Without its field.
        "zed record 1\nprogram\n\n".to_string(),
    ] {
        assert_eq!(Record::from_bytes(text.as_bytes()), bad, "{text:?}");
    }
    // Every address prints as 64 digits that parse back to it.
    for a in [ContentAddress([0; 32]), ContentAddress([255; 32]), a] {
        assert_eq!(ContentAddress::parse(&a.to_string()), Some(a));
    }
}

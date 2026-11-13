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
const DOUBLE: &str =
    "main(m: MainArgs) {\n  n = int(m.stdin[0]) else 0;\n  m.stdout <- \"${n * 2}\";\n}\n";

/// [`DOUBLE`] with another local name and another layout.
const DOUBLE_AGAIN: &str = "main(m: MainArgs) {\n\n    count = int(m.stdin[0])   else 0;\n    m.stdout <- \"${count * 2}\";\n}\n";

/// Triples it: the same ports, another meaning.
const TRIPLE: &str =
    "main(m: MainArgs) {\n  n = int(m.stdin[0]) else 0;\n  m.stdout <- \"${n * 3}\";\n}\n";

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
    assert_eq!(record.program, Some(p.address().unwrap()));
    assert!(
        bytes.starts_with(
            format!("zed record 1\nprogram 64\n{}\n", p.address().unwrap()).as_bytes()
        ),
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
        load(DOUBLE.as_bytes()).unwrap().address().unwrap(),
        load(DOUBLE_AGAIN.as_bytes()).unwrap().address().unwrap()
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
        load(DOUBLE.as_bytes()).unwrap().address().unwrap(),
        load(TRIPLE.as_bytes()).unwrap().address().unwrap(),
    );
    assert_ne!(ours, theirs);
    let (status, out, err) = zedc(&["replay", &other, &rec], "");
    assert_eq!((status, out.as_str()), (2, ""));
    assert_eq!(
        err,
        format!(
            "{rec}: this record was written by a run of a different program: `main` or a \
             definition it uses, or a port of `main`, has changed since. A replay must run the \
             program that wrote the record. Replay it with the source as it was when the record \
             was written, or run this program again with `--record <out>` to make a record of \
             it.\n"
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
            "{old}: this record does not name the program that wrote it, so it cannot be \
             checked against this one; it was written by an older zedc. Run the program again \
             with `--record <out>` to make a record that names it.\n"
        )
    );
    assert_eq!(
        load(DOUBLE.as_bytes())
            .unwrap()
            .replay(&record)
            .err()
            .as_deref(),
        Some(
            "this record does not name the program that wrote it, so it cannot be checked \
             against this one; it was written by an older zedc. Run the program again with \
             `--record <out>` to make a record that names it."
        )
    );
}

#[test]
fn the_inputs_a_program_reads_are_part_of_the_address() {
    // The two terms give the same line; one reads standard input and the other a file.
    let lines = "main(m: MainArgs) {\n  m.stdout <- m.stdin[0] else \"a\";\n}\n";
    let files =
        "main(m: MainArgs) {\n  fs = main::files;\n  m.stdout <- fs[\"1\"] else \"a\";\n}\n";
    let (a, b) = (
        load(lines.as_bytes()).unwrap(),
        load(files.as_bytes()).unwrap(),
    );
    assert_ne!(a.address().unwrap(), b.address().unwrap());
}

#[test]
fn a_program_entry_must_be_first_and_well_formed() {
    let a = load(DOUBLE.as_bytes()).unwrap().address().unwrap();
    let hex = a.to_string();
    let record = Record {
        program: Some(a),
        args: vec!["x".into()],
        ..Record::default()
    };
    assert_eq!(Record::from_bytes(&record.to_bytes()), Ok(record));
    // Each is refused at the byte where its bad entry starts: 13 is just after `zed record 1`.
    let bad = |at: usize| {
        Err(format!(
            "this record, which `zedc run --record` writes, cannot be read from byte {at} on: the \
             entry that starts there is cut short or has been changed. A record is read only as \
             it was written; make it again with `zedc run <file> --record <out>`."
        ))
    };
    for (text, at) in [
        // After another entry.
        (format!("zed record 1\narg 1\nx\nprogram 64\n{hex}\n"), 21),
        // Twice.
        (
            format!("zed record 1\nprogram 64\n{hex}\nprogram 64\n{hex}\n"),
            89,
        ),
        // Not 64 hexadecimal digits.
        (format!("zed record 1\nprogram 63\n{}\n", &hex[1..]), 13),
        (
            format!(
                "zed record 1\nprogram 64\n{}\n",
                hex.replace(|c: char| c.is_ascii_digit(), "g")
            ),
            13,
        ),
        // Without its field.
        ("zed record 1\nprogram\n\n".to_string(), 13),
    ] {
        assert_eq!(Record::from_bytes(text.as_bytes()), bad(at), "{text:?}");
    }
    // Every address prints as 64 digits that parse back to it.
    for a in [ContentAddress([0; 32]), ContentAddress([255; 32]), a] {
        assert_eq!(ContentAddress::parse(&a.to_string()), Some(a));
    }
}

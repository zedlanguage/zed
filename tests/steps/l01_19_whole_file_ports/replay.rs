//! The replay harness: `--record` saves every input the wave read, and `zedc replay` runs the
//! wave again from the record alone.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::Value;
use zedc::run::{Record, load};

use super::{dir, run, zedc};

#[test]
fn a_replay_reads_the_record_not_the_world() {
    let d = dir("replay");
    let (prices, rec) = (d.join("prices.txt"), d.join("wave.rec"));
    std::fs::write(&prices, "4\n").unwrap();
    let src = format!(
        "main(stdin: Lines, fs: Files) -> (stdout: Lines) {{\n  \
         unit = int(trim(fs[\"{}\"])) else 0;\n  qty = int(stdin[1]) else 0;\n  \
         stdout <- \"total ${{unit * qty}}\";\n}}\n",
        prices.display()
    );
    let rec_s = rec.to_str().unwrap();
    let out = run("replay", &src, "3\n", &["--record", rec_s]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "total 12\n"));
    // The world changes; the replay still sees the wave as recorded.
    std::fs::write(&prices, "100\n").unwrap();
    let prog = d.join("prog.zed");
    let out = zedc(&["replay", prog.to_str().unwrap(), rec_s], "999\n");
    assert_eq!((out.status, out.stdout.as_str()), (0, "total 12\n"));
    // A fresh run sees the new world.
    assert_eq!(run("replay", &src, "3\n", &[]).stdout, "total 300\n");
}

#[test]
fn a_read_the_record_lacks_stops_the_replay() {
    let p =
        load(b"main(fs: Files) -> (stdout: Lines) {\n  stdout <- fs[\"a.txt\"] else \"-\";\n}\n")
            .unwrap();
    let record = Record {
        program: Some(p.address().unwrap()),
        ..Record::default()
    };
    let e = p.replay(&record).err();
    assert_eq!(
        e.as_deref(),
        Some(
            "port `fs`: the program reads \"a.txt\" here, and the record holds no read of it, so \
             the replay cannot go on: a replay reads nothing from outside, only what the record \
             holds. The run that wrote the record did not read \"a.txt\", so its inputs differed \
             from these, or the record has been changed. Replay with the inputs of the recorded \
             run, or make a new record with `zedc run <file> --record <out>`."
        )
    );
}

#[test]
fn a_record_round_trips_any_bytes() {
    let mut files = BTreeMap::new();
    files.insert(
        Value::str("dir/with space\nand newline"),
        Value::str("x\n\ny"),
    );
    files.insert(Value::str("gone.txt"), Value::atom("notFound"));
    files.insert(
        Value::str("locked"),
        Value::io_error("read", "locked", "Permission denied (os error 13)"),
    );
    // A record written before `#ioError` had its payload holds a bare one.
    files.insert(Value::str("old"), Value::atom("ioError"));
    let mut lines = BTreeMap::new();
    lines.insert("stdin".to_string(), Arc::from(&b"\xff 12 34\n\n"[..]));
    // No program: a record as written before step L1.19b still reads back.
    let record = Record {
        program: None,
        lines,
        files: BTreeMap::from([("fs".to_string(), files)]),
        args: vec!["--".to_string(), "a\nb".to_string()],
    };
    let bytes = record.to_bytes();
    assert!(bytes.starts_with(b"zed record 1\nlines 5 9\nstdin"));
    assert_eq!(Record::from_bytes(&bytes), Ok(record));
}

#[test]
fn a_damaged_record_is_rejected() {
    let good = b"zed record 1\nlines 5 3\nstdinab\n\n".to_vec();
    assert!(Record::from_bytes(&good).is_ok());
    assert_eq!(
        Record::from_bytes(b"zed record 2\n"),
        Err(
            "this file is not a record that `zedc run --record` writes: such a record starts \
             with the line `zed record 1`, and this file does not. Name the file `--record` \
             wrote, or make a record with `zedc run <file> --record <out>`."
                .to_string()
        )
    );
    // Each is refused at its one entry, which starts at byte 13, just after `zed record 1`.
    for bad in [
        &b"zed record 1\nlines 5 9\nstdinab\n\n"[..],
        b"zed record 1\nlines 5 3\nstdinab\n",
        b"zed record 1\nsocket 1\nx\n",
        b"zed record 1\nmissing 2 1 4\nfsa\n",
    ] {
        assert_eq!(
            Record::from_bytes(bad),
            Err(
                "this record, which `zedc run --record` writes, cannot be read from byte 13 on: \
                 the entry that starts there is cut short or has been changed. A record is read \
                 only as it was written; make it again with `zedc run <file> --record <out>`."
                    .to_string()
            ),
            "{}",
            String::from_utf8_lossy(bad)
        );
    }
}

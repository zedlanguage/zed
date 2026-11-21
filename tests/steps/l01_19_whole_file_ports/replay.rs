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
        "main(m: MainArgs) {{\n  fs = main::files;\n  \
         unit = int(trim(fs[\"{}\"])) else #invalid -> 0 else #ioError -> 0 else #notFound -> 0;\n  qty = int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0;\n  \
         m.stdout <- \"total ${{unit * qty}}\";\n}}\n",
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
    let p = load(
        b"main(m: MainArgs) {\n  fs = main::files;\n  m.stdout <- fs[\"a.txt\"] else #ioError -> \"-\" else #notFound -> \"-\";\n}\n",
    )
    .unwrap();
    let record = Record {
        program: Some(p.address().unwrap()),
        ..Record::default()
    };
    let e = p.replay(&record).err();
    assert_eq!(
        e.as_deref(),
        Some(
            "3:15: the port `main::files` could not answer a read: the program reads \"a.txt\" here, and \
             the record holds no read of it, so the replay cannot go on: a replay reads nothing \
             from outside, only what the record holds. The run that wrote the record did not \
             read \"a.txt\", so its inputs differed from these, or the record has been changed. \
             Replay with the inputs of the recorded run, or make a new record with `zedc run \
             <file> --record <out>`.\n  [1] 3:15: the run stopped here\n      \
             3 |   m.stdout <- fs[\"a.txt\"] else #ioError -> \"-\" else #notFound -> \"-\";\n        \
               |               ^^^^^^^^^^^"
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
            "1: this file is not a record that `zedc run --record` writes: such a record starts \
             with the line `zed record 1`, and this file does not. Name the file `--record` \
             wrote, or make a record with `zedc run <file> --record <out>`."
                .to_string()
        )
    );
    let remake = "make it again with `zedc run <file> --record <out>`.";
    let short = |line: usize| {
        format!(
            "{line}: the record is cut short: the file ends inside the entry that starts on this \
             line, so the file was cut after it was written, or a length on this line has been \
             changed. A replay reads only a whole record; {remake}"
        )
    };
    let changed = |line: usize, why: &str| {
        format!(
            "{line}: the record has been changed: {why}. A replay reads a record only as `zedc \
             run --record` wrote it; {remake}"
        )
    };
    let begins = "this line should begin an entry, with a kind such as `lines` or `text` and \
                  then the length in bytes of each of the entry's fields, and it does not";
    // Each is refused at the line its bad entry starts on; a field may hold line ends, so the
    // entry after one with a field `a\nb` starts on line 5.
    for (bad, want) in [
        (
            &b"zed rec"[..],
            format!(
                "1: the record is cut short: it ends before the end of its first line, `zed record \
             1`, so the file was cut after it was written. A replay reads only a whole record; \
             {remake}"
            ),
        ),
        (b"zed record 1\nlines", short(2)),
        (b"zed record 1\nlines 5 9\nstdinab\n\n", short(2)),
        (b"zed record 1\nlines 5 3\nstdinab", short(2)),
        (b"zed record 1\nlines 5 3\nstdinab\n\nx", short(5)),
        (
            b"zed record 1\nlines 5 3\nstdina\nb\nsocket 1\nx\n",
            changed(
                5,
                "`socket` is not a kind of entry that `zedc run --record` writes, which are `program`, `lines`, `text`, `missing`, `error` and `arg`",
            ),
        ),
        (
            b"zed record 1\nlines 5 1\nstdinab\n",
            changed(
                2,
                "the entry that starts on this line does not end where the lengths on the line say: the byte after its fields is not a line end",
            ),
        ),
        (b"zed record 1\nlines 5 x\nstdinab\n", changed(2, begins)),
        (b"zed record 1\n\n", changed(2, begins)),
        (b"zed record 1\nlines \xff\n", changed(2, begins)),
        (
            b"zed record 1\nmissing 2 1 4\nfsabcde\n",
            changed(
                2,
                "an entry of the kind `missing` has 2 fields, and the one that starts on this line has 3",
            ),
        ),
        // The name of a port is text; the bytes of a `Lines` input need not be.
        (
            b"zed record 1\nlines 5 1\nstdi\xffx\n",
            changed(
                2,
                "a field of the `lines` entry that starts on this line, which holds a name or a text, is not UTF-8",
            ),
        ),
        (
            b"zed record 1\ntext 2 1\nfsa\n",
            changed(
                2,
                "an entry of the kind `text` has 3 fields, and the one that starts on this line has 2",
            ),
        ),
        (
            b"zed record 1\nerror 2 1 1\nfsab\n",
            changed(
                2,
                "an entry of the kind `error` has 2 fields or 4, and the one that starts on this line has 3",
            ),
        ),
        (
            b"zed record 1\narg 1 1\nab\n",
            changed(
                2,
                "an entry of the kind `arg` has 1 field, and the one that starts on this line has 2",
            ),
        ),
        (
            b"zed record 1\nlines 5\nstdin\n",
            changed(
                2,
                "an entry of the kind `lines` has 2 fields, and the one that starts on this line has 1",
            ),
        ),
    ] {
        assert_eq!(
            Record::from_bytes(bad),
            Err(want),
            "{}",
            String::from_utf8_lossy(bad)
        );
    }
    // A `missing` entry of 2 fields is whole, as is a bare `error`.
    assert!(Record::from_bytes(b"zed record 1\nmissing 2 1\nfsa\nerror 2 1\nfsb\n").is_ok());
}

#[test]
fn a_record_that_lacks_the_input_of_a_port_stops_the_replay() {
    let p = load(b"main(m: MainArgs) {\n  m.stdout <- m.stdin[0] else #ioError -> \"\" else #outOfBounds -> \"\";\n}\n").unwrap();
    // Every run records the input of `m.stdin`, so only a changed record lacks it.
    let record = Record {
        program: Some(p.address().unwrap()),
        ..Record::default()
    };
    assert_eq!(
        p.replay(&record).err().as_deref(),
        Some(
            "the record holds no input for the port `m.stdin`, which the program reads, so the \
             replay cannot go on: a replay reads nothing from outside, only what the record \
             holds. Every run records the input of each port it reads, so the record has been \
             changed since it was written. Replay with the record as it was written, or make a \
             new record with `zedc run <file> --record <out>`."
        )
    );
    // A run through the API that gives the port no bytes is the caller's mistake, not the
    // record's.
    let files = |_: &str| -> Arc<dyn zed_kernel::Lookup> { unreachable!("no `Files` port") };
    assert_eq!(
        p.run(&BTreeMap::new(), files).err().as_deref(),
        Some(
            "the input port `m.stdin` was given nothing to read: a run gives each `Lines` input \
             its bytes by the name of its port, and no bytes were given for `m.stdin`."
        )
    );
}

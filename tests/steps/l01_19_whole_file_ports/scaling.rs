//! Whole-file ports at the rule of low complexity (DESIGN.md Part G): splitting and joining
//! lines, a wave over a long input, a record of many reads, and a wave of many reads. The
//! inputs and checks of the benchmarks in `bench.rs`, each run here once at a small size.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Lookup, Value};
use zedc::run::{Program, Record, join_lines, load, split_lines};

/// A `Files` port whose every path holds its own name.
#[derive(Debug)]
pub(super) struct Echo;

impl Lookup for Echo {
    fn get(&self, key: &Value) -> Result<Value, String> {
        Ok(key.clone())
    }
}

/// `n` lines, `line 0` to `line n-1`, each ended by `\r\n`.
pub(super) fn lines(n: usize) -> Vec<u8> {
    (0..n)
        .map(|i| format!("line {i}\r\n"))
        .collect::<String>()
        .into_bytes()
}

/// Splits `n` lines ended by `\r\n` and joins them again: each `\r\n` is written as `\n`.
pub(super) fn split_and_join(input: &[u8], n: usize) {
    let out = join_lines("stdout", &split_lines("stdin", input)).unwrap();
    assert_eq!(out.len(), input.len() - n);
}

#[test]
fn a_lines_input_is_split_and_joined() {
    split_and_join(&lines(3), 3);
}

/// A wave writing the last of `n` lines on standard input, and the input.
pub(super) fn last_line_wave(n: usize) -> (Program, BTreeMap<String, Arc<[u8]>>) {
    let src = format!(
        "main(m: MainArgs) {{\n  m.stdout <- m.stdin[{}] else \"\";\n}}\n",
        n - 1
    );
    let input = BTreeMap::from([("m.stdin".to_string(), Arc::from(lines(n)))]);
    (load(src.as_bytes()).unwrap(), input)
}

/// Runs a wave of [`last_line_wave`]: it writes `line n-1` and nothing else.
pub(super) fn reads_the_last_line(
    program: &Program,
    input: &BTreeMap<String, Arc<[u8]>>,
    n: usize,
) {
    let wave = program.run(input, |_| Arc::new(Echo)).unwrap();
    let [(_, written)] = wave.writes.as_slice() else {
        panic!("one port written")
    };
    assert_eq!(written, format!("line {}\n", n - 1).as_bytes());
}

#[test]
fn a_wave_reads_the_last_of_its_lines() {
    let (program, input) = last_line_wave(3);
    reads_the_last_line(&program, &input, 3);
}

/// A record of `n` reads of `main::files`, `dir/file{i}.txt` holding `contents {i}\n`.
pub(super) fn record_of_reads(n: usize) -> Record {
    let reads = (0..n).map(|i| {
        (
            Value::str(&format!("dir/file{i}.txt")),
            Value::str(&format!("contents {i}\n")),
        )
    });
    Record {
        files: BTreeMap::from([("main::files".to_string(), reads.collect())]),
        ..Record::default()
    }
}

/// Writes `record` and reads it back: it holds its `n` reads.
pub(super) fn reads_back(record: &Record, n: usize) {
    let back = Record::from_bytes(&record.to_bytes()).unwrap();
    assert_eq!(back.files["main::files"].len(), n);
    assert_eq!(&back, record);
}

#[test]
fn a_record_of_reads_is_written_and_read_back() {
    reads_back(&record_of_reads(3), 3);
}

/// A `main` reading `n` distinct paths of `main::files`.
pub(super) fn distinct_paths(n: usize) -> Program {
    let reads: String = (0..n)
        .map(|i| format!("  a{i} = fs[\"p{i}\"];\n"))
        .collect();
    let src = format!(
        "main(m: MainArgs) {{\n  fs = main::files;\n{reads}  m.stdout <- a0 else \"\";\n}}\n"
    );
    load(src.as_bytes()).unwrap()
}

/// Runs a wave of [`distinct_paths`]: its record holds each of the `n` reads.
pub(super) fn records_each_path(program: &Program, n: usize) {
    let wave = program.run(&BTreeMap::new(), |_| Arc::new(Echo)).unwrap();
    assert_eq!(wave.record.files["main::files"].len(), n);
}

#[test]
fn a_wave_reading_distinct_paths_records_each() {
    records_each_path(&distinct_paths(3), 3);
}

/// `n` lines, `line 0` to `line n-1`, ended in turn by `\n`, `\r\n` and a lone `\r`, then one
/// line of `n` bytes, so the reads below cut many line ends in two and join one long line
/// across many reads.
pub(super) fn mixed_lines(n: usize) -> Vec<u8> {
    let mut text: Vec<u8> = (0..n)
        .flat_map(|i| {
            let end: &[u8] = [&b"\n"[..], b"\r\n", b"\r"][i % 3];
            [format!("line {i}").as_bytes(), end].concat()
        })
        .collect();
    text.extend(std::iter::repeat_n(b'x', n));
    text
}

/// Reads [`mixed_lines`] in reads of 7 bytes, a number prime to the line lengths, so `\r`
/// falls at the end of a read and its `\n` at the start of the next all through the input:
/// `n` lines and the long last line.
pub(super) fn reads_in_small_pieces(text: &[u8], n: usize) {
    let mut count = 0;
    let mut reader = zed_kernel::lines::LineReader::new();
    for read in text.chunks(7) {
        reader.read(read, |_| count += 1);
    }
    reader.finish(|l| {
        assert_eq!(l.len(), n);
        count += 1;
    });
    assert_eq!(count, n + 1);
}

#[test]
fn lines_read_in_small_reads_are_found_whole() {
    // 30 lines: each of the three line ends falls at the end of a read more than once.
    reads_in_small_pieces(&mixed_lines(30), 30);
}

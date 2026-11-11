//! Whole-file ports at the rule of low complexity (DESIGN.md Part G): splitting and joining
//! lines, a wave over a long input, a record of many reads, and a wave of many reads.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Lookup, Value};
use zed_tests::scaling::{check, inputs};
use zedc::run::{Record, join_lines, load, split_lines};

/// A `Files` port whose every path holds its own name.
#[derive(Debug)]
struct Echo;

impl Lookup for Echo {
    fn get(&self, key: &Value) -> Result<Value, String> {
        Ok(key.clone())
    }
}

/// `n` lines, `line 0` to `line n-1`, each ended by `\r\n`.
fn lines(n: usize) -> Vec<u8> {
    (0..n)
        .map(|i| format!("line {i}\r\n"))
        .collect::<String>()
        .into_bytes()
}

#[test]
fn a_long_lines_input_is_split_and_joined_in_linear_time() {
    let texts = inputs(20_000, lines);
    check("splitting and joining n lines", 20_000, |n| {
        let input = &texts[&n];
        let out = join_lines("stdout", &split_lines("stdin", input)).unwrap();
        assert_eq!(out.len(), input.len() - n);
    });
}

#[test]
fn a_wave_reading_the_last_of_many_lines_scales() {
    let waves = inputs(20_000, |n| {
        let src = format!("main(m: MainArgs) {{\n  m.stdout <- m.stdin[{n}] else \"\";\n}}\n");
        let input = BTreeMap::from([("m.stdin".to_string(), Arc::from(lines(n)))]);
        (load(src.as_bytes()).unwrap(), input)
    });
    check("a wave over n lines", 20_000, |n| {
        let (program, input) = &waves[&n];
        let wave = program.run(input, |_| Arc::new(Echo)).unwrap();
        let [(_, written)] = wave.writes.as_slice() else {
            panic!("one port written")
        };
        assert_eq!(written, format!("line {}\n", n - 1).as_bytes());
    });
}

#[test]
fn a_record_of_many_reads_is_written_and_read_back_in_linear_time() {
    let records = inputs(20_000, |n| {
        let reads = (0..n).map(|i| {
            (
                Value::str(&format!("dir/file{i}.txt")),
                Value::str(&format!("contents {i}\n")),
            )
        });
        Record {
            files: BTreeMap::from([("files()".to_string(), reads.collect())]),
            ..Record::default()
        }
    });
    check(
        "writing and reading back a record of n reads",
        20_000,
        |n| {
            let back = Record::from_bytes(&records[&n].to_bytes()).unwrap();
            assert_eq!(back.files["files()"].len(), n);
        },
    );
}

#[test]
fn a_wave_reading_many_distinct_paths_scales() {
    let programs = inputs(2_000, |n| {
        let reads: String = (0..n)
            .map(|i| format!("  a{i} = fs[\"p{i}\"];\n"))
            .collect();
        let src = format!(
            "main(m: MainArgs) {{\n  fs = files();\n{reads}  m.stdout <- a0 else \"\";\n}}\n"
        );
        load(src.as_bytes()).unwrap()
    });
    check("a wave reading n paths", 2_000, |n| {
        let wave = programs[&n]
            .run(&BTreeMap::new(), |_| Arc::new(Echo))
            .unwrap();
        assert_eq!(wave.record.files["files()"].len(), n);
    });
}

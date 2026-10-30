//! The port runtime of `zed-rt` splits and joins lines exactly as the interpreter does, on
//! every byte string of a small alphabet that holds each case: an empty line, `\r\n`, a bare
//! `\r`, a missing last `\n`, a multibyte character and a byte that is not UTF-8.

use zed_kernel::{Family, Value};
use zedc::run::{join_lines, split_lines};

/// Every string over `alphabet` up to length `n`, as bytes.
fn strings(alphabet: &[&[u8]], n: usize) -> Vec<Vec<u8>> {
    let mut out = vec![Vec::new()];
    let mut last = vec![Vec::new()];
    for _ in 0..n {
        let next: Vec<Vec<u8>> = last
            .iter()
            .flat_map(|s| {
                alphabet.iter().map(move |a| {
                    let mut t = s.clone();
                    t.extend_from_slice(a);
                    t
                })
            })
            .collect();
        out.extend(next.iter().cloned());
        last = next;
    }
    out
}

#[test]
fn lines_split_as_the_interpreter_splits_them() {
    let alphabet: &[&[u8]] = &[b"a", b"\n", b"\r", b"\xff", "é".as_bytes()];
    let all = strings(alphabet, 6);
    assert_eq!(all.len(), 19531);
    for s in &all {
        assert_eq!(zed_rt::ports::lines(s), split_lines(s), "{s:?}");
    }
}

#[test]
fn a_push_writes_the_bytes_the_interpreter_writes() {
    let pushes = vec![
        Value::str("x"),
        Value::str(""),
        Value::Family(Family::of(vec![
            (Value::Int(2), Value::str("b")),
            (Value::Int(1), Value::str("a")),
        ])),
        Value::Family(Family::of(Vec::<(Value, Value)>::new())),
        Value::Int(1),
        Value::Family(Family::of(vec![(Value::Int(1), Value::Int(7))])),
    ];
    for v in &pushes {
        assert_eq!(zed_rt::ports::write("out", v), join_lines("out", v), "{v}");
    }
}

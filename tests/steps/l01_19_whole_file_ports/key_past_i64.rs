//! A literal key of 2^63 or more on the lines or the arguments misses with `#outOfBounds`
//! (row FAIL-ports-key-past-i64, found by TEST-complete-ports, author P189, P188). The
//! checker gave a literal index past 64 bits the unknown type and recorded no read of a dense
//! family, so the read was written as a lookup that misses with `#notFound`.
//!
//! DESIGN.md step L1.19: a `Lines` input is "the family of its `n` lines keyed from 0 ... a
//! read at a key outside `0..<n` giving `#outOfBounds`, since the keys are one integer interval
//! with every key present (sec:type_language, the `m[k]` row)"; step L1.19a says the same of
//! `m.args`. The author's decision on `#outOfBounds` (2026-11-11): a missed read gives it on
//! the full integer level, not only on 64-bit keys.

use zed_tests::step_helpers::l01_16_elaboration::elab;
use zed_tests::step_helpers::l01_19_whole_file_ports::run_bytes;

/// Runs `m.stdout <- (m.<port>[<key>] else #outOfBounds -> "oob") else #ioError -> "other";`,
/// with `pre` before it in `main`, on standard input `a`, and gives the exit status and output.
/// A line of `m.stdin` may also be `#ioError`, so its `else` names that atom too; an argument
/// is `String` once `#outOfBounds` is taken, so its read has no second `else` (every `else`
/// names the atoms it takes, DESIGN.md sec:failure, QUESTIONS A113).
fn read(name: &str, pre: &str, port: &str, key: &str) -> (u8, String, String) {
    let rest = if port == "stdin" {
        " else #ioError -> \"other\""
    } else {
        ""
    };
    let src = format!(
        "main(m: MainArgs) {{\n  {pre}m.stdout <- (m.{port}[{key}] else #outOfBounds -> \"oob\"){rest};\n}}\n"
    );
    let out = run_bytes(name, &src, b"a\n", &[]);
    (out.status, out.stdout, out.stderr)
}

#[test]
fn a_key_past_64_bits_is_out_of_bounds() {
    let mut wrong = Vec::new();
    for k in [
        "9223372036854775808",
        "18446744073709551616",
        "99999999999999999999999",
    ] {
        for port in ["stdin", "args"] {
            let (status, out, err) = read(&format!("key_past_i64_{port}_{}", k.len()), "", port, k);
            if (status, out.as_str()) != (0, "oob\n") {
                wrong.push(format!("m.{port}[{k}]: {status} {out:?}\n{err}"));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The other side of the boundary, `2^63 - 1`, the largest key of 64 bits; the same key past
/// 64 bits held in a name, so the read is not of a literal; and the line that is there, as a
/// control.
#[test]
fn keys_beside_the_64_bit_boundary() {
    let cases = [
        ("max_stdin", "", "stdin", "9223372036854775807", "oob\n"),
        ("max_args", "", "args", "9223372036854775807", "oob\n"),
        (
            "named",
            "k = 9223372036854775808;\n  ",
            "stdin",
            "k",
            "oob\n",
        ),
        ("zero", "", "stdin", "0", "a\n"),
    ];
    let mut wrong = Vec::new();
    for (name, pre, port, key, want) in cases {
        let (status, out, err) = read(&format!("key_beside_i64_{name}"), pre, port, key);
        if (status, out.as_str()) != (0, want) {
            wrong.push(format!("{name}: m.{port}[{key}]: {status} {out:?}\n{err}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Row CHECK-big-literal-key-paths: the other reads at a literal key, a list, a range and the
/// second level of a key path, treat a key past 64 bits as they treat `2^63 - 1`, the largest
/// key of 64 bits and as far outside: each is rejected at compile time, as a read that can
/// never find its key, with the same headline but for the key. The audit of the checker found
/// `Frame::Index1` the one read that took a literal key apart by `Value::Int` (walk.rs); the
/// others read the key's type, which holds a key past 64 bits as it holds any.
#[test]
fn other_reads_at_a_key_past_64_bits_are_as_at_the_largest_64_bit_key() {
    let reads = [
        ("list", "[10, 20][K]"),
        ("range", "(0 ..< 3)[K]"),
        ("level2", "[[1], [2]][0][K]"),
    ];
    let mut wrong = Vec::new();
    for (name, read) in reads {
        // The exit status, the output, and the headline after the file name with the key
        // written `K`: the underlines below it are as long as the key.
        let run = |k: &str, tag: &str| {
            let src = format!(
                "main(m: MainArgs) {{\n  m.stdout <- String({} else #outOfBounds -> -1);\n}}\n",
                read.replace('K', k)
            );
            let out = run_bytes(&format!("big_key_{name}_{tag}"), &src, b"", &[]);
            let head = out.stderr.lines().next().unwrap_or("");
            let head = head.split_once("prog.zed:").map_or(head, |(_, h)| h);
            (out.status, out.stdout, head.replace(k, "K"))
        };
        let max = run("9223372036854775807", "max");
        if max.0 != 1 || !max.1.is_empty() || !max.2.contains("can never find its key") {
            wrong.push(format!("{name}: 2^63 - 1 gives {max:?}"));
        }
        for k in [
            "9223372036854775808",
            "18446744073709551616",
            "99999999999999999999999",
        ] {
            let got = run(k, &k.len().to_string());
            if got != max {
                wrong.push(format!("{name}: {k} gives {got:?}, 2^63 - 1 {max:?}"));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A tuple has no component at a literal index past 64 bits, which the checker rejects as it
/// rejects any index past the last component.
#[test]
fn a_tuple_index_past_64_bits_is_rejected() {
    // (index written, index printed): 2^63 prints as its power, shorter than its digits
    // (`Rat::integer_text`, KEPT-power-form-print); 10^23 - 1 = 9 * R23 is no power.
    for (k, printed) in [
        ("2", "2"),
        ("9223372036854775808", "2^63"),
        ("99999999999999999999999", "99999999999999999999999"),
    ] {
        let src = format!("x = (1, 2)[{k}];\n");
        let err = elab(&src)
            .err()
            .unwrap_or_else(|| panic!("{src}: accepted"));
        assert!(
            err.iter()
                .any(|e| e.contains(&format!("has no component {printed}"))),
            "{src}: {err:?}"
        );
    }
}

//! The port runtime of one wave (step L1.36, sec:ports): a `Lines` input's bytes as the
//! family of its lines, and the bytes a push to a `Lines` output writes. Written apart from
//! the interpreter's (`zedc::run`), so the differential oracle compares the two.

use zed_kernel::{Family, Value};

/// The lines of `bytes`, the input of port `port`, keyed from 0: a line ends at `\n`, at `\r\n`
/// or at a lone `\r`, which a last line may lack; a line that is not UTF-8 is
/// `#ioError(op: "read", path: port, why: "the line at key K is not UTF-8")`. One pass over the
/// whole input, apart from the interpreter's incremental reader.
pub fn lines(port: &str, bytes: &[u8]) -> Value {
    let mut out = Vec::new();
    let mut start = 0;
    while start < bytes.len() {
        let end = bytes[start..]
            .iter()
            .position(|b| matches!(b, b'\n' | b'\r'))
            .map_or(bytes.len(), |i| start + i);
        let line = &bytes[start..end];
        // The line end's length: two for `\r\n`, one for `\n` or a lone `\r`, none at the end.
        let ends = match &bytes[end..] {
            [b'\r', b'\n', ..] => 2,
            [] => 0,
            _ => 1,
        };
        let v = match std::str::from_utf8(line) {
            Ok(s) => Value::str(s),
            Err(_) => Value::io_error(
                "read",
                port,
                &format!("the line at key {} is not UTF-8", out.len()),
            ),
        };
        out.push((Value::Int(out.len() as i64), v));
        start = end + ends;
    }
    Value::Family(Family::of(out))
}

/// The bytes a push of `v` to `Lines` port `port` writes: each line of a family, or the one
/// string, followed by `\n`.
pub fn write(port: &str, v: &Value) -> Result<Vec<u8>, String> {
    let lines = match v {
        // An empty level holds no line, so it writes nothing, as before empty levels were
        // kept (DESIGN.md says only that a family of strings writes one line per entry).
        Value::Family(f) => f
            .leaves()
            .into_iter()
            .map(|(_, v)| v)
            .filter(|v| !matches!(v, Value::Family(f) if f.is_empty()))
            .collect(),
        v => vec![v.clone()],
    };
    let mut out = Vec::new();
    for line in lines {
        match line {
            Value::Str(s) => {
                s.chunks().for_each(|c| out.extend_from_slice(c.as_bytes()));
                out.push(b'\n');
            }
            other => {
                return Err(format!(
                    "port `{port}` writes lines of text, and the program pushed {other} to it, which is \
                     not a string: a `Lines` port takes a `Utf8String`, written as one line, or a \
                     family of strings, written one line per entry in key order. Repair: push the \
                     value's text in its place, made with `Utf8String(…)`"
                ));
            }
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lines_split_as_the_interpreter_does() {
        let f = |b: &[u8]| match lines("stdin", b) {
            Value::Family(f) => f.leaves().into_iter().map(|(_, v)| v).collect::<Vec<_>>(),
            _ => unreachable!(),
        };
        assert_eq!(f(b""), Vec::<Value>::new());
        assert_eq!(f(b"\n"), vec![Value::str("")]);
        assert_eq!(f(b"a\r\nb"), vec![Value::str("a"), Value::str("b")]);
        assert_eq!(f(b"a\rb"), vec![Value::str("a"), Value::str("b")]);
        assert_eq!(f(b"\r"), vec![Value::str("")]);
        assert_eq!(f(b"a\r\r\n"), vec![Value::str("a"), Value::str("")]);
        assert_eq!(
            f(b"a\n\rb"),
            vec![Value::str("a"), Value::str(""), Value::str("b")]
        );
        assert_eq!(
            f(b"a\n\nb\n"),
            vec![Value::str("a"), Value::str(""), Value::str("b")]
        );
        assert_eq!(
            f(b"ok\n\xff\n"),
            vec![
                Value::str("ok"),
                Value::io_error("read", "stdin", "the line at key 1 is not UTF-8")
            ]
        );
        assert_eq!(write("o", &Value::str("x")).unwrap(), b"x\n");
        let e = write("o", &Value::Int(1)).unwrap_err();
        assert!(
            e.starts_with("port `o` writes lines of text, and the program pushed 1 to it")
                && e.contains("`Utf8String(…)`"),
            "{e}"
        );
    }
}

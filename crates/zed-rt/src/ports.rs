//! The port runtime of one wave (step L1.36, sec:ports): a `Lines` input's bytes as the
//! family of its lines, and the bytes a push to a `Lines` output writes. Written apart from
//! the interpreter's (`zedc::run`), so the differential oracle compares the two.

use zed_kernel::{Family, Value};

/// The lines of `bytes`, keyed from 1: a line ends at `\n`, which a last line may lack; a
/// `\r` before the `\n` is not part of the line; a line that is not UTF-8 is a bare
/// `#ioError`.
pub fn lines(bytes: &[u8]) -> Value {
    let mut out = Vec::new();
    let mut start = 0;
    while start < bytes.len() {
        let end = bytes[start..]
            .iter()
            .position(|b| *b == b'\n')
            .map_or(bytes.len(), |i| start + i);
        let mut line = &bytes[start..end];
        if let [rest @ .., b'\r'] = line {
            line = rest;
        }
        let v = match std::str::from_utf8(line) {
            Ok(s) => Value::str(s),
            Err(_) => Value::atom("ioError"),
        };
        out.push((Value::Int(out.len() as i64 + 1), v));
        start = end + 1;
    }
    Value::Family(Family::of(out))
}

/// The bytes a push of `v` to `Lines` port `port` writes: each line of a family, or the one
/// string, followed by `\n`.
pub fn write(port: &str, v: &Value) -> Result<Vec<u8>, String> {
    let lines = match v {
        Value::Family(f) => f.leaves().into_iter().map(|(_, v)| v).collect(),
        v => vec![v.clone()],
    };
    let mut out = Vec::new();
    for line in lines {
        match line {
            Value::Str(s) => {
                out.extend_from_slice(s.as_bytes());
                out.push(b'\n');
            }
            other => return Err(format!("port `{port}` takes strings; {other} was pushed")),
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lines_split_as_the_interpreter_does() {
        let f = |b: &[u8]| match lines(b) {
            Value::Family(f) => f.leaves().into_iter().map(|(_, v)| v).collect::<Vec<_>>(),
            _ => unreachable!(),
        };
        assert_eq!(f(b""), Vec::<Value>::new());
        assert_eq!(f(b"\n"), vec![Value::str("")]);
        assert_eq!(f(b"a\r\nb"), vec![Value::str("a"), Value::str("b")]);
        assert_eq!(
            f(b"a\n\nb\n"),
            vec![Value::str("a"), Value::str(""), Value::str("b")]
        );
        assert_eq!(f(b"\xff\n"), vec![Value::atom("ioError")]);
        assert_eq!(write("o", &Value::str("x")).unwrap(), b"x\n");
        assert!(write("o", &Value::Int(1)).is_err());
    }
}

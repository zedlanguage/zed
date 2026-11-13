//! The units the step tests compiled on the day of the census that had a refusal, read from
//! `programs.txt`: each unit is a line `== <origin> <bytes>`, then that many bytes of text, then
//! a line break. The origin names the step test that compiled it first, and then, after `#`, the
//! first 8 hex digits of a hash of its text. The units are censused in pieces, each under 60 s.

use std::path::Path;
use std::sync::OnceLock;

/// Each unit of the file at `path`, its origin and its text, in the file's order.
pub fn read(path: &Path) -> Vec<(String, String)> {
    let bytes = std::fs::read(path).expect("the programs file is readable");
    let mut out = Vec::new();
    let mut at = 0;
    while at < bytes.len() {
        let end = at
            + bytes[at..]
                .iter()
                .position(|&b| b == b'\n')
                .expect("a header line");
        let head = std::str::from_utf8(&bytes[at..end]).expect("a UTF-8 header");
        let head = head
            .strip_prefix("== ")
            .expect("a header begins with `== `");
        let (origin, len) = head.rsplit_once(' ').expect("an origin and a length");
        let len: usize = len.parse().expect("a length in bytes");
        let text = &bytes[end + 1..end + 1 + len];
        let text = String::from_utf8_lossy(text).into_owned();
        out.push((origin.to_string(), text));
        at = end + 1 + len + 1;
    }
    out
}

/// Each unit of `programs.txt`, its origin and its text, in the file's order.
pub fn all() -> &'static [(String, String)] {
    static UNITS: OnceLock<Vec<(String, String)>> = OnceLock::new();
    UNITS.get_or_init(|| read(&zed_tests::steps_dir().join("m0_12_refusal_census/programs.txt")))
}

/// The units of piece `k` of `n`: the k-th of n runs of consecutive units of nearly equal
/// number.
pub fn piece(k: usize, n: usize) -> &'static [(String, String)] {
    let units = all();
    &units[units.len() * k / n..units.len() * (k + 1) / n]
}

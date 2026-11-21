//! The units the step tests compiled on the day of the census that had a refusal, read from
//! `programs.txt`: each unit is a line `== <origin> <bytes>`, then that many bytes of text, then
//! a line break. The origin names the step test that compiled it first, and then, after `#`, the
//! first 8 hex digits of a hash of its text on the day of the census. Since then each bare
//! `e else d` of a unit names the atoms it takes, as the checker's repair writes them (plan row
//! ELSE-explicit-atoms), and the hash, kept as the unit's name, is no longer that of its text.
//! The units are censused in pieces ([`piece`]).

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

/// The units of piece `k` of `n`: [`every_nth`] of [`all`].
pub fn piece(k: usize, n: usize) -> Vec<&'static (String, String)> {
    every_nth(all(), k, n)
}

/// The items of `items` at positions k, k + n, k + 2n and so on, in order: piece `k` of `n`
/// pieces dealt like cards. Pieces 0 to n - 1 hold every item exactly once (an item at position
/// i is in piece i mod n alone), and their sizes differ by at most one. `n` is 1 or more.
///
/// Why dealt and not cut into runs of consecutive items (FLAKE-m0_12-seeds-load, 2026-11-20):
/// the slow units of `programs.txt` sit next to each other, since each step test that compiled
/// one wrote several of its kind in a row. Measured one after another on one thread at load 23
/// to 31 (seeds.rs `output`, the thread's CPU time, 14.1 s for all 120): units 47, 48 and 49
/// (`l01_29_diagnostics`, 15, 42 and 79 KB) took 0.74, 1.90 and 1.95 s, units 96, 97 and 100
/// (`l01_38_presburger::one_scope`) 2.89, 0.41 and 0.79 s, unit 22 (`l01_26_type_resolution`
/// scaling, 165 KB) 1.83 s, unit 15 (`l01_22`, 52 KB) 0.70 s and unit 111 (`l01_39`) 0.42 s; each
/// of the other 111 units took 0.25 s or less. Cut into runs, 47 to 49 fell in one piece of the
/// census (`programs_4`, 10 units: 10 to 11 s of CPU and 11 to 18 s alone at load 80) and in
/// one of the seed test's 8 pieces, whose 30 units took 8.7 s one after another at load 50.
/// Dealt into 20 pieces, these nine units fall in pieces 15, 2, 7, 8, 9, 16, 17, 0 and 11, nine
/// different pieces. Whether two units share a piece depends only on their distance mod n, so
/// putting other units before all of these (seeds.rs puts the `.zed` files of the repository
/// first) moves them all to other pieces together and keeps them apart. The test that the
/// pieces cover every unit once is in cases.rs. Which units are slow is measured, not proved: a
/// change to the checker can make another unit slow, and the piece times in seeds.rs and mod.rs
/// are then to be measured again.
pub fn every_nth<T>(items: &[T], k: usize, n: usize) -> Vec<&T> {
    items.iter().skip(k).step_by(n).collect()
}

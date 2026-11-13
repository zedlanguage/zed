//! Reads back the shortest text of every finite `f32`, all 2^32 bit patterns, at `f32`, and
//! exits with status 1 at the first that does not read back to its own bits. `every_f32 [part]`
//! checks one of the eight parts of 2^29 patterns (0 to 7); with no argument, all eight.
//!
//! A hand-run check, not a test: the 2^32 patterns took about 70 minutes of processor time
//! (each eighth 31 to 51 s on 32 cores at a load of 45, TESTS-unignore-all, 2026-11-13), past
//! what a run of the tests may spend on one check. The tests read back a million random
//! patterns, every subnormal and first normal, and the top of the range
//! (`num::float_text::tests::shortest_texts_of_sampled_floats_read_back` in zed-kernel). Run it
//! after any change to `read_float` or to the printing of floats it reads.

use std::process::ExitCode;

use zed_kernel::num::{FloatFormat, read_float};

/// The first pattern of `bits` whose shortest text does not read back to it, with that text.
fn first_wrong(bits: std::ops::Range<u64>) -> Option<(u32, String)> {
    bits.map(|b| b as u32).find_map(|b| {
        let x = f32::from_bits(b);
        let text = format!("{x:e}");
        (x.is_finite() && read_float(&text, FloatFormat::F32) != Some(Ok(u64::from(b))))
            .then_some((b, text))
    })
}

/// The patterns from `part * 2^29` to the next part, split across every core.
fn part_wrong(part: u64) -> Option<(u32, String)> {
    let (start, end) = (part << 29, (part + 1) << 29);
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()) as u64;
    let step = (end - start).div_ceil(threads);
    std::thread::scope(|s| {
        let runs: Vec<_> = (0..threads)
            .map(|i| {
                let (from, to) = (start + i * step, (start + (i + 1) * step).min(end));
                s.spawn(move || first_wrong(from..to))
            })
            .collect();
        runs.into_iter().find_map(|r| r.join().expect("a part's thread"))
    })
}

fn main() -> ExitCode {
    let parts: Vec<u64> = match std::env::args().nth(1) {
        Some(p) => match p.parse() {
            Ok(p) if p < 8 => vec![p],
            _ => {
                eprintln!("every_f32: the part is a number from 0 to 7, not `{p}`");
                return ExitCode::FAILURE;
            }
        },
        None => (0..8).collect(),
    };
    for part in parts {
        if let Some((b, text)) = part_wrong(part) {
            println!("part {part}: the bits {b:#010x} print as `{text}`, which reads back otherwise");
            return ExitCode::FAILURE;
        }
        println!("part {part}: every pattern reads back");
    }
    ExitCode::SUCCESS
}

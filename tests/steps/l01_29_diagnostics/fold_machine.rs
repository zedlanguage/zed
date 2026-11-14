//! A constant's fold, and the types and messages that follow from it, are the same on every
//! machine and under every memory limit (plan row CONST-fold-machine; DESIGN
//! sec:checking_in_zed, deterministic checking). The checker folds a power of literals with the
//! kernel's evaluator, each step held to a fixed bound of 2^27 bits (`FOLD_ASK_BITS` in
//! zedc-check), not to the memory the machine has free. Before, `x = (2^64 + 13) ^ (2^20);
//! 2 ^ (x - x)` was accepted where the machine gave the fold's 65 MiB and rejected under a
//! lower limit on the process's data (`RLIMIT_DATA`).

use std::process::Command;

use zedc::build::Build;
use zedc::run::load_for;

/// Set in a child process that runs a test under a lowered `RLIMIT_DATA`: the bytes of data
/// the child may take beyond what it holds when the test starts.
const MARGIN_VAR: &str = "ZED_FOLD_MACHINE_DATA_MARGIN";

/// The program `src` built for Linux x86_64: its rendered diagnostics, or `None` when it
/// compiles.
pub(super) fn built(src: &str) -> Option<String> {
    let build = Build::default().for_target("x86_64-linux");
    load_for(src.as_bytes(), &build).err()
}

/// `main` pushing `2 ^ (x - x)` after `b = 2^64 + 13; x = b ^ (<k>);`: accepted where the
/// checker folds `x`, so that `x - x` is 0, and rejected where it does not, since `x - x` may
/// then be negative.
fn program(k: &str) -> String {
    format!(
        "main(m: MainArgs) {{\n    b = 2^64 + 13;\n    x = b ^ ({k});\n    \
         m.stdout <- String(2 ^ (x - x));\n}}\n"
    )
}

/// In the parent, runs the test `name` again in two child processes, with `RLIMIT_DATA`
/// lowered to what each holds plus 64 MiB and plus 2 GiB, and returns `None` once both have
/// passed; in a child, lowers its own limit and returns the margin.
fn under_two_limits(name: &str) -> Option<u64> {
    if let Some(m) = std::env::var_os(MARGIN_VAR) {
        let margin: u64 = m
            .to_str()
            .and_then(|m| m.parse().ok())
            .expect("a byte count");
        lower_data_limit(margin);
        return Some(margin);
    }
    let full = format!("fold_machine::{name}");
    for margin in [64u64 << 20, 2u64 << 30] {
        let out = Command::new(std::env::current_exe().expect("the test binary has a path"))
            .args(["--exact", &full, "--nocapture", "--test-threads=1"])
            .env(MARGIN_VAR, margin.to_string())
            // One malloc arena and a fixed mmap threshold, as the L1.17a helpers set them
            // (`step_helpers::l01_17_value_representation::in_child_at`), so a large request
            // is its own mapping, which the limit counts.
            .env("MALLOC_ARENA_MAX", "1")
            .env("MALLOC_MMAP_THRESHOLD_", "131072")
            .output()
            .expect("the test binary runs");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            out.status.success() && stdout.contains("1 passed"),
            "{full} with RLIMIT_DATA at its data plus {margin} bytes: {}\n{stdout}\n{}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
    }
    None
}

/// Lowers this process's `RLIMIT_DATA` to its data now (`VmData`) plus `margin` bytes, and
/// checks that twice the margin is then refused.
fn lower_data_limit(margin: u64) {
    let status = std::fs::read_to_string("/proc/self/status").expect("Linux has /proc");
    let kib: u64 = status
        .lines()
        .find_map(|l| l.strip_prefix("VmData:"))
        .and_then(|v| v.trim().strip_suffix("kB"))
        .and_then(|v| v.trim().parse().ok())
        .expect("/proc/self/status has VmData in kB");
    let limit = (kib << 10) + margin;
    rustix::process::setrlimit(
        rustix::process::Resource::Data,
        rustix::process::Rlimit {
            current: Some(limit),
            maximum: Some(limit),
        },
    )
    .expect("a process may lower its own limit");
    let words = usize::try_from(margin / 4).expect("the margin fits a usize");
    assert!(
        Vec::<u64>::new().try_reserve_exact(words).is_err(),
        "the lowered limit refuses twice the margin"
    );
}

/// The rejection of [`program`] at `2^20`, where `x` is not folded: `x - x` may be negative.
const NOT_FOLDED: &str = r#"4:24: Int power with an exponent that may be negative: `2 : int ^ (x - x) : int`. Try `exponent = x - x; if exponent >= 0 { 2 ^ exponent } else { … }` instead.
  [1]  4:28: this `-` gives int
       4 |     m.stdout <- String(2 ^ (x - x));
         |                        ^^^^^^^^^^^ [16, 17]
         |                            ^^^^^^^ [1]
         |                             ^ [2]
         |                                 ^ [15]
  [2]  4:29: `x` is int here
  [3]  3:9: `x` is defined as this expression, int
       3 |     x = b ^ (2^20);
         |         ^ [5]  ^^ [14]
         |         ^^^^^^^^^^ [3, 4]
         |             ^^^^^^ [12]
         |              ^ [13]
  [4]  3:9: this `^` gives int
  [5]  3:9: `b` is int here
  [6]  2:9: `b` is defined as this expression, int
       2 |     b = 2^64 + 13;
         |         ^ [9]  ^^ [11]
         |         ^^^^ [8]
         |         ^^^^^^^^^ [6, 7]
         |           ^^ [10]
  [7]  2:9: this `+` gives int
  [8]  2:9: this `^` gives int
  [9]  2:9: this literal, 2, is 2
  [10] 2:11: this literal, 64, is 64
  [11] 2:16: this literal, 13, is 13
  [12] 3:13: this `^` gives 1048576
  [13] 3:14: this literal, 2, is 2
  [14] 3:16: this literal, 20, is 20
  [15] 4:33: `x` is int here
  [16] 4:24: repair: `exponent = x - x; if exponent >= 0 { 2 ^ exponent } else { … }`
  [17] 4:24: repair: `2r ^ (x - x)`"#;

/// The first line of [`NOT_FOLDED`], the same at every exponent.
const HEADLINE: &str =
    "4:24: Int power with an exponent that may be negative: `2 : int ^ (x - x) : int`.";

/// `(2^64 + 13) ^ (2^20)` asks for 8 * 65 * 2^20 bits, 65 MiB, past the bound: it is not
/// folded without a limit, nor under a limit of 64 MiB, which refused it before, nor under one
/// of 2 GiB, which gave it.
#[test]
fn a_fold_past_the_bound_is_refused_under_every_limit() {
    let child = under_two_limits("a_fold_past_the_bound_is_refused_under_every_limit");
    assert_eq!(
        built(&program("2^20")).as_deref(),
        Some(NOT_FOLDED),
        "margin {child:?}"
    );
}

/// A fold within the bound is made under every limit, the low one included.
#[test]
fn a_fold_within_the_bound_is_made_under_every_limit() {
    let child = under_two_limits("a_fold_within_the_bound_is_made_under_every_limit");
    // 1024 * 65 bits, and 258111 * 65 bits, the largest power of this base the bound
    // allows: 258111 * 65 * 8 <= 2^27 < 258112 * 65 * 8.
    for k in ["2^10", "258111"] {
        assert_eq!(built(&program(k)), None, "b ^ ({k}), margin {child:?}");
    }
}

/// The bound is exact: one more in the exponent and the power asks for more than 2^27 bits.
#[test]
fn the_bound_is_exact() {
    assert_eq!(built(&program("258111")), None);
    let past = built(&program("258112")).expect("past the bound, `x` is not folded");
    assert!(past.starts_with(HEADLINE), "{past}");
}

/// A power folds or not by its own size: a large fold elsewhere in the file changes neither
/// the verdict nor the message of a small one.
#[test]
fn a_fold_does_not_depend_on_another() {
    let src = "main(m: MainArgs) {\n    b = 2^64 + 13;\n    y = b ^ (2^20);\n    \
               x = b ^ (2^10);\n    m.stdout <- String(2 ^ (x - x) + y);\n}\n";
    assert_eq!(built(src), None);
}

/// `n` powers within the bound, each folded and read by `2 ^ (x - x)`, or past it, each
/// refused at once, with no number built.
pub(super) fn powers(n: usize, k: &str) -> String {
    let mut src = String::from("main(m: MainArgs) {\n    b = 2^64 + 13;\n    s = 0");
    for i in 0..n {
        src += &format!(";\n    x{i} = b ^ ({k})");
    }
    src += ";\n    m.stdout <- String(s";
    for i in 0..n {
        src += &format!(" + 2 ^ (x{i} - x{i})");
    }
    src + ");\n}\n"
}

#[test]
fn many_powers_within_the_bound_are_folded_and_past_it_refused() {
    for n in [1, 3] {
        assert_eq!(built(&powers(n, "2^10")), None, "{n}");
        assert!(built(&powers(n, "2^40")).is_some(), "{n}");
    }
}

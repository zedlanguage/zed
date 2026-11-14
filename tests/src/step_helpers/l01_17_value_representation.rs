//! Memory-limit helpers of step L1.17a (tests/steps/l01_17_value_representation/memory_check.rs).
//!
//! A test that must see an allocation refused runs again in a child process, builds its
//! operands, and then lowers the child's address-space limit (`RLIMIT_AS`) to what it already
//! uses plus [`MARGIN`]. An allocation that was not asked for first would then abort the child,
//! which the parent reports as a failure.

use std::process::Command;

/// Set in the child process that runs a test under the lowered limit.
const CHILD: &str = "ZED_L1_17A_UNDER_LIMIT";

/// The address space a child may take beyond what it holds once its operands of `width` bits
/// are built: half the bytes of one of them, so building any of them again is refused, at
/// every width. A test sized by it keeps its ratio of operand to margin when its width is
/// made smaller to run faster.
pub const fn margin(width: u64) -> u64 {
    width / 16
}

/// The address space the child may take beyond what it holds once its operands of [`WIDE`]
/// bits are built, 64 MiB.
pub const MARGIN: u64 = margin(WIDE);

/// The width, in bits, of the operands in the child: 128 MiB, twice [`MARGIN`], so building
/// any of them again is refused.
pub const WIDE: u64 = 1 << 30;

/// In the parent, runs the test `name` of the module `module` (a `module_path!()`, whose first
/// segment is the test target's crate) again in a child process and returns `false` once it
/// has passed there; in the child, returns `true`.
pub fn in_child_at(module: &str, name: &str) -> bool {
    if std::env::var_os(CHILD).is_some() {
        return true;
    }
    // A test's name within its binary is its module path without the crate.
    let full = match module.split_once("::") {
        Some((_, path)) => format!("{path}::{name}"),
        None => name.to_string(),
    };
    let out = Command::new(std::env::current_exe().expect("the test binary has a path"))
        .args(["--exact", &full, "--nocapture", "--test-threads=1"])
        .env(CHILD, "1")
        // One malloc arena, so no thread reserves a new 64 MiB heap under the limit.
        .env("MALLOC_ARENA_MAX", "1")
        // A fixed mmap threshold, so an allocation of 128 KiB or more is its own mapping, which
        // the limit counts: glibc otherwise raises the threshold to the size of each mapped
        // block freed, up to 32 MiB, and serves a later large allocation from freed heap
        // inside the limit, where it is not refused.
        .env("MALLOC_MMAP_THRESHOLD_", "131072")
        .output()
        .expect("the test binary runs");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success() && stdout.contains("1 passed"),
        "{full} under the lowered limit: {}\n{stdout}\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    false
}

/// Lowers this process's address-space limit to what it uses now plus [`MARGIN`], and checks
/// that a request of twice the margin is then refused.
pub fn lower_limit() {
    lower_limit_by(MARGIN);
}

/// Lowers this process's address-space limit to what it uses now plus `margin` bytes, and
/// checks that a request of twice the margin is then refused.
pub fn lower_limit_by(margin: u64) {
    let status = std::fs::read_to_string("/proc/self/status").expect("Linux has /proc");
    let kib: u64 = status
        .lines()
        .find_map(|l| l.strip_prefix("VmSize:"))
        .and_then(|v| v.trim().strip_suffix("kB"))
        .and_then(|v| v.trim().parse().ok())
        .expect("/proc/self/status has VmSize in kB");
    let limit = (kib << 10) + margin;
    rustix::process::setrlimit(
        rustix::process::Resource::As,
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

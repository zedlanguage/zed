//! The benchmarks of `stack`, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates, author P169 and P178: a test that measures work at two sizes, or
//! needs an unusual size such as a depth past a thread's stack, is a benchmark). What they check
//! besides the ratios is checked at small sizes by the tests of `stack.rs`: that a run is on the
//! stack mapped for it and gives its result by `tests::a_run_is_on_its_own_stack_and_gives_its_result`,
//! and that a stack under a memory limit grows as the run reaches it, by `GROW` at a time, and
//! not again on a second run as deep, by `tests::a_stack_under_a_memory_limit_grows_as_the_run_reaches_it`.

use std::sync::atomic::{AtomicUsize, Ordering};

use super::Stack;
use super::tests::depth;
use crate::limits::tests::{in_child, status};

#[test]
fn a_run_goes_deeper_than_its_thread_stack() {
    // 100,000 frames of at least a kilobyte: more than 100 MB, on a thread of 2 MiB.
    let got = std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| Stack::new().unwrap().run(|| depth(100_000)))
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(got, 100_000);
}

/// The frames of the smaller run: about 0.4 GB of stack, and 3.3 GB at 8n. The 1x run takes
/// about 0.26 s, under the 1 s of P169: most of its time is the kernel's, making pages writable
/// and zeroing them, and the check runs each size twice, so 1x at 1 s would hold 13 GB of stack
/// at 8n and take about 20 s, the limit of a piece.
const FRAMES: u64 = 400_000;

#[test]
fn a_stack_under_a_memory_limit_grows_in_work_linear_in_its_depth() {
    // The handler of faults makes a part of `GROW` bytes writable per fault, O(1) each, so a
    // run to depth n takes O(n / GROW) faults beside its O(n) frames. At n and 8n frames, the
    // instructions of the run, the handler's included, are held under 10.5 times; and the bytes
    // made writable, which count the faults and with them the work in the kernel that
    // instructions in user mode do not count, under 9 times (`hold_linear`). Each run makes its
    // own stack, an O(1) mapping, inside the measured run: a fresh stack is what a run starts
    // on, and a `Stack` is not `Sync`, so it cannot be built before the check and shared with
    // the check's thread.
    let Some(out) = in_child(
        "stack::bench::a_stack_under_a_memory_limit_grows_in_work_linear_in_its_depth",
        || {
            crate::limits::enforce(&zed_kernel::limits::MainLimits {
                memory: Some(16 << 30),
                ..Default::default()
            })
            .unwrap();
            // The bytes made writable by the last run at each size.
            let writable = [AtomicUsize::new(0), AtomicUsize::new(0)];
            crate::scaling::check_instructions_only(
                "a stack under a memory limit run to depth n",
                FRAMES as usize,
                1,
                |n| {
                    let s = Stack::new().unwrap();
                    assert_eq!(s.run(|| depth(n as u64)), n as u64);
                    let (grows, _) = s.grows.as_ref().unwrap();
                    writable[usize::from(n as u64 != FRAMES)].store(
                        grows.high.load(Ordering::Relaxed) - grows.writable.load(Ordering::Relaxed),
                        Ordering::Relaxed,
                    );
                },
            );
            crate::scaling::hold_linear(
                &format!(
                    "a stack under a memory limit run to depths {FRAMES} and {}",
                    8 * FRAMES
                ),
                "bytes made writable",
                writable[0].load(Ordering::Relaxed) as u64,
                writable[1].load(Ordering::Relaxed) as u64,
            );
        },
    ) else {
        return;
    };
    let (code, err) = status(&out);
    // The child's measurements and bench lines, for the run's log.
    eprint!("{err}");
    assert_eq!(
        code,
        Some(0),
        "{err}{}",
        String::from_utf8_lossy(&out.stdout)
    );
}

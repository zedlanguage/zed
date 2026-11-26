//! The tests of the counting allocator and of the meter's heap.
//!
//! They are an integration test, not a `tests` module of the crate, because a test binary built
//! from the crate that holds the `#[global_allocator]` cannot count the standard library's own
//! allocations when std is a shared library (zrun's `-C prefer-dynamic`;
//! FAIL-std-allocations-uncounted). rustc defines `__rust_alloc` and the other entry points of the
//! global allocator in the binary. When the allocator is in the binary's own crate, as in the
//! crate's unit-test binary, they are hidden symbols (`readelf --dyn-syms` does not list them), so
//! libstd.so's calls bind to its own default entry points, which call `System`:
//! `std::env::var_os("PATH")` counted 0 bytes there. When the allocator is in a crate the binary
//! links, as here and in every other test binary, they are exported and libstd.so binds to them.
//! A hidden symbol cannot be exported by a link argument, so the crate's unit tests are turned off
//! (`[lib] test = false`) and these tests run where every test binary runs.

#[cfg(target_os = "linux")]
use std::alloc::{GlobalAlloc, Layout};
#[cfg(target_os = "linux")]
use std::ffi::c_void;
use std::hint::black_box;
#[cfg(target_os = "linux")]
use std::sync::atomic::Ordering::Relaxed;
#[cfg(target_os = "linux")]
use zed_alloc_count::meter::{self, ours};
#[cfg(target_os = "linux")]
use zed_alloc_count::{Counting, metered, pthread_create};
use zed_alloc_count::{Live, allocated, live, measuring};

// The meter's `malloc` in this test binary, which the tests of `metered` need.
zed_alloc_count::meter_entry_points!();

/// The allocator, called by hand. It is the binary's global allocator too, so a block it gives
/// may be freed by either.
#[cfg(target_os = "linux")]
static COUNTING: Counting = Counting;

/// The bytes `f` allocates on this thread and the threads it starts.
fn bytes_of(f: impl FnOnce()) -> u64 {
    let start = allocated();
    f();
    allocated() - start
}

#[test]
fn a_block_counts_its_size_and_a_grown_block_its_new_size() {
    assert_eq!(bytes_of(|| drop(black_box(vec![0u8; 1000]))), 1000);
    assert_eq!(
        bytes_of(|| drop(black_box(Vec::<u64>::with_capacity(10)))),
        80
    );
    let grown = bytes_of(|| {
        let mut v = Vec::<u8>::with_capacity(100);
        v.reserve_exact(300);
        black_box(v);
    });
    assert_eq!(grown, 100 + 300);
}

/// The standard library's own allocations, which libstd.so makes when std is a shared library,
/// are counted (FAIL-std-allocations-uncounted): `var_os` copies the value into a block of at
/// least its length.
#[test]
fn the_standard_librarys_own_allocations_are_counted() {
    let path = std::env::var_os("PATH").expect("PATH is set");
    let n = bytes_of(|| drop(black_box(std::env::var_os("PATH"))));
    assert!(
        n >= path.len() as u64,
        "{n} bytes counted for {}",
        path.len()
    );
}

#[test]
fn a_refused_request_counts_nothing() {
    // Two requests near `isize::MAX` bytes would overflow the count if they were counted.
    for _ in 0..2 {
        let asked = bytes_of(|| {
            assert!(
                Vec::<u8>::new()
                    .try_reserve_exact(isize::MAX as usize)
                    .is_err()
            );
        });
        assert_eq!(asked, 0);
    }
}

#[test]
fn freeing_counts_nothing() {
    let v = black_box(vec![1u8; 4096]);
    assert_eq!(bytes_of(|| drop(v)), 0);
}

#[test]
fn live_bytes_count_what_is_kept_and_the_peak_counts_what_was_held_at_once() {
    let (kept, l) = live(|| {
        drop(black_box(vec![0u8; 5000]));
        black_box(vec![0u8; 1000])
    });
    assert_eq!(
        l,
        Live {
            net: 1000,
            peak: 5000
        }
    );
    let (_, l) = live(|| drop(kept));
    assert_eq!(
        l,
        Live {
            net: -1000,
            peak: 0
        }
    );
    let (grown, l) = live(|| {
        let mut v = Vec::<u8>::with_capacity(100);
        v.reserve_exact(300);
        black_box(v)
    });
    assert_eq!(l.net, 300);
    assert_eq!(grown.capacity(), 300);
}

#[test]
fn a_measurement_inside_another_adds_to_it() {
    let ((inner, keep), outer) = live(|| {
        let a = black_box(vec![0u8; 100]);
        let (b, inner) = live(|| {
            drop(black_box(vec![0u8; 700]));
            black_box(vec![0u8; 200])
        });
        (inner, (a, b))
    });
    assert_eq!(
        inner,
        Live {
            net: 200,
            peak: 700
        }
    );
    assert_eq!(
        outer,
        Live {
            net: 300,
            peak: 800
        }
    );
    drop(keep);
    // Off again: a free outside any measurement changes nothing.
    assert_eq!(live(|| ()).1, Live { net: 0, peak: 0 });
}

#[test]
fn a_measurement_that_panics_leaves_none_running() {
    let caught = std::panic::catch_unwind(|| live(|| panic!("inside")));
    assert!(caught.is_err());
    assert!(!measuring());
}

#[test]
fn a_measurement_counts_no_other_thread() {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
    // Another thread allocates and frees all through the measurement; the measurement
    // waits until it has done so 100 times, and still sees only its own blocks.
    let (stop, done) = (
        Arc::new(AtomicBool::new(false)),
        Arc::new(AtomicU64::new(0)),
    );
    let other = {
        let (stop, done) = (Arc::clone(&stop), Arc::clone(&done));
        std::thread::spawn(move || {
            let mut kept = Vec::new();
            while !stop.load(Ordering::Relaxed) {
                kept.push(black_box(vec![0u8; 4096]));
                if kept.len() == 8 {
                    kept.clear();
                }
                done.fetch_add(1, Ordering::Relaxed);
            }
        })
    };
    let (kept, l) = live(|| {
        let start = done.load(Ordering::Relaxed);
        drop(black_box(vec![0u8; 64]));
        while done.load(Ordering::Relaxed) < start + 100 {
            std::hint::spin_loop();
        }
        black_box(vec![0u8; 10])
    });
    stop.store(true, Ordering::Relaxed);
    other.join().unwrap();
    drop(kept);
    assert_eq!(l, Live { net: 10, peak: 64 });
}

// Off Linux the count is of the whole process, which other threads add to.
#[cfg(target_os = "linux")]
#[test]
fn other_threads_do_not_change_this_threads_count() {
    let stop = std::sync::atomic::AtomicBool::new(false);
    std::thread::scope(|s| {
        // Four threads beside the measured one, as tests running beside it are: none of them
        // started by it.
        for _ in 0..4 {
            s.spawn(|| {
                while !stop.load(Relaxed) {
                    black_box(vec![0u8; 64]);
                }
            });
        }
        let measured = s.spawn(|| {
            (0..100)
                .map(|_| bytes_of(|| drop(black_box(vec![0u8; 512]))))
                .collect::<Vec<_>>()
        });
        let bytes = measured.join().unwrap();
        stop.store(true, Relaxed);
        assert_eq!(bytes, vec![512; 100]);
    });
}

#[cfg(target_os = "linux")]
#[test]
fn a_thread_counts_in_the_count_of_the_thread_that_started_it() {
    let mut child = 0;
    let mut grandchild = 0;
    let all = bytes_of(|| {
        std::thread::spawn(|| {
            let start = allocated();
            let inner = std::thread::spawn(|| bytes_of(|| drop(black_box(vec![0u8; 4096]))));
            let inner = inner.join().unwrap();
            (allocated() - start, inner)
        })
        .join()
        .map(|(c, g)| (child, grandchild) = (c, g))
        .unwrap()
    });
    assert_eq!(grandchild, 4096);
    // The child's count holds the grandchild's block and what starting it allocated.
    assert!(child >= 4096, "{child}");
    assert!(all >= child, "{all} {child}");
}

#[cfg(target_os = "linux")]
#[test]
#[expect(
    unsafe_code,
    reason = "starting a thread by pthread_create itself, as C code does"
)]
fn a_thread_started_by_a_direct_call_of_pthread_create_is_counted() {
    extern "C" fn run(_: *mut c_void) -> *mut c_void {
        black_box(vec![0u8; 3000]);
        std::ptr::null_mut()
    }
    let bytes = bytes_of(|| {
        let mut thread = 0;
        // SAFETY: a fresh `pthread_t` to fill, no attributes, and a routine that takes no
        // argument; the thread is joined at once.
        unsafe {
            assert_eq!(
                pthread_create(&mut thread, std::ptr::null(), run, std::ptr::null_mut()),
                0
            );
            assert_eq!(libc::pthread_join(thread, std::ptr::null_mut()), 0);
        }
    });
    assert!(bytes >= 3000, "{bytes}");
}

/// A fixed workload of every kind of request: 100 blocks of 1 to 100 bytes, all held at
/// once (`alloc`); 100 zeroed blocks of 10 to 1,000 bytes, each freed at once
/// (`alloc_zeroed`); and a vector of 16 bytes grown in place or by a copy to 64, 256 and
/// 1,024 bytes (`realloc`).
fn workload() {
    let held: Vec<Box<[u8]>> = (1..=100u8)
        .map(|n| black_box(vec![n; usize::from(n)]).into_boxed_slice())
        .collect();
    drop(black_box(held));
    for n in 1..=100 {
        drop(black_box(vec![0u8; 10 * n]));
    }
    let mut v = Vec::<u8>::with_capacity(16);
    for size in [64, 256, 1024] {
        v.reserve_exact(size);
        assert_eq!(v.capacity(), size);
    }
    drop(black_box(v));
}

/// The bytes [`workload`] allocates: its blocks, the vector of 100 boxes that holds the
/// first ones (16 bytes a box), and the four sizes of the grown vector.
const WORKLOAD_BYTES: u64 = 5050 + 100 * 16 + 10 * 5050 + 16 + 64 + 256 + 1024;

/// The most bytes [`workload`] holds at once: the first 100 blocks and the vector of boxes.
const WORKLOAD_PEAK: u64 = 5050 + 100 * 16;

#[test]
fn a_fixed_workload_counts_its_bytes_exactly() {
    for _ in 0..3 {
        assert_eq!(bytes_of(workload), WORKLOAD_BYTES);
        let ((), l) = live(workload);
        assert_eq!(
            l,
            Live {
                net: 0,
                peak: WORKLOAD_PEAK
            }
        );
    }
}

// Off Linux the count is of the whole process, which other threads add to.
#[cfg(target_os = "linux")]
#[test]
fn a_fixed_workload_counts_its_bytes_exactly_on_each_of_many_threads() {
    // Eight threads run the workload at once, ten times each, each measured on its own
    // thread; the thread that started them counts all of their bytes and their starts.
    let threads = 8;
    let mut each = Vec::new();
    let all = bytes_of(|| {
        std::thread::scope(|s| {
            let runs: Vec<_> = (0..threads)
                .map(|_| {
                    s.spawn(|| {
                        (0..10)
                            .map(|_| (bytes_of(workload), live(workload).1))
                            .collect::<Vec<_>>()
                    })
                })
                .collect();
            each = runs.into_iter().map(|r| r.join().unwrap()).collect();
        });
    });
    for runs in &each {
        for &(bytes, l) in runs {
            assert_eq!(bytes, WORKLOAD_BYTES);
            assert_eq!(
                l,
                Live {
                    net: 0,
                    peak: WORKLOAD_PEAK
                }
            );
        }
    }
    assert!(all >= threads * 20 * WORKLOAD_BYTES, "{all}");
}

#[cfg(target_os = "linux")]
#[test]
fn a_fixed_workload_counts_the_same_bytes_in_a_metered_run() {
    assert_eq!(metered(|| bytes_of(workload)), WORKLOAD_BYTES);
    assert_eq!(
        metered(|| live(workload).1),
        Live {
            net: 0,
            peak: WORKLOAD_PEAK
        }
    );
}

/// The layouts the metered heap's tests ask for: each class's edges, sizes past a span, and
/// alignments from 1 to a page.
#[cfg(target_os = "linux")]
fn layouts() -> Vec<Layout> {
    let sizes = [
        1,
        15,
        16,
        17,
        64,
        65,
        80,
        81,
        127,
        128,
        129,
        4095,
        4096,
        100_000,
        meter::SPAN - 1,
        meter::SPAN,
        3 * meter::SPAN + 5,
    ];
    let aligns = [1, 8, 16, 32, 64, 4096];
    sizes
        .iter()
        .flat_map(|&s| aligns.map(|a| Layout::from_size_align(s, a).unwrap()))
        .collect()
}

#[cfg(target_os = "linux")]
#[test]
#[expect(unsafe_code, reason = "calling the allocator by hand")]
fn a_metered_run_gives_distinct_aligned_blocks_of_its_own_that_hold_what_is_written() {
    metered(|| {
        let mut blocks = Vec::new();
        for layout in layouts().into_iter().cycle().take(3 * layouts().len()) {
            // SAFETY: every layout has a size that is not 0.
            let block = unsafe { COUNTING.alloc(layout) };
            assert!(!block.is_null(), "{layout:?}");
            assert!(ours(block), "{layout:?}");
            assert_eq!(block as usize % layout.align(), 0, "{layout:?}");
            // SAFETY: the block is `layout.size()` bytes long.
            unsafe { block.write_bytes(blocks.len() as u8, layout.size()) };
            blocks.push((block, layout));
        }
        let mut ranges: Vec<_> = blocks
            .iter()
            .map(|&(b, l)| (b as usize, b as usize + l.size()))
            .collect();
        ranges.sort_unstable();
        assert!(
            ranges.windows(2).all(|w| w[0].1 <= w[1].0),
            "blocks overlap"
        );
        for (i, &(block, layout)) in blocks.iter().enumerate() {
            // SAFETY: the block is live and `layout.size()` bytes long.
            let bytes = unsafe { std::slice::from_raw_parts(block, layout.size()) };
            assert!(bytes.iter().all(|&b| b == i as u8), "{layout:?}");
            // SAFETY: allocated just above with `layout`.
            unsafe { COUNTING.dealloc(block, layout) };
        }
    });
}

/// Where a fixed metered run places its blocks: for each block, the order in which the run
/// first used its span, and its offset in the span. Spans start at multiples of
/// [`meter::SPAN`] (the reservation is aligned to it), and every block here is smaller.
#[cfg(target_os = "linux")]
#[expect(unsafe_code, reason = "calling the allocator by hand")]
fn placements() -> Vec<(usize, usize)> {
    metered(|| {
        let mut spans = Vec::new();
        let mut place = |b: *mut u8| {
            let span = b as usize / meter::SPAN;
            let i = spans.iter().position(|&s| s == span).unwrap_or_else(|| {
                spans.push(span);
                spans.len() - 1
            });
            (i, b as usize % meter::SPAN)
        };
        let mut out = Vec::new();
        let mut live = Vec::new();
        for i in 0..3000usize {
            let layout = Layout::from_size_align(1 + i * 37 % 5000, 1 << (i % 7)).unwrap();
            // SAFETY: a size that is not 0.
            let b = unsafe { COUNTING.alloc(layout) };
            out.push(place(b));
            live.push((b, layout));
        }
        for i in 0..1500usize {
            let (b, layout) = live[i * 7919 % 3000];
            if !b.is_null() {
                // SAFETY: allocated above with `layout` and not yet freed.
                unsafe { COUNTING.dealloc(b, layout) };
                live[i * 7919 % 3000].0 = std::ptr::null_mut();
            }
        }
        for (b, layout) in &mut live {
            if !b.is_null() {
                // SAFETY: live, allocated with `layout`; the new size is not 0.
                *b = unsafe { COUNTING.realloc(*b, *layout, layout.size() * 3) };
                *layout = Layout::from_size_align(layout.size() * 3, layout.align()).unwrap();
                out.push(place(*b));
            }
        }
        for (b, layout) in live {
            if !b.is_null() {
                // SAFETY: live, allocated or grown with `layout`.
                unsafe { COUNTING.dealloc(b, layout) };
            }
        }
        out
    })
}

/// A metered run's heap follows the run's own calls alone, so the instructions each call
/// spends do too: the same run places every block the same way whatever came before it, a
/// churned glibc heap, earlier metered runs, and another metered run holding spans at the
/// same time (TEST-meter-allocator-bias). This is the exact form of what
/// `zed_tests::scaling_tests::the_instructions_of_a_run_repeat` sees through the counter.
#[cfg(target_os = "linux")]
#[test]
fn a_metered_run_places_its_blocks_the_same_way_whatever_came_before() {
    let first = placements();
    let kept: Vec<Vec<u8>> = (0..2000).map(|i| vec![1; 1 + i * 13 % 900]).collect();
    let held = std::sync::Barrier::new(2);
    let done = std::sync::Barrier::new(2);
    std::thread::scope(|s| {
        s.spawn(|| {
            metered(|| {
                let mine: Vec<Vec<u64>> = (0..5000).map(|i| vec![2; 1 + i % 3000]).collect();
                held.wait();
                done.wait();
                black_box(mine);
            })
        });
        held.wait();
        for _ in 0..3 {
            assert_eq!(placements(), first);
        }
        done.wait();
    });
    black_box(kept);
    assert_eq!(placements(), first);
}

#[cfg(target_os = "linux")]
#[test]
#[expect(unsafe_code, reason = "calling the allocator by hand")]
fn a_block_freed_in_a_metered_run_serves_the_next_request_of_its_class_zeroed_if_asked() {
    metered(|| {
        for layout in layouts() {
            // SAFETY: a size that is not 0, and blocks freed with the layout they came with.
            unsafe {
                let a = COUNTING.alloc(layout);
                a.write_bytes(7, layout.size());
                COUNTING.dealloc(a, layout);
                let b = COUNTING.alloc_zeroed(layout);
                assert_eq!(a, b, "{layout:?}");
                let bytes = std::slice::from_raw_parts(b, layout.size());
                assert!(bytes.iter().all(|&x| x == 0), "{layout:?}");
                COUNTING.dealloc(b, layout);
            }
        }
    });
}

#[cfg(target_os = "linux")]
#[test]
fn a_metered_block_grown_in_its_class_stays_and_one_grown_past_it_moves_with_its_bytes() {
    metered(|| {
        let mut v: Vec<u8> = Vec::with_capacity(65);
        let at = v.as_ptr();
        v.extend(0..65);
        v.reserve_exact(80 - 65);
        assert_eq!(v.as_ptr(), at, "65 and 80 bytes are one class");
        v.reserve_exact(1000);
        assert_ne!(v.as_ptr(), at);
        assert!(ours(v.as_ptr().cast_mut()));
        assert!(v.iter().copied().eq(0..65));
        v.shrink_to_fit();
        assert!(v.iter().copied().eq(0..65));
    });
}

#[cfg(target_os = "linux")]
#[test]
#[expect(unsafe_code, reason = "calling the allocator by hand")]
fn blocks_outside_a_metered_run_are_the_c_librarys_and_a_metered_block_grown_after_moves_out() {
    let mut outside = vec![1u8; 100];
    assert!(!ours(outside.as_mut_ptr()));
    let mut inside = metered(|| {
        outside.reserve_exact(100_000);
        assert!(
            !ours(outside.as_mut_ptr()),
            "grown inside a run: still the C library's"
        );
        // Aligned to half a span: the C library's.
        let big = Layout::from_size_align(16, meter::SPAN / 2).unwrap();
        // SAFETY: a size that is not 0, freed with its layout.
        unsafe {
            let b = COUNTING.alloc(big);
            assert!(!b.is_null() && !ours(b));
            COUNTING.dealloc(b, big);
        }
        vec![2u8; 5000]
    });
    assert!(ours(inside.as_mut_ptr()));
    inside.reserve_exact(50_000);
    assert!(
        !ours(inside.as_mut_ptr()),
        "grown after the run: moved out of its heap"
    );
    assert!(outside[..100].iter().all(|&b| b == 1) && inside.iter().all(|&b| b == 2));
}

/// Whether the page at `at` is mapped readable, by `/proc/self/maps`.
#[cfg(target_os = "linux")]
fn readable(at: usize) -> bool {
    let maps = std::fs::read_to_string("/proc/self/maps").unwrap();
    maps.lines().any(|line| {
        let mut fields = line.split_whitespace();
        let range = fields.next().unwrap();
        let perms = fields.next().unwrap();
        let (lo, hi) = range.split_once('-').unwrap();
        let lo = usize::from_str_radix(lo, 16).unwrap();
        let hi = usize::from_str_radix(hi, 16).unwrap();
        (lo..hi).contains(&at) && perms.starts_with('r')
    })
}

#[cfg(target_os = "linux")]
#[test]
fn a_span_is_unmapped_once_its_heap_has_ended_and_its_last_block_is_freed_anywhere() {
    // A span of its own (larger than `SPAN`), so no other test's block shares it.
    let kept = metered(|| vec![3u8; 2 * meter::SPAN]);
    let at = kept.as_ptr() as usize;
    assert!(readable(at));
    let kept = std::thread::spawn(move || {
        assert!(
            readable(at),
            "the heap has ended but one block of the span is out"
        );
        kept
    })
    .join()
    .unwrap();
    std::thread::spawn(move || drop(kept)).join().unwrap();
    assert!(
        !readable(at),
        "the last block freed on another thread unmaps its span"
    );
    let at = metered(|| {
        let v = vec![4u8; 2 * meter::SPAN];
        let at = v.as_ptr() as usize;
        drop(v);
        at
    });
    assert!(
        !readable(at),
        "a span whose blocks were all freed is unmapped as its heap ends"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn threads_started_in_a_metered_run_have_heaps_of_their_own_and_threads_outside_none() {
    let (theirs, mine) = metered(|| {
        let mut mine = vec![0u8; 100];
        let theirs = std::thread::spawn(|| {
            let mut v = vec![0u8; 100];
            assert!(ours(v.as_mut_ptr()));
            v
        })
        .join()
        .unwrap();
        mine.push(1);
        (theirs, mine)
    });
    assert!(ours(theirs.as_ptr().cast_mut()) && ours(mine.as_ptr().cast_mut()));
    assert_ne!(
        meter::owner(theirs.as_ptr().cast_mut()),
        meter::owner(mine.as_ptr().cast_mut())
    );
    let mut outside = std::thread::spawn(|| vec![0u8; 100]).join().unwrap();
    assert!(!ours(outside.as_mut_ptr()));
}

/// The variable that makes [`reserve_part_metered`] run, in the process
/// [`a_metered_run_works_where_the_system_refuses_the_full_reservation`] starts.
#[cfg(target_os = "linux")]
const RESERVE_ROLE: &str = "ZED_ALLOC_COUNT_RESERVE_ROLE";

/// The meter's heap works where the system refuses its reservation of 64 TiB, as valgrind does
/// (job b29 j4: "reserving 70368748371968 bytes of address space for the meter's allocator:
/// Invalid argument"), by a smaller one. The test starts this binary under an address-space
/// limit of 32 GiB (`ulimit -v`, which sets RLIMIT_AS, setrlimit(2): "mmap(2) ... will fail with
/// the error ENOMEM upon exceeding this limit"), where [`reserve_part_metered`] counts the fixed
/// workload in a metered run. Before the fallback, the child stopped on that panic.
#[cfg(target_os = "linux")]
#[test]
fn a_metered_run_works_where_the_system_refuses_the_full_reservation() {
    let exe = std::env::current_exe().expect("this test binary");
    let out = std::process::Command::new("sh")
        .args(["-c", "ulimit -v 33554432 && exec \"$0\" \"$@\""])
        .arg(exe)
        .args(["--exact", "--test-threads=1", "--nocapture"])
        .arg("reserve_part_metered")
        .env(RESERVE_ROLE, "1")
        .output()
        .expect("sh starts");
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "{text}{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(text.contains("1 passed"), "{text}");
}

/// The part of [`a_metered_run_works_where_the_system_refuses_the_full_reservation`] that runs
/// under the limit; does nothing in a run of its own.
#[cfg(target_os = "linux")]
#[test]
fn reserve_part_metered() {
    if std::env::var_os(RESERVE_ROLE).is_none() {
        return;
    }
    let (bytes, mut v) = metered(|| (bytes_of(workload), vec![0u8; 100]));
    assert_eq!(bytes, WORKLOAD_BYTES);
    assert!(ours(v.as_mut_ptr()));
}

/// The variable that gives a process of this test binary its part in
/// [`a_test_gives_back_what_it_freed_when_it_ends`].
#[cfg(all(target_os = "linux", target_env = "gnu"))]
const TRIM_ROLE: &str = "ZED_ALLOC_COUNT_TRIM_ROLE";

/// The resident memory of this process, in kB, as the kernel reports it (`VmRSS` of
/// `/proc/self/status`, proc_pid_status(5)).
#[cfg(all(target_os = "linux", target_env = "gnu"))]
fn resident_kb() -> u64 {
    let status = std::fs::read_to_string("/proc/self/status").expect("/proc/self/status");
    let line = (status.lines())
        .find_map(|l| l.strip_prefix("VmRSS:"))
        .expect("a VmRSS line");
    let kb = line.trim().strip_suffix("kB").expect("VmRSS in kB");
    kb.trim().parse().expect("VmRSS a number")
}

/// What a test freed is given back to the kernel when its thread ends, so a later test in the
/// same process does not run on top of it (TEST-l01-26-peak-memory; `start` in the crate calls
/// `malloc_trim` as each thread the main thread started ends). The test starts this binary with
/// one test thread and two tests that run in turn, by name. The first, on its own thread,
/// allocates 4096 blocks of 64 KiB, under glibc's mmap threshold of 128 KiB, so they come from
/// a heap of an arena, with a 16-byte block kept between each two, and frees the large ones:
/// each freed block lies between kept ones, so `free` cannot give it back from the heap's top,
/// and 256 MiB stays resident. The second reads the process's resident memory, which must be
/// under 128 MiB. Without the trim it read 265,968 kB on 2026-11-22; with it, the kept
/// blocks and the binary.
#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn a_test_gives_back_what_it_freed_when_it_ends() {
    let exe = std::env::current_exe().expect("this test binary");
    let out = std::process::Command::new(exe)
        .args(["--exact", "--test-threads=1", "--nocapture"])
        .args(["trim_part_1_frees", "trim_part_2_reads"])
        .env(TRIM_ROLE, "1")
        .output()
        .expect("this test binary starts");
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "{text}{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(text.contains("2 passed"), "{text}");
}

/// The first part of [`a_test_gives_back_what_it_freed_when_it_ends`]; does nothing in a run of
/// its own.
#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn trim_part_1_frees() {
    if std::env::var_os(TRIM_ROLE).is_none() {
        return;
    }
    // This binary links no zed_meter_settings, which turns it on in the other test binaries.
    zed_alloc_count::give_back_as_each_test_ends();
    static KEPT: std::sync::Mutex<Vec<Vec<u8>>> = std::sync::Mutex::new(Vec::new());
    let mut kept = KEPT.lock().unwrap();
    let large: Vec<Vec<u8>> = (0..4096)
        .map(|i| {
            let block = vec![1u8; 64 << 10];
            kept.push(vec![i as u8; 16]);
            block
        })
        .collect();
    black_box(&large);
    drop(large);
    println!("resident after the frees: {} kB", resident_kb());
}

/// The second part of [`a_test_gives_back_what_it_freed_when_it_ends`]; does nothing in a run of
/// its own.
#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn trim_part_2_reads() {
    if std::env::var_os(TRIM_ROLE).is_none() {
        return;
    }
    let kb = resident_kb();
    println!("resident in the next test: {kb} kB");
    assert!(kb < 128 << 10, "{kb} kB still resident");
}

//! Completeness tests of the run's stack (row TEST-complete-crates, author P189): each way a
//! stack under a memory limit is set up, grows, stops, or passes a fault on (DESIGN.md
//! sec:ports, "`main` may limit its own run"; COMPLEXITY.md R10). Each test that sets a limit
//! runs in a child process, since a limit holds for every thread of a process. The case list is
//! `crates/zed-rt/COMPLETENESS.md`.

use super::tests::depth;
use super::*;
use crate::limits::tests::{in_child, status};
use std::os::unix::process::ExitStatusExt;
use std::sync::atomic::AtomicBool;
use zed_kernel::limits::MainLimits;

/// The limits of a run that may hold `b` bytes.
fn memory(b: u64) -> MainLimits {
    MainLimits {
        memory: Some(b),
        ..MainLimits::default()
    }
}

/// The bytes writable at the top of `s`, and its record.
fn held(s: &Stack) -> usize {
    let (g, _) = s.grows.as_ref().expect("a stack under a limit");
    g.high.load(Ordering::Relaxed) - g.writable.load(Ordering::Relaxed)
}

/// Sets the action for `SIGSEGV` to `handler`, with no `SA_SIGINFO`, and makes the process
/// leave no core dump when a fault ends it.
fn plain_segv(handler: libc::sighandler_t) {
    #[expect(unsafe_code, reason = "signal and prctl are libc calls")]
    // SAFETY: each handler given is a function of one `c_int`, or SIG_DFL or SIG_IGN; prctl
    // only sets a flag of the process.
    unsafe {
        assert_ne!(libc::signal(libc::SIGSEGV, handler), libc::SIG_ERR);
        assert_eq!(libc::prctl(libc::PR_SET_DUMPABLE, 0), 0);
    }
}

/// Writes through a null pointer: a fault in no stack.
fn fault() -> ! {
    #[expect(unsafe_code, reason = "the test writes through a null pointer")]
    // SAFETY: the write faults, as the test means it to.
    unsafe {
        std::ptr::write_volatile(std::ptr::null_mut::<u8>(), 1);
    }
    unreachable!("a write through a null pointer was given")
}

#[test]
fn a_stack_smaller_than_one_step_is_writable_whole_and_stops_at_its_guard_page() {
    let Some(out) = in_child(
        "stack::completeness::a_stack_smaller_than_one_step_is_writable_whole_and_stops_at_its_guard_page",
        || {
            // Data the process held before the limit, freed after: room for the whole stack
            // and the handler's own, so the run reaches the guard page before the system
            // refuses a part (the existing tests stop at the refusal).
            let before = std::hint::black_box(vec![1u8; 16 << 20]);
            crate::limits::enforce(&memory(128 << 10)).unwrap();
            drop(before);
            let s = Stack::new().unwrap();
            // As large as the limit, and one step of growth is more: writable whole.
            assert_eq!((s.len(), held(&s)), (128 << 10, 128 << 10));
            assert_eq!(s.run(|| depth(20)), 20);
            s.run(|| depth(1_000_000));
            unreachable!("a run past its stack was given");
        },
    ) else {
        return;
    };
    let (code, err) = status(&out);
    assert_eq!(code, Some(3), "{err}");
    assert!(
        err.ends_with(
            "Memory limit of `main` passed: the run's stack holds 131072 B (128 KiB) and needs \
             more, past 131072 B (128 KiB).\n"
        ),
        "{err}"
    );
}

extern "C" fn exit_7(signal: libc::c_int) {
    #[expect(unsafe_code, reason = "_exit is a libc call")]
    // SAFETY: _exit is async-signal-safe.
    unsafe {
        libc::_exit(if signal == libc::SIGSEGV { 7 } else { 8 })
    }
}

#[test]
fn a_fault_outside_the_stacks_is_passed_to_a_plain_handler_before() {
    let Some(out) = in_child(
        "stack::completeness::a_fault_outside_the_stacks_is_passed_to_a_plain_handler_before",
        || {
            plain_segv(exit_7 as *const () as libc::sighandler_t);
            crate::limits::enforce(&memory(64 << 20)).unwrap();
            let _s = Stack::new().unwrap();
            fault();
        },
    ) else {
        return;
    };
    let (code, err) = status(&out);
    assert_eq!(code, Some(7), "{err}");
    assert!(!err.contains("Memory limit"), "{err}");
}

#[test]
fn a_fault_outside_the_stacks_with_the_default_or_ignored_before_ends_as_sigsegv_does() {
    for (name, action) in [("default", libc::SIG_DFL), ("ignored", libc::SIG_IGN)] {
        let test = "stack::completeness::a_fault_outside_the_stacks_with_the_default_or_ignored_before_ends_as_sigsegv_does";
        const WHICH: &str = "ZED_RT_STACK_BEFORE";
        if std::env::var_os("ZED_RT_LIMITS_CHILD").is_some() {
            if std::env::var(WHICH).as_deref() == Ok(name) {
                plain_segv(action);
                crate::limits::enforce(&memory(64 << 20)).unwrap();
                let _s = Stack::new().unwrap();
                fault();
            }
            continue;
        }
        let out = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", test, "--test-threads=1", "--nocapture"])
            .env("ZED_RT_LIMITS_CHILD", test)
            .env(WHICH, name)
            .output()
            .unwrap();
        let (_, err) = status(&out);
        assert_eq!(out.status.signal(), Some(libc::SIGSEGV), "{name}: {err}");
        assert!(!err.contains("Memory limit"), "{name}: {err}");
    }
}

static PASSED_ON: AtomicBool = AtomicBool::new(false);

extern "C" fn record(_: libc::c_int) {
    PASSED_ON.store(true, Ordering::SeqCst);
}

/// Sends this thread a `SIGSEGV` whose fault address is `at`, as a fault there would.
fn segv_at(at: usize) {
    #[expect(unsafe_code, reason = "rt_tgsigqueueinfo is a system call")]
    // SAFETY: the siginfo is zeroed and owned here; on x86_64 Linux `si_signo` is at byte 0,
    // `si_code` at byte 8 and `si_addr` at byte 16 (siginfo.h). A process may send itself a
    // signal with a negative `si_code` (rt_sigqueueinfo(2)).
    unsafe {
        let mut info: libc::siginfo_t = std::mem::zeroed();
        let p = ptr::from_mut(&mut info).cast::<u8>();
        p.cast::<i32>().write(libc::SIGSEGV);
        p.add(8).cast::<i32>().write(libc::SI_QUEUE);
        p.add(16).cast::<usize>().write(at);
        let r = libc::syscall(
            libc::SYS_rt_tgsigqueueinfo,
            libc::getpid(),
            libc::gettid(),
            libc::SIGSEGV,
            &info,
        );
        assert_eq!(r, 0, "{}", io::Error::last_os_error());
    }
}

#[test]
fn a_fault_on_a_writable_page_or_outside_the_stack_is_not_its_growth() {
    let Some(out) = in_child(
        "stack::completeness::a_fault_on_a_writable_page_or_outside_the_stack_is_not_its_growth",
        || {
            plain_segv(record as *const () as libc::sighandler_t);
            crate::limits::enforce(&memory(64 << 20)).unwrap();
            let s = Stack::new().unwrap();
            let (g, _) = s.grows.as_ref().unwrap();
            let (low, high) = (
                g.low.load(Ordering::Relaxed),
                g.high.load(Ordering::Relaxed),
            );
            let writable = g.writable.load(Ordering::Relaxed);
            for (at, what) in [
                (writable, "the lowest writable byte"),
                (high - 1, "the top byte"),
                (high, "the byte above the stack"),
                (low - s.page - 1, "the byte below the guard page"),
            ] {
                PASSED_ON.store(false, Ordering::SeqCst);
                segv_at(at);
                assert!(PASSED_ON.load(Ordering::SeqCst), "{what} was not passed on");
                assert_eq!(held(&s), GROW, "{what} grew the stack");
            }
            // A fault in the part not yet writable grows it, and is not passed on.
            PASSED_ON.store(false, Ordering::SeqCst);
            segv_at(writable - 1);
            assert!(!PASSED_ON.load(Ordering::SeqCst));
            assert_eq!(held(&s), 2 * GROW);
        },
    ) else {
        return;
    };
    let (code, err) = status(&out);
    assert_eq!(
        code,
        Some(0),
        "{err}{}",
        String::from_utf8_lossy(&out.stdout)
    );
}

#[test]
fn a_limited_address_space_refuses_the_reservation_under_a_memory_limit() {
    let Some(out) = in_child(
        "stack::completeness::a_limited_address_space_refuses_the_reservation_under_a_memory_limit",
        || {
            #[expect(unsafe_code, reason = "sysinfo, sysconf and setrlimit are libc calls")]
            // SAFETY: sysinfo writes the zeroed struct owned here; the others only read or set
            // a limit of this child process.
            let (machine, page) = unsafe {
                let mut info: libc::sysinfo = std::mem::zeroed();
                assert_eq!(libc::sysinfo(&mut info), 0);
                let r = libc::rlimit {
                    rlim_cur: 8 << 30,
                    rlim_max: 8 << 30,
                };
                crate::limits::enforce(&memory(1 << 40)).unwrap();
                assert_eq!(libc::setrlimit(libc::RLIMIT_AS, &r), 0);
                (
                    (info.totalram + info.totalswap) * u64::from(info.mem_unit),
                    libc::sysconf(libc::_SC_PAGESIZE) as u64,
                )
            };
            assert!(
                machine > 16 << 30,
                "the test needs more than 16 GiB of memory and swap"
            );
            // A stack as large as the machine, the limit being larger, is refused.
            let e = Stack::new().unwrap_err();
            let bytes = machine.div_ceil(page) * page;
            assert_eq!(
                e,
                reserve(bytes as usize, &io::Error::from_raw_os_error(libc::ENOMEM))
            );
        },
    ) else {
        return;
    };
    let (code, err) = status(&out);
    assert_eq!(
        code,
        Some(0),
        "{err}{}",
        String::from_utf8_lossy(&out.stdout)
    );
}

#[test]
fn a_limit_already_full_refuses_the_handlers_stack() {
    let Some(out) = in_child(
        "stack::completeness::a_limit_already_full_refuses_the_handlers_stack",
        || {
            crate::limits::enforce(&memory(32 << 20)).unwrap();
            // Fill the limit with private writable pages, then free eight: room for the
            // message, not for the handler's stack of `ALT` bytes.
            let mut pages = Vec::with_capacity(16 << 10);
            #[expect(unsafe_code, reason = "the mappings are libc calls")]
            // SAFETY: each mapping is new and anonymous; the ones unmapped are never used.
            unsafe {
                loop {
                    let p = libc::mmap(
                        ptr::null_mut(),
                        4096,
                        libc::PROT_READ | libc::PROT_WRITE,
                        libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                        -1,
                        0,
                    );
                    if p == libc::MAP_FAILED {
                        break;
                    }
                    assert!(pages.len() < pages.capacity(), "the limit was not reached");
                    pages.push(p);
                }
                for p in pages.drain(pages.len() - 8..) {
                    libc::munmap(p, 4096);
                }
            }
            const { assert!(ALT > 8 * 4096) };
            let e = Stack::new().unwrap_err();
            assert_eq!(e, too_small(32 << 20));
        },
    ) else {
        return;
    };
    let (code, err) = status(&out);
    assert_eq!(
        code,
        Some(0),
        "{err}{}",
        String::from_utf8_lossy(&out.stdout)
    );
}

#[test]
fn each_refusal_to_set_up_the_stack_says_the_program_never_started_and_how_to_repair_it() {
    assert_eq!(
        unable("the page size was not given"),
        "the program could not start: before it runs, it reserves address space for a stack as \
         large as the machine's memory and swap together, so that deep recursion is limited by \
         memory alone, and the page size was not given. Repairs: run the program again; if it \
         fails the same way, run it with `zedc run`, which does not reserve this stack"
    );
    let e = reserve(4096, &io::Error::from_raw_os_error(libc::ENOMEM));
    assert!(
        e.contains("the system refused to reserve 4096 bytes (Cannot allocate memory"),
        "{e}"
    );
    assert!(e.contains("`ulimit -v unlimited`"), "{e}");
    assert_eq!(
        too_small(1),
        "Memory limit of `main` passed: the run's stack cannot start within the 1 B the run may \
         hold. Repair: raise `memory:` in `@limits` before `main`"
    );
}

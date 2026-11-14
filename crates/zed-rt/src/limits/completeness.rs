//! Completeness tests of the limits of `main` (row TEST-complete-crates, author P189): each
//! way the system can refuse a limit, and how a soft and a hard limit are set (DESIGN.md
//! sec:ports, getrlimit(2)). The case list is `crates/zed-rt/COMPLETENESS.md`.

use super::tests::{in_child, status};
use super::*;

/// The message of a refused step, as `system` writes it for `what` and `e`.
fn refused(what: &str, e: &str) -> String {
    format!(
        "the program could not start: it limits its own run, written before `main`, and the \
         system refused to {what} ({e}). Repair: run the program again; if it fails the same \
         way, remove the limit before `main`"
    )
}

#[test]
fn a_signal_the_system_lets_no_one_catch_is_refused_with_the_message_for_a_start() {
    // SIGKILL and SIGSTOP cannot be caught (signal(7)): sigaction fails with EINVAL and
    // nothing changes, so the test needs no child process.
    for signal in [libc::SIGKILL, libc::SIGSTOP] {
        let e = install(signal, on_cpu).unwrap_err();
        let os = io::Error::from_raw_os_error(libc::EINVAL).to_string();
        assert_eq!(
            e,
            refused("catch a signal of its limits", &os),
            "signal {signal}"
        );
    }
}

#[test]
fn a_resource_the_system_does_not_have_is_refused_when_its_limit_is_read() {
    // getrlimit fails with EINVAL for a resource out of range, before any limit is written.
    let e = set_limit(9999, 1, None, "memory").unwrap_err();
    let os = io::Error::from_raw_os_error(libc::EINVAL).to_string();
    assert_eq!(e, refused("read its limit on memory", &os));
}

#[test]
fn no_memory_limit_is_in_force_in_a_process_that_set_none() {
    // The harness process never calls `enforce` (`in_child`).
    assert_eq!(memory_limit(), None);
}

#[test]
fn a_soft_limit_above_the_hard_one_is_lowered_to_it_and_a_hard_one_never_raised() {
    let Some(out) = in_child(
        "limits::completeness::a_soft_limit_above_the_hard_one_is_lowered_to_it_and_a_hard_one_never_raised",
        || {
            let read = || {
                let mut r = libc::rlimit {
                    rlim_cur: 0,
                    rlim_max: 0,
                };
                #[expect(unsafe_code, reason = "getrlimit is a libc call")]
                // SAFETY: `r` is an rlimit owned here, which getrlimit fills.
                let ok = unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut r) };
                assert_eq!(ok, 0);
                (r.rlim_cur, r.rlim_max)
            };
            let (_, hard) = read();
            assert!(hard > 64, "the test needs a hard limit above 64 open files");
            // A soft limit past the inherited hard one is the hard one; the hard one stays.
            set_limit(libc::RLIMIT_NOFILE, u64::MAX, None, "open files").unwrap();
            assert_eq!(read(), (hard, hard));
            // A hard limit asked above the inherited one is the inherited one.
            set_limit(libc::RLIMIT_NOFILE, 16, Some(u64::MAX), "open files").unwrap();
            assert_eq!(read(), (16, hard));
            // A hard limit below: both are set, and the soft one is lowered to the new hard one.
            set_limit(libc::RLIMIT_NOFILE, 48, Some(32), "open files").unwrap();
            assert_eq!(read(), (32, 32));
            // Asked again above it, the lowered hard limit is the inherited one now.
            set_limit(libc::RLIMIT_NOFILE, 64, Some(64), "open files").unwrap();
            assert_eq!(read(), (32, 32));
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

//! The run's own close of standard output and standard error (DESIGN.md sec:ports, "A port's
//! close that fails", step L7.3p, plan row PORT-stdout-close-status). No program closes the two
//! streams, which were open before `main` began, so the runtime closes them when the run ends:
//! after `main` returns, once every entry pushed to `m.stdout` and `m.stderr` is written, and
//! after a stop's message. On Linux close(2) runs the file system's `flush` and gives its result
//! (fs/open.c), so a close is where an NFS server reports a quota passed or a device an I/O error
//! that no write reported (close(2)); a run whose every push was acknowledged `#ok` can still have
//! lost output, and only the exit status can say so.
//!
//! What a failure does, as gnulib's `close_stdout` does for C programs (lib/closeout.c): a
//! failed close of descriptor 1 writes the message of the row "Standard output failed when the
//! run closed it" (sec:diagnostics) on standard error, a failed close of either makes the exit
//! status 1 where it would have been 0, and a failed close of descriptor 2 writes nothing, since
//! standard error is the one place a message could go. Unlike `close_stdout`, a nonzero status
//! is kept, since it already says the run failed and may say how.
//!
//! The code runs in a signal handler too, where a limit of `main` stops the run (`fault_exit`),
//! so it allocates nothing, takes no lock and calls only async-signal-safe functions
//! (signal-safety(7): `readlink`, `close` and `write`).
//!
//! Sources, each read on 2026-11-22:
//! - close(2), Linux man-pages 6.13 (2024-07-23), read in full: "ENOSPC, EDQUOT: On NFS, these
//!   errors are not normally reported against the first write which exceeds the available
//!   storage space, but instead against a subsequent write(2), fsync(2), or close()"; and in
//!   "Dealing with error returns from close()", that the kernel "always releases the file
//!   descriptor early in the close operation", so a retry may close another thread's descriptor.
//! - Linux fs/open.c (torvalds/linux master): `SYSCALL_DEFINE1(close)` detaches the descriptor
//!   with `file_close_fd` and then calls `filp_close_sync`, which returns `filp_flush`'s result,
//!   the file's `f_op->flush`; restart codes become `-EINTR`. fs/nfs/file.c `nfs_file_flush`
//!   writes back with `nfs_wb_all` and returns `filemap_check_wb_err`, the write-back error.
//! - gnulib lib/closeout.c `close_stdout` (coreutils/gnulib master): a failed
//!   `close_stream(stdout)` prints "write error" and calls `_exit(exit_failure)`; a failed
//!   `close_stream(stderr)` calls `_exit(exit_failure)` with no message. lib/close-stream.c
//!   ignores an `fclose` failure "if there was no previous error, no data remains to be flushed,
//!   and fclose failed with EBADF".
//! - signal-safety(7), Linux man-pages 6.13: `close`, `readlink` and `write` are in its list.
//!
//! These are read, not tested: the tests (`close_binary` in tests/steps/l01_36a_executables)
//! fail a close with a seccomp filter, which checks this code's answer to a failed close, and
//! cannot check that a real NFS server or device fails a close as the sources say.

use std::ffi::c_int;
use std::fmt::Write as _;

use crate::limits::Line;

/// Closes descriptors 1 and 2, standard output and then standard error, at the end of a run
/// whose exit status is `status`, and gives the status the process exits with: 1 where a close
/// failed and `status` is 0, else `status`. A failed close of descriptor 1 writes the row's
/// message on standard error first. The caller flushes Rust's buffer of standard output
/// before, since bytes left in it would be lost unreported.
///
/// A close that gives `EBADF` is no failure: the descriptor was not open, so the process was
/// started with the stream closed and no output went to it that a close could lose (gnulib's
/// `close_stream` likewise ignores `EBADF` on a stream with nothing pending). Cost: three
/// system calls, `readlink` of `/proc/self/fd/1` (made before the close, since the name is gone
/// after it, and needed only to name the file in the message) and the two closes.
pub fn standard_streams(status: u8) -> u8 {
    let failed = close_both();
    if failed && status == 0 { 1 } else { status }
}

/// [`standard_streams`] for a stop, whose status [`crate::limits::FAULT`] is kept: the closes
/// and the message only.
pub(crate) fn after_stop() {
    close_both();
}

/// Closes descriptor 1, writing the row's message if that fails, then descriptor 2; whether
/// either close failed.
fn close_both() -> bool {
    let mut path = [0u8; 4096];
    let named = file_of(1, &mut path);
    let out = close(1);
    if let Some(e) = out {
        message(e, named);
    }
    let err = close(2);
    out.is_some() || err.is_some()
}

/// The path of the file open at descriptor `fd`, read into `buf`, or `None` when the system
/// gives none, as for a pipe or a socket.
fn file_of(fd: c_int, buf: &mut [u8; 4096]) -> Option<&str> {
    let mut link = Line::new();
    let _ = write!(link, "/proc/self/fd/{fd}\0");
    #[expect(unsafe_code, reason = "readlink is a libc call")]
    // SAFETY: `link` holds a NUL-ended path, and `readlink` writes at most `buf.len()` bytes
    // into `buf`, which is borrowed mutably for the call.
    let n = unsafe {
        libc::readlink(
            link.bytes().as_ptr().cast(),
            buf.as_mut_ptr().cast(),
            buf.len(),
        )
    };
    let n = usize::try_from(n)
        .ok()
        .filter(|&n| n > 0 && n < buf.len())?;
    // A pipe or a socket reads as `pipe:[inode]` or `socket:[inode]`, which names no file.
    std::str::from_utf8(&buf[..n])
        .ok()
        .filter(|p| p.starts_with('/'))
}

/// Closes descriptor `fd`; the error number when the close failed with any error but `EBADF`.
/// A close is not retried after `EINTR`: on Linux the descriptor is released before `flush`
/// runs, so a second close could close a descriptor another thread has just opened (close(2),
/// "Dealing with error returns from close()").
fn close(fd: c_int) -> Option<c_int> {
    #[expect(unsafe_code, reason = "close is a libc call")]
    // SAFETY: `close` takes a descriptor number and touches no memory of Rust's. Descriptors 1
    // and 2 are not owned by any Rust value: `std::io::Stdout` and `Stderr` write to the
    // numbers, and treat `EBADF` from a write after the close as success.
    let r = unsafe { libc::close(fd) };
    if r == 0 {
        return None;
    }
    std::io::Error::last_os_error()
        .raw_os_error()
        .filter(|&e| e != libc::EBADF)
}

/// An error number close(2) can give, by its name, the system's text for it (glibc's
/// `strerror`, copied, since `strerror` is not async-signal-safe) and what it means for the
/// output, in the program's terms.
struct Errno {
    code: c_int,
    name: &'static str,
    text: &'static str,
    means: &'static str,
}

/// The errors a file system's `flush` gives back through close(2) (close(2), "ERRORS", and
/// "NOTES" on NFS; nfs_file_flush in fs/nfs/file.c gives the error of the writes it waits
/// on), each with the words of its message.
const ERRNOS: [Errno; 7] = [
    Errno {
        code: libc::EIO,
        name: "EIO",
        text: "Input/output error",
        means: "the device reported an input or output error",
    },
    Errno {
        code: libc::ENOSPC,
        name: "ENOSPC",
        text: "No space left on device",
        means: "the device has no space left",
    },
    Errno {
        code: libc::EDQUOT,
        name: "EDQUOT",
        text: "Disk quota exceeded",
        means: "the disk quota is used up",
    },
    Errno {
        code: libc::EINTR,
        name: "EINTR",
        text: "Interrupted system call",
        means: "a signal interrupted the close",
    },
    Errno {
        code: libc::EFBIG,
        name: "EFBIG",
        text: "File too large",
        means: "the file passed the largest size the file system allows",
    },
    Errno {
        code: libc::ESTALE,
        name: "ESTALE",
        text: "Stale file handle",
        means: "the file was removed on the server",
    },
    Errno {
        code: libc::EROFS,
        name: "EROFS",
        text: "Read-only file system",
        means: "the file system is read-only",
    },
];

/// Writes on standard error the message of the row "Standard output failed when the run
/// closed it" for the error number `e` of the close of descriptor 1, which was the file
/// `file` where the system named it (DESIGN.md sec:diagnostics): the headline with the
/// system's error, then the descriptor, the error's name and text and the file, then the
/// repairs.
fn message(e: c_int, file: Option<&str>) {
    let known = ERRNOS.iter().find(|k| k.code == e);
    let mut line = Line::new();
    let _ = line.write_str("Standard output failed when the run closed it: `close(1)` gave ");
    match known {
        Some(k) => {
            let _ = write!(line, "{}, {}", k.name, k.means);
        }
        None => {
            let _ = write!(line, "error number {e}");
        }
    }
    let _ = line.write_str("; output written before it may be lost.\n");
    write_all(line.bytes());
    let mut line = Line::new();
    let _ = line.write_str("The run closed standard output, descriptor 1");
    if file.is_some() {
        let _ = line.write_str(", which was the file `");
    }
    write_all(line.bytes());
    if let Some(f) = file {
        write_all(f.as_bytes());
    }
    let mut line = Line::new();
    if file.is_some() {
        let _ = line.write_str("`");
    }
    match known {
        Some(k) => {
            let _ = writeln!(line, ", and the system gave {} (\"{}\").", k.name, k.text);
        }
        None => {
            let _ = writeln!(line, ", and the system gave error number {e}.");
        }
    }
    write_all(line.bytes());
    let fix = if matches!(e, libc::ENOSPC | libc::EDQUOT) {
        "Free space on the device or raise the quota, and run again."
    } else {
        "Check the device or the server that holds the file, and run again."
    };
    write_all(fix.as_bytes());
    write_all(
        b" To see the failure in the program and act on it, write the output as a file and read \
          the acknowledgment:\n    ack = main::files[\"out.txt\"] <- text;\n    match ack { #ok -> \
          0, #ioError(op:, path:, why:, text:) -> { m.stderr <- \"cannot ${op} ${path}: \
          ${text}\"; 1 } }\n",
    );
}

/// Writes `bytes` to descriptor 2, as much as it takes; a failed write ends it, since there is
/// nowhere else to report it.
fn write_all(mut bytes: &[u8]) {
    while !bytes.is_empty() {
        #[expect(unsafe_code, reason = "write is a libc call")]
        // SAFETY: `write` reads `bytes`, which is borrowed for the call.
        let n = unsafe { libc::write(libc::STDERR_FILENO, bytes.as_ptr().cast(), bytes.len()) };
        match usize::try_from(n) {
            Ok(n) if n > 0 => bytes = &bytes[n..],
            _ if std::io::Error::last_os_error().raw_os_error() == Some(libc::EINTR) => {}
            _ => return,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_listed_error_has_its_own_name_and_number() {
        for (i, a) in ERRNOS.iter().enumerate() {
            for b in &ERRNOS[i + 1..] {
                assert_ne!(a.code, b.code, "{} and {}", a.name, b.name);
            }
            // The text copied from glibc is the system's own.
            let system = std::io::Error::from_raw_os_error(a.code).to_string();
            assert!(system.starts_with(a.text), "{}: {system}", a.name);
        }
    }
}

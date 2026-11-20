//! The limits `main` may set on its own run (DESIGN.md sec:ports, "`main` may limit its own
//! run"): `@limits(memory: b, cpu: d)`, `@timeout(d)` and `@kill(…)` written before `main`. The
//! checker reads them from the program's text, the run and an executable carry them, and the
//! runtime (`zed_rt::limits`) enforces them in the program's own process. The memory limit in
//! force is kept here too, so that the kernel's message for an allocation the system refuses
//! names it ([`crate::num::memory_clause`]).
//!
//! This file imports no other file of the crate: the numbers (`num/room.rs`) and the values
//! read the memory limit in force from it, so an import back would close a cycle between files
//! (step S.1f). The checker turns a written number of seconds into a [`Duration`] itself
//! (`seconds` in zedc-check's `check/limits.rs`).

use std::sync::{Mutex, OnceLock};
use std::time::Duration;

/// The limits written before `main`; every field `None` when none is.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MainLimits {
    /// `memory: b`, the bytes the run may hold at once.
    pub memory: Option<u64>,
    /// `cpu: d`, the processor time of all the run's threads together.
    pub cpu: Option<Duration>,
    /// `@timeout(d)`, the deadline on the run's whole life, from the process's start.
    pub timeout: Option<Duration>,
    /// `@kill(…)`, the deadline of the releases a stop makes.
    pub kill: Kill,
}

/// How a stop of the run ends its releases (DESIGN.md sec:ffi, "A stop's releases have a
/// deadline").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kill {
    /// `@kill(#term, grace: d)`: the releases run for at most `d`; 10 s when nothing is written.
    Term(Duration),
    /// `@kill(#kill)`: a stop exits at once, with no release.
    Kill,
}

/// The grace period of a stop's releases where `@kill` sets none (DESIGN.md sec:ffi).
pub const DEFAULT_GRACE: Duration = Duration::from_secs(10);

impl Default for Kill {
    fn default() -> Kill {
        Kill::Term(DEFAULT_GRACE)
    }
}

impl Kill {
    /// The grace period: `d` for `#term`, none for `#kill`.
    pub fn grace(self) -> Duration {
        match self {
            Kill::Term(d) => d,
            Kill::Kill => Duration::ZERO,
        }
    }
}

impl MainLimits {
    /// Whether nothing is limited: no limit and the default `@kill`.
    pub fn is_none(&self) -> bool {
        *self == MainLimits::default()
    }

    /// The limits as text, one per line, `memory <bytes>`, `cpu <ns>`, `timeout <ns>`,
    /// `kill term <ns>` or `kill kill`, each only where it is written: what an executable
    /// holds of them.
    pub fn to_text(&self) -> String {
        let mut text = String::new();
        if let Some(b) = self.memory {
            text.push_str(&format!("memory {b}\n"));
        }
        if let Some(d) = self.cpu {
            text.push_str(&format!("cpu {}\n", d.as_nanos()));
        }
        if let Some(d) = self.timeout {
            text.push_str(&format!("timeout {}\n", d.as_nanos()));
        }
        match self.kill {
            Kill::Term(d) if d == DEFAULT_GRACE => {}
            Kill::Term(d) => text.push_str(&format!("kill term {}\n", d.as_nanos())),
            Kill::Kill => text.push_str("kill kill\n"),
        }
        text
    }

    /// The limits `text` holds, as [`MainLimits::to_text`] writes them.
    pub fn from_text(text: &str) -> Result<MainLimits, String> {
        let mut limits = MainLimits::default();
        let nanos = |n: &str| n.parse::<u64>().ok().map(Duration::from_nanos);
        for line in text.lines() {
            let bad = || format!("`{line}` is not a limit of `main`");
            match line.split_once(' ').ok_or_else(bad)? {
                ("memory", b) => limits.memory = Some(b.parse().map_err(|_| bad())?),
                ("cpu", d) => limits.cpu = Some(nanos(d).ok_or_else(bad)?),
                ("timeout", d) => limits.timeout = Some(nanos(d).ok_or_else(bad)?),
                ("kill", "kill") => limits.kill = Kill::Kill,
                ("kill", rest) => {
                    let d = rest.strip_prefix("term ").and_then(nanos);
                    limits.kill = Kill::Term(d.ok_or_else(bad)?);
                }
                _ => return Err(bad()),
            }
        }
        Ok(limits)
    }
}

/// `d` as a message writes a limit: `5 min`, `2 h` or `60 s` where it is a whole number of
/// those, else in seconds with the decimals it has, `0.25 s`.
pub fn duration_text(d: Duration) -> String {
    let (s, ns) = (d.as_secs(), d.subsec_nanos());
    match (s, ns) {
        (s, 0) if s >= 3600 && s % 3600 == 0 => format!("{} h", s / 3600),
        (s, 0) if s >= 60 && s % 60 == 0 => format!("{} min", s / 60),
        (s, 0) => format!("{s} s"),
        (s, ns) => {
            let frac = format!("{ns:09}");
            format!("{s}.{} s", frac.trim_end_matches('0'))
        }
    }
}

/// The memory limit in force in this process and the bytes of data the process held when it
/// was set, which the run's count leaves out (`zedc run` holds its compiler's data beside the
/// run's); set once, by [`set_memory`].
static MEMORY: OnceLock<(u64, u64)> = OnceLock::new();

/// Records that this process runs under the memory limit `limit`, counted from `base` bytes
/// of data, which the process held before the run. Only the program's own process sets it,
/// once, as the runtime sets the operating system's limit.
pub fn set_memory(limit: u64, base: u64) {
    let _ = MEMORY.set((limit, base));
}

/// The memory limit in force, and the bytes of data the process held before the run, if one
/// is.
pub fn memory() -> Option<(u64, u64)> {
    MEMORY.get().copied()
}

/// The bytes of data this process holds, as the operating system counts them against its
/// limit on data (`VmData` of `/proc/self/status`, the count `RLIMIT_DATA` limits); `None`
/// where that file is missing or unreadable.
pub fn data_bytes() -> Option<u64> {
    proc_bytes("/proc/self/status", "VmData")
}

/// The bytes of the field `key` of the Linux file `path` (`/proc/self/status`,
/// `/proc/meminfo`), whose sizes are written in kB, as [`proc_kib`] reads them; `None` where
/// the file is missing or unreadable, or [`proc_kib`] finds no such field.
pub fn proc_bytes(path: &str, key: &str) -> Option<u64> {
    proc_kib(&std::fs::read_to_string(path).ok()?, key)
}

/// The bytes of the field `key` of `text`, a line `key:` then spaces or tabs, a count and
/// ` kB`, as Linux writes `VmData:   1234 kB`: the count times 1024 (the kernel's kB is
/// 1024 bytes, `proc(5)`). `key` is written without its colon, and the colon must follow it,
/// so `VmData` does not take a line `VmDataX:`. `None` where no line has the field, its value
/// is not a count in kB, or the bytes pass `u64`. Linear in the length of `text`. Test:
/// `a_proc_field_is_read_in_kib_and_only_by_its_whole_key` (this module), on written text and
/// the real `/proc/meminfo`; it cannot catch a kernel that writes another unit.
pub fn proc_kib(text: &str, key: &str) -> Option<u64> {
    let value = text
        .lines()
        .find_map(|l| l.strip_prefix(key)?.strip_prefix(':'))?;
    let kib: u64 = value.trim().strip_suffix("kB")?.trim().parse().ok()?;
    kib.checked_mul(1024)
}

/// The bytes of data the operating system counts for the run under the memory limit in force:
/// the process's data less what it held before the run; `None` when no limit is in force or
/// the count cannot be read. The limit is enforced by this count, which holds memory the
/// allocator freed and kept for reuse, and leaves out memory the run reuses that the compiler
/// of `zedc run` freed before the run began, so it can be far from what the run holds
/// ([`held`]): 25 MiB for two numbers of 2.8 MiB, 32 KiB for a number of 4 MiB
/// (MSG-run-stop-repairs). The count when the system last refused the run memory, if it has
/// ([`refused`]).
pub fn data_held() -> Option<u64> {
    match *at_refusal() {
        Some((_, data)) => data,
        None => data_now(),
    }
}

/// [`data_held`] now.
fn data_now() -> Option<u64> {
    let (_, base) = memory()?;
    Some(data_bytes()?.saturating_sub(base))
}

/// What the run held, [`held`] and [`data_held`], when the system last refused it memory under
/// the memory limit; `None` until it has.
static AT_REFUSAL: Mutex<Option<(Option<u64>, Option<u64>)>> = Mutex::new(None);

/// [`AT_REFUSAL`], locked; a lock a panic left poisoned still holds the counts.
fn at_refusal() -> std::sync::MutexGuard<'static, Option<(Option<u64>, Option<u64>)>> {
    AT_REFUSAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// Records what the run holds now, under the memory limit in force, as what it held when the
/// system refused it the memory a step asked for: the message is written once the error has
/// reached the run's caller, and by then the step's operands and everything the run built are
/// freed, so a count read then names the memory of a run that has ended (MSG-run-stop-repairs:
/// 19 KiB for a run that held two numbers of 2.8 MiB). Called where the kernel asks the system
/// for memory and is refused; nothing without a limit. A message about a later refusal of a
/// size no machine holds, which asks the system nothing, names this count too.
pub fn refused() {
    if memory().is_some() {
        *at_refusal() = Some((held_now(), data_now()));
    }
}

/// The allocator's count of the bytes the process has in use, and that count when the memory
/// limit was set; set once, by [`count_in_use`].
static IN_USE: OnceLock<(fn() -> u64, u64)> = OnceLock::new();

/// Records `count`, the allocator's count of the bytes the process has in use, and `base`, its
/// value when the run began, for [`held`]. The runtime sets it with the memory limit, since it
/// asks the C library's allocator, which takes `unsafe` code this crate does not have.
pub fn count_in_use(count: fn() -> u64, base: u64) {
    let _ = IN_USE.set((count, base));
}

/// The bytes the run holds under the memory limit in force: the allocator's count of the bytes
/// in use less that count when the run began ([`count_in_use`]); `None` when no limit is in
/// force or the runtime registered no count. Memory freed and kept for reuse is not counted.
/// Not proved exact: under `zedc run` the compiler's own data that is freed during the run is
/// taken off the run's bytes, so the figure may be lower than the run's values by that amount.
/// Classified (PROOF-sweep-zed-kernel): message only. The one reader of this figure is
/// `num::room::memory_clause`, which prints it in the message of a step refused under the
/// limit; the limit itself is enforced by the operating system's count of the run's data
/// (`RLIMIT_DATA`, set in `zed_rt::limits`), which this figure does not feed. So an error in
/// it changes one number in that message, never when the run stops or what it computes.
/// The runtime's own count of its values is plan row MAIN-limits-count. The count when the
/// system last refused the run memory, if it has ([`refused`]).
pub fn held() -> Option<u64> {
    match *at_refusal() {
        Some((held, _)) => held,
        None => held_now(),
    }
}

/// [`held`] now.
fn held_now() -> Option<u64> {
    memory()?;
    let (count, base) = IN_USE.get()?;
    Some(count().saturating_sub(*base))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_limits_read_back_from_their_text() {
        let all = MainLimits {
            memory: Some(1 << 20),
            cpu: Some(Duration::from_millis(2500)),
            timeout: Some(Duration::from_secs(300)),
            kill: Kill::Term(Duration::from_secs(3)),
        };
        for l in [
            all,
            MainLimits::default(),
            MainLimits {
                kill: Kill::Kill,
                ..MainLimits::default()
            },
        ] {
            assert_eq!(MainLimits::from_text(&l.to_text()), Ok(l));
        }
        assert_eq!(MainLimits::default().to_text(), "");
        assert!(MainLimits::from_text("memory x\n").is_err());
        assert!(MainLimits::from_text("kill soon\n").is_err());
    }

    #[test]
    fn a_duration_is_written_in_the_largest_whole_unit() {
        let t = duration_text;
        assert_eq!(t(Duration::from_secs(60)), "1 min");
        assert_eq!(t(Duration::from_secs(300)), "5 min");
        assert_eq!(t(Duration::from_secs(7200)), "2 h");
        assert_eq!(t(Duration::from_secs(90)), "90 s");
        assert_eq!(t(Duration::from_secs(1)), "1 s");
        assert_eq!(t(Duration::from_millis(250)), "0.25 s");
        assert_eq!(t(Duration::from_millis(1500)), "1.5 s");
    }

    #[test]
    fn the_data_of_this_process_is_read() {
        assert!(data_bytes().is_some_and(|b| b > 0));
    }

    #[test]
    fn a_proc_field_is_read_in_kib_and_only_by_its_whole_key() {
        let status = "Name:\tzed\nVmDataX:\t 7 kB\nVmData:\t    1234 kB\nThreads:\t4\n";
        assert_eq!(proc_kib(status, "VmData"), Some(1234 * 1024));
        assert_eq!(proc_kib(status, "VmDat"), None);
        assert_eq!(proc_kib(status, "Threads"), None);
        assert_eq!(proc_kib(status, "VmSize"), None);
        assert_eq!(proc_kib("MemTotal: 0 kB\n", "MemTotal"), Some(0));
        assert_eq!(proc_kib("MemTotal: x kB\n", "MemTotal"), None);
        let max = format!("MemTotal: {} kB\n", u64::MAX / 1024);
        assert_eq!(proc_kib(&max, "MemTotal"), Some(u64::MAX / 1024 * 1024));
        let over = format!("MemTotal: {} kB\n", u64::MAX / 1024 + 1);
        assert_eq!(proc_kib(&over, "MemTotal"), None);
        assert!(proc_bytes("/proc/meminfo", "MemTotal").is_some_and(|b| b > 0));
    }
}

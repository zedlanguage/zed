//! The limits `main` may set on its own run (DESIGN.md sec:ports, "`main` may limit its own
//! run"): `@limits(memory: b, cpu: d)`, `@timeout(d)` and `@kill(…)` written before `main`. The
//! checker reads them from the program's text, the run and an executable carry them, and the
//! runtime (`zed_rt::limits`) enforces them in the program's own process. The memory limit in
//! force is kept here too, so that the kernel's message for an allocation the system refuses
//! names it ([`crate::num::memory_clause`]).

use std::sync::OnceLock;
use std::time::Duration;

use crate::num::Rat;

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

/// `r` seconds as a [`Duration`], rounded up to a whole nanosecond, so that a limit is never
/// shorter than written; `None` where `r` is not above 0 or is longer than `u64::MAX`
/// nanoseconds (585 years). O(size of `r`).
pub fn seconds(r: &Rat) -> Option<Duration> {
    if r.is_negative() || r.is_zero() {
        return None;
    }
    let (n, d) = r.built_parts().ok()?;
    let nanos = (&*n * 1_000_000_000u32 + &*d - 1u32) / &*d;
    u64::try_from(&nanos).ok().map(Duration::from_nanos)
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
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find_map(|l| l.strip_prefix("VmData:"))?;
    let kib: u64 = line.trim().strip_suffix("kB")?.trim().parse().ok()?;
    kib.checked_mul(1024)
}

/// The bytes the run holds under the memory limit in force: the process's data less what it
/// held before the run; `None` when no limit is in force or the count cannot be read.
pub fn held() -> Option<u64> {
    let (_, base) = memory()?;
    Some(data_bytes()?.saturating_sub(base))
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
    fn a_number_of_seconds_is_rounded_up_to_a_nanosecond() {
        let rat = |n: i64, d: i64| Rat::new(n.into(), d.into()).expect("a nonzero denominator");
        assert_eq!(seconds(&rat(5, 2)), Some(Duration::from_millis(2500)));
        assert_eq!(seconds(&rat(1, 3)), Some(Duration::from_nanos(333_333_334)));
        assert_eq!(seconds(&rat(0, 1)), None);
        assert_eq!(seconds(&rat(-1, 1)), None);
        assert_eq!(seconds(&rat(i64::MAX, 1)), None);
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
}

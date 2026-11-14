//! The limits written before `main` (DESIGN.md sec:ports, "`main` may limit its own run"):
//! `@limits(memory: b, cpu: d)`, `@timeout(d)` and `@kill(#term, grace: d)` or `@kill(#kill)`.
//! The resolver has checked where they stand and their form (`Resolver::main_fact` in
//! zedc-resolve) and resolved their arguments; here each argument must be a constant the text
//! fixes, as for `@stack(bytes: b)`: a positive number of bytes for `memory:`, and a positive
//! number of seconds, an `int` or a `rat`, for each duration (a `Duration` is written `2r`
//! before step L12 gives units). The limits found go to [`Info::limits`], which the run and an
//! executable carry, and the memory limit bounds the numbers the checker can size
//! (`Ck::powers_over_main_limit`).
//!
//! `Ck::main_limits` in `check/walk.rs` checks each argument with the walk and reads the value
//! the text fixes for it; this file judges that value and writes the rejection. The walk calls
//! this file and this file calls nothing of the walk: a call each way would be a cycle between
//! files, which Zed forbids (step S.1f, `tests/steps/s_01f_import_graph`). For the same reason
//! `seconds` is here and not in `zed_kernel::limits`, which the kernel's numbers read for the
//! memory limit in force and which therefore imports no number.

use std::time::Duration;

use super::*;

/// The target `target`, as `build.target` names it (`x86_64-linux`), as a message names it:
/// the system, then the architecture, `Linux x86_64`. A name of another form is kept as it is.
pub(super) fn target_text(target: &str) -> String {
    let Some((arch, os)) = target.split_once('-') else {
        return target.to_string();
    };
    let os = match os {
        "linux" => "Linux",
        "macos" => "macOS",
        "windows" => "Windows",
        other => other,
    };
    format!("{os} {arch}")
}

/// `r` seconds as a [`Duration`], rounded up to a whole nanosecond, so that a limit is never
/// shorter than written; `None` where `r` is not above 0 or is longer than `u64::MAX`
/// nanoseconds (585 years). O(size of `r`).
fn seconds(r: &Rat) -> Option<Duration> {
    if r.is_negative() || r.is_zero() {
        return None;
    }
    let (n, d) = r.built_parts().ok()?;
    let nanos = (&*n * 1_000_000_000u32 + &*d - 1u32) / &*d;
    u64::try_from(&nanos).ok().map(Duration::from_nanos)
}

impl<'a> Ck<'_, 'a> {
    /// The expression `e` names: the value of the `name = value` binder a name reads, followed
    /// through a chain of names, as `d` in `d = 1r/2r; @limits(cpu: d)`, since [`Ck::fixed_value`]
    /// reads a `rat` only from its literals and their operations. A visited set ends a chain
    /// that comes back to a name; O(length of the chain).
    pub(super) fn through_names(&self, e: &'a Expr) -> &'a Expr {
        let mut x = e;
        let mut seen = HashSet::new();
        while seen.insert(x.span)
            && let Some(v) = self.bound_value(x)
        {
            x = v;
        }
        x
    }

    /// The bytes of `memory: code`, written at `at`, whose fixed value is `value`, a positive
    /// `int`; `None`, with the rejection, where the text fixes no value, or one that is not
    /// positive or passes the target's address space.
    pub(super) fn bytes_limit(
        &mut self,
        at: Span,
        code: &str,
        value: Option<Value>,
    ) -> Option<u64> {
        let why = match value {
            Some(Value::Int(b)) if b > 0 => return Some(b.unsigned_abs()),
            Some(Value::Int(_)) => format!(
                "`memory: {code}` leaves the run no memory: the memory limit of `main` is a \
                 number of bytes above 0, as `memory: 1048576` for 1 MiB."
            ),
            Some(Value::Big(r)) if !r.is_negative() => format!(
                "`memory: {code}` is more memory than {} addresses: write at most `2^63`.",
                self.t
                    .target
                    .map_or("a 64-bit target".to_string(), target_text)
            ),
            Some(_) => format!(
                "`memory: {code}` is not a number of bytes: the memory limit of `main` is an \
                 `int` above 0, as `memory: 1048576` for 1 MiB."
            ),
            None => format!(
                "`memory: {code}` is not a constant: the memory limit of `main` is fixed when \
                 the program is built. Write the number of bytes, as `memory: 1048576`."
            ),
        };
        self.error_with(at, why, Vec::new());
        None
    }

    /// The duration of `code`, written at `at` after `field` (`cpu: `, `grace: ` or nothing for
    /// `@timeout`), whose fixed value is `value`: a positive number of seconds, an `int` or a
    /// `rat`; `None`, with the rejection, where the text fixes no value or one that is not
    /// positive.
    pub(super) fn duration_limit(
        &mut self,
        at: Span,
        code: &str,
        field: &str,
        value: Option<Value>,
    ) -> Option<Duration> {
        let d = match value {
            Some(Value::Int(s)) if s > 0 => Some(Duration::from_secs(s.unsigned_abs())),
            Some(Value::Int(_)) => None,
            Some(Value::Big(r) | Value::Rat(r)) => seconds(&r),
            Some(_) => {
                let why = format!(
                    "`{field}{code}` is not a number of seconds: write an `int` or a `rat` \
                     above 0, as `{field}2r` for 2 s or `{field}1r/2r` for half a second."
                );
                self.error_with(at, why, Vec::new());
                return None;
            }
            None => {
                let why = format!(
                    "`{field}{code}` is not a constant: a limit of `main` is fixed when the \
                     program is built. Write the number of seconds, as `{field}60r`."
                );
                self.error_with(at, why, Vec::new());
                return None;
            }
        };
        if d.is_none() {
            let why = format!(
                "`{field}{code}` is not a time the run can have: a limit of `main` is a number \
                 of seconds above 0 and below 2^64 nanoseconds, as `{field}60r`."
            );
            self.error_with(at, why, Vec::new());
        }
        d
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn a_target_is_named_system_first() {
        assert_eq!(target_text("x86_64-linux"), "Linux x86_64");
        assert_eq!(target_text("aarch64-macos"), "macOS aarch64");
        assert_eq!(target_text("riscv64-windows"), "Windows riscv64");
        assert_eq!(target_text("riscv64-plan9"), "plan9 riscv64");
        assert_eq!(target_text("wasm"), "wasm");
    }
}

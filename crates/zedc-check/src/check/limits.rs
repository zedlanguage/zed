//! The limits written before `main` (DESIGN.md sec:ports, "`main` may limit its own run"):
//! `@limits(memory: b, cpu: d)`, `@timeout(d)` and `@kill(#term, grace: d)` or `@kill(#kill)`.
//! The resolver has checked where they stand and their form (`Resolver::main_fact` in
//! zedc-resolve) and resolved their arguments; here each argument must be a constant the text
//! fixes, as for `@stack(bytes: b)`: a positive number of bytes for `memory:`, and a positive
//! number of seconds, an `int` or a `rat`, for each duration (a `Duration` is written `2r`
//! before step L12 gives units). The limits found go to [`Info::limits`], which the run and an
//! executable carry, and the memory limit bounds the numbers the checker can size
//! (`Ck::powers_over_main_limit`).

use std::time::Duration;

use zed_kernel::limits::{Kill, MainLimits, seconds};

use super::walk::target_text;
use super::*;

impl<'a> Ck<'_, 'a> {
    /// Reads the limits written before the unit's `main` in `unit` into [`Info::limits`],
    /// rejecting each argument that is not a positive constant, and keeps the memory limit with
    /// its spans for [`Ck::powers_over_main_limit`]. Called after the walk: each argument is
    /// checked as an expression of the top scope ([`Ck::walk_alone`]), where a name reads the
    /// binding the walk found and an operation on literals is folded, as `1r/2r`. O(number of
    /// top-level statements + size of the arguments).
    pub(super) fn main_limits(&mut self, unit: &'a [Stmt]) {
        let Some(annots) = unit.iter().find_map(|s| match &s.kind {
            StmtKind::Annotated { annots, decl }
                if matches!(&decl.bare().kind, StmtKind::Function(f) if f.main.is_some()) =>
            {
                Some(annots)
            }
            _ => None,
        }) else {
            return;
        };
        let mut limits = MainLimits::default();
        for a in annots {
            let args = a.positional.iter().chain(a.named.iter().map(|(_, e)| e));
            for e in args.filter(|e| !matches!(e.kind, ExprKind::Atom(_))) {
                self.walk_alone(e);
            }
            let arg = |n: &str| a.named.iter().find(|(w, _)| w == n).map(|(_, e)| e);
            match a.name.as_str() {
                "limits" => {
                    if let Some(e) = arg("memory") {
                        limits.memory = self.bytes_limit(e);
                        if let Some(b) = limits.memory {
                            self.main_memory = Some((b, a.span, e.span));
                        }
                    }
                    if let Some(e) = arg("cpu") {
                        limits.cpu = self.duration_limit(e, "cpu: ");
                    }
                }
                "timeout" => {
                    if let Some(e) = a.positional.first() {
                        limits.timeout = self.duration_limit(e, "");
                    }
                }
                "kill" => match arg("grace") {
                    Some(e) => {
                        let d = self.duration_limit(e, "grace: ");
                        limits.kill = Kill::Term(d.unwrap_or(limits.kill.grace()));
                    }
                    None if matches!(
                        a.positional.first().map(|e| &e.kind),
                        Some(ExprKind::Atom(x)) if x == "kill"
                    ) =>
                    {
                        limits.kill = Kill::Kill;
                    }
                    None => {}
                },
                _ => {}
            }
        }
        self.info.limits = limits;
    }

    /// The expression `e` names: the value of the `name = value` binder a name reads, followed
    /// through a chain of names, as `d` in `d = 1r/2r; @limits(cpu: d)`, since [`Ck::fixed_value`]
    /// reads a `rat` only from its literals and their operations. A visited set ends a chain
    /// that comes back to a name; O(length of the chain).
    fn through_names(&self, e: &'a Expr) -> &'a Expr {
        let mut x = e;
        let mut seen = HashSet::new();
        while seen.insert(x.span)
            && let Some(v) = self.bound_value(x)
        {
            x = v;
        }
        x
    }

    /// The bytes `e` fixes for `memory: e`, a positive `int`; `None`, with the rejection,
    /// where it fixes none, or one that is not positive or passes the target's address space.
    fn bytes_limit(&mut self, e: &'a Expr) -> Option<u64> {
        let code = self.code(Some(e.span)).unwrap_or("the limit");
        let why = match self.fixed_value(self.through_names(e)) {
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
        self.error_with(e.span, why, Vec::new());
        None
    }

    /// The duration `e` fixes, written after `field` (`cpu: `, `grace: ` or nothing for
    /// `@timeout`): a positive number of seconds, an `int` or a `rat`; `None`, with the
    /// rejection, where it fixes none or one that is not positive.
    fn duration_limit(&mut self, e: &'a Expr, field: &str) -> Option<Duration> {
        let code = self.code(Some(e.span)).unwrap_or("the limit");
        let d = match self.fixed_value(self.through_names(e)) {
            Some(Value::Int(s)) if s > 0 => Some(Duration::from_secs(s.unsigned_abs())),
            Some(Value::Int(_)) => None,
            Some(Value::Big(r) | Value::Rat(r)) => seconds(&r),
            Some(_) => {
                let why = format!(
                    "`{field}{code}` is not a number of seconds: write an `int` or a `rat` \
                     above 0, as `{field}2r` for 2 s or `{field}1r/2r` for half a second."
                );
                self.error_with(e.span, why, Vec::new());
                return None;
            }
            None => {
                let why = format!(
                    "`{field}{code}` is not a constant: a limit of `main` is fixed when the \
                     program is built. Write the number of seconds, as `{field}60r`."
                );
                self.error_with(e.span, why, Vec::new());
                return None;
            }
        };
        if d.is_none() {
            let why = format!(
                "`{field}{code}` is not a time the run can have: a limit of `main` is a number \
                 of seconds above 0 and below 2^64 nanoseconds, as `{field}60r`."
            );
            self.error_with(e.span, why, Vec::new());
        }
        d
    }
}

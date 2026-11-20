//! A count or index held as `u32` (DRY-len-as-u32-checked, 2026-11-20): [`to_u32`], the one
//! conversion for the workspace. It replaces 76 casts `len() as u32`, which kept the low 32
//! bits of a count past `u32::MAX` and so gave a wrong id with no error, and the hand-written
//! copies `u32::try_from(len).expect(..)`.
//!
//! The bound. Each count converted is the length of a vector held in memory, or an index into
//! one. On a 64-bit target nothing bounds such a length below 2^32: a vector of 2^32 one-byte
//! entries takes 4 GiB. So no site can prove its count fits, and none relies on it: past
//! `u32::MAX` the conversion panics, naming what was counted and the count, where the cast
//! went on with a wrong id. The sites keep `u32` ids because they halve the memory of the
//! tables that hold them; a workspace that needs more than 2^32 of one kind of id needs those
//! tables widened, and the panic says which. Test:
//! `tests::a_count_past_u32_max_is_refused_and_one_at_it_is_kept`.
//!
//! [`to_u32_below`] is for tables that keep the top values as markers (`u32::MAX` for "none"
//! in zed-kernel `types/bucket.rs` and `types/empty/escape.rs`, `u32::MAX - 1` for "not
//! reached" in zedc-lattice `schedule.rs`): there `to_u32` would let an id equal a marker.
//! Test: `tests::an_id_at_a_marker_is_refused_and_one_below_it_is_kept`.

/// `n` as a `u32`, for a count or index of `what` (a plural noun, such as "definitions").
///
/// # Panics
///
/// When `n` is past `u32::MAX`, with the message "more than 4294967295 {what}: {n}" at the
/// caller's line.
#[track_caller]
#[inline]
pub fn to_u32(n: usize, what: &str) -> u32 {
    match u32::try_from(n) {
        Ok(v) => v,
        Err(_) => panic!("more than {} {what}: {n}", u32::MAX),
    }
}

/// `n` as a `u32` below `bound`, for an id of `what` where the values from `bound` up are kept
/// as markers (such as `u32::MAX` for "none"), so an id equal to a marker would read as one.
///
/// # Panics
///
/// When `n` is `bound` or more, with the message "more than {bound} {what}: {n}" at the
/// caller's line.
#[track_caller]
#[inline]
pub fn to_u32_below(n: usize, bound: u32, what: &str) -> u32 {
    match u32::try_from(n) {
        Ok(v) if v < bound => v,
        _ => panic!("more than {bound} {what}: {n}"),
    }
}

#[cfg(test)]
mod tests {
    use super::{to_u32, to_u32_below};

    #[test]
    fn a_count_past_u32_max_is_refused_and_one_at_it_is_kept() {
        assert_eq!(to_u32(0, "nodes"), 0);
        assert_eq!(to_u32(7, "nodes"), 7);
        assert_eq!(to_u32(u32::MAX as usize, "nodes"), u32::MAX);
        let past = u32::MAX as usize + 1;
        let refused = std::panic::catch_unwind(|| to_u32(past, "nodes"));
        let message = refused.expect_err("u32::MAX + 1 is refused");
        let text = message
            .downcast_ref::<String>()
            .expect("the message is formatted");
        assert_eq!(text, "more than 4294967295 nodes: 4294967296");
        // The cast it replaces keeps the low 32 bits: 0 here, a wrong id with no error.
        assert_eq!(past as u32, 0);
    }

    /// The panic message of `f`, which must panic.
    fn refusal(f: impl FnOnce() -> u32 + std::panic::UnwindSafe) -> String {
        let message = std::panic::catch_unwind(f).expect_err("refused");
        message
            .downcast_ref::<String>()
            .expect("the message is formatted")
            .clone()
    }

    #[test]
    fn an_id_at_a_marker_is_refused_and_one_below_it_is_kept() {
        assert_eq!(to_u32_below(4, 5, "slots"), 4);
        let max = u32::MAX as usize;
        assert_eq!(to_u32_below(max - 1, u32::MAX, "slots"), u32::MAX - 1);
        assert_eq!(
            refusal(|| to_u32_below(5, 5, "slots")),
            "more than 5 slots: 5"
        );
        assert_eq!(
            refusal(|| to_u32_below(max, u32::MAX, "slots")),
            "more than 4294967295 slots: 4294967295"
        );
        assert_eq!(
            refusal(|| to_u32_below(max + 1, u32::MAX, "slots")),
            "more than 4294967295 slots: 4294967296"
        );
        // `to_u32` keeps `u32::MAX`, which a table with that marker would read as the marker.
        assert_eq!(to_u32(max, "slots"), u32::MAX);
        // A bound of 0 keeps no id, and the top of `usize` is named in full
        // (TEST-dry-shared-units).
        assert_eq!(
            refusal(|| to_u32_below(0, 0, "slots")),
            "more than 0 slots: 0"
        );
        assert_eq!(
            refusal(|| to_u32(usize::MAX, "nodes")),
            format!("more than 4294967295 nodes: {}", usize::MAX)
        );
    }
}

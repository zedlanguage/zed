//! The hash that the digests of types, nodes and expressions are built with. It imports no
//! other module of `types`, so the modules that only hash, such as `bdd::set`, depend on no
//! more of the type algebra than this.

/// Combines two hashes; the digests of types, nodes and expressions are built with it from
/// their children's, so that each is computed once, when it is made.
pub(crate) fn mix(a: u64, b: u64) -> u64 {
    if crate::address::SHORT {
        return crate::address::short64(salted(mix_byte(a, b)));
    }
    salted(crate::digest::step(a, b))
}

thread_local! {
    /// Set while [`blind`] runs: names are then left out of the order of types.
    static BLIND: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Set while [`names_first`] runs: the names-aware digests are then compared first.
    static NAMED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// `f` run with the order of types reading the names-aware digests before the name-free ones
/// ([`digests_cmp`]): the order of the atoms when they were ordered by the digests of names,
/// which the printer follows so that the names it takes do not depend on the name-free order.
/// Only comparisons may run inside: a table ordered by the other order is not to be read.
pub(crate) fn names_first<R>(f: impl FnOnce() -> R) -> R {
    /// Puts back the flag as it was, also when `f` panics.
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            NAMED.set(self.0);
        }
    }
    let _restore = Restore(NAMED.replace(true));
    f()
}

/// The order of two nodes by their name-free and names-aware digests `(p, n)`: the name-free
/// first, then the names-aware ([`named_cmp`]); under [`names_first`], the names-aware first.
pub(crate) fn digests_cmp((p, n): (u64, u64), (q, m): (u64, u64)) -> std::cmp::Ordering {
    match NAMED.get() {
        true => n.cmp(&m).then(p.cmp(&q)),
        false => p.cmp(&q).then_with(|| named_cmp(n, m)),
    }
}

/// `f` run with definition names left out of the order of types: the names-aware digests are
/// not compared ([`named_cmp`]), and two keys of groups of one canonical form are equal
/// (`rec::Key::order`), so that two types equal but for definition names compare equal.
pub(crate) fn blind<R>(f: impl FnOnce() -> R) -> R {
    /// Puts back the flag as it was, also when `f` panics.
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            BLIND.set(self.0);
        }
    }
    let _restore = Restore(BLIND.replace(true));
    f()
}

/// Whether [`blind`] is running.
pub(crate) fn names_blind() -> bool {
    BLIND.get()
}

/// The order of two names-aware digests: equal while [`blind`] runs.
pub(crate) fn named_cmp(a: u64, b: u64) -> std::cmp::Ordering {
    match names_blind() {
        true => std::cmp::Ordering::Equal,
        false => a.cmp(&b),
    }
}

/// `mix` of the short-addresses build, whose digests keep 8 bits: a function of the two
/// arguments' bytes folded together that is one-to-one in each argument while the other is
/// fixed. Keeping the low 8 bits of the full mix made each step a random map of 256 values,
/// whose image is about 63% of them, and a type's digest is the end of a chain of such steps:
/// the names a0 to a99999 reached 73 of the 256 atom digests and the tuple types over them 31
/// (BUCKET-cmp-cost).
fn mix_byte(a: u64, b: u64) -> u64 {
    u64::from(spread(spread(fold(a)) ^ fold(b)))
}

/// The bytes of `x` combined by exclusive or: `x` itself when it is below 256.
fn fold(x: u64) -> u8 {
    let x = x ^ (x >> 32);
    let x = x ^ (x >> 16);
    (x ^ (x >> 8)) as u8
}

/// A one-to-one map of bytes that moves every bit: each step, an addition, a multiplication by
/// an odd number or an exclusive or with the value shifted right, is one-to-one.
fn spread(x: u8) -> u8 {
    let x = x.wrapping_add(0x3b);
    let x = (x ^ (x >> 4)).wrapping_mul(0xc5);
    let x = (x ^ (x >> 3)).wrapping_mul(0x9d);
    x ^ (x >> 4)
}

#[cfg(test)]
thread_local! {
    /// A test's change of every digest made on its thread (module `print`'s tests): a thread with
    /// another salt orders the atoms of its diagrams as another hash would.
    pub(crate) static SALT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// `h` with this thread's salt. Read by `try_with`, which std marks inline, so the read is one
/// instruction in `mix`. `SALT.get()` and `SALT.with` are not marked inline, and were called out
/// of line and through a pointer: each `mix` took 39 instructions with them and takes 19 now, and
/// they were 6% of the instructions of `bdd`'s parity scaling test (KERNEL-alloc-count-cost). A `const`
/// thread-local with no destructor is never gone, so the `0` is never used.
#[cfg(test)]
fn salted(h: u64) -> u64 {
    h ^ SALT.try_with(std::cell::Cell::get).unwrap_or(0)
}

#[cfg(not(test))]
#[inline]
fn salted(h: u64) -> u64 {
    h
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_short_mix_is_one_to_one_in_each_argument() {
        // A chain of mixes keeps every byte it is given apart, so the digests of the
        // short-addresses build spread over all 256 values (BUCKET-cmp-cost).
        for x in 0..256u64 {
            let mut by_a = [false; 256];
            let mut by_b = [false; 256];
            for y in 0..256u64 {
                by_a[mix_byte(y, x) as usize] = true;
                by_b[mix_byte(x, y) as usize] = true;
            }
            assert!(by_a.iter().all(|&s| s) && by_b.iter().all(|&s| s), "{x}");
        }
        assert_eq!(
            fold(0x1234_5678_9abc_def0),
            0x12 ^ 0x34 ^ 0x56 ^ 0x78 ^ 0x9a ^ 0xbc ^ 0xde ^ 0xf0
        );
    }
}

//! The hash that the digests of types, nodes and expressions are built with. It imports no
//! other module of `types`, so the modules that only hash, such as `bdd::set`, depend on no
//! more of the type algebra than this.

/// Combines two hashes; the digests of types, nodes and expressions are built with it from
/// their children's, so that each is computed once, when it is made.
pub(crate) fn mix(a: u64, b: u64) -> u64 {
    // splitmix64's finalizer.
    let mut z = (a.rotate_left(29) ^ b).wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    crate::address::short64(salted(z ^ (z >> 31)))
}

#[cfg(test)]
thread_local! {
    /// A test's change of every digest made on its thread (module `print`'s tests): a thread with
    /// another salt orders the atoms of its diagrams as another hash would.
    pub(crate) static SALT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn salted(h: u64) -> u64 {
    h ^ SALT.get()
}

#[cfg(not(test))]
#[inline]
fn salted(h: u64) -> u64 {
    h
}

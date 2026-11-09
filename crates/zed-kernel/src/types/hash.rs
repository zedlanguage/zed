//! The hash that the digests of types, nodes and expressions are built with. It imports no
//! other module of `types`, so the modules that only hash, such as `bdd::set`, depend on no
//! more of the type algebra than this.

/// Combines two hashes; the digests of types, nodes and expressions are built with it from
/// their children's, so that each is computed once, when it is made.
pub(crate) fn mix(a: u64, b: u64) -> u64 {
    if crate::address::SHORT {
        return crate::address::short64(salted(mix_byte(a, b)));
    }
    // splitmix64's finalizer.
    let mut z = (a.rotate_left(29) ^ b).wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    salted(z ^ (z >> 31))
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

/// The hasher of the memo of restricted list cells (`bdd::list::Memo`), of the thread's tables of
/// live rows, morphism types and set nodes: splitmix64's finalizer on each `u64` in turn.
/// SipHash took an eighth of the restriction of a list of three blocks. It is here, beside
/// `mix`, so that `bdd::set` hashes with it without importing `bdd` (s_01f_import_graph).
#[derive(Default)]
pub(crate) struct KeyHasher(u64);

impl std::hash::Hasher for KeyHasher {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.write_u64(u64::from(b));
        }
    }

    fn write_u64(&mut self, x: u64) {
        let mut z = (self.0.rotate_left(29) ^ x).wrapping_add(0x9e37_79b9_7f4a_7c15);
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        self.0 = z ^ (z >> 31);
    }

    fn finish(&self) -> u64 {
        self.0
    }
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

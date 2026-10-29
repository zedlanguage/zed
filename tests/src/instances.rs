//! Instances for the finite-model harness (step M0.10) and the steps that reuse it: exhaustive
//! enumerations in shortlex order, cut to the rung 6 bounds of [`zed_kernel::budgets`], and
//! seeded random instances beyond them.

use zed_kernel::budgets::{BMC_FLOATS, BMC_INT};
use zed_kernel::{Family, Value};

/// How many seeded random instances each law runs beyond its exhaustive ones.
pub const RANDOM_INSTANCES: usize = 512;

/// A SplitMix64 generator, so that every random instance is reproducible from its seed.
pub struct Rng(u64);

impl Rng {
    /// A generator from `seed`.
    pub fn new(seed: u64) -> Self {
        Rng(seed)
    }

    /// The next 64 random bits.
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A number in `0..n`.
    pub fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }

    /// A number in `lo..=hi`.
    pub fn int(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.below((hi - lo + 1) as usize) as i64
    }

    /// One element of `xs`.
    pub fn pick<T: Clone>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len())].clone()
    }

    /// A sequence of at most `max_len` elements of `alphabet`, its length uniform.
    pub fn seq<T: Clone>(&mut self, alphabet: &[T], max_len: usize) -> Vec<T> {
        let n = self.below(max_len + 1);
        (0..n).map(|_| self.pick(alphabet)).collect()
    }
}

/// The integers of the rung 6 instance, `-8..=8`.
pub fn bmc_ints() -> Vec<i64> {
    BMC_INT.collect()
}

/// The floats of the rung 6 instance, as values.
pub fn bmc_floats() -> Vec<Value> {
    BMC_FLOATS.iter().map(|&x| Value::float(x)).collect()
}

/// Every sequence of at most `max_len` elements of `alphabet`, in shortlex order: by length,
/// then lexicographically in the alphabet's order.
pub fn shortlex<T: Clone>(alphabet: &[T], max_len: usize) -> Vec<Vec<T>> {
    let mut out = vec![vec![]];
    let mut level = vec![vec![]];
    for _ in 0..max_len {
        let mut next = Vec::new();
        for prefix in &level {
            for a in alphabet {
                let mut s: Vec<T> = prefix.clone();
                s.push(a.clone());
                next.push(s);
            }
        }
        out.extend(next.iter().cloned());
        level = next;
    }
    out
}

/// Every partial map from `keys` to `alphabet`: each key absent or bound to one element.
pub fn partial_maps<T: Clone>(keys: &[i64], alphabet: &[T]) -> Vec<Vec<(i64, T)>> {
    let mut out = vec![vec![]];
    for &k in keys {
        let mut next = Vec::new();
        for m in &out {
            next.push(m.clone());
            for a in alphabet {
                let mut m = m.clone();
                m.push((k, a.clone()));
                next.push(m);
            }
        }
        out = next;
    }
    out
}

/// The sequence `xs` as a family `0..n -> x`.
pub fn seq_value<T: Clone + Into<Value>>(xs: &[T]) -> Value {
    Value::Family(Family::of(
        xs.iter().enumerate().map(|(i, x)| (i as i64, x.clone())),
    ))
}

/// The partial map `m` as a one-level family.
pub fn map_value<T: Clone + Into<Value>>(m: &[(i64, T)]) -> Value {
    Value::Family(Family::of(m.iter().cloned()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shortlex_orders_by_length_then_alphabet() {
        let s = shortlex(&[1, 2], 2);
        assert_eq!(
            s,
            vec![
                vec![],
                vec![1],
                vec![2],
                vec![1, 1],
                vec![1, 2],
                vec![2, 1],
                vec![2, 2]
            ]
        );
        assert_eq!(shortlex(&bmc_ints(), 2).len(), 1 + 17 + 289);
    }

    #[test]
    fn partial_maps_count_absent_as_a_choice() {
        let m = partial_maps(&[0, 1], &['a', 'b']);
        assert_eq!(m.len(), 9);
        assert!(m.contains(&vec![(1, 'b')]));
    }

    #[test]
    fn random_draws_repeat_from_one_seed() {
        let (mut a, mut b) = (Rng::new(7), Rng::new(7));
        let xs: Vec<i64> = (0..50).map(|_| a.int(-8, 8)).collect();
        let ys: Vec<i64> = (0..50).map(|_| b.int(-8, 8)).collect();
        assert_eq!(xs, ys);
        assert!(xs.iter().all(|x| (-8..=8).contains(x)));
        assert!(xs.contains(&-8) && xs.contains(&8));
    }
}

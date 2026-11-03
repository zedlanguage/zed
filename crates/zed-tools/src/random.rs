//! The random generator of the fuzz: Dart's `Random(seed)` on its virtual machine, a
//! multiply-with-carry generator, so that a seed keeps naming the sentences it named when the
//! tool was written in Dart.

const A: u64 = 0xffff_da61;

/// A generator's state.
#[derive(Clone, Debug)]
pub struct Random {
    state: u64,
}

impl Random {
    /// The generator of `seed`.
    pub fn new(seed: i64) -> Random {
        // Thomas Wang's 64-bit mix.
        let mut n = seed as u64;
        n = (!n).wrapping_add(n << 21);
        n ^= n >> 24;
        n = n.wrapping_mul(265);
        n ^= n >> 14;
        n = n.wrapping_mul(21);
        n ^= n >> 28;
        n = n.wrapping_add(n << 31);
        let mut r = Random {
            state: if n == 0 { 0x5a17 } else { n },
        };
        for _ in 0..4 {
            r.next_state();
        }
        r
    }

    fn next_state(&mut self) {
        self.state = (A * (self.state & 0xffff_ffff)).wrapping_add(self.state >> 32);
    }

    /// A number below `max`, which is not 0 and at most 2^32.
    pub fn next_int(&mut self, max: u64) -> u64 {
        if max.is_power_of_two() {
            self.next_state();
            return self.state & 0xffff_ffff & (max - 1);
        }
        loop {
            self.next_state();
            let rnd = self.state & 0xffff_ffff;
            let result = rnd % max;
            if rnd - result + max <= 1 << 32 {
                return result;
            }
        }
    }

    /// A number in `[0, 1)`.
    pub fn next_double(&mut self) -> f64 {
        let high = self.next_int(1 << 26) as f64;
        let low = self.next_int(1 << 27) as f64;
        (high * (1u64 << 27) as f64 + low) / (1u64 << 53) as f64
    }
}

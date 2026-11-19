//! A set of small numbers, one bit each.

/// The bits in a word of a [`BitSet`].
const WORD: usize = u64::BITS as usize;

/// The word holding bit `i`, and the bit's mask in it.
fn place(i: usize) -> (usize, u64) {
    (i / WORD, 1 << (i % WORD))
}

/// A set of numbers `0..`, one bit each in words of 64. It grows as numbers are added, so a
/// number past its end is simply absent; [`BitSet::new`] makes room for numbers below `n` at
/// once, so a set of known size is never resized. Two sets are equal when they hold the same
/// numbers, whatever room each has.
#[derive(Clone, Debug, Default)]
pub struct BitSet(Vec<u64>);

impl BitSet {
    /// The empty set, with room for the numbers below `n`.
    pub fn new(n: usize) -> BitSet {
        BitSet(vec![0; n.div_ceil(WORD)])
    }

    /// Adds `i`; whether it was absent.
    pub fn insert(&mut self, i: usize) -> bool {
        let (w, bit) = place(i);
        if w >= self.0.len() {
            self.0.resize(w + 1, 0);
        }
        let absent = self.0[w] & bit == 0;
        self.0[w] |= bit;
        absent
    }

    /// Whether `i` is in the set.
    pub fn contains(&self, i: usize) -> bool {
        let (w, bit) = place(i);
        self.0.get(w).is_some_and(|x| x & bit != 0)
    }

    /// Adds `other`'s numbers; whether any was new. O(words of `other`).
    pub fn union(&mut self, other: &BitSet) -> bool {
        if other.0.len() > self.0.len() {
            self.0.resize(other.0.len(), 0);
        }
        let mut grew = false;
        for (a, b) in self.0.iter_mut().zip(&other.0) {
            grew |= b & !*a != 0;
            *a |= b;
        }
        grew
    }

    /// The numbers, ascending, in O(words + numbers): each word gives its lowest bit and
    /// clears it, where testing all 64 bits of each word costs 64 steps a word.
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.0.iter().enumerate().flat_map(|(w, &word)| {
            let mut rest = word;
            std::iter::from_fn(move || {
                if rest == 0 {
                    return None;
                }
                let b = rest.trailing_zeros() as usize;
                rest &= rest - 1;
                Some(w * WORD + b)
            })
        })
    }
}

/// Equal when the same numbers are in both: words past the shorter set's end must be 0.
impl PartialEq for BitSet {
    fn eq(&self, other: &BitSet) -> bool {
        let (short, long) = if self.0.len() <= other.0.len() {
            (&self.0, &other.0)
        } else {
            (&other.0, &self.0)
        };
        long[..short.len()] == short[..] && long[short.len()..].iter().all(|&x| x == 0)
    }
}

impl Eq for BitSet {}

#[cfg(test)]
mod tests {
    use super::BitSet;

    /// The union of a longer set into a shorter one keeps every number: zed-tools' `Bits::add`
    /// zipped the words and dropped those past the shorter set's end, so 100 was lost here.
    #[test]
    fn a_union_with_a_longer_set_keeps_its_high_numbers() {
        let mut a = BitSet::new(64);
        let mut b = BitSet::new(128);
        b.insert(100);
        assert!(a.union(&b));
        assert!(a.contains(100));
        assert!(!a.union(&b));
    }

    /// A number past the room made is absent, not a panic (`Bits::has` indexed past the end;
    /// zir's `Swapped::contains` gave false).
    #[test]
    fn numbers_past_the_end_are_absent() {
        let a = BitSet::new(10);
        assert!(!a.contains(10_000));
        assert!(!BitSet::default().contains(0));
    }

    /// Equality is of the numbers held, not of the room: a set made with room for 1000 and
    /// one grown to 5 hold the same {5}.
    #[test]
    fn sets_with_the_same_numbers_are_equal_whatever_their_room() {
        let mut a = BitSet::new(1000);
        let mut b = BitSet::default();
        a.insert(5);
        b.insert(5);
        assert_eq!(a, b);
        assert_eq!(b, a);
        b.insert(700);
        assert_ne!(a, b);
    }

    /// `iter` gives the numbers ascending, across words and at both ends of a word, against a
    /// list of flags.
    #[test]
    fn iter_gives_the_numbers_ascending() {
        let picks = [0, 1, 63, 64, 65, 127, 128, 200, 255];
        let mut a = BitSet::new(256);
        for &i in picks.iter().rev() {
            assert!(a.insert(i));
            assert!(!a.insert(i));
        }
        assert_eq!(a.iter().collect::<Vec<_>>(), picks);
        let flags: Vec<usize> = (0..256).filter(|&i| a.contains(i)).collect();
        assert_eq!(flags, picks);
    }
}

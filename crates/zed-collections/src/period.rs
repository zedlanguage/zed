//! The least period of a sequence that is a whole number of copies of a block: the length of the
//! shortest block `s[..p]` such that `s` is that block repeated `|s| / p` times.
//!
//! Used by zed-kernel's empty-type sweep (the rows of a clause read as a word) and by zedc-lattice
//! [`Classed`]'s periodic tails, whose residue table modulo a period is kept at its least period
//! so that one set has one table (the canonical form of `Tail::new` in zedc-lattice
//! `classed.rs`).
//!
//! The method: the failure function of Knuth, Morris and Pratt, "Fast pattern matching in
//! strings", SIAM J. Comput. 6(2):323–350, 1977, doi:10.1137/0206024 (read 2026-11-26 from the
//! scanned journal pages, p. 327): "Let f[j] be the largest i less than j such that
//! pattern[1] . . . pattern[i − 1] = pattern[j − i + 1] . . . pattern[j − 1]", so `f[j] - 1`
//! is the length of the longest proper border of the first `j - 1` letters; the prefix function
//! below is that value, indexed from 0. Their definition of a period, p. 333, (5): "We say that
//! p is a period of α if α[i] = α[i + p] for 1 ≤ i ≤ |α| − p". The fact used, with its proof
//! here so that nothing rests on the citation: let `b = f[n - 1]` be the length of the longest
//! proper border of `s` (a prefix that is also a suffix, shorter than `s`), and `q = n - b`.
//! (1) `q` is the least period of `s` as a word, `s[i] == s[i + q]` for all `i + q < n`: a border
//! of length `b` is the same thing as a period `n - b` (the prefix `s[..b]` equals the suffix
//! `s[q..]` exactly when `s[i] == s[i + q]` for every `i < b`), so the longest border gives the
//! least period. (2) If `q` divides `n`, `s` is `s[..q]` repeated. (3) If some `p` divides `n`
//! with `s = s[..p]` repeated, then `p` is a period, so `p >= q`; and by the periodicity lemma,
//! Knuth, Morris and Pratt (same paper, p. 334): "LEMMA 1. If p and q are periods of α, and
//! p + q ≤ |α| + gcd(p, q), then gcd(p, q) is a period of α." (read 2026-11-26). It is the
//! following theorem read on words: extend α without end once with period p and once with
//! period q; the two sequences agree on α's |α| ≥ p + q − gcd(p, q) letters, so they are one
//! sequence with periods p and q, hence gcd(p, q) = a·p − b·q (a, b ≥ 0) as well. N. J. Fine
//! and H. S. Wilf, "Uniqueness theorems for periodic functions", Proc.
//! AMS 16(1):109–114, 1965, doi:10.1090/S0002-9939-1965-0174934-9 (read 2026-11-26, p. 109):
//! "THEOREM 1. Let {f_n}, {g_n} be two periodic sequences of periods h, k, respectively. If
//! f_n = g_n for h + k − (h, k) consecutive integers n, then f_n = g_n for all n." Here
//! `p` divides `n` and `p >= q`, and if `p < n` then `p <= n / 2`, so
//! `p + q <= 2p <= n`, and `gcd(p, q)` is a period that divides `p`, hence `n`; it is at most `q`
//! and a period, so equal to `q` by (1), so `q` divides `n`. So when `q` does not divide `n`, no
//! `p < n` does, and the least repeating block is `s` itself. Tests:
//! `tests::the_least_period_is_found_against_every_divisor` checks every word over two letters up
//! to length 12 against the divisors tried one by one, which catches a wrong border, a wrong
//! fallback to `n`, and an off-by-one in either.

/// The least `p` such that `s` is `s[..p]` repeated (`p` divides `s.len()`), by the prefix
/// function: O(|s|). `s` must not be empty.
// Complexity tradeoff: naive version, each divisor `d` of `n` tried in turn, O(n·d(n)) for d(n)
// divisors (1,344 for some `n` under 10^9); used: the prefix function, O(n), each step of the
// inner `while` paid for by an earlier increase of `k` (the amortized bound of the paper above).
pub fn least_period<T: Eq>(s: &[T]) -> usize {
    let n = s.len();
    let mut f = vec![0usize; n];
    for i in 1..n {
        let mut k = f[i - 1];
        while k > 0 && s[i] != s[k] {
            k = f[k - 1];
        }
        if s[i] == s[k] {
            k += 1;
        }
        f[i] = k;
    }
    let p = n - f[n - 1];
    if n.is_multiple_of(p) { p } else { n }
}

#[cfg(test)]
mod tests {
    use super::least_period;

    /// The least divisor `d` of `s.len()` with `s` equal to `s[..d]` repeated, tried one by one.
    fn by_divisors(s: &[bool]) -> usize {
        let n = s.len();
        (1..=n)
            .find(|d| n.is_multiple_of(*d) && (0..n).all(|i| s[i] == s[i % d]))
            .expect("n itself")
    }

    #[test]
    fn the_least_period_is_found_against_every_divisor() {
        let mut checked = 0;
        for n in 1..=12usize {
            for bits in 0u32..(1 << n) {
                let s: Vec<bool> = (0..n).map(|i| bits >> i & 1 == 1).collect();
                assert_eq!(least_period(&s), by_divisors(&s), "{s:?}");
                checked += 1;
            }
        }
        assert_eq!(checked, (1 << 13) - 2);
        assert_eq!(least_period(&[1, 2, 1, 2, 1, 2]), 2);
        assert_eq!(least_period(&[1, 2, 1, 2, 1]), 5);
        assert_eq!(least_period(&[7]), 1);
    }
}

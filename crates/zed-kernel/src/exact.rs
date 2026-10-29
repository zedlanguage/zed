//! Float reductions that read no evaluation order: the exact sum and the canonical tree
//! (DESIGN.md sec:reduction).

/// The fixed-point accumulator width, in 64-bit limbs. Every finite double is an integer
/// multiple of 2^-1074 below 2^1024, so its magnitude in those units needs 2098 bits; 35
/// limbs leave 142 bits of headroom, enough for more than 2^64 summands.
const LIMBS: usize = 35;

type Acc = [u64; LIMBS];

fn add_shifted(acc: &mut Acc, mantissa: u64, shift: u32) {
    let limb = (shift / 64) as usize;
    let bit = shift % 64;
    let wide = (mantissa as u128) << bit;
    let mut carry = 0u128;
    for (i, part) in [wide as u64, (wide >> 64) as u64].into_iter().enumerate() {
        let s = acc[limb + i] as u128 + part as u128 + carry;
        acc[limb + i] = s as u64;
        carry = s >> 64;
    }
    let mut i = limb + 2;
    while carry != 0 {
        let s = acc[i] as u128 + carry;
        acc[i] = s as u64;
        carry = s >> 64;
        i += 1;
    }
}

/// `a - b`, where `a >= b`.
fn sub(a: &Acc, b: &Acc) -> Acc {
    let mut out = [0u64; LIMBS];
    let mut borrow = false;
    for i in 0..LIMBS {
        let (d, b1) = a[i].overflowing_sub(b[i]);
        let (d, b2) = d.overflowing_sub(borrow as u64);
        out[i] = d;
        borrow = b1 || b2;
    }
    out
}

fn cmp(a: &Acc, b: &Acc) -> std::cmp::Ordering {
    a.iter().rev().cmp(b.iter().rev())
}

fn bit(acc: &Acc, i: u32) -> bool {
    acc[(i / 64) as usize] >> (i % 64) & 1 == 1
}

fn any_below(acc: &Acc, i: u32) -> bool {
    (0..i).any(|j| bit(acc, j))
}

/// Rounds the magnitude `acc × 2^-1074` to the nearest double, ties to even.
fn round(acc: &Acc) -> f64 {
    let top = (0..LIMBS)
        .rev()
        .find(|&i| acc[i] != 0)
        .expect("exact_sum rounds only a nonzero magnitude");
    let high = top as u32 * 64 + 63 - acc[top].leading_zeros();
    if high < 53 {
        // Below 2^53 units the value is a subnormal or the smallest binade, exactly
        // representable, and the product by the smallest subnormal is exact.
        return acc[0] as f64 * f64::from_bits(1);
    }
    let shift = high - 52;
    let mut m = 0u64;
    for j in 0..53 {
        if bit(acc, shift + j) {
            m |= 1 << j;
        }
    }
    let half = bit(acc, shift - 1);
    let sticky = any_below(acc, shift - 1);
    let mut exp = shift + 1;
    if half && (sticky || m & 1 == 1) {
        m += 1;
        if m == 1 << 53 {
            m >>= 1;
            exp += 1;
        }
    }
    if exp >= 2047 {
        return f64::INFINITY;
    }
    f64::from_bits((exp as u64) << 52 | (m & ((1 << 52) - 1)))
}

/// The exact sum of `xs`, rounded once to the nearest double (ties to even). An infinity
/// is the result if one is present, NaN if both infinities or any NaN are, and the sum of
/// only negative zeros is `-0.0`, as IEEE addition gives. The result does not depend on the
/// order of `xs`, so no tree is needed.
pub fn exact_sum(xs: &[f64]) -> f64 {
    let (mut pos, mut neg) = ([0u64; LIMBS], [0u64; LIMBS]);
    let (mut pinf, mut ninf, mut nan) = (false, false, false);
    let mut all_neg_zero = !xs.is_empty();
    for &x in xs {
        if x.is_nan() {
            nan = true;
            continue;
        }
        if x.is_infinite() {
            if x > 0.0 {
                pinf = true
            } else {
                ninf = true
            }
            continue;
        }
        all_neg_zero &= x == 0.0 && x.is_sign_negative();
        let bits = x.to_bits();
        let biased = ((bits >> 52) & 0x7ff) as u32;
        let frac = bits & ((1 << 52) - 1);
        let (mantissa, shift) = if biased == 0 {
            (frac, 0)
        } else {
            (frac | 1 << 52, biased - 1)
        };
        add_shifted(if x < 0.0 { &mut neg } else { &mut pos }, mantissa, shift);
    }
    if nan || (pinf && ninf) {
        return f64::NAN;
    }
    if pinf {
        return f64::INFINITY;
    }
    if ninf {
        return f64::NEG_INFINITY;
    }
    match cmp(&pos, &neg) {
        std::cmp::Ordering::Less => -round(&sub(&neg, &pos)),
        std::cmp::Ordering::Greater => round(&sub(&pos, &neg)),
        std::cmp::Ordering::Equal if all_neg_zero => -0.0,
        std::cmp::Ordering::Equal => 0.0,
    }
}

/// Reduces a nonempty sequence on the canonical tree of (sec:reduction), whose shape depends
/// on its length alone: one element is itself; a power-of-two length reduces its two halves;
/// any other length `n`, with `p` the largest power of two dividing `n`, reduces the first
/// `n - p` elements and the last `p`. The left result is always combined with the right.
pub fn canonical_tree<T: Clone, E>(
    xs: &[T],
    op: &mut impl FnMut(T, T) -> Result<T, E>,
) -> Result<T, E> {
    let n = xs.len();
    assert!(
        n > 0,
        "the canonical tree of an empty level is the empty-fold rule's business"
    );
    if n == 1 {
        return Ok(xs[0].clone());
    }
    let p = 1 << n.trailing_zeros();
    let split = if p == n { n / 2 } else { n - p };
    let left = canonical_tree(&xs[..split], op)?;
    let right = canonical_tree(&xs[split..], op)?;
    op(left, right)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_sum_rounds_once() {
        // Left to right, 0.1 + 0.2 + 0.3 rounds twice and gives 0.6000000000000001.
        assert_eq!(0.1 + 0.2 + 0.3, 0.6000000000000001);
        assert_eq!(exact_sum(&[0.1, 0.2, 0.3]), 0.6);
        assert_eq!(exact_sum(&[1e100, 1.0, -1e100]), 1.0);
        assert_eq!(exact_sum(&[1e308, 1e308, -1e308]), 1e308);
        assert_eq!(exact_sum(&[f64::MAX, f64::MAX]), f64::INFINITY);
        assert_eq!(exact_sum(&[-f64::MAX, -f64::MAX]), f64::NEG_INFINITY);
    }

    #[test]
    fn exact_sum_matches_order_free_reference() {
        // Shuffles of one multiset give one bit pattern.
        let xs = [3.5e-310, 1e16, -1.0, 2.5, -1e16, 7e-300, 1.0 / 3.0];
        let a = exact_sum(&xs);
        let mut ys = xs;
        ys.reverse();
        assert_eq!(a.to_bits(), exact_sum(&ys).to_bits());
        ys.swap(1, 4);
        assert_eq!(a.to_bits(), exact_sum(&ys).to_bits());
    }

    #[test]
    fn ties_round_to_even() {
        // 2^53 + 1 is a tie between 2^53 and 2^53 + 2; the even one is 2^53.
        let two53 = 9007199254740992.0;
        assert_eq!(exact_sum(&[two53, 1.0]), two53);
        // 2^53 + 3 is a tie between 2^53 + 2 and 2^53 + 4; the even mantissa is 2^53 + 4.
        assert_eq!(exact_sum(&[two53, 3.0]), two53 + 4.0);
        // A tie broken by a sticky bit far below rounds up.
        assert_eq!(exact_sum(&[two53, 1.0, 1e-300]), two53 + 2.0);
    }

    #[test]
    fn carries_and_round_up_into_the_next_binade() {
        // Three values with all-ones mantissas fill bits 0..159 of the accumulator; one more
        // unit carries through two whole limbs, giving exactly 2^159 units, 2^-915.
        let ones = |biased: u64| f64::from_bits(biased << 52 | ((1 << 52) - 1));
        let xs = [ones(1), ones(54), ones(107), f64::from_bits(1)];
        assert_eq!(exact_sum(&xs), 2f64.powi(-915));
        // 2^54 - 1 is a tie between 2^54 - 2, whose mantissa is odd, and 2^54.
        let two54 = 18014398509481984.0;
        assert_eq!(exact_sum(&[two54 - 2.0, 1.0]), two54);
    }

    #[test]
    fn subnormals_and_zeros() {
        let tiny = f64::from_bits(1);
        assert_eq!(exact_sum(&[tiny, tiny]), f64::from_bits(2));
        assert_eq!(exact_sum(&[tiny, -tiny]).to_bits(), 0.0f64.to_bits());
        assert_eq!(exact_sum(&[-0.0, -0.0]).to_bits(), (-0.0f64).to_bits());
        assert_eq!(exact_sum(&[-0.0, 0.0]).to_bits(), 0.0f64.to_bits());
        assert_eq!(exact_sum(&[]).to_bits(), 0.0f64.to_bits());
        assert_eq!(
            exact_sum(&[f64::MIN_POSITIVE, -tiny]),
            f64::MIN_POSITIVE - tiny
        );
    }

    #[test]
    fn specials() {
        assert!(exact_sum(&[1.0, f64::NAN]).is_nan());
        assert!(exact_sum(&[f64::INFINITY, f64::NEG_INFINITY]).is_nan());
        assert_eq!(exact_sum(&[f64::INFINITY, -1e308]), f64::INFINITY);
        assert_eq!(exact_sum(&[f64::NEG_INFINITY, 1.0]), f64::NEG_INFINITY);
    }

    fn shape(n: usize) -> String {
        let leaves: Vec<String> = (0..n).map(|i| format!("e{i}")).collect();
        canonical_tree(&leaves, &mut |a, b| Ok::<_, ()>(format!("({a} ⊕ {b})"))).unwrap()
    }

    #[test]
    fn canonical_tree_shapes() {
        assert_eq!(shape(1), "e0");
        assert_eq!(shape(3), "((e0 ⊕ e1) ⊕ e2)");
        // The example of (sec:reduction).
        assert_eq!(shape(6), "(((e0 ⊕ e1) ⊕ (e2 ⊕ e3)) ⊕ (e4 ⊕ e5))");
        assert_eq!(shape(7), "((((e0 ⊕ e1) ⊕ (e2 ⊕ e3)) ⊕ (e4 ⊕ e5)) ⊕ e6)");
    }

    #[test]
    fn canonical_tree_depth_is_floor_log_plus_popcount_minus_one() {
        fn depth(n: usize) -> usize {
            let leaves = vec![0usize; n];
            canonical_tree(&leaves, &mut |a: usize, b: usize| Ok::<_, ()>(a.max(b) + 1)).unwrap()
        }
        for n in 1..200usize {
            let expected = n.ilog2() as usize + n.count_ones() as usize - 1;
            assert_eq!(depth(n), expected, "n = {n}");
        }
    }
}

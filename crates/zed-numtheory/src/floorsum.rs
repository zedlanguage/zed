//! The floor sum `Σ ⌊(a·i + b) / m⌋` over `0 <= i < n` (FLOORSUM-bits): one routine for every
//! user, zedc-affine's `lines::floor_sum` and through it the two-variable counts of
//! zedc-solvers (`twovar.rs`) and the preimages of `x mod c` (plan row MOD-pre-width).

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::Signed;

/// `Σ ⌊(a·i + b) / m⌋` for `i` from 0 below `n`, with `m` above zero and `n` at least zero; `a`
/// and `b` may have either sign.
///
/// # Panics
///
/// If `m <= 0` or `n < 0`.
pub fn floor_sum(n: &BigInt, m: &BigInt, a: &BigInt, b: &BigInt) -> BigInt {
    assert!(
        m.is_positive() && !n.is_negative(),
        "floor_sum needs m > 0 and n >= 0, not m = {m}, n = {n}"
    );
    let (mut n, mut m) = (n.clone(), m.clone());
    let pairs = |n: &BigInt| (n * &(n - 1u32)) >> 1u32;
    let (q, mut a) = a.div_mod_floor(&m);
    let mut ans = &pairs(&n) * &q;
    let (q, mut b) = b.div_mod_floor(&m);
    ans += &n * &q;
    loop {
        if a >= m {
            let (q, r) = a.div_mod_floor(&m);
            ans += &pairs(&n) * &q;
            a = r;
        }
        if b >= m {
            let (q, r) = b.div_mod_floor(&m);
            ans += &n * &q;
            b = r;
        }
        let top = &(&a * &n) + &b;
        if top < m {
            return ans;
        }
        (n, b) = top.div_mod_floor(&m);
        std::mem::swap(&mut m, &mut a);
    }
}

/// [`floor_sum`] on words, `None` when a step would overflow `i128`; the caller then takes
/// [`floor_sum`]. On words each step of the AtCoder Library's form (`floor_sum` there) is O(1),
/// so its O(log m) rounds are the cost, and the bit cost that [`floor_sum`] is built for does
/// not arise.
///
/// # Panics
///
/// If `m <= 0` or `n < 0`.
pub fn floor_sum_i128(n: i128, m: i128, a: i128, b: i128) -> Option<i128> {
    assert!(
        m > 0 && n >= 0,
        "floor_sum_i128 needs m > 0 and n >= 0, not m = {m}, n = {n}"
    );
    // `n (n − 1) / 2`, halving the even factor first so only the product can overflow.
    let pairs = |n: i128| {
        if n % 2 == 0 {
            (n / 2).checked_mul(n - 1)
        } else {
            n.checked_mul((n - 1) / 2)
        }
    };
    let (mut n, mut m, mut a, mut b) = (n, m, a, b);
    let mut ans: i128 = 0;
    loop {
        // `div_euclid` by `m > 0` is the floor, so negative `a` and `b` reduce as in
        // [`floor_sum`].
        if !(0..m).contains(&a) {
            ans = ans.checked_add(pairs(n)?.checked_mul(a.div_euclid(m))?)?;
            a = a.rem_euclid(m);
        }
        if !(0..m).contains(&b) {
            ans = ans.checked_add(n.checked_mul(b.div_euclid(m))?)?;
            b = b.rem_euclid(m);
        }
        let top = a.checked_mul(n)?.checked_add(b)?;
        if top < m {
            return Some(ans);
        }
        (n, b) = (top / m, top % m);
        (m, a) = (a, m);
    }
}

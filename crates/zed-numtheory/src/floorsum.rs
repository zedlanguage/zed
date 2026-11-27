//! The floor sum `Σ ⌊(a·i + b) / m⌋` over `0 <= i < n` (FLOORSUM-bits): one routine for every
//! user, zedc-affine's `lines::floor_sum` and through it the two-variable counts of
//! zedc-solvers (`twovar.rs`) and the preimages of `x mod c` (plan row MOD-pre-width).

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{Signed, Zero};

/// `Σ ⌊(a·i + b) / m⌋` for `i` from 0 below `n`, with `m` above zero and `n` at least zero; `a`
/// and `b` may have either sign.
///
/// The rounds are those of the AtCoder Library's `floor_sum` (atcoder/math.hpp,
/// `floor_sum_unsigned`), but after the first no round multiplies two large numbers: each
/// number a round needs comes from those of the two rounds before by multiplications by a
/// quotient of Euclid's algorithm on `(m, a mod m)`, divisions with such a quotient, and
/// additions.
///
/// The AtCoder rounds. Write `F(n, m, a, b)` for the sum. With `a = q_a m + a₀` and
/// `b = q_b m + b₀` by floor division, `⌊(a i + b)/m⌋ = q_a i + q_b + ⌊(a₀ i + b₀)/m⌋`, so
/// `F = q_a n(n−1)/2 + q_b n + F(n, m, a₀, b₀)`. For `0 <= a₀, b₀ < m`, let
/// `top = a₀ n + b₀`. Every term is below `top / m` (`a₀ i + b₀ < top` for `i < n`), so when
/// `top < m` the sum is 0. Otherwise, counting the lattice points under the line by rows,
/// `F(n, m, a₀, b₀) = F(⌊top/m⌋, a₀, m, top mod m)`, and the next round reduces `m` by `a₀`.
/// So round `j` has, after its reduction, `(n_j, m_j, a_j, b_j)` with `0 <= a_j, b_j < m_j`,
/// adds `q_j n_j (n_j − 1)/2 + t_j n_j`, and gives round `j + 1`
/// `n_(j+1) = top_j div m_j`, `m_(j+1) = a_j`, and `m_j` and `b'_(j+1) = top_j mod m_j` to
/// reduce by `a_j`: `q_(j+1) = m_j div a_j`, `a_(j+1) = m_j mod a_j`,
/// `t_(j+1) = b'_(j+1) div a_j`, `b_(j+1) = b'_(j+1) mod a_j`. It stops at the first round with
/// `top_j < m_j`, which is `n_(j+1) = 0`, since `top_j >= 0`. Round 0 has `q_0 = q_a`,
/// `t_0 = q_b`.
///
/// Proof that `n_(j+1)` and `b'_(j+1)` need no product of two large numbers, for `j >= 1`,
/// writing `k = j − 1` (round `k` went on, so `top_k >= m_k`):
///
/// (a) By division with remainder, `m_k n_j + b'_j = top_k = a_k n_k + b_k`.
/// (b) By the reduction of round `j`, `a_j = m_k − q_j a_k` and `b_j = b'_j − t_j a_k`.
/// (c) So `top_j = a_j n_j + b_j = (m_k n_j + b'_j) − a_k (q_j n_j + t_j)`
///     `= a_k (n_k − q_j n_j − t_j) + b_k` by (a).
/// (d) `a_k > 0`: `top_k >= m_k > b_k` makes `a_k n_k > 0`. Write `b_k = u_j a_k + r` with
///     `u_j = b_k div a_k` and `0 <= r < a_k`. Then `top_j = a_k X + r` with the integer
///     `X = n_k − q_j n_j − t_j + u_j`, and since `m_j = a_k`, division with remainder being
///     unique, `n_(j+1) = top_j div m_j = X` and `b'_(j+1) = top_j mod m_j = r = b_k mod a_k`.
///
/// So with `c_j = t_j − u_j`, `n_(j+1) = n_(j−1) − q_j n_j − c_j`. Round 0 computes `top_0`
/// itself, the one product of two large numbers, and `n_1` and `b'_1` from it.
///
/// Proof that the squares need none either: the sum needs `n_j (n_j − 1)/2`, which is
/// `(S_j − n_j)/2` with `S_j = n_j²`. With `P_j = n_j n_(j+1)`, multiplying the recurrence by
/// `n_j`, and by `n_(j−1)` and `n_(j+1)`:
///
/// (e) `P_j = n_j n_(j−1) − q_j n_j² − c_j n_j = P_(j−1) − q_j S_j − c_j n_j`;
/// (f) `n_(j+1) n_(j−1) = S_(j−1) − q_j P_(j−1) − c_j n_(j−1)`;
/// (g) `S_(j+1) = n_(j+1) n_(j−1) − q_j n_(j+1) n_j − c_j n_(j+1)`
///     `= S_(j−1) − q_j P_(j−1) − c_j n_(j−1) − q_j P_j − c_j n_(j+1)` by (f).
///
/// Round 0 computes `S_0`, `S_1` and `P_0` by three products.
///
/// Sizes. `0 <= t_j, u_j <= q_j`: `b'_j` and `b_(j−1)` are below `m_(j−1)` (`b'_1 < m_0` as a
/// remainder, `b'_j = b_(j−2) mod a_(j−2) < a_(j−2) = m_(j−1)` by (d)), so their quotients by
/// `a_(j−1)` are at most `m_(j−1) div a_(j−1) = q_j`. And `n` never grows:
/// `top_j < m_j n_j + m_j`, so `n_(j+1) <= n_j`. So every number of a round is at most
/// `max(m, n²)` in size, and each step of a round is a division with the quotient `q_j`, `t_j`
/// or `u_j`, a product by one of them, or an addition.
///
/// Complexity tradeoff: for numbers of `d` digits (`n` of `ℓ` digits), the first round is
/// O(M(d + ℓ)) bit operations (its products and divisions), and round `j` after it is
/// O((d + ℓ)(1 + log q_j)); the `q_j` are the quotients of Euclid's algorithm on `(m, a₀)`, so
/// `Σ (1 + log q_j) = O(d)`, and the whole is O(M(d + ℓ) + d (d + ℓ)): O(d²) when `ℓ = O(d)`.
/// Naive, the AtCoder form, multiplies `a_j n_j` and `n_j (n_j − 1)` each round, numbers of
/// size about that of `m_j`, which fall by only about `log q_j` bits a round: O(d·M(d)). Faster,
/// O(M(d) log d) in a half-gcd form (a product tree over the quotients, the derivation in plan
/// row MOD-pre-width's note), is not published (literature search of 2026-11-22, named in that
/// note) and not proved, so by QUESTIONS A83 this O(d²) form is the one used. Measured: plan
/// row FLOORSUM-bits, `bench::the_floor_sum_takes_d_squared`.
///
/// # Panics
///
/// If `m <= 0` or `n < 0`.
pub fn floor_sum(n: &BigInt, m: &BigInt, a: &BigInt, b: &BigInt) -> BigInt {
    assert!(
        m.is_positive() && !n.is_negative(),
        "floor_sum needs m > 0 and n >= 0, not m = {m}, n = {n}"
    );
    // Round 0: the reduction of `a` and `b`, of either sign, and the products.
    let (q, mut a_prev) = a.div_mod_floor(m);
    let (t, mut b_prev) = b.div_mod_floor(m);
    let mut sq_prev = n * n;
    let mut ans = &q * &((&sq_prev - n) >> 1u32) + &t * n;
    let top = &(&a_prev * n) + &b_prev;
    if top < *m {
        return ans;
    }
    // From here every number is at least 0, so `div_rem` is the floor division.
    let (mut n_cur, mut b_cut) = top.div_rem(m);
    let mut sq_cur = &n_cur * &n_cur;
    let mut prod_prev = n * &n_cur;
    let (mut m_prev, mut n_prev) = (m.clone(), n.clone());
    // Round `j`, with `m_prev`, `a_prev`, `b_prev` = `m_(j−1)`, `a_(j−1)`, `b_(j−1)`,
    // `b_cut` = `b'_j`, `n_prev`, `n_cur` = `n_(j−1)`, `n_j`, `sq_prev`, `sq_cur` =
    // `S_(j−1)`, `S_j` and `prod_prev` = `P_(j−1)`.
    loop {
        let (q, a_cur) = div_rem_short(&m_prev, &a_prev);
        let (t, b_cur) = div_rem_short(&b_cut, &a_prev);
        ans += &q * &((&sq_cur - &n_cur) >> 1u32);
        ans += &t * &n_cur;
        let (u, b_next) = div_rem_short(&b_prev, &a_prev);
        let c = t - u;
        // (d).
        let n_next = &n_prev - &(&q * &n_cur) - &c;
        debug_assert!(!n_next.is_negative(), "n_(j+1) = top_j div m_j >= 0");
        if n_next.is_zero() {
            return ans;
        }
        // (e) and (g).
        let prod_cur = &prod_prev - &(&q * &sq_cur) - &(&c * &n_cur);
        let sq_next =
            &sq_prev - &(&q * &prod_prev) - &(&c * &n_prev) - &(&q * &prod_cur) - &(&c * &n_next);
        m_prev = std::mem::replace(&mut a_prev, a_cur);
        (b_prev, b_cut) = (b_cur, b_next);
        (n_prev, n_cur) = (n_cur, n_next);
        (sq_prev, sq_cur) = (sq_cur, sq_next);
        prod_prev = prod_cur;
    }
}

/// `(a div b, a mod b)` for `a >= 0` and `b > 0`, by long division in steps of at most 63
/// quotient bits, each guessed from the leading bits of `a` and `b`: O(len(a)(1 + len(q)))
/// word operations for a quotient `q`, so O(d (1 + log q)) for the rounds of [`floor_sum`].
///
/// Complexity tradeoff: num-bigint 0.4.8 divides by Burnikel and Ziegler's recursive division
/// once the dividend has more than 128 words and the divisor more than 64
/// (`BURNIKEL_ZIEGLER_THRESHOLD`, biguint/division.rs lines 216 and 343), with products of
/// half-size numbers even when the quotient is one word. Each round of [`floor_sum`] divides
/// numbers of about the same size, so its 520-word benchmark allocated 130.3 times the bytes
/// of the 65-word one, over the limit of 84 (plan row FLOORSUM-bits); this division
/// allocates three numbers of `a`'s size a step.
///
/// One step, with `r` the remainder so far (`r >= b`, `e = bits(r) − bits(b)`):
/// `sh = max(0, e − 62)` and `D = b·2^sh`, so `bits(D) = t = bits(b) + sh` and
/// `bits(r) <= t + 62`. With `s = max(0, t − 64)`, `A = ⌊r / 2^s⌋` and `B = ⌊D / 2^s⌋`, the guess
/// is `g = ⌊A / B⌋`, and the quotient of the step is `p = ⌊r / D⌋`.
///
/// (a) `p <= g`: `A 2^s <= r < (A + 1) 2^s` and `B 2^s <= D`, so `p <= r / D < (A + 1) / B`;
///     then `p B < A + 1`, so `p B <= A` and `p <= g`.
/// (b) `g <= p + 1`: if `s = 0`, `A = r` and `B = D`, so `g = p`. Otherwise `bits(D) = s + 64`,
///     so `B >= 2^63`, and `A < 2^(t + 62 − s) = 2^126`. With `D < (B + 1) 2^s`,
///     `r / D > A / (B + 1)`, and `A / B − A / (B + 1) = A / (B (B + 1)) < 2^126 / 2^126 = 1`,
///     so `g <= A / B < r / D + 1`: the integer `g − 1 < r / D` is at most `p`.
/// (c) Sizes: `p <= r / D < 2^(t + 62) / 2^(t − 1) = 2^63`, so `g <= p + 1 < 2^64` fits a word,
///     and `A < 2^126` and `B < 2^64` fit `u128`.
///
/// So `r − g D` is `r − p D` (from 0 below `D`) or that less `D`, which one addition of `D`
/// mends. The remainder then has at most `t` bits, so the next step has `e` at most `sh`: from
/// `e > 62` each step takes 62 bits off `e`, and a step with `e <= 62` (`sh = 0`) ends with
/// `r < b`.
pub(crate) fn div_rem_short(a: &BigInt, b: &BigInt) -> (BigInt, BigInt) {
    debug_assert!(!a.is_negative() && b.is_positive());
    let b_bits = b.bits();
    let mut r = a.clone();
    let mut q = BigInt::zero();
    while r >= *b {
        let sh = (r.bits() - b_bits).saturating_sub(62);
        let t = b_bits + sh;
        let s = t.saturating_sub(64);
        let big_a = leading(&r, s);
        // `⌊D / 2^s⌋`: the leading 64 bits of `b` when it has 64 or more; otherwise `D / 2^s` is
        // `b·2^(sh − s)`, exact, with `sh − s = min(t, 64) − bits(b)`.
        let big_b = if b_bits >= 64 {
            leading(b, b_bits - 64)
        } else {
            leading(b, 0) << (t.min(64) - b_bits)
        };
        let mut g = u64::try_from(big_a / big_b).expect("the guess is below 2^64, (c)");
        r -= (b * g) << sh;
        if r.is_negative() {
            r += b << sh;
            g -= 1;
        }
        debug_assert!(!r.is_negative(), "the guess is at most one over, (b)");
        q += BigInt::from(g) << sh;
    }
    (q, r)
}

/// `⌊x / 2^s⌋` for `x >= 0`, when it is below 2^128: three words of `x` from word `s / 64`,
/// shifted by `s mod 64`.
fn leading(x: &BigInt, s: u64) -> u128 {
    let mut words = x.magnitude().iter_u64_digits().skip((s / 64) as usize);
    let mut next = || u128::from(words.next().unwrap_or(0));
    let (w0, w1, w2) = (next(), next(), next());
    let low = w0 | w1 << 64;
    match s % 64 {
        0 => low,
        k => low >> k | w2 << (128 - k),
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

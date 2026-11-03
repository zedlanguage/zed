//! Exact integer feasibility of rows over two variables (DESIGN.md sec:domains, step L1.38).
//!
//! The rows `cx·x + cy·y + k >= 0` bound `y` above by lines `(p·x + q) / r` where `cy < 0`, and
//! below where `cy > 0`; the others bound `x`. At an integer `x` the integer values of `y` are
//! those from `⌈l(x)⌉` to `⌊u(x)⌋`, where `u` is the least upper line and `l` the greatest
//! lower one, so their number is `⌊u(x)⌋ - ⌈l(x)⌉ + 1` wherever `u(x) >= l(x)`, and that never
//! falls below zero there. The envelopes `u` and `l` are found by the convex hull trick, and
//! their pieces split the line into ranges, on each of which `u` and `l` are single lines; on
//! each, `u - l >= 0` holds on a range, since `u - l` is linear there. The integer points of a
//! range are counted by the floor sum of each of the two lines, in steps logarithmic in the
//! coefficients, so the test takes O(m log m) for `m` rows, with no search over values. An
//! unbounded range is cut to a bounded one that has a point exactly when it has: where `u - l`
//! rises without end, up to the first `x` where `u - l >= 1`, which has a point; where it is
//! constant, one period of the two lines, past which the counts repeat. A point is found by
//! bisection on the counts of the prefixes of a range with points.

use super::int::Int;
use super::linear::{Q, Term};

/// The line `(p·x + q) / r`, with `r` above zero.
#[derive(Clone)]
struct Line {
    p: Int,
    q: Int,
    r: Int,
}

impl Line {
    fn slope(&self) -> Q {
        Q::new(self.p.clone(), self.r.clone())
    }

    fn icpt(&self) -> Q {
        Q::new(self.q.clone(), self.r.clone())
    }

    fn neg(&self) -> Line {
        Line {
            p: -&self.p,
            q: -&self.q,
            r: self.r.clone(),
        }
    }

    /// `⌊(p·x + q) / r⌋`.
    fn floor(&self, x: &Int) -> Int {
        (&(&self.p * x) + &self.q).div_floor(&self.r)
    }

    /// `⌈(p·x + q) / r⌉`.
    fn ceil(&self, x: &Int) -> Int {
        -&self.neg().floor(x)
    }

    /// `Σ ⌊(p·x + q) / r⌋` over the `n` integers from `s`.
    fn floor_sum(&self, s: &Int, n: &Int) -> Int {
        floor_sum(n, &self.r, &self.p, &(&(&self.p * s) + &self.q))
    }
}

/// `Σ ⌊(a·i + b) / m⌋` for `i` from 0 below `n`, with `m` above zero and `n` at least zero (the
/// AtCoder Library's floor_sum): each round swaps the roles of `a` and `m` as in Euclid's
/// algorithm, so the rounds are logarithmic in `m`.
fn floor_sum(n: &Int, m: &Int, a: &Int, b: &Int) -> Int {
    let two = Int::from(2);
    let (mut n, mut m) = (n.clone(), m.clone());
    let mut ans = Int::ZERO;
    let pairs = |n: &Int| (n * &(n - &Int::ONE)).div_floor(&two);
    ans = &ans + &(&pairs(&n) * &a.div_floor(&m));
    let mut a = a.mod_floor(&m);
    ans = &ans + &(&n * &b.div_floor(&m));
    let mut b = b.mod_floor(&m);
    loop {
        if a >= m {
            ans = &ans + &(&pairs(&n) * &a.div_floor(&m));
            a = a.mod_floor(&m);
        }
        if b >= m {
            ans = &ans + &(&n * &b.div_floor(&m));
            b = b.mod_floor(&m);
        }
        let top = &(&a * &n) + &b;
        if top < m {
            return ans;
        }
        n = top.div_floor(&m);
        b = top.mod_floor(&m);
        std::mem::swap(&mut m, &mut a);
    }
}

/// The least of the lines at each `x`: each line of it from left to right, with the `x` where
/// it starts, `None` for the first.
fn least(lines: &[Line]) -> Vec<(usize, Option<Q>)> {
    let keyed: Vec<(Q, Q)> = lines.iter().map(|l| (l.slope(), l.icpt())).collect();
    let mut order: Vec<usize> = (0..lines.len()).collect();
    // Slope falling, so each line is least to the right of the ones before; of equal slopes
    // only the lowest counts.
    order.sort_by(|&i, &j| (keyed[j].0.cmp(&keyed[i].0)).then_with(|| keyed[i].1.cmp(&keyed[j].1)));
    order.dedup_by(|j, i| keyed[*i].0 == keyed[*j].0);
    let mut env: Vec<(usize, Option<Q>)> = Vec::new();
    for i in order {
        loop {
            let Some((top, start)) = env.last() else {
                env.push((i, None));
                break;
            };
            let (s, t) = (&keyed[*top], &keyed[i]);
            // Where `t` meets the top: past it `t` is the less.
            let x = t.1.sub(&s.1).div(&s.0.sub(&t.0));
            if start.as_ref().is_some_and(|st| x <= *st) {
                env.pop();
                continue;
            }
            env.push((i, Some(x)));
            break;
        }
    }
    env
}

/// The integer range `[lo, hi]`, either end unbounded when `None`, narrowed by `lo2` and `hi2`.
fn narrow(range: &mut (Option<Int>, Option<Int>), lo2: Option<Int>, hi2: Option<Int>) {
    if let Some(v) = lo2 {
        range.0 = Some(range.0.take().map_or(v.clone(), |o| o.max(v)));
    }
    if let Some(v) = hi2 {
        range.1 = Some(range.1.take().map_or(v.clone(), |o| o.min(v)));
    }
}

/// An integer point of the rows, over `x[x]` and, when given, `x[y]`, or `None` when they have
/// none. Without `want` a point found is answered by zeros.
pub(crate) fn point(
    rows: &[(&[Term], &Int)],
    x: usize,
    y: Option<usize>,
    want: bool,
) -> Option<(Int, Int)> {
    let mut xs: (Option<Int>, Option<Int>) = (None, None);
    let (mut upper, mut lower): (Vec<Line>, Vec<Line>) = (Vec::new(), Vec::new());
    for (a, k) in rows {
        let at = |v: usize| {
            a.iter()
                .find(|(i, _)| *i == v)
                .map_or(Int::ZERO, |(_, c)| c.clone())
        };
        let cx = at(x);
        let cy = y.map_or(Int::ZERO, at);
        let k = (*k).clone();
        if cy.is_zero() {
            if cx.is_positive() {
                narrow(&mut xs, Some(-&k.div_floor(&cx)), None);
            } else if cx.is_negative() {
                narrow(&mut xs, None, Some(k.div_floor(&-&cx)));
            } else if k.is_negative() {
                return None;
            }
        } else if cy.is_negative() {
            upper.push(Line {
                p: cx,
                q: k,
                r: -&cy,
            });
        } else {
            lower.push(Line {
                p: -&cx,
                q: -&k,
                r: cy,
            });
        }
    }
    if let (Some(lo), Some(hi)) = &xs
        && lo > hi
    {
        return None;
    }
    if upper.is_empty() || lower.is_empty() {
        // `y` is bounded on one side at most: any `x` in its range has a point.
        let v = match &xs {
            (Some(lo), _) if lo.is_positive() => lo.clone(),
            (_, Some(hi)) if hi.is_negative() => hi.clone(),
            _ => Int::ZERO,
        };
        let w = match (lower.is_empty(), upper.is_empty()) {
            (false, _) => lower.iter().map(|l| l.ceil(&v)).max().expect("a line"),
            (_, false) => upper.iter().map(|l| l.floor(&v)).min().expect("a line"),
            _ => Int::ZERO,
        };
        return Some((v, w));
    }
    let u = least(&upper);
    let negs: Vec<Line> = lower.iter().map(Line::neg).collect();
    let l = least(&negs);
    let (mut i, mut j) = (0, 0);
    let mut left: Option<Q> = None;
    loop {
        let ni = u.get(i + 1).and_then(|e| e.1.clone());
        let nj = l.get(j + 1).and_then(|e| e.1.clone());
        let right = match (&ni, &nj) {
            (Some(a), Some(b)) => Some(a.min(b).clone()),
            (Some(a), None) => Some(a.clone()),
            (None, b) => b.clone(),
        };
        if let Some(p) = piece(&upper[u[i].0], &lower[l[j].0], &left, &right, &xs, want) {
            return Some(p);
        }
        let r = right?;
        if ni.as_ref() == Some(&r) {
            i += 1;
        }
        if nj.as_ref() == Some(&r) {
            j += 1;
        }
        left = Some(r);
    }
}

/// A point with `x` in `(left, right]` and in `xs`, where `ua` is the least upper line and `lb`
/// the greatest lower one, or `None` when there is none.
fn piece(
    ua: &Line,
    lb: &Line,
    left: &Option<Q>,
    right: &Option<Q>,
    xs: &(Option<Int>, Option<Int>),
    want: bool,
) -> Option<(Int, Int)> {
    let mut range = xs.clone();
    narrow(
        &mut range,
        left.as_ref().map(|q| &q.floor() + &Int::ONE),
        right.as_ref().map(Q::floor),
    );
    // `g = ua - lb = dg·x + g0`; where `g >= 0` there is a real `y`.
    let dg = ua.slope().sub(&lb.slope());
    let g0 = ua.icpt().sub(&lb.icpt());
    if dg.is_zero() {
        if g0.is_negative() {
            return None;
        }
    } else {
        let at = g0.neg().div(&dg);
        if dg.is_positive() {
            narrow(&mut range, Some(at.ceil()), None);
        } else {
            narrow(&mut range, None, Some(at.floor()));
        }
    }
    // An unbounded range cut to a bounded one with a point exactly when it has one.
    let period = || &ua.slope().d - &Int::ONE;
    let past_one = || Q::of(Int::ONE).sub(&g0).div(&dg);
    let (s, t) = match range {
        (Some(s), Some(t)) => (s, t),
        (None, None) => (Int::ZERO, period()),
        (Some(s), None) if dg.is_zero() => {
            let t = &s + &period();
            (s, t)
        }
        (None, Some(t)) if dg.is_zero() => (&t - &period(), t),
        (Some(s), None) => {
            let t = past_one().ceil().max(s.clone());
            (s, t)
        }
        (None, Some(t)) => (past_one().floor().min(t.clone()), t),
    };
    if s > t {
        return None;
    }
    let count =
        |s: &Int, n: &Int| -> Int { &(&ua.floor_sum(s, n) + &lb.neg().floor_sum(s, n)) + n };
    let n = &(&t - &s) + &Int::ONE;
    if !count(&s, &n).is_positive() {
        return None;
    }
    if !want {
        return Some((Int::ZERO, Int::ZERO));
    }
    // The least prefix length with a point: the counts are never below zero, so the prefix
    // counts rise.
    let (mut lo, mut hi) = (Int::ONE, n);
    let two = Int::from(2);
    while lo < hi {
        let mid = (&lo + &hi).div_floor(&two);
        if count(&s, &mid).is_positive() {
            hi = mid;
        } else {
            lo = &mid + &Int::ONE;
        }
    }
    let v = &(&s + &lo) - &Int::ONE;
    let w = lb.ceil(&v);
    Some((v, w))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_floor_sum_matches_the_sum() {
        for n in 0..12i64 {
            for m in 1..7i64 {
                for a in -9..9i64 {
                    for b in -9..9i64 {
                        let want: i64 = (0..n).map(|i| (a * i + b).div_euclid(m)).sum();
                        let got = floor_sum(&n.into(), &m.into(), &a.into(), &b.into());
                        assert_eq!(got, Int::from(want), "n {n} m {m} a {a} b {b}");
                    }
                }
            }
        }
    }
}

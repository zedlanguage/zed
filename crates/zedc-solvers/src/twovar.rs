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

use super::linear::{Q, Term};
use zedc_int::int::{Int, IntRange, meet_range, row_range};

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
        (&(&self.p * x) + &self.q).div_ceil(&self.r)
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

/// The integer range `[lo, hi]`, either end unbounded when `None`, narrowed by `lo2` and `hi2`
/// ([`meet_range`], with the ends passed apart as the callers here have them).
fn narrow(range: &mut IntRange, lo2: Option<Int>, hi2: Option<Int>) {
    meet_range(range, (lo2, hi2));
}

/// The bounds of `x` and the lines that bound `y` above and below.
type Split = (IntRange, Vec<Line>, Vec<Line>);

/// The bounds that the rows over `x[x]` and, when given, `x[y]`, put on `x`, and the lines that
/// bound `y` above and below, with `x` read negated where `flip` is set; `None` when a row with
/// neither variable, or the bounds of `x`, show that the rows have no point.
fn split(rows: &[(&[Term], &Int)], x: usize, y: Option<usize>, flip: bool) -> Option<Split> {
    let mut xs: (Option<Int>, Option<Int>) = (None, None);
    let (mut upper, mut lower): (Vec<Line>, Vec<Line>) = (Vec::new(), Vec::new());
    for (a, k) in rows {
        let at = |v: usize| {
            a.iter()
                .find(|(i, _)| *i == v)
                .map_or(Int::ZERO, |(_, c)| c.clone())
        };
        let cx = if flip { -&at(x) } else { at(x) };
        let cy = y.map_or(Int::ZERO, at);
        let k = (*k).clone();
        if cy.is_zero() {
            if !cx.is_zero() {
                meet_range(&mut xs, row_range(&cx, &k, false).0);
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
    Some((xs, upper, lower))
}

/// An integer point of the rows, over `x[x]` and, when given, `x[y]`, or `None` when they have
/// none. Without `want` a point found is answered by zeros.
pub fn point(
    rows: &[(&[Term], &Int)],
    x: usize,
    y: Option<usize>,
    want: bool,
) -> Option<(Int, Int)> {
    let (xs, upper, lower) = split(rows, x, y, false)?;
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

/// The least and the greatest integer `x[x]` of the integer points of the rows over `x[x]` and
/// `x[y]`, each `None` where `x` has no bound that way; `None` when the rows have no point.
///
/// Complexity tradeoff: naive version, a search over values of `x`: one feasibility question
/// of the rows for each value tried, O(log d) questions for an end at distance d from a known
/// point (`hull_side` of zedc-presburger, each question a run of the Omega test). Used: the
/// envelopes of [`point`], scanned from the left (for the greatest, with `x` negated): the
/// first piece of the line where the envelopes leave an integer point holds the least `x`, and
/// inside it the least `x` with a point is found by bisection on the floor-sum counts of its
/// prefixes. O(m log m) for `m` rows, plus O(log w) floor sums for the width `w` of that
/// piece, each logarithmic in the coefficients; no feasibility question is asked. Integer
/// programs in two variables can be solved in O(log) arithmetic steps (Eisenbrand and Rote,
/// "Fast 2-variable integer programming", IPCO 2001); the scan is simpler, exact at any
/// magnitude, and reuses the envelopes and counts of [`point`].
pub fn ends(rows: &[(&[Term], &Int)], x: usize, y: usize) -> Option<(Option<Int>, Option<Int>)> {
    let lo = least_x(rows, x, y, false)?;
    let hi = least_x(rows, x, y, true)?;
    Some((lo, hi.map(|v| -&v)))
}

/// The least integer `x` (negated `x` where `flip` is set) of the integer points of the rows:
/// `Some(None)` when the points reach every value below some `x`, `None` when there is no
/// point.
fn least_x(rows: &[(&[Term], &Int)], x: usize, y: usize, flip: bool) -> Option<Option<Int>> {
    let (xs, upper, lower) = split(rows, x, Some(y), flip)?;
    if upper.is_empty() || lower.is_empty() {
        // `y` is bounded on one side at most: every integer `x` in its range has a point.
        return Some(xs.0);
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
        let (ua, lb) = (&upper[u[i].0], &lower[l[j].0]);
        // The pieces run from the left, so the first with a point holds the least `x`, which
        // [`piece`] finds when the piece is bounded on the left. It is not only where no
        // bound of `x` and no earlier piece closes it and `ua - lb` does not rise: falling to
        // the right, it is 1 or more far enough left; constant, the counts repeat with the
        // period of the lines. Either way the points reach every value to the left.
        if let Some((v, _)) = piece(ua, lb, &left, &right, &xs, true) {
            let rises = ua.slope().sub(&lb.slope()).is_positive();
            let open = left.is_none() && xs.0.is_none() && !rises;
            return Some((!open).then_some(v));
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

/// Exact integer projection of two-variable rows onto `x`: either an exact finite union of
/// disjoint closed intervals (an absent end infinite), or `Holed` where some segment's narrow
/// strip `0 <= u(x) - l(x) < 1` contains an internal hole (a non-convex strip or periodic stride).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TwoVarProj {
    /// Exact finite union of disjoint closed intervals (an absent end infinite).
    Ranges(Vec<(Option<Int>, Option<Int>)>),
    /// Some narrow strip `0 <= u(x) - l(x) < 1` contains an internal hole or periodic stride.
    Holed,
}

/// Appends a closed interval `(lo, hi)` (ignoring empty ones) to a sorted list of disjoint
/// intervals, merging with the previous interval when adjacent or overlapping.
fn push_range(out: &mut Vec<(Option<Int>, Option<Int>)>, r: (Option<Int>, Option<Int>)) {
    if let (Some(a), Some(b)) = (&r.0, &r.1)
        && a > b
    {
        return;
    }
    if let Some((_, prev_hi)) = out.last_mut() {
        match (&*prev_hi, &r.0) {
            (None, _) => return,
            (Some(ph), Some(cl)) if &(ph + &Int::ONE) >= cl => {
                *prev_hi = match (&*prev_hi, &r.1) {
                    (_, None) => None,
                    (Some(a), Some(b)) => Some(a.clone().max(b.clone())),
                    (None, _) => None,
                };
                return;
            }
            (Some(_), None) => {
                *prev_hi = match (&*prev_hi, &r.1) {
                    (_, None) => None,
                    (Some(a), Some(b)) => Some(a.clone().max(b.clone())),
                    (None, _) => None,
                };
                return;
            }
            _ => {}
        }
    }
    out.push(r);
}

/// Exact integer projection of `ua >= y >= lb` over a finite strip `[a, b]` where
/// `0 <= ua(x) - lb(x) < 1` for every `x` in `[a, b]`, so each `x` has either 0 or 1 integer `y`.
/// Returns `Some(None)` if empty, `Some(Some((lo, hi)))` if the feasible `x` values form one
/// contiguous interval, or `None` if there is an internal hole.
fn convex_strip(ua: &Line, lb: &Line, a: Int, b: Int) -> Option<Option<(Int, Int)>> {
    if a > b {
        return Some(None);
    }
    let two = Int::from(2);
    // Opposite (or zero) slopes: `floor(ua(x)) - ceil(lb(x))` is monotone in `x`, so feasible
    // integers always form a single contiguous interval with zero holes, found in O(log(b - a)).
    if !ua.p.is_negative() && !lb.p.is_positive() {
        if ua.floor(&b) < lb.ceil(&b) {
            return Some(None);
        }
        if ua.floor(&a) >= lb.ceil(&a) {
            return Some(Some((a, b)));
        }
        let (mut lo, mut hi) = (a, b.clone());
        while lo < hi {
            let mid = (&lo + &hi).div_floor(&two);
            if ua.floor(&mid) >= lb.ceil(&mid) {
                hi = mid;
            } else {
                lo = &mid + &Int::ONE;
            }
        }
        return Some(Some((lo, b)));
    }
    if !ua.p.is_positive() && !lb.p.is_negative() {
        if ua.floor(&a) < lb.ceil(&a) {
            return Some(None);
        }
        if ua.floor(&b) >= lb.ceil(&b) {
            return Some(Some((a, b)));
        }
        let (mut lo, mut hi) = (a.clone(), b);
        while lo < hi {
            let mid = (&(&lo + &hi) + &Int::ONE).div_floor(&two);
            if ua.floor(&mid) >= lb.ceil(&mid) {
                lo = mid;
            } else {
                hi = &mid - &Int::ONE;
            }
        }
        return Some(Some((a, hi)));
    }
    // Same nonzero slope sign: since `0 <= ua(x) - lb(x) < 1`, each `x` contributes 0 or 1 to
    // `count(s, n) = sum_{i=0}^{n-1} (floor(ua(s+i)) - ceil(lb(s+i)) + 1)`.
    let count =
        |s: &Int, n: &Int| -> Int { &(&ua.floor_sum(s, n) + &lb.neg().floor_sum(s, n)) + n };
    let len = &(&b - &a) + &Int::ONE;
    let tot = count(&a, &len);
    if !tot.is_positive() {
        return Some(None);
    }
    if tot == len {
        return Some(Some((a, b)));
    }
    // First `1`: least `m` in `1..=len` with `count(a, m) > 0`.
    let (mut lo, mut hi) = (Int::ONE, len.clone());
    while lo < hi {
        let mid = (&lo + &hi).div_floor(&two);
        if count(&a, &mid).is_positive() {
            hi = mid;
        } else {
            lo = &mid + &Int::ONE;
        }
    }
    let first = &(&a + &lo) - &Int::ONE;
    // Last `1`: least `m` in `lo..=len` with `count(a, m) == tot`.
    let (mut lo2, mut hi2) = (lo, len);
    while lo2 < hi2 {
        let mid = (&lo2 + &hi2).div_floor(&two);
        if count(&a, &mid) == tot {
            hi2 = mid;
        } else {
            lo2 = &mid + &Int::ONE;
        }
    }
    let last = &(&a + &lo2) - &Int::ONE;
    if (&(&last - &first) + &Int::ONE) == tot {
        Some(Some((first, last)))
    } else {
        None
    }
}

/// Exact integer projection of rows over `x[x]` and (when given) `x[y]` onto `x[x]`, returning
/// `TwoVarProj::Ranges` whenever every envelope segment's narrow strip `0 <= u(x) - l(x) < 1`
/// is hole-free, and `TwoVarProj::Holed` otherwise.
///
/// Complexity tradeoff: naive version, Pugh's Omega projection (W. Pugh, "A practical algorithm
/// for exact array dependence analysis", CACM 35(8), 1992, sec. "Projection") emits O(b)
/// splinters for a lower bound with coefficient `b` and upper coefficient `a >= 2`, taking O(k)
/// splinters per projection on `persist` (`x + k*y >= -1000`, `x - (j+2)*y >= 0`) and O(k^2)
/// across k tests; or the general solver + cover (`Level::open` + `solve_omega` + `exact_each`).
/// Used: convex lower and concave upper envelopes in O(m log m) for m rows (the convex hull
/// trick of [`point`]), swept across O(m) segments. On `u(x) - l(x) >= 1` every integer `x` has
/// an integer `y` (solid range, O(1)); on `0 <= u(x) - l(x) < 1` each `x` has 0 or 1 integer
/// `y`, so `floor_sum` counts points in O(log M) arithmetic steps (or O(log w) binary search
/// when slopes have opposite signs, where `n(x)` is monotone and guaranteed hole-free).
/// Structural refusal (`Holed`) only when a narrow strip genuinely has an internal hole, with
/// no size threshold or cap.
pub fn project_convex(rows: &[(&[Term], &Int)], x: usize, y: Option<usize>) -> TwoVarProj {
    let Some((xs, upper, lower)) = split(rows, x, y, false) else {
        return TwoVarProj::Ranges(Vec::new());
    };
    if upper.is_empty() || lower.is_empty() {
        return TwoVarProj::Ranges(vec![xs]);
    }
    let u = least(&upper);
    let negs: Vec<Line> = lower.iter().map(Line::neg).collect();
    let l = least(&negs);
    let (mut i, mut j) = (0, 0);
    let mut left: Option<Q> = None;
    let mut out: Vec<(Option<Int>, Option<Int>)> = Vec::new();
    let one = Q::of(Int::ONE);
    loop {
        let ni = u.get(i + 1).and_then(|e| e.1.clone());
        let nj = l.get(j + 1).and_then(|e| e.1.clone());
        let right = match (&ni, &nj) {
            (Some(a), Some(b)) => Some(a.min(b).clone()),
            (Some(a), None) => Some(a.clone()),
            (None, b) => b.clone(),
        };
        let mut range = xs.clone();
        narrow(
            &mut range,
            left.as_ref().map(|q| &q.floor() + &Int::ONE),
            right.as_ref().map(Q::floor),
        );
        let non_empty = !matches!(&range, (Some(a), Some(b)) if a > b);
        if non_empty {
            let (ua, lb) = (&upper[u[i].0], &lower[l[j].0]);
            let dg = ua.slope().sub(&lb.slope());
            let g0 = ua.icpt().sub(&lb.icpt());
            if dg.is_zero() {
                if !g0.is_negative() {
                    if g0 >= one {
                        push_range(&mut out, range);
                    } else {
                        // Parallel lines with `0 <= g0 < 1`: `n(x) in {0, 1}` is periodic with
                        // period `d = ua.slope().d`.
                        let d = ua.slope().d;
                        let count = |s: &Int, n: &Int| -> Int {
                            &(&ua.floor_sum(s, n) + &lb.neg().floor_sum(s, n)) + n
                        };
                        match range {
                            (Some(lo), Some(hi)) => {
                                let len = &(&hi - &lo) + &Int::ONE;
                                if len <= d {
                                    match convex_strip(ua, lb, lo, hi) {
                                        Some(Some((a, b))) => {
                                            push_range(&mut out, (Some(a), Some(b)));
                                        }
                                        Some(None) => {}
                                        None => return TwoVarProj::Holed,
                                    }
                                } else {
                                    let c = count(&lo, &d);
                                    if c == d {
                                        push_range(&mut out, (Some(lo), Some(hi)));
                                    } else if c.is_positive() {
                                        if len >= &d + &d {
                                            return TwoVarProj::Holed;
                                        }
                                        match convex_strip(ua, lb, lo, hi) {
                                            Some(Some((a, b))) => {
                                                push_range(&mut out, (Some(a), Some(b)));
                                            }
                                            Some(None) => {}
                                            None => return TwoVarProj::Holed,
                                        }
                                    }
                                }
                            }
                            (lo, hi) => {
                                let s0 = lo.clone().unwrap_or(Int::ZERO);
                                let c = count(&s0, &d);
                                if c == d {
                                    push_range(&mut out, (lo, hi));
                                } else if c.is_positive() {
                                    return TwoVarProj::Holed;
                                }
                            }
                        }
                    }
                }
            } else {
                let at0 = g0.neg().div(&dg);
                if dg.is_positive() {
                    narrow(&mut range, Some(at0.ceil()), None);
                } else {
                    narrow(&mut range, None, Some(at0.floor()));
                }
                if !matches!(&range, (Some(a), Some(b)) if a > b) {
                    let at1 = one.sub(&g0).div(&dg);
                    if dg.is_positive() {
                        let cut = at1.ceil();
                        let mut tip = range.clone();
                        narrow(&mut tip, None, Some(&cut - &Int::ONE));
                        if let (Some(a), Some(b)) = tip
                            && a <= b
                        {
                            match convex_strip(ua, lb, a, b) {
                                Some(Some((lo, hi))) => push_range(&mut out, (Some(lo), Some(hi))),
                                Some(None) => {}
                                None => return TwoVarProj::Holed,
                            }
                        }
                        let mut solid = range;
                        narrow(&mut solid, Some(cut), None);
                        push_range(&mut out, solid);
                    } else {
                        let cut = at1.floor();
                        let mut solid = range.clone();
                        narrow(&mut solid, None, Some(cut.clone()));
                        push_range(&mut out, solid);
                        let mut tip = range;
                        narrow(&mut tip, Some(&cut + &Int::ONE), None);
                        if let (Some(a), Some(b)) = tip
                            && a <= b
                        {
                            match convex_strip(ua, lb, a, b) {
                                Some(Some((lo, hi))) => push_range(&mut out, (Some(lo), Some(hi))),
                                Some(None) => {}
                                None => return TwoVarProj::Holed,
                            }
                        }
                    }
                }
            }
        }
        let Some(r) = right else {
            break;
        };
        if ni.as_ref() == Some(&r) {
            i += 1;
        }
        if nj.as_ref() == Some(&r) {
            j += 1;
        }
        left = Some(r);
    }
    TwoVarProj::Ranges(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The rows `c0·x + c1·y + k >= 0` as `ends` reads them.
    fn ends_of(rows: &[([i64; 2], i64)]) -> Option<(Option<Int>, Option<Int>)> {
        let terms: Vec<(Vec<Term>, Int)> = (rows.iter())
            .map(|(c, k)| {
                let t = (0..2).filter(|&i| c[i] != 0).map(|i| (i, Int::from(c[i])));
                (t.collect(), Int::from(*k))
            })
            .collect();
        let refs: Vec<(&[Term], &Int)> = terms.iter().map(|(t, k)| (&t[..], k)).collect();
        ends(&refs, 0, 1)
    }

    #[test]
    fn the_ends_match_a_search_of_the_box() {
        // Random rows over `x`, `y` in a box, from a new seed each run: the least and greatest
        // `x` of the integer points, against every point of the box. The box rows come first
        // and last, so the envelopes see them in both orders.
        let (mut rng, _) = crate::seed::Rng::fresh("the_ends_match_a_search_of_the_box");
        let mut next = |m: i64| rng.int(-m, m);
        for case in 0..4000 {
            let b = 1 + case % 9;
            let mut rows: Vec<([i64; 2], i64)> = vec![([1, 0], b), ([0, -1], b)];
            for _ in 0..(1 + case % 4) {
                rows.push(([next(4), next(4)], next(12)));
            }
            rows.extend([([-1, 0], b), ([0, 1], b)]);
            let holds = |x: i64, y: i64| rows.iter().all(|(c, k)| c[0] * x + c[1] * y + k >= 0);
            let xs: Vec<i64> = (-b..=b)
                .filter(|&x| (-b..=b).any(|y| holds(x, y)))
                .collect();
            let want = xs.first().map(|lo| {
                let hi = xs.last().expect("a point");
                (Some(Int::from(*lo)), Some(Int::from(*hi)))
            });
            assert_eq!(ends_of(&rows), want, "rows {rows:?}");
        }
    }

    #[test]
    fn an_end_with_no_bound_is_none() {
        // `0 <= y <= 3`, `x >= 2y - 5`: no greatest `x`; least -5.
        let rows = [([0, 1], 0), ([0, -1], 3), ([1, -2], 5)];
        assert_eq!(ends_of(&rows), Some((Some(Int::from(-5)), None)));
        // `x == 2y + 1` read as two rows, no bound at all: both ends open.
        let rows = [([1, -2], -1), ([-1, 2], 1)];
        assert_eq!(ends_of(&rows), Some((None, None)));
        // `2y <= x <= 2y` and `x` odd by `x == 2y + 1`: no point, though the reals have one.
        let rows = [([1, -2], 0), ([-1, 2], 0), ([1, -2], -1)];
        assert_eq!(ends_of(&rows), None);
        // Parallel lines with points only at every third `x`: `3y <= x <= 3y`, so the points
        // reach every value both ways.
        let rows = [([1, -3], 0), ([-1, 3], 0)];
        assert_eq!(ends_of(&rows), Some((None, None)));
        // `x - 3y` in [1, 1] and `x <= 10`: the greatest is 10, the least open.
        let rows = [([1, -3], -1), ([-1, 3], 1), ([-1, 0], 10)];
        assert_eq!(ends_of(&rows), Some((None, Some(Int::from(10)))));
    }

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

    /// The rows `c0·x + c1·y + k >= 0` as `point` reads them, over `x` and, when `y`, `y`.
    fn point_of(rows: &[([i64; 2], i64)], y: bool, want: bool) -> Option<(Int, Int)> {
        let terms: Vec<(Vec<Term>, Int)> = (rows.iter())
            .map(|(c, k)| {
                let t = (0..2).filter(|&i| c[i] != 0).map(|i| (i, Int::from(c[i])));
                (t.collect(), Int::from(*k))
            })
            .collect();
        let refs: Vec<(&[Term], &Int)> = terms.iter().map(|(t, k)| (&t[..], k)).collect();
        point(&refs, 0, y.then_some(1), want)
    }

    #[test]
    fn the_points_match_a_search_of_the_box() {
        // Random rows over `x`, `y` in a box, from a new seed each run, as for the ends: `point`
        // must give a point of the rows exactly when the box has one, and without `want` answer
        // it by zeros. Both answers occur.
        let (mut rng, _) = crate::seed::Rng::fresh("the_points_match_a_search_of_the_box");
        let mut next = |m: i64| rng.int(-m, m);
        // Both answers on built rows, so the check could fail either way on every run: the
        // box `-1 <= x, y <= 1` alone holds (0, 0); with `x - 2 >= 0` added, `x >= 2` lies
        // outside it, so there is no point.
        let square = |extra: Option<([i64; 2], i64)>| {
            let mut rows = vec![([1, 0], 1), ([0, -1], 1)];
            rows.extend(extra);
            rows.extend([([-1, 0], 1), ([0, 1], 1)]);
            rows
        };
        assert!(points_agree(&square(None), 1), "the box alone: no point");
        assert!(
            !points_agree(&square(Some(([1, 0], -2))), 1),
            "x >= 2: a point"
        );
        for case in 0..2000 {
            let b = 1 + case % 9;
            let mut rows: Vec<([i64; 2], i64)> = vec![([1, 0], b), ([0, -1], b)];
            for _ in 0..(1 + case % 4) {
                rows.push(([next(4), next(4)], next(12)));
            }
            rows.extend([([-1, 0], b), ([0, 1], b)]);
            points_agree(&rows, b);
        }
    }

    /// [`point_of`] on `rows`, which hold the box `-b <= x, y <= b`, against a search of the
    /// box; returns whether the box has a point.
    fn points_agree(rows: &[([i64; 2], i64)], b: i64) -> bool {
        let holds = |x: i64, y: i64| rows.iter().all(|(c, k)| c[0] * x + c[1] * y + k >= 0);
        let exists = (-b..=b).any(|x| (-b..=b).any(|y| holds(x, y)));
        match point_of(rows, true, true) {
            Some((x, y)) => {
                // The box rows keep the point in the box.
                let at = (-b..=b)
                    .flat_map(|i| (-b..=b).map(move |j| (i, j)))
                    .find(|&(i, j)| Int::from(i) == x && Int::from(j) == y);
                let holds = at.is_some_and(|(i, j)| holds(i, j));
                assert!(exists && holds, "rows {rows:?} point {x:?} {y:?}");
            }
            None => assert!(!exists, "rows {rows:?}"),
        }
        let zeros = exists.then_some((Int::ZERO, Int::ZERO));
        assert_eq!(point_of(rows, true, false), zeros, "rows {rows:?}");
        exists
    }

    #[test]
    fn a_point_of_one_variable_or_of_y_bounded_one_way() {
        let p = |x: i64, y: i64| Some((Int::from(x), Int::from(y)));
        // Over `x` alone: `3 <= x <= 5` gives the least; `-7 <= x <= -4` the greatest; an empty
        // range or a row `-1 >= 0` with neither variable has none.
        assert_eq!(
            point_of(&[([1, 0], -3), ([-1, 0], 5)], false, true),
            p(3, 0)
        );
        assert_eq!(
            point_of(&[([1, 0], 7), ([-1, 0], -4)], false, true),
            p(-4, 0)
        );
        assert_eq!(point_of(&[([1, 0], -3), ([-1, 0], 2)], false, true), None);
        assert_eq!(point_of(&[([0, 0], -1)], false, true), None);
        // `y >= x + 1` and `x <= -4`: `y` bounded below only, at `x = -4`.
        assert_eq!(
            point_of(&[([-1, 1], -1), ([-1, 0], -4)], true, true),
            p(-4, -3)
        );
        // `y <= 2x` and `x >= 3`: `y` bounded above only, at `x = 3`.
        assert_eq!(point_of(&[([2, -1], 0), ([1, 0], -3)], true, true), p(3, 6));
        // `y <= 2x` alone, `x` free: at `x = 0`.
        assert_eq!(point_of(&[([2, -1], 0)], true, true), p(0, 0));
        // `0 <= y <= x`, no bound of `x`: the gap `x - 0` rises without end to the right, so
        // the least `x` is 0 and there is no greatest; `0 <= y <= -x` is its mirror.
        let rising = [([1, -1], 0), ([0, 1], 0)];
        assert_eq!(ends_of(&rising), Some((Some(Int::ZERO), None)));
        assert_eq!(point_of(&rising, true, true), p(0, 0));
        let falling = [([-1, -1], 0), ([0, 1], 0)];
        assert_eq!(ends_of(&falling), Some((None, Some(Int::ZERO))));
        assert_eq!(point_of(&falling, true, true), p(-1, 0));
        // `y >= 0` and `x >= 2`: `y` bounded one way, so the ends are those of `x`.
        assert_eq!(
            ends_of(&[([0, 1], 0), ([1, 0], -2)]),
            Some((Some(Int::from(2)), None))
        );
        // `x == 3y`, points at every third `x`, with `x >= 4`: least 6, no greatest; with
        // `x <= 10`: greatest 9, no least.
        let third = [([1, -3], 0), ([-1, 3], 0)];
        let from = [third[0], third[1], ([1, 0], -4)];
        assert_eq!(ends_of(&from), Some((Some(Int::from(6)), None)));
        let to = [third[0], third[1], ([-1, 0], 10)];
        assert_eq!(ends_of(&to), Some((None, Some(Int::from(9)))));
        assert_eq!(point_of(&from, true, true), p(6, 2));
        assert_eq!(
            point_of(&to, true, true).map(|(x, y)| x == &y * &Int::from(3)),
            Some(true)
        );
    }

    fn proj_of(rows: &[([i64; 2], i64)], y: bool) -> TwoVarProj {
        let terms: Vec<(Vec<Term>, Int)> = (rows.iter())
            .map(|(c, k)| {
                let t = (0..2).filter(|&i| c[i] != 0).map(|i| (i, Int::from(c[i])));
                (t.collect(), Int::from(*k))
            })
            .collect();
        let refs: Vec<(&[Term], &Int)> = terms.iter().map(|(t, k)| (&t[..], k)).collect();
        project_convex(&refs, 0, y.then_some(1))
    }

    #[test]
    fn project_convex_matches_a_search_of_the_box() {
        let (mut rng, _) = crate::seed::Rng::fresh("project_convex_matches_a_search_of_the_box");
        let mut next = |m: i64| rng.int(-m, m);
        let mut saw_ranges = 0usize;
        let mut saw_holed = 0usize;
        for case in 0..4000 {
            let b = 1 + case % 11;
            let mut rows: Vec<([i64; 2], i64)> = vec![([1, 0], b), ([0, -1], b)];
            for _ in 0..(1 + case % 5) {
                rows.push(([next(5), next(5)], next(15)));
            }
            rows.extend([([-1, 0], b), ([0, 1], b)]);
            let holds = |x: i64, y: i64| rows.iter().all(|(c, k)| c[0] * x + c[1] * y + k >= 0);
            let xs: Vec<i64> = (-b..=b)
                .filter(|&x| (-b..=b).any(|y| holds(x, y)))
                .collect();
            match proj_of(&rows, true) {
                TwoVarProj::Ranges(ranges) => {
                    saw_ranges += 1;
                    let mut got: Vec<i64> = Vec::new();
                    for (lo, hi) in ranges {
                        let l = lo.expect("bounded lo").to_i128().unwrap() as i64;
                        let h = hi.expect("bounded hi").to_i128().unwrap() as i64;
                        assert!(l <= h, "inverted range ({l}, {h}) for {rows:?}");
                        if let Some(&prev) = got.last() {
                            assert!(l > prev + 1, "unmerged ranges for {rows:?}");
                        }
                        got.extend(l..=h);
                    }
                    assert_eq!(got, xs, "rows {rows:?}");
                }
                TwoVarProj::Holed => {
                    saw_holed += 1;
                    // Every `Holed` return must genuinely have a gap in `xs`.
                    let has_gap = xs.windows(2).any(|w| w[1] > w[0] + 1);
                    assert!(has_gap, "spurious Holed on convex {xs:?} for {rows:?}");
                }
            }
        }
        assert!(
            saw_ranges > 0 && saw_holed > 0,
            "saw {saw_ranges} ranges, {saw_holed} holed"
        );
    }

    #[test]
    fn project_convex_unbounded_and_parallel_cases() {
        let r = |lo: Option<i64>, hi: Option<i64>| {
            TwoVarProj::Ranges(vec![(lo.map(Int::from), hi.map(Int::from))])
        };
        // Opposite-slope persist wedge: `x + 16y >= -1000` and `x - 18y >= 0`.
        // Real intersection at x = -18000/34 = -529.41; first integer x with integer y is -522 (y=-29).
        assert_eq!(
            proj_of(&[([1, 16], 1000), ([1, -18], 0)], true),
            r(Some(-522), None)
        );
        // Parallel stride `x == 2y` (unbounded): Holed.
        assert_eq!(
            proj_of(&[([1, -2], 0), ([-1, 2], 0)], true),
            TwoVarProj::Holed
        );
        // Parallel stride `x == 2y` restricted to `[0, 1]`: convex `[0, 0]`.
        assert_eq!(
            proj_of(
                &[([1, -2], 0), ([-1, 2], 0), ([1, 0], 0), ([-1, 0], 1)],
                true
            ),
            r(Some(0), Some(0))
        );
        // Parallel wide strip `2y <= x <= 2y + 2` (`g0 = 1`): solid `(-inf, +inf)`.
        assert_eq!(proj_of(&[([1, -2], 0), ([-1, 2], 2)], true), r(None, None));
        // Empty parallel strip `2y + 1 <= x <= 2y + 1` with `x == 2y`: empty.
        assert_eq!(
            proj_of(&[([1, -2], 0), ([-1, 2], 0), ([1, -2], -1)], true),
            TwoVarProj::Ranges(vec![])
        );
    }
}

//! Exact meet, union and difference of sets with tails (row CLASSED-periodic-tail), each answer
//! in the one form of [`Classed::tailed`], the form zedc-presburger `exact::ended` builds, so
//! that a set made by these and the same set read by the cover are equal. [`Classed::meet`],
//! [`Classed::join`], [`Classed::join_all`], [`Classed::meet_ranges`] and [`Classed::minus`]
//! come here where a set has tails.
//!
//! The method. Each set is, far enough up, the values whose residue a table marks: its tail
//! above, or a table of one letter (every value, for a ray, or none, for a set bounded above).
//! The same below. Far up, the answer is the two tables combined value by value: for ends `u1`
//! and `u2`, from `u = max(u1, u2)` up, over a table of length `lcm(T1, T2)` read at `r mod T1`
//! and `r mod T2`, cut to its least period ([`Table::new`]). The same below at the lesser end.
//! Between the two ends each set is cut to the stretch and held as a few classes
//! ([`ClassUnion`]: its tail's residues each a class within the stretch, and its own ranges and
//! class), and the operation is done there by the existing operations of sets without tails.
//! Last, the ends are moved in to where the answer starts to agree with its tables, which is the
//! one form ([`normal`]).
//!
//! Complexity. The table of the answer has `lcm(T1, T2)` letters, its exact size before the cut,
//! so it is the cost of the answer and not a limit to add: O(lcm) to build and cut (zed-collections
//! `period::least_period`). Between the ends the operation is that of sets without tails, at
//! their cost: O(p log p) for p ranges where it keeps one class, and where the classes of the
//! two sides differ the values of the stretch listed, O(v) for the v values of both sets there,
//! as [`Classed::join`] and [`Classed::minus`] list two classes without tails. That may be more
//! than the answer's own values (`[0, 10^6)` with the even values past it, joined with the odd
//! values from 1, lists the odd values below `10^6` to give `[0, +inf)`), as the same union
//! without tails does. The answer's form keeps its values between its two ends as plain
//! ranges, each value of a class listed (the form of `exact::ended`), O(v) for those v values.
//! The walk that moves an end in is O(1) for each gap and
//! each piece of every integer passed, O(T) for each piece of a class passed, and O(lcm) of the
//! two tables of the answer past the other end, where a scan compares them. Test:
//! `tests::tailed_operations_agree_with_the_values_listed` (random sets against the values listed
//! one by one and against the one form built from them); bench: zedc-presburger
//! `exact::tests::bench::tailed_operations_scale_with_the_table` (coprime steps, so the table is
//! their product).

use std::cmp::{max, min};

use super::{Classed, Tail};
use crate::class_union::ClassUnion;
use crate::interval::{End, IntervalSet, Num};
use crate::lattice::{Congruence, Lattice};

/// The operation [`combined`] does.
#[derive(Clone, Copy, Debug)]
pub(super) enum Op {
    /// The values in both.
    Meet,
    /// The values in either.
    Join,
    /// The values in the first and not the second.
    Minus,
}

impl Op {
    fn of(self, a: bool, b: bool) -> bool {
        match self {
            Op::Meet => a && b,
            Op::Join => a || b,
            Op::Minus => a && !b,
        }
    }
}

/// A residue table modulo its length, at its least period, with for each residue the distance
/// back and forward to the nearest residue of each kind, so that the nearest value of a kind is
/// found in O(1).
struct Table {
    have: Vec<bool>,
    /// The length, as a number.
    n: Num,
    /// `back[k][r]`: the least `d >= 0` with `have[(r - d) mod len] == (k == 1)`; `usize::MAX`
    /// where no residue is of that kind.
    back: [Vec<usize>; 2],
    /// `fwd[k][r]`: the least `d >= 0` with `have[(r + d) mod len] == (k == 1)`.
    fwd: [Vec<usize>; 2],
}

impl Table {
    /// The table `have`, cut to its least period (zed-collections `period::least_period`, O(n)),
    /// so that one periodic set has one table: two tables of one set read from residue 0 repeat
    /// one least block, which is that set's least period (proof at [`Classed::tailed`]).
    fn new(mut have: Vec<bool>) -> Table {
        let d = zed_collections::period::least_period(&have);
        have.truncate(d);
        let len = have.len();
        let dist = |kind: bool, back: bool| {
            // Two rounds of the cycle, so that a residue's nearest of a kind may lie across the
            // wrap; the distance is kept from the second round on. O(len).
            let mut out = vec![usize::MAX; len];
            let mut cur = usize::MAX;
            for i in 0..2 * len {
                let r = if back {
                    i % len
                } else {
                    (2 * len - 1 - i) % len
                };
                cur = if have[r] == kind {
                    0
                } else {
                    cur.saturating_add(1)
                };
                if i >= len {
                    out[r] = cur;
                }
            }
            out
        };
        Table {
            n: Num::from(len as u64),
            back: [dist(false, true), dist(true, true)],
            fwd: [dist(false, false), dist(true, false)],
            have,
        }
    }

    /// The one letter of a table of one value or none.
    fn uniform(&self) -> Option<bool> {
        (self.have.len() == 1).then(|| self.have[0])
    }

    fn residue(&self, v: &Num) -> usize {
        let r = v.rem_euclid(&self.n).to_i128();
        r.expect("a residue below the table's length") as usize
    }

    fn at(&self, v: &Num) -> bool {
        self.have[self.residue(v)]
    }

    /// The greatest value at or below `v` whose residue is of the kind `kind`.
    fn last(&self, kind: bool, v: &Num) -> Option<Num> {
        let d = self.back[usize::from(kind)][self.residue(v)];
        (d != usize::MAX).then(|| v - &Num::from(d as u64))
    }

    /// The least value at or above `v` whose residue is of the kind `kind`.
    fn first(&self, kind: bool, v: &Num) -> Option<Num> {
        let d = self.fwd[usize::from(kind)][self.residue(v)];
        (d != usize::MAX).then(|| v + &Num::from(d as u64))
    }

    /// The table of the values negated: `v` marked where `-v` was.
    fn negated(&self) -> Table {
        let len = self.have.len();
        Table::new((0..len).map(|r| self.have[(len - r) % len]).collect())
    }

    fn tail(&self, end: End) -> Tail {
        Tail::new(end, &self.have)
    }
}

/// The table of length `lcm(a, b)` with `op` of `a` at `r mod |a|` and `b` at `r mod |b|`, cut
/// to its least period. Proof that it is the answer's table: for `v` past both ends, `v mod |a|`
/// is `(v mod lcm) mod |a|`, as `|a|` divides the lcm, and the same for `b`.
fn combined_table(a: &[bool], b: &[bool], op: Op) -> Table {
    let (la, lb) = (a.len(), b.len());
    let g = gcd(la, lb);
    let len = (la / g)
        .checked_mul(lb)
        .expect("the table of the answer, its own size, fits in memory");
    Table::new((0..len).map(|i| op.of(a[i % la], b[i % lb])).collect())
}

fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// The set far up: from the end on, the values its table marks. A tail above gives its own; a
/// set with none is a ray there (one letter `true`, from the ray's start) or bounded (one
/// letter `false`, from one past its greatest value), and never from at or below the end of a
/// tail below, where that tail reads the values.
fn view_above(s: &Classed) -> (End, Vec<bool>) {
    let tails = s.tails.as_deref();
    if let Some(t) = tails.and_then(|t| t.above.as_ref()) {
        return (t.end.clone(), t.have.to_vec());
    }
    let floor = (tails.and_then(|t| t.below.as_ref())).map_or(End::NegInf, |t| t.end.succ());
    match s.ranges.last() {
        None => (End::NegInf, vec![false]),
        Some((lo, End::PosInf)) => (max(lo.clone(), floor), vec![true]),
        Some((_, hi)) => (max(hi.succ(), floor), vec![false]),
    }
}

/// [`view_above`] below: the end up to which the table reads the set. A tail above with the end
/// `-inf` reads every value, so the set below is that tail.
fn view_below(s: &Classed) -> (End, Vec<bool>) {
    let tails = s.tails.as_deref();
    if let Some(t) = tails.and_then(|t| t.below.as_ref()) {
        return (t.end.clone(), t.have.to_vec());
    }
    let above = tails.and_then(|t| t.above.as_ref());
    if let Some(t) = above.filter(|t| t.end == End::NegInf) {
        return (End::PosInf, t.have.to_vec());
    }
    let ceil = above.map_or(End::PosInf, |t| t.end.pred());
    match s.ranges.first() {
        None => (End::PosInf, vec![false]),
        Some((End::NegInf, hi)) => (min(hi.clone(), ceil), vec![true]),
        Some((lo, _)) => (min(lo.pred(), ceil), vec![false]),
    }
}

/// The values of `s` within `[lo, hi]` (both finite), as classes: each residue a tail marks, a
/// class within the part of the stretch the tail reads, and `s`'s own ranges and class within
/// the part between its tails. Exact: by [`Classed::tailed`], those are its values there.
/// O(T) classes for a table of `T` letters.
fn within(s: &Classed, lo: &End, hi: &End) -> ClassUnion {
    let mut u = ClassUnion::empty();
    let tails = s.tails.as_deref();
    let below = tails.and_then(|t| t.below.as_ref());
    let above = tails.and_then(|t| t.above.as_ref());
    let mut periodic = |t: &Tail, a: End, b: End| {
        if a <= b {
            for (r, _) in t.have.iter().enumerate().filter(|(_, m)| **m) {
                let class = Congruence::new(t.step.clone(), Num::from(r as u64));
                u.add(Classed::new(
                    IntervalSet::range(a.clone(), b.clone()),
                    class,
                ));
            }
        }
    };
    if let Some(t) = above {
        periodic(t, max(t.end.clone(), lo.clone()), hi.clone());
    }
    if let Some(t) = below {
        periodic(t, lo.clone(), min(t.end.clone(), hi.clone()));
    }
    let a = below.map_or(lo.clone(), |t| max(lo.clone(), t.end.succ()));
    let b = above.map_or(hi.clone(), |t| min(hi.clone(), t.end.pred()));
    if a <= b {
        u.add(Classed::new(
            s.ranges.meet(&IntervalSet::range(a, b)),
            s.class.clone(),
        ));
    }
    u
}

/// `op` of the two unions of classes, none with tails, by the operations of sets without
/// tails: the union joined, the meet of each pair (`(∪A) ∩ (∪B) = ∪(A ∩ B)`), and for the
/// difference each class of the first with every class of the second taken away in turn.
fn apply(a: &ClassUnion, b: &ClassUnion, op: Op) -> Classed {
    let mut u = ClassUnion::empty();
    match op {
        Op::Join => u = a.join(b),
        Op::Meet => {
            for x in a.sets() {
                for y in b.sets() {
                    u.add(x.meet(y));
                }
            }
        }
        Op::Minus => {
            for x in a.sets() {
                let mut left = x.clone();
                for y in b.sets() {
                    if left.is_empty() {
                        break;
                    }
                    left = left.minus(y);
                }
                u.add(left);
            }
        }
    }
    u.into_classed()
}

/// `op` of `a` and `b`, at least one with tails, exact, in the one form (module doc).
pub(super) fn combined(a: &Classed, b: &Classed, op: Op) -> Classed {
    let ((ua, ta), (ub, tb)) = (view_above(a), view_above(b));
    let ((la, sa), (lb, sb)) = (view_below(a), view_below(b));
    let (u_end, above) = (max(ua, ub), combined_table(&ta, &tb, op));
    let (l_end, below) = (min(la, lb), combined_table(&sa, &sb, op));
    // The stretch between: finite or empty, as a view's end above is finite or `-inf`, and below
    // finite or `+inf`.
    let (lo, hi) = (l_end.succ(), u_end.pred());
    let middle = if lo <= hi {
        apply(&within(a, &lo, &hi), &within(b, &lo, &hi), op)
    } else {
        Classed::plain(IntervalSet::empty())
    };
    normal(l_end, &below, middle, u_end, &above)
}

/// The set that is `below`'s values up to `l_end`, `middle` (no tails, within `(l_end, u_end)`)
/// between, and `above`'s values from `u_end` up, in the one form of `exact::ended`: where the
/// tables are of one letter, no tails and the set as [`Classed::new`] keeps it; else the tail
/// above from `u`, the least value of the set at or above `p`, one more than the greatest value
/// where the set and the table above differ ([`ray_start`]); the same below on the values
/// negated; one tail over every value (end `-inf`) where the set is its table everywhere; both
/// tails over a wider set of every integer where the two ends meet; and else the wider set
/// `(-inf, l] ∪ (E ∩ (l, u)) ∪ [u, +inf)` as plain ranges. Each is a function of the set alone
/// (proof at `exact::ended` and [`Classed::tailed`]), so the form is.
fn normal(l_end: End, below: &Table, middle: Classed, u_end: End, above: &Table) -> Classed {
    let ray = |lo: End, hi: End| Classed::plain(IntervalSet::range(lo, hi));
    if let (Some(b), Some(a)) = (below.uniform(), above.uniform()) {
        let mut set = middle;
        if a {
            set = set.join(&ray(u_end, End::PosInf));
        }
        if b {
            set = set.join(&ray(End::NegInf, l_end));
        }
        return set;
    }
    let whole = |t: &Table| {
        let top = Classed::plain(IntervalSet::top());
        Classed::tailed(top, None, Some(t.tail(End::NegInf)))
    };
    let u = match above.uniform() {
        None => match ray_start(above, &u_end, &middle, &l_end, below) {
            None => return whole(above),
            u => u,
        },
        Some(_) => None,
    };
    let l = match below.uniform() {
        None => {
            let negated = Classed::new(
                middle.ranges.neg(),
                match &middle.class {
                    Congruence::Class { modulus, residue } => {
                        Congruence::new(modulus.clone(), -residue)
                    }
                    c => c.clone(),
                },
            );
            let (b, a) = (below.negated(), above.negated());
            match ray_start(&b, &-&l_end, &negated, &-&u_end, &a) {
                None => return whole(below),
                l => l.map(|l| -&l),
            }
        }
        Some(_) => None,
    };
    let fin = |v: &Num| End::Fin(v.clone());
    if let (Some(l), Some(u)) = (&l, &u)
        && &(l + &Num::ONE) >= u
    {
        let top = Classed::plain(IntervalSet::top());
        return Classed::tailed(top, Some(below.tail(fin(l))), Some(above.tail(fin(u))));
    }
    let lo = l.as_ref().map_or(End::NegInf, |l| fin(&(l + &Num::ONE)));
    let hi = u.as_ref().map_or(End::PosInf, |u| fin(&(u - &Num::ONE)));
    let between = IntervalSet::range(lo.clone(), hi.clone());
    let mut pieces: Vec<(End, End)> =
        (Classed::new(middle.ranges.meet(&between), middle.class.clone()).pieces()).collect();
    listed(above, max(u_end, lo.clone()), hi.clone(), &mut pieces);
    listed(below, lo, min(l_end, hi), &mut pieces);
    if let Some(l) = &l {
        pieces.push((End::NegInf, fin(l)));
    }
    if let Some(u) = &u {
        pieces.push((fin(u), End::PosInf));
    }
    let wider = Classed::plain(IntervalSet::from_pieces(pieces));
    Classed::tailed(
        wider,
        l.as_ref().map(|l| below.tail(fin(l))),
        u.as_ref().map(|u| above.tail(fin(u))),
    )
}

/// The values of `[a, b]` that `t` marks, pushed as pieces: the stretch whole for a table of
/// one `true`, nothing for one `false`, and else each marked value. A table of more letters is
/// listed only between its view's end and the end of the answer's tail on that side, fewer
/// than its length of values: the end above `u` is less than `p + T` (the next marked value
/// from `p`), and `p` is at most the view's end `u_end`, as the walk compares from below it
/// (the same below).
fn listed(t: &Table, a: End, b: End, pieces: &mut Vec<(End, End)>) {
    if a > b {
        return;
    }
    match t.uniform() {
        Some(true) => pieces.push((a, b)),
        Some(false) => {}
        None => {
            let (End::Fin(a), End::Fin(b)) = (a, b) else {
                unreachable!("a table of two kinds is listed between finite ends");
            };
            let mut v = a;
            while v <= b {
                if t.at(&v) {
                    pieces.push((End::Fin(v.clone()), End::Fin(v.clone())));
                }
                v = &v + &Num::ONE;
            }
        }
    }
}

/// For [`normal`], with `above` of two kinds: the least value `u` of the set at or above `p`,
/// one more than the greatest value where the set and `above` differ; `None` where they never
/// differ. The set below `u_end` is `middle` within `(l_end, u_end)` and `below`'s values up to
/// `l_end`.
fn ray_start(
    above: &Table,
    u_end: &End,
    middle: &Classed,
    l_end: &End,
    below: &Table,
) -> Option<Num> {
    let d = last_differing(above, u_end, middle, l_end, below)?;
    Some(
        (above.first(true, &(&d + &Num::ONE)))
            .expect("a table of two kinds marks a value at or above any"),
    )
}

/// The greatest value below `u_end` where the set differs from `above` (see [`ray_start`]).
/// Walk: from `u_end - 1` down through the pieces of `middle` and the gaps between them, each in
/// O(1) by the table's distances, or O(T) for a piece of a class ([`differs_in`]); then past
/// `l_end`, where the set is `below`, a scan of at most the lcm of the two tables' lengths, as
/// two different periodic sets differ within any run of their periods' lcm.
fn last_differing(
    above: &Table,
    u_end: &End,
    middle: &Classed,
    l_end: &End,
    below: &Table,
) -> Option<Num> {
    let End::Fin(u) = u_end else {
        // `-inf`: the table reads every value.
        return None;
    };
    let mut cur = u - &Num::ONE;
    if End::Fin(cur.clone()) > *l_end {
        let step = middle.strided();
        for (a, b) in middle.ranges.pieces().rev() {
            let (End::Fin(a), End::Fin(b)) = (a, b) else {
                unreachable!("the stretch between the ends is finite");
            };
            // The gap `(b, cur]`, no member: a marked value there differs.
            let x = above.last(true, &cur).expect("a table of two kinds");
            if &x > b {
                return Some(x);
            }
            if let Some(x) = differs_in(above, a, b, step) {
                return Some(x);
            }
            cur = a - &Num::ONE;
        }
        let x = above.last(true, &cur).expect("a table of two kinds");
        if End::Fin(x.clone()) > *l_end {
            return Some(x);
        }
        let End::Fin(l) = l_end else {
            unreachable!("an end below under a finite value is finite");
        };
        cur = l.clone();
    }
    if below.have == above.have {
        return None;
    }
    let (lb, la) = (below.have.len(), above.have.len());
    let span = (lb / gcd(lb, la)) * la;
    let (mut rb, mut ra) = (below.residue(&cur), above.residue(&cur));
    for k in 0..span {
        if below.have[rb] != above.have[ra] {
            return Some(&cur - &Num::from(k as u64));
        }
        rb = (rb + lb - 1) % lb;
        ra = (ra + la - 1) % la;
    }
    unreachable!("two different least-period tables differ within the lcm of their lengths")
}

/// The greatest `x` in `[a, b]`, a piece of a set (its values those of `step`'s class there, or
/// every value where `step` is `None`), where membership and `t` differ. With a class `r mod m`:
/// a value `t` marks out of the class (for each marked residue `s` the greatest `x <= b` with
/// `x ≡ s (mod T)`, or the one `T` below it where `x` is in the class and `T` is no multiple of
/// `m`, as `x - T` is then out of it; none where `m` divides `T`, as then all such `x` are in it),
/// or a value of the class `t` does not mark (each unmarked `s` met with the class by the Chinese
/// remainder theorem, [`Congruence::meet`]). O(T).
fn differs_in(t: &Table, a: &Num, b: &Num, step: Option<(&Num, &Num)>) -> Option<Num> {
    let Some((m, r)) = step else {
        return t.last(false, b).filter(|x| x >= a);
    };
    let n = &t.n;
    let divides = n.rem_euclid(m).is_zero();
    let r = &r.rem_euclid(m);
    let mut best: Option<Num> = None;
    for (s, &mark) in t.have.iter().enumerate() {
        let s = Num::from(s as u64);
        let x = if mark {
            let x = b - &(b - &s).rem_euclid(n);
            if x.rem_euclid(m) != *r {
                Some(x)
            } else if !divides {
                Some(&x - n)
            } else {
                None
            }
        } else {
            match Congruence::new(n.clone(), s).meet(&Congruence::new(m.clone(), r.clone())) {
                Congruence::Class { modulus, residue } => {
                    Some(b - &(b - &residue).rem_euclid(&modulus))
                }
                Congruence::Bottom => None,
            }
        };
        if let Some(x) = x
            && &x >= a
            && best.as_ref().is_none_or(|y| &x > y)
        {
            best = Some(x);
        }
    }
    best
}

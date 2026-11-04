//! The order of two flattened sequences of parts when the walk of [`Formula::cmp`] meets
//! parts grouped at other places on each side. Each sequence is parsed bottom up into
//! symbols kept in one arena per call, each symbol stored once: a constraint, a negation, a
//! conjunction or disjunction (by the root of its sequence), a run of one symbol repeated,
//! or a chunk of two or more symbols. The parse is that of Mehlhorn, Sundar and Uhrig
//! ("Maintaining dynamic sequences under equality tests in polylogarithmic time",
//! Algorithmica 17, 1997): at even levels each run of one symbol becomes a run symbol, and at
//! odd levels, where no two neighbors are equal, deterministic coin tossing (Cole and
//! Vishkin) colors each symbol from its number and those of the four before it, and a chunk
//! starts at each symbol whose color is above both its neighbors'. Each choice depends only on
//! a few neighbors, so a sequence has one parse however it was grouped, two equal sequences
//! have one root, and joining two parsed sequences reparses only a few symbols at each level
//! near the join. A symbol equal to another is the same entry of the arena, so equal symbols
//! are found equal exactly, without a hash. Two sequences are compared by walking their
//! parses from the start, passing over each symbol the two share.
//
// Complexity tradeoff: a sequence of length N has a parse of O(log N) levels, and joining two
// parsed sequences reparses O(1) symbols at each, so a part's sequence costs O(k log N) for
// its k parts, and both sides O(e log N) for e distinct edges, each shared part read once per
// call (the memo below). The walk of two parses opens symbols only where they differ, which
// by the same locality is O(1) symbols at each of O(log N) levels before the first
// difference, and the same again inside each element it compares (inferred from the parse;
// measured only together with it). The counts of runs are integers of O(log N) bits. When
// the sharing makes N exponential in the n distinct parts, as in
// `l01_38_presburger::shared::shifted_chains`, this is O(n^2). The exact methods known for
// comparing two such compressed sequences (this parse; recompression, Jeż 2015; its longest
// common extension, I 2017) cost n log N too; a hash of each sequence would be linear but
// cannot decide equality alone. No answer is given up; the cost is. A complete solution keeps
// each part's parse with the part, so that it is built once and not once per call.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::mem;
use std::slice;

use num_bigint::BigUint;
use num_traits::{One, Zero};

use super::super::{Con, Formula};
use super::{Id, Side};

/// A symbol's number in the arena.
type S = usize;

/// A symbol and how many times it is repeated in a row.
type Entry = (S, BigUint);

/// A symbol of a parse.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Sym {
    /// A constraint.
    Con(Con),
    /// The negation of an element.
    Not(S),
    /// A conjunction or disjunction ([`Formula::rank`]), by the root of its flattened parts,
    /// `None` when it has none.
    Seq(u8, Option<S>),
    /// At the given odd level, the symbol repeated the given number of times, at least 2.
    Run(usize, S, BigUint),
    /// At the given even level, two or more symbols.
    Chunk(usize, Box<[S]>),
}

/// The symbols of one call and the results of the shared parts read so far.
pub(super) struct Canon {
    syms: Vec<Sym>,
    ids: HashMap<Sym, S>,
    /// Each shared compound part read: the root of its flattened parts for a conjunction or
    /// disjunction, the element for a negation.
    memo: HashMap<Id, Option<S>>,
}

/// A sequence being built: the root of its parts so far, then elements not yet parsed.
#[derive(Default)]
struct Build {
    root: Option<S>,
    leaves: Vec<S>,
}

impl Canon {
    pub(super) fn new() -> Canon {
        Canon {
            syms: Vec::new(),
            ids: HashMap::new(),
            memo: HashMap::new(),
        }
    }

    /// The order of the parts the two sides have left, read as flattened ([`Formula::cmp`]).
    pub(super) fn cmp_rest(&mut self, kind: u8, a: &Side<'_>, b: &Side<'_>) -> Ordering {
        let x = self.rest(kind, a);
        let y = self.rest(kind, b);
        self.cmp_seqs(x, y)
    }

    /// The root of the parts `side` has left, innermost level first.
    fn rest(&mut self, kind: u8, side: &Side<'_>) -> Option<S> {
        let mut seq = Build::default();
        for (left, _) in side.left.iter().rev() {
            for g in left.as_slice() {
                match g {
                    Formula::Con(c) => {
                        let l = self.intern(Sym::Con(c.clone()));
                        seq.leaves.push(l);
                    }
                    g => {
                        let v = self.value(g);
                        self.put(&mut seq, kind, g, v);
                    }
                }
            }
        }
        self.finish(seq)
    }

    fn intern(&mut self, s: Sym) -> S {
        if let Some(&i) = self.ids.get(&s) {
            return i;
        }
        let i = self.syms.len();
        self.syms.push(s.clone());
        self.ids.insert(s, i);
        i
    }

    /// The level of the parse a symbol is made at: 0 for an element.
    fn level(&self, s: S) -> usize {
        match &self.syms[s] {
            Sym::Run(l, ..) | Sym::Chunk(l, _) => *l,
            Sym::Con(_) | Sym::Not(_) | Sym::Seq(..) => 0,
        }
    }

    /// The result of the compound part `f`: the root of its flattened parts for a conjunction
    /// or disjunction, its element for a negation. A shared part is read once per call.
    fn value(&mut self, f: &Formula) -> Option<S> {
        /// A part whose parts are being read, with its sequence so far and its key when shared.
        struct Frame<'a> {
            node: &'a Formula,
            left: slice::Iter<'a, Formula>,
            seq: Build,
            id: Option<Id>,
        }
        let id = Id::of(f);
        if let Some(v) = id.as_ref().and_then(|id| self.memo.get(id)) {
            return *v;
        }
        let mut stack = vec![Frame {
            node: f,
            left: f.kids().iter(),
            seq: Build::default(),
            id,
        }];
        loop {
            let top = stack.last_mut().expect("the part being read");
            match top.left.next() {
                Some(Formula::Con(c)) => {
                    let l = self.intern(Sym::Con(c.clone()));
                    top.seq.leaves.push(l);
                }
                Some(g) => {
                    let id = Id::of(g);
                    match id.as_ref().and_then(|id| self.memo.get(id)) {
                        Some(&v) => {
                            let kind = top.node.rank();
                            self.put(&mut top.seq, kind, g, v);
                        }
                        None => stack.push(Frame {
                            node: g,
                            left: g.kids().iter(),
                            seq: Build::default(),
                            id,
                        }),
                    }
                }
                None => {
                    let Frame { node, seq, id, .. } = stack.pop().expect("the part being read");
                    let v = match node {
                        Formula::Not(_) => Some(self.intern(Sym::Not(seq.leaves[0]))),
                        _ => self.finish(seq),
                    };
                    if let Some(id) = id {
                        self.memo.insert(id, v);
                    }
                    match stack.last_mut() {
                        Some(top) => {
                            let kind = top.node.rank();
                            self.put(&mut top.seq, kind, node, v);
                        }
                        None => return v,
                    }
                }
            }
        }
    }

    /// Adds the compound part `g`, of result `v` ([`Canon::value`]), to a sequence of a
    /// node of the variant `kind`: its parts when it flattens into the node, else itself.
    fn put(&mut self, seq: &mut Build, kind: u8, g: &Formula, v: Option<S>) {
        if g.flattens_into(kind) {
            self.flush(seq);
            seq.root = self.concat(seq.root, v);
        } else {
            let l = match g {
                Formula::Not(_) => v.expect("a negation's element"),
                _ => self.intern(Sym::Seq(g.rank(), v)),
            };
            seq.leaves.push(l);
        }
    }

    fn flush(&mut self, seq: &mut Build) {
        if !seq.leaves.is_empty() {
            let leaves = mem::take(&mut seq.leaves)
                .into_iter()
                .map(|l| (l, BigUint::one()))
                .collect();
            let part = self.join(None, leaves, None);
            seq.root = self.concat(seq.root, part);
        }
    }

    fn finish(&mut self, mut seq: Build) -> Option<S> {
        self.flush(&mut seq);
        seq.root
    }

    fn concat(&mut self, a: Option<S>, b: Option<S>) -> Option<S> {
        match (a, b) {
            (None, x) | (x, None) => x,
            (Some(_), Some(_)) => self.join(a, Vec::new(), b),
        }
    }

    /// The root of the sequence `a`, then the elements `mid`, then the sequence `b`, given
    /// by their roots. At each level the parse of the whole is that of `a` but for its last
    /// few units, the new units, and that of `b` but for its first few: a cut in `a` holds in
    /// the whole when the two symbols from it on are in `a`, and one in `b` when the five
    /// before it are in `b`, since a color reads the four symbols before it.
    fn join(&mut self, a: Option<S>, mut mid: Vec<Entry>, b: Option<S>) -> Option<S> {
        let mut fa = a.map(|r| Finger::new(self, r, true));
        let mut fb = b.map(|r| Finger::new(self, r, false));
        let mut l = 0;
        loop {
            let open = |f: &Option<Finger>| f.as_ref().is_some_and(|f| !f.done);
            if !open(&fa) && !open(&fb) {
                match mid.as_slice() {
                    [] => return None,
                    [(x, n)] if n.is_one() => return Some(*x),
                    _ => {}
                }
            }
            let chunks = l % 2 == 1;
            let (rem_a, mut ctx_a) = match &mut fa {
                Some(f) if !f.done => {
                    f.cut(self, l, if chunks { 2 } else { 1 }, 4 * chunks as usize)
                }
                _ => (Vec::new(), Vec::new()),
            };
            let (rem_b, ctx_b) = match &mut fb {
                Some(f) if !f.done => f.cut(self, l, if chunks { 5 } else { 1 }, chunks as usize),
                _ => (Vec::new(), Vec::new()),
            };
            let mut window = rem_a;
            window.reverse();
            window.append(&mut mid);
            window.extend(rem_b);
            mid = if chunks {
                ctx_a.reverse();
                self.chunk(l, &ctx_a, &window, ctx_b.first().copied())
            } else {
                self.runs(l, window)
            };
            l += 1;
        }
    }

    /// The units of the even level `l` over `window`, whose ends are ends of runs: each run of
    /// one symbol, as a run symbol, or the symbol itself when it is alone.
    fn runs(&mut self, l: usize, window: Vec<Entry>) -> Vec<Entry> {
        let mut out: Vec<Entry> = Vec::new();
        let mut cur: Option<Entry> = None;
        for (x, c) in window {
            match &mut cur {
                Some((y, n)) if *y == x => *n += c,
                _ => {
                    if let Some(r) = cur.replace((x, c)) {
                        out.push(self.run(l, r));
                    }
                }
            }
        }
        if let Some(r) = cur {
            out.push(self.run(l, r));
        }
        out
    }

    fn run(&mut self, l: usize, (x, n): Entry) -> Entry {
        if n.is_one() {
            (x, n)
        } else {
            (self.intern(Sym::Run(l + 1, x, n)), BigUint::one())
        }
    }

    /// The units of the odd level `l` over `window`, whose start is the start of the
    /// sequence or a cut and whose end its end or a cut, with no two neighbors equal: `left`
    /// holds the up to four symbols before the window, fewer only at the start, and `right`
    /// the one after it, if any.
    fn chunk(&mut self, l: usize, left: &[S], window: &[Entry], right: Option<S>) -> Vec<Entry> {
        debug_assert!(window.iter().all(|(_, n)| n.is_one()), "one of each");
        debug_assert!(
            window.windows(2).all(|w| w[0].0 != w[1].0),
            "no equal neighbors"
        );
        // Before the start of the sequence, numbers no symbol has, distinct from each other.
        let mut colors: Vec<usize> = (1..=4 - left.len())
            .rev()
            .map(|j| usize::MAX - (j - 1))
            .collect();
        colors.extend(left);
        colors.extend(window.iter().map(|(x, _)| *x));
        colors.extend(right);
        // Four rounds of coin tossing take distinct neighbors of 64 bits to colors below 6
        // with distinct neighbors, each round reading the one before.
        for _ in 0..4 {
            colors = colors
                .windows(2)
                .map(|w| {
                    let k = (w[0] ^ w[1]).trailing_zeros() as usize;
                    2 * k + ((w[1] >> k) & 1)
                })
                .collect();
        }
        let n = window.len();
        let mut out = Vec::new();
        let mut start = 0;
        for i in 1..=n {
            // A cut needs two symbols before it and one after it in the sequence.
            let cut = i == n
                || (left.len() + i >= 2
                    && i + 1 < colors.len()
                    && colors[i] > colors[i - 1]
                    && colors[i] > colors[i + 1]);
            if cut {
                let kids: Vec<S> = window[start..i].iter().map(|(x, _)| *x).collect();
                let x = match kids.as_slice() {
                    [x] => *x,
                    _ => self.intern(Sym::Chunk(l + 1, kids.into())),
                };
                out.push((x, BigUint::one()));
                start = i;
            }
        }
        out
    }

    /// The order of the two sequences of the given roots: lexicographic, the elements
    /// ordered as [`Formula::cmp`] orders them. Each step passes over a symbol the two share,
    /// opens the higher of two others, or compares two elements, inside which it goes on.
    fn cmp_seqs(&self, a: Option<S>, b: Option<S>) -> Ordering {
        fn start(r: Option<S>) -> Vec<Entry> {
            r.map(|s| vec![(s, BigUint::one())]).unwrap_or_default()
        }
        /// Takes one of the symbol on top.
        fn take(f: &mut Vec<Entry>) {
            let top = f.last_mut().expect("a symbol on top");
            top.1 -= 1u8;
            if top.1.is_zero() {
                f.pop();
            }
        }
        // For each pair of elements being compared, the symbols left of each, the next last.
        let mut frames: Vec<(Vec<Entry>, Vec<Entry>)> = vec![(start(a), start(b))];
        while let Some((fa, fb)) = frames.last_mut() {
            let (x, y) = match (fa.last(), fb.last()) {
                (None, None) => {
                    frames.pop();
                    continue;
                }
                (None, Some(_)) => return Ordering::Less,
                (Some(_), None) => return Ordering::Greater,
                (Some((x, _)), Some((y, _))) => (*x, *y),
            };
            if x == y {
                let (na, nb) = (fa.pop().expect("x").1, fb.pop().expect("y").1);
                match na.cmp(&nb) {
                    Ordering::Less => fb.push((y, nb - na)),
                    Ordering::Greater => fa.push((x, na - nb)),
                    Ordering::Equal => {}
                }
                continue;
            }
            let (hx, hy) = (self.level(x), self.level(y));
            if hx > 0 && hx >= hy {
                self.open(fa);
            }
            if hy > 0 && hy >= hx {
                self.open(fb);
            }
            if hx > 0 || hy > 0 {
                continue;
            }
            take(fa);
            take(fb);
            let inner = match (&self.syms[x], &self.syms[y]) {
                (Sym::Con(p), Sym::Con(q)) => match p.cmp(q) {
                    Ordering::Equal => continue,
                    o => return o,
                },
                (Sym::Not(p), Sym::Not(q)) => (start(Some(*p)), start(Some(*q))),
                (Sym::Seq(j, p), Sym::Seq(k, q)) if j == k => (start(*p), start(*q)),
                _ => return self.rank(x).cmp(&self.rank(y)),
            };
            frames.push(inner);
        }
        Ordering::Equal
    }

    /// The rank of an element's variant ([`Formula::rank`]).
    fn rank(&self, s: S) -> u8 {
        match &self.syms[s] {
            Sym::Con(_) => 0,
            Sym::Not(_) => 1,
            Sym::Seq(k, _) => *k,
            Sym::Run(..) | Sym::Chunk(..) => unreachable!("an element"),
        }
    }

    /// Replaces the symbol on top of `f` by the symbols it is made of.
    fn open(&self, f: &mut Vec<Entry>) {
        let (s, k) = f.pop().expect("a symbol on top");
        match &self.syms[s] {
            Sym::Run(_, x, n) => f.push((*x, n * k)),
            Sym::Chunk(_, xs) => {
                if !k.is_one() {
                    f.push((s, k - 1u8));
                }
                f.extend(xs.iter().rev().map(|&x| (x, BigUint::one())));
            }
            Sym::Con(_) | Sym::Not(_) | Sym::Seq(..) => unreachable!("an element is not opened"),
        }
    }
}

/// One side of a join, read outward from it: from its end for the side on the left, from its
/// start for the side on the right.
struct Finger {
    left: bool,
    /// For each level from 0 to the root's: the entries read, outward, each unit of the
    /// level above them expanded in turn.
    rows: Vec<Row>,
    /// How many entries of the current level, outward, are already reparsed in the join.
    dropped: usize,
    /// Whether every unit of the side is reparsed in the join.
    done: bool,
}

#[derive(Default)]
struct Row {
    entries: Vec<Entry>,
    /// The number of entries of each unit of the level above, outward.
    groups: Vec<usize>,
    /// The entry of the row above to expand next, and how many of its repeats are expanded.
    next: (usize, usize),
}

impl Finger {
    fn new(c: &Canon, root: S, left: bool) -> Finger {
        let mut rows: Vec<Row> = (0..=c.level(root)).map(|_| Row::default()).collect();
        let top = rows.last_mut().expect("the root's row");
        top.entries.push((root, BigUint::one()));
        top.groups.push(1);
        Finger {
            left,
            rows,
            dropped: 0,
            done: false,
        }
    }

    /// Expands one more unit into row `l`, or returns false when the side has no more.
    fn grow(&mut self, c: &Canon, l: usize) -> bool {
        let s = self.rows.len() - 1;
        // The lowest row from `l` up whose row above has an entry not yet expanded into it.
        let mut k = l;
        while k < s && self.rows[k].next.0 == self.rows[k + 1].entries.len() {
            k += 1;
        }
        if k >= s {
            return false;
        }
        for j in (l..=k).rev() {
            let (at, used) = self.rows[j].next;
            let (p, n) = &self.rows[j + 1].entries[at];
            let p = *p;
            self.rows[j].next = if *n == BigUint::from(used + 1) {
                (at + 1, 0)
            } else {
                (at, used + 1)
            };
            let row = &mut self.rows[j];
            let before = row.entries.len();
            match &c.syms[p] {
                Sym::Run(lv, x, n) if *lv == j + 1 => row.entries.push((*x, n.clone())),
                Sym::Chunk(lv, xs) if *lv == j + 1 => {
                    let one = |&x: &S| (x, BigUint::one());
                    if self.left {
                        row.entries.extend(xs.iter().rev().map(one));
                    } else {
                        row.entries.extend(xs.iter().map(one));
                    }
                }
                _ => row.entries.push((p, BigUint::one())),
            }
            row.groups.push(row.entries.len() - before);
        }
        true
    }

    /// At level `l`, drops the fewest units of the level above, outward, that hold the
    /// entries already dropped and `margin` more, and returns the entries they hold that are
    /// not yet dropped, outward, and the `want` entries after them, fewer at the side's end.
    fn cut(&mut self, c: &Canon, l: usize, margin: usize, want: usize) -> (Vec<Entry>, Vec<S>) {
        let need = BigUint::from(self.dropped + margin);
        let mut held = BigUint::ZERO;
        let (mut k, mut e) = (0, 0);
        while held < need {
            if k == self.rows[l].groups.len() && !self.grow(c, l) {
                self.done = true;
                break;
            }
            let n = self.rows[l].groups[k];
            for (_, m) in &self.rows[l].entries[e..e + n] {
                held += m;
            }
            e += n;
            k += 1;
        }
        if !self.done && k == self.rows[l].groups.len() && !self.grow(c, l) {
            self.done = true;
        }
        let mut skip = BigUint::from(self.dropped);
        let mut rem = Vec::new();
        for (x, m) in &self.rows[l].entries[..e] {
            if skip >= *m {
                skip -= m;
            } else {
                rem.push((*x, m - &skip));
                skip = BigUint::ZERO;
            }
        }
        let mut ctx = Vec::new();
        let mut i = e;
        while !self.done && ctx.len() < want {
            if i == self.rows[l].entries.len() && !self.grow(c, l) {
                break;
            }
            let (x, m) = &self.rows[l].entries[i];
            let mut m = m.clone();
            while !m.is_zero() && ctx.len() < want {
                ctx.push(*x);
                m -= 1u8;
            }
            i += 1;
        }
        self.dropped = k;
        (rem, ctx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::presburger::{Lin, Rel};

    /// A small generator of numbers, fixed so that the tests are the same each run.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: usize) -> usize {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % n as u64) as usize
        }
    }

    fn leaf(c: &mut Canon, k: usize) -> S {
        c.intern(Sym::Con(Con {
            lin: Lin::constant(k as i64),
            rel: Rel::Ge,
        }))
    }

    fn scratch(c: &mut Canon, xs: &[S]) -> Option<S> {
        c.join(
            None,
            xs.iter().map(|&x| (x, BigUint::one())).collect(),
            None,
        )
    }

    /// The root of `xs` joined at random places, at random depths.
    fn joined(c: &mut Canon, xs: &[S], rng: &mut Rng) -> Option<S> {
        if xs.len() < 2 || rng.below(4) == 0 {
            return scratch(c, xs);
        }
        let at = rng.below(xs.len() + 1);
        let a = joined(c, &xs[..at], rng);
        let b = joined(c, &xs[at..], rng);
        c.concat(a, b)
    }

    fn written(c: &Canon, r: Option<S>) -> Vec<S> {
        let mut out = Vec::new();
        let mut f: Vec<Entry> = r.map(|s| vec![(s, BigUint::one())]).unwrap_or_default();
        while let Some((s, n)) = f.last().cloned() {
            if c.level(s) == 0 {
                f.pop();
                let n: usize = n.try_into().expect("a small count");
                out.extend(std::iter::repeat_n(s, n));
            } else {
                c.open(&mut f);
            }
        }
        out
    }

    /// Random sequences over few symbols, so with long runs and repeats, and periodic ones.
    fn sequence(c: &mut Canon, rng: &mut Rng) -> Vec<S> {
        let symbols = 1 + rng.below(4);
        let len = rng.below(300);
        match rng.below(3) {
            0 => (0..len).map(|_| leaf(c, rng.below(symbols))).collect(),
            1 => {
                let period: Vec<usize> =
                    (0..1 + rng.below(6)).map(|_| rng.below(symbols)).collect();
                (0..len)
                    .map(|i| leaf(c, period[i % period.len()]))
                    .collect()
            }
            _ => {
                let mut xs = Vec::new();
                while xs.len() < len {
                    let x = leaf(c, rng.below(symbols));
                    xs.extend(std::iter::repeat_n(x, 1 + rng.below(9)));
                }
                xs
            }
        }
    }

    #[test]
    fn a_sequence_joined_anywhere_has_the_root_of_its_parse_from_scratch() {
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        let mut c = Canon::new();
        for round in 0..3000 {
            let xs = sequence(&mut c, &mut rng);
            let whole = scratch(&mut c, &xs);
            assert_eq!(written(&c, whole), xs, "round {round}");
            for _ in 0..3 {
                assert_eq!(
                    joined(&mut c, &xs, &mut rng),
                    whole,
                    "round {round}: {xs:?}"
                );
            }
        }
    }

    #[test]
    fn sequences_compare_as_written_out() {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        let mut c = Canon::new();
        for round in 0..3000 {
            let xs = sequence(&mut c, &mut rng);
            // Another sequence equal to it up to a random place, then differing or ending.
            let at = rng.below(xs.len() + 1);
            let mut ys = xs[..at].to_vec();
            match rng.below(3) {
                0 => {}
                1 => ys.extend(sequence(&mut c, &mut rng)),
                _ => ys.extend_from_slice(&xs[at..]),
            }
            let con = |c: &Canon, s: &S| match &c.syms[*s] {
                Sym::Con(k) => k.clone(),
                _ => unreachable!("a constraint"),
            };
            let order = xs
                .iter()
                .map(|s| con(&c, s))
                .cmp(ys.iter().map(|s| con(&c, s)));
            let (x, y) = (joined(&mut c, &xs, &mut rng), joined(&mut c, &ys, &mut rng));
            assert_eq!(c.cmp_seqs(x, y), order, "round {round}");
            assert_eq!(c.cmp_seqs(y, x), order.reverse(), "round {round}");
        }
    }
}

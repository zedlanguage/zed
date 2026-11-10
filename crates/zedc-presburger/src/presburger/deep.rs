//! The operations on [`Formula`] that follow its nesting: the fold that the maps of a formula
//! are written with, and drop, compare, hash and show. Each keeps its own stack on the heap,
//! so a formula's depth is limited by the machine's memory alone.
//!
//! A part of a formula may be held by more than one parent ([`Formula`]). Each operation but
//! show reads such a part once per call: it keeps the part's result in a map keyed by the part
//! ([`Id`]), so its cost is the number of distinct parts and not the size of the tree written
//! out. A part held by one parent alone is reached once and is not kept in the map. Hash,
//! which `==` also reads first, reads a compound part once at all: its hash is kept with it.

// Complexity tradeoff: naive version, the derived `Drop`, `Clone`, `PartialEq`, `Ord`, `Hash`,
// `Debug` and `Display` and the recursive maps, O(n) time but O(depth) thread stack, so a
// formula about 4,000 deep overflowed a 2 MiB thread. Used: each walk keeps its work on the
// heap (a post-order fold with a context passed down, or a work list), O(distinct parts) time
// with a map for parts held by two parents or more. Tradeoffs: heap memory of O(depth) for the
// stack and O(shared parts) for the map, a larger constant than plain recursion; the order,
// equality and printed text are those of the derived forms. Tests `l01_38_presburger::deep`
// (100,000 guards on a 2 MiB thread; 8.0 times from 12,500 to 100,000);
// COMPLEXITY.md row S27.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::mem;
use std::slice;

use super::formula::{Con, Formula, Id, Lin, Model, Names, Rel, Shared, Sig, as_is};

mod canon;

use canon::{Canon, Side};

impl Con {
    /// The constraint, moved out of `c`, with `c` left the constraint `0 >= 0` of no atoms.
    pub fn take(c: &mut Con) -> Con {
        Con {
            lin: mem::take(&mut c.lin),
            rel: c.rel,
        }
    }
}

/// A part kept for [`Formula::negate`]'s and drop's moves: a constraint, which needs no
/// allocation.
fn hole() -> Formula {
    Formula::Con(Con {
        lin: Lin::default(),
        rel: Rel::Ge,
    })
}

/// The parts of a node read as if each conjunction directly in a conjunction, and each
/// disjunction directly in a disjunction, were flattened into it, on a stack as deep as the
/// nesting of the node's own kind.
// Complexity tradeoff: a part of the node's own kind reached by several paths is read at each,
// so that show agrees with the formula written out (`l01_38_presburger::shared` asserts it).
// Show writes the formula out, so a chain of names each conjoining the two before it prints in
// size exponential in its length, as written out it would: messages have no syntax that names
// a part of a formula, so the printed text cannot refer to a part already printed. Compare
// does not read through `Flat` but pairs the two sides' parts ([`Formula::cmp`]), and the
// hash is a fold linear in the distinct parts. No answer is given up. A complete solution
// prints a named part by its name, once messages have a syntax for that.
struct Flat<'a> {
    /// The node's variant ([`Formula::rank`]).
    kind: u8,
    /// The parts left at each level of the node's own kind, the innermost last.
    left: Vec<slice::Iter<'a, Formula>>,
}

impl<'a> Flat<'a> {
    fn of(g: &'a Formula) -> Flat<'a> {
        Flat {
            kind: g.rank(),
            left: vec![g.kids().iter()],
        }
    }
}

impl<'a> Iterator for Flat<'a> {
    type Item = &'a Formula;

    fn next(&mut self) -> Option<&'a Formula> {
        loop {
            match self.left.last_mut()?.next() {
                Some(h) if h.flattens_into(self.kind) => self.left.push(h.kids().iter()),
                Some(h) => return Some(h),
                None => {
                    self.left.pop();
                }
            }
        }
    }
}

impl Formula {
    /// The fold of the formula from its constraints up. Each part is reached with a context:
    /// `ctx` at the root, and `down(node, c)` at each part directly under a node reached with
    /// `c`. `up(node, c, results)` gives a node's result from its parts' results, in order.
    /// A shared part reached again with a context it was folded with takes its result from
    /// then, so `up` is called once for each distinct part and context.
    pub(super) fn fold<C: Copy + Eq + Hash, R: Clone>(
        &self,
        ctx: C,
        down: impl Fn(&Formula, C) -> C,
        mut up: impl FnMut(&Formula, C, Vec<R>) -> R,
    ) -> R {
        /// A node whose parts are being folded, the parts left, where its parts' results
        /// start in the list of results, and its key when it is shared.
        struct Frame<'a, C> {
            node: &'a Formula,
            ctx: C,
            left: slice::Iter<'a, Formula>,
            start: usize,
            id: Option<Id>,
        }
        // A constraint, the commonest root, needs no list.
        if let Formula::Con(_) = self {
            return up(self, ctx, Vec::new());
        }
        let mut seen: HashMap<(Id, C), R> = HashMap::new();
        let mut results: Vec<R> = Vec::new();
        let mut stack = vec![Frame {
            node: self,
            ctx,
            left: self.kids().iter(),
            start: 0,
            id: None,
        }];
        while let Some(top) = stack.last_mut() {
            match top.left.next() {
                Some(g) => {
                    let ctx = down(top.node, top.ctx);
                    let id = match Id::of(g) {
                        Some(id) => match seen.get(&(id, ctx)) {
                            Some(r) => {
                                results.push(r.clone());
                                continue;
                            }
                            None => Some(Id::any(g)),
                        },
                        None => None,
                    };
                    stack.push(Frame {
                        node: g,
                        ctx,
                        left: g.kids().iter(),
                        start: results.len(),
                        id,
                    });
                }
                None => {
                    let Frame {
                        node,
                        ctx,
                        start,
                        id,
                        ..
                    } = stack.pop().expect("the top frame");
                    let parts = results.split_off(start);
                    let r = up(node, ctx, parts);
                    if let Some(id) = id {
                        seen.insert((id, ctx), r.clone());
                    }
                    results.push(r);
                }
            }
        }
        results.pop().expect("the root's result")
    }

    /// [`Formula::holds`]: a conjunction is read up to its first part that fails and a
    /// disjunction up to its first part that holds, so a part decided early is not walked
    /// through. A shared part is read once.
    pub(super) fn holds_as(&self, vs: &Model) -> bool {
        if let Formula::Con(c) = self {
            return c.holds(vs);
        }
        let mut seen: HashMap<Id, bool> = HashMap::new();
        // The nodes being read, each with the parts left and its key when shared, and the
        // value of the part just read.
        let mut stack = vec![(self, self.kids().iter(), None)];
        let mut value: Option<bool> = None;
        while let Some((node, left, _)) = stack.last_mut() {
            if let Some(v) = value.take() {
                let decided = match node {
                    Formula::And(_) => !v,
                    Formula::Or(_) => v,
                    Formula::Not(_) => true,
                    Formula::Con(_) => unreachable!("a constraint has no parts"),
                };
                if decided {
                    let v = if matches!(node, Formula::Not(_)) {
                        !v
                    } else {
                        v
                    };
                    if let Some((_, _, Some(id))) = stack.pop() {
                        seen.insert(id, v);
                    }
                    value = Some(v);
                    continue;
                }
            }
            match left.next() {
                Some(Formula::Con(c)) => value = Some(c.holds(vs)),
                Some(g) => match Id::of(g) {
                    Some(id) => match seen.get(&id) {
                        Some(&v) => value = Some(v),
                        None => stack.push((g, g.kids().iter(), Some(id))),
                    },
                    None => stack.push((g, g.kids().iter(), None)),
                },
                // Every part read and none decided: a conjunction holds, a disjunction fails.
                None => {
                    let v = matches!(node, Formula::And(_));
                    if let Some((_, _, Some(id))) = stack.pop() {
                        seen.insert(id, v);
                    }
                    value = Some(v);
                }
            }
        }
        value.expect("the root's value")
    }

    /// Calls `f` on each constraint, in order; the constraints of a shared part are met at
    /// its first place alone.
    pub(super) fn walk<'a>(&'a self, f: &mut dyn FnMut(&'a Con)) {
        let mut seen: HashSet<Id> = HashSet::new();
        let mut stack = vec![slice::from_ref(self).iter()];
        while let Some(top) = stack.last_mut() {
            match top.next() {
                Some(Formula::Con(c)) => f(c),
                Some(g) => {
                    if Id::of(g).is_none_or(|id| seen.insert(id)) {
                        stack.push(g.kids().iter());
                    }
                }
                None => {
                    stack.pop();
                }
            }
        }
    }

    /// Whether the formula has a disjunction or a negation, which pushed in may make one.
    /// A shared part is read at its first place alone.
    pub fn chooses(&self) -> bool {
        let mut seen: HashSet<Id> = HashSet::new();
        let mut stack = vec![self];
        while let Some(g) = stack.pop() {
            match g {
                Formula::Or(_) | Formula::Not(_) => return true,
                Formula::Con(_) | Formula::And(_) => {
                    if Id::of(g).is_none_or(|id| seen.insert(id)) {
                        stack.extend(g.kids())
                    }
                }
            }
        }
        false
    }

    /// The parts of a conjunction or a disjunction, moved out when no other holder shares
    /// them and copied, one level deep, when one does, or `None` for another formula.
    pub fn into_parts(mut self) -> Option<Vec<Formula>> {
        match &mut self {
            Formula::And(gs) | Formula::Or(gs) => Some(match Shared::get_mut(gs) {
                Some(v) => mem::take(v),
                None => gs.to_vec(),
            }),
            Formula::Con(_) | Formula::Not(_) => None,
        }
    }

    /// The formula under a negation, moved out when no other holder shares it, or `None`
    /// for another formula.
    pub fn into_negated(mut self) -> Option<Formula> {
        match &mut self {
            Formula::Not(g) => Some(match Shared::get_mut(g) {
                Some(h) => mem::replace(h, hole()),
                None => (**g).clone(),
            }),
            Formula::Con(_) | Formula::And(_) | Formula::Or(_) => None,
        }
    }

    /// The parts directly under `self`, moved to `out` when no other holder shares them.
    fn take_kids(&mut self, out: &mut Vec<Formula>) {
        match self {
            Formula::Con(_) => {}
            Formula::Not(g) => {
                if let Some(h) = Shared::get_mut(g) {
                    out.push(mem::replace(h, hole()));
                }
            }
            Formula::And(gs) | Formula::Or(gs) => {
                if let Some(v) = Shared::get_mut(gs) {
                    out.append(v);
                }
            }
        }
    }

    /// The order of the two nodes alone: their variants, then their constraints.
    fn cmp_node(&self, other: &Formula) -> Ordering {
        match (self, other) {
            (Formula::Con(a), Formula::Con(b)) => a.cmp(b),
            _ => self.rank().cmp(&other.rank()),
        }
    }

    /// Whether the two compound nodes are one part.
    fn same(&self, other: &Formula) -> bool {
        match (self, other) {
            (Formula::Not(a), Formula::Not(b)) => Shared::same(a, b),
            (Formula::And(a), Formula::And(b)) | (Formula::Or(a), Formula::Or(b)) => {
                Shared::same(a, b)
            }
            _ => false,
        }
    }
}

impl Drop for Formula {
    fn drop(&mut self) {
        // Each part no other holder shares is moved to the list before its parent goes, and
        // its parts before it goes in turn, so a part dropped here has no parts of its own to
        // drop and this recursion is one level deep. A shared part is left to its other
        // holders, the last of which drops it the same way.
        let mut stack = Vec::new();
        self.take_kids(&mut stack);
        while let Some(mut g) = stack.pop() {
            g.take_kids(&mut stack);
        }
    }
}

impl Clone for Formula {
    /// A copy that shares the parts of `self`, at the cost of the root.
    fn clone(&self) -> Formula {
        match self {
            Formula::Con(c) => Formula::Con(c.clone()),
            Formula::Not(g) => Formula::Not(g.clone()),
            Formula::And(gs) => Formula::And(gs.clone()),
            Formula::Or(gs) => Formula::Or(gs.clone()),
        }
    }
}

/// A pair of nodes of one variant whose parts are being compared, read as flattened, with the
/// key of the pair when one of the two is shared.
struct Level<'a> {
    kind: u8,
    a: Side<'a>,
    b: Side<'a>,
    key: Option<(Id, Id)>,
}

impl<'a> Level<'a> {
    fn of(x: &'a Formula, y: &'a Formula, key: Option<(Id, Id)>) -> Level<'a> {
        Level {
            kind: x.rank(),
            a: Side::of(x),
            b: Side::of(y),
            key,
        }
    }

    /// Leaves each inner level with no parts left. A pair of parts entered together and left
    /// together had equal parts read as flattened, so it is kept as equal.
    fn settle(&mut self, equal: &mut HashSet<(Id, Id)>, entries: &mut [Option<(Id, Id)>]) {
        while self.a.left.len() + self.b.left.len() > 0 {
            match (self.a.done(), self.b.done()) {
                (Some(None), _) => {
                    self.a.left.pop();
                }
                (_, Some(None)) => {
                    self.b.left.pop();
                }
                (Some(Some(s)), Some(Some(t))) if s == t => {
                    self.a.left.pop();
                    self.b.left.pop();
                    equal.extend(entries[s].take());
                }
                // Two levels entered with other partners, the later entry first: its partner,
                // entered after the other's, is no longer open, while the other's partner may
                // be the next level out and run out here too.
                (Some(Some(s)), Some(Some(t))) => {
                    if s > t {
                        self.a.left.pop();
                    } else {
                        self.b.left.pop();
                    }
                }
                // A part entered with a partner whose parts are not yet all read: the pair is
                // not kept, and its partner's level is left alone when its parts run out.
                (Some(Some(_)), _) => {
                    self.a.left.pop();
                }
                (_, Some(Some(_))) => {
                    self.b.left.pop();
                }
                (None, None) => return,
            }
        }
    }
}

impl Ord for Formula {
    /// The order the derived one would give on the formula with each conjunction directly in a
    /// conjunction, and each disjunction directly in a disjunction, flattened into it
    /// (`Flat`): the variants in the order they are declared, then the constraints, or the
    /// parts in order with a prefix first. A conjunction that [`Formula::and`] keeps whole,
    /// since it is shared, is then equal to the one written out. A part compared with itself is
    /// equal at once (COMPLEXITY.md S31), and a pair of parts one of which is shared is
    /// compared once per call: a pair found equal is kept. Two kept parts of the level's own
    /// kind met at one point of the two flattened sequences are entered together, and kept as
    /// equal when their parts run out together, so a pair met again is passed over. A shared
    /// part of the level's own kind entered a second time in one call, alone or with another
    /// partner, is not read through again: the parts the two sides have left at the level are
    /// compared as sequences parsed the same way whatever their grouping (`Canon`).
    // Complexity tradeoff: until a shared part is entered twice, the walk reads each part once
    // per parent read (a visited set of the shared parts entered), so its cost is linear in
    // the distinct parts and edges and it stops at the first difference; formulas whose kept
    // parts line up never leave it (`l01_38_presburger::shared`, the scaling tests of chains).
    // Two that group one sequence at other places on each side, so that a shared part is
    // entered again, cost O(e log N) for e distinct edges and N parts written out ([`Canon`]),
    // which is O(n^2) when N is exponential in the n distinct parts (`shared::shifted_chains`,
    // COMPLEXITY.md S31b); read through, they cost N. The parse is built once per call, so a
    // pair compared again is parsed again. No answer is given up; the cost is. A complete
    // solution keeps each part's parse with it.
    fn cmp(&self, other: &Formula) -> Ordering {
        /// Whether `g` is shared and was entered before in this call, which it now is.
        fn again(read: &mut HashSet<Id>, g: &Formula) -> bool {
            g.is_shared() && !read.insert(Id::any(g))
        }
        match self.cmp_node(other) {
            Ordering::Equal => {}
            o => return o,
        }
        if self.same(other) {
            return Ordering::Equal;
        }
        let mut equal: HashSet<(Id, Id)> = HashSet::new();
        // The key of each pair entered together, until it is kept as equal.
        let mut entries: Vec<Option<(Id, Id)>> = Vec::new();
        // The shared parts of a level's own kind entered so far.
        let mut read: HashSet<Id> = HashSet::new();
        let mut canon: Option<Canon> = None;
        let mut level = Level::of(self, other, None);
        let mut above: Vec<Level> = Vec::new();
        loop {
            level.settle(&mut equal, &mut entries);
            let (x, y) = (level.a.peek(), level.b.peek());
            let kind = level.kind;
            let twice = match (x, y) {
                (Some(x), Some(y)) if x.flattens_into(kind) && y.flattens_into(kind) => {
                    if x.same(y) {
                        level.a.advance();
                        level.b.advance();
                        continue;
                    }
                    // Whether each is shared.
                    let (sx, sy) = (x.is_shared(), y.is_shared());
                    let key = (Id::any(x), Id::any(y));
                    if equal.contains(&key) {
                        level.a.advance();
                        level.b.advance();
                        continue;
                    }
                    let twice = (sx && !read.insert(Id::any(x))) | (sy && !read.insert(Id::any(y)));
                    if !twice {
                        level.a.advance();
                        level.b.advance();
                        entries.push(Some(key));
                        level.a.enter(x, Some(entries.len() - 1));
                        level.b.enter(y, Some(entries.len() - 1));
                        continue;
                    }
                    true
                }
                (Some(x), _) if x.flattens_into(kind) => {
                    if !again(&mut read, x) {
                        level.a.advance();
                        level.a.enter(x, None);
                        continue;
                    }
                    true
                }
                (_, Some(y)) if y.flattens_into(kind) => {
                    if !again(&mut read, y) {
                        level.b.advance();
                        level.b.enter(y, None);
                        continue;
                    }
                    true
                }
                _ => false,
            };
            if twice {
                match canon
                    .get_or_insert_with(Canon::new)
                    .cmp_rest(kind, &level.a, &level.b)
                {
                    Ordering::Equal => {}
                    o => return o,
                }
                match above.pop() {
                    Some(l) => equal.extend(mem::replace(&mut level, l).key),
                    None => return Ordering::Equal,
                }
                continue;
            }
            match (x, y) {
                (Some(x), Some(y)) => {
                    level.a.advance();
                    level.b.advance();
                    match x.cmp_node(y) {
                        Ordering::Equal if x.kids().is_empty() && y.kids().is_empty() => {}
                        Ordering::Equal if x.same(y) => {}
                        Ordering::Equal => {
                            let key =
                                (x.is_shared() || y.is_shared()).then(|| (Id::any(x), Id::any(y)));
                            if key.as_ref().is_some_and(|k| equal.contains(k)) {
                                continue;
                            }
                            above.push(mem::replace(&mut level, Level::of(x, y, key)));
                        }
                        o => return o,
                    }
                }
                (Some(_), None) => return Ordering::Greater,
                (None, Some(_)) => return Ordering::Less,
                (None, None) => match above.pop() {
                    Some(l) => equal.extend(mem::replace(&mut level, l).key),
                    None => return Ordering::Equal,
                },
            }
        }
    }
}

impl PartialOrd for Formula {
    fn partial_cmp(&self, other: &Formula) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Formula {
    /// `cmp` gives `Equal`, after a check of the two hashes (`Formula::sig`): formulas equal
    /// under `Ord` have equal hashes, so two compound formulas whose hashes differ are unequal
    /// without being compared. Equal hashes prove nothing, and the pair is then compared.
    // Complexity tradeoff: naive version, `cmp` on every `==`, which reads the two formulas
    // until they differ, and on formulas whose shared parts are grouped at other places on
    // each side parses both, O(n log N) for n distinct parts and N parts written out, O(d^2)
    // on `shifted_chains` of depth d (COMPLEXITY.md S31b). Used: the hashes compared first,
    // each found once per node, in time linear in its distinct parts and edges, and kept with
    // the node (`Sig`), so an unequal pair costs O(1) once both are hashed. Tradeoffs: 40
    // bytes per compound node for the kept hash; the first `==` on a formula pays for hashing
    // the parts not yet hashed, which a pair that differs early, compared by `cmp` alone, would
    // not read; equal pairs, and pairs whose hashes collide, still cost what `cmp` costs, and
    // `cmp` itself, which needs an order and not only inequality, is not helped. No answer
    // changes, since a hash never decides equality. Tests `l01_38_presburger::shared`
    // (`unequal_formulas_grouped_at_other_places_compare_in_time_near_linear_in_the_depth`,
    // `equal_formulas_hash_alike_however_their_runs_are_grouped`) and
    // `deep::tests::formulas_whose_hashes_collide_are_compared`.
    fn eq(&self, other: &Formula) -> bool {
        if !matches!(self, Formula::Con(_))
            && !matches!(other, Formula::Con(_))
            && !self.same(other)
            && self.sig() != other.sig()
        {
            return false;
        }
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Formula {}

/// An odd multiplier, 2^64 divided by (1 + √5) / 2.
const BASE: u64 = 0x9e37_79b9_7f4a_7c15;

impl Formula {
    /// The hash kept for this compound node when it is of its own variant, or the one this
    /// call found when another variant's hash is kept in its parts (`spill`).
    fn known(&self, spill: &HashMap<Id, Sig>) -> Option<Sig> {
        let kept = match self {
            Formula::Con(_) => return None,
            Formula::Not(g) => Shared::sig(g, self.rank()),
            Formula::And(gs) | Formula::Or(gs) => Shared::sig(gs, self.rank()),
        };
        kept.or_else(|| spill.get(&Id::any(self)).copied())
    }

    /// Keeps `sig` with this compound node's parts, or in `spill` when they keep the hash of a
    /// node of another variant that holds them too.
    fn keep(&self, sig: Sig, spill: &mut HashMap<Id, Sig>) {
        let kept = match self {
            Formula::Con(_) => unreachable!("a constraint keeps no hash"),
            Formula::Not(g) => Shared::keep_sig(g, sig),
            Formula::And(gs) | Formula::Or(gs) => Shared::keep_sig(gs, sig),
        };
        if !kept {
            spill.insert(Id::any(self), sig);
        }
    }

    /// The node's hash from its parts' hashes, given in order: the hash of its variant and its
    /// constraint, or of its parts' numbers read as flattened (`Flat`). A part of the node's own
    /// variant adds its polynomial in its place, so that it is hashed as flattened at the cost
    /// of its own parts.
    fn sig_of(&self, parts: impl Iterator<Item = Sig>) -> Sig {
        // A fixed hasher, so that the number of a formula does not change between runs.
        let mut h = DefaultHasher::new();
        let rank = self.rank();
        h.write_u8(rank);
        let (mut seq, mut pow) = (0u64, 1u64);
        match self {
            Formula::Con(c) => c.hash(&mut h),
            Formula::Not(_) => {
                for p in parts {
                    h.write_u64(p.n);
                }
            }
            Formula::And(_) | Formula::Or(_) => {
                for p in parts {
                    if p.rank == rank && p.rank >= 2 {
                        seq = seq.wrapping_mul(p.pow).wrapping_add(p.seq);
                        pow = pow.wrapping_mul(p.pow);
                    } else {
                        seq = seq.wrapping_mul(BASE).wrapping_add(p.n);
                        pow = pow.wrapping_mul(BASE);
                    }
                }
                h.write_u64(seq);
                h.write_u64(pow);
            }
        }
        Sig {
            rank,
            n: h.finish(),
            seq,
            pow,
        }
    }

    /// The hash of the formula ([`Sig`]). A compound node's hash is found once and kept with
    /// its parts, so a later call reads it in O(1); the first call finds the hashes of the
    /// parts not yet hashed bottom up on an explicit stack, each once, in time linear in their
    /// number and their edges. A constraint's hash is found at each call, in time linear in
    /// its size.
    pub(super) fn sig(&self) -> Sig {
        if let Formula::Con(_) = self {
            return self.sig_of(std::iter::empty());
        }
        let spill: HashMap<Id, Sig> = HashMap::new();
        if let Some(s) = self.known(&spill) {
            return s;
        }
        self.sig_walk(spill)
    }

    /// [`Formula::sig`] of a compound node whose hash is not kept.
    fn sig_walk(&self, mut spill: HashMap<Id, Sig>) -> Sig {
        let part = |k: &Formula, spill: &HashMap<Id, Sig>| match k {
            Formula::Con(_) => k.sig_of(std::iter::empty()),
            _ => k
                .known(spill)
                .expect("each compound part is hashed before its parent"),
        };
        // The nodes being hashed, each with the index of the first part not known to be hashed.
        let mut stack: Vec<(&Formula, usize)> = vec![(self, 0)];
        while let Some((g, from)) = stack.last_mut() {
            let kids = g.kids();
            let next = (kids[*from..].iter())
                .position(|k| !matches!(k, Formula::Con(_)) && k.known(&spill).is_none());
            if let Some(i) = next {
                // That part is hashed before this node is read again.
                *from += i + 1;
                let k = &kids[*from - 1];
                stack.push((k, 0));
                continue;
            }
            let g: &Formula = g;
            let sig = g.sig_of(kids.iter().map(|k| part(k, &spill)));
            g.keep(sig, &mut spill);
            stack.pop();
            if stack.is_empty() {
                return sig;
            }
        }
        unreachable!("the root returns its hash")
    }
}

impl Hash for Formula {
    /// Writes one number made from the tree bottom up (`Formula::sig`): each node's number is
    /// the hash of its variant and its constraint, or of its parts' numbers read as flattened
    /// (`Flat`), so that formulas equal under [`Ord`] write equal numbers. A compound node's
    /// number is found once and kept with it.
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.sig().n);
    }
}

/// A piece of the text of a formula: a formula yet to be shown, or text.
enum Piece<'a> {
    Formula(&'a Formula),
    Text(&'static str),
}

/// Shows the formula with `show` for each node, as the derived form does when `debug`, each
/// symbol of a constraint written through `name`; each node pushes the pieces it is made of,
/// in reverse, onto one list. A shared part is written out at each place it is held, so the
/// text is as long as the tree written out.
fn show(root: &Formula, f: &mut fmt::Formatter<'_>, debug: bool, name: Names) -> fmt::Result {
    let mut stack = vec![Piece::Formula(root)];
    while let Some(piece) = stack.pop() {
        let g = match piece {
            Piece::Text(t) => {
                f.write_str(t)?;
                continue;
            }
            Piece::Formula(g) => g,
        };
        if debug {
            match g {
                Formula::Con(c) => write!(f, "Con({c:?})")?,
                Formula::Not(h) => {
                    f.write_str("Not(")?;
                    stack.extend([Piece::Text(")"), Piece::Formula(h)]);
                }
                Formula::And(_) | Formula::Or(_) => {
                    f.write_str(if matches!(g, Formula::And(_)) {
                        "And(["
                    } else {
                        "Or(["
                    })?;
                    stack.push(Piece::Text("])"));
                    let kids: Vec<&Formula> = Flat::of(g).collect();
                    for (i, h) in kids.into_iter().enumerate().rev() {
                        stack.push(Piece::Formula(h));
                        if i > 0 {
                            stack.push(Piece::Text(", "));
                        }
                    }
                }
            }
            continue;
        }
        match g {
            Formula::Con(c) => c.show(f, name)?,
            Formula::Not(h) => {
                f.write_str("!")?;
                match &**h {
                    Formula::Con(_) | Formula::And(_) | Formula::Or(_) => {
                        f.write_str("(")?;
                        stack.extend([Piece::Text(")"), Piece::Formula(h)]);
                    }
                    Formula::Not(_) => stack.push(Piece::Formula(h)),
                }
            }
            Formula::And(_) | Formula::Or(_) if Flat::of(g).next().is_none() => {
                write!(f, "{}", matches!(g, Formula::And(_)))?
            }
            Formula::And(_) | Formula::Or(_) => {
                let sep = if matches!(g, Formula::And(_)) {
                    " && "
                } else {
                    " || "
                };
                // A conjunction directly in a conjunction, or a disjunction directly in a
                // disjunction, is written as if flattened into it ([`Flat`]).
                let kids: Vec<&Formula> = Flat::of(g).collect();
                for (i, h) in kids.into_iter().enumerate().rev() {
                    // A conjunction or disjunction of two or more parts is in parentheses.
                    let wrap = matches!(h, Formula::And(_) | Formula::Or(_))
                        && Flat::of(h).nth(1).is_some();
                    if wrap {
                        stack.push(Piece::Text(")"));
                    }
                    stack.push(Piece::Formula(h));
                    if wrap {
                        stack.push(Piece::Text("("));
                    }
                    if i > 0 {
                        stack.push(Piece::Text(sep));
                    }
                }
            }
        }
    }
    Ok(())
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        show(self, f, false, as_is)
    }
}

/// A formula shown with each symbol written through a function ([`Formula::written`]).
struct Written<'a>(&'a Formula, Names);

impl fmt::Display for Written<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        show(self.0, f, false, self.1)
    }
}

impl Formula {
    /// The text of `Display` with each symbol written as `name` of it, for a message that names
    /// a symbol by the name the program wrote and not the one elaboration made of it. The
    /// order of the terms and the parts is the formula's own, which follows the symbols as
    /// they are and not as they are written: so it is the order of the written names, except
    /// where one written name is another followed by digits (`a` and `a1`, `a@2` sorting after
    /// `a1`). Linear in the text.
    pub fn written(&self, name: fn(&str) -> &str) -> String {
        Written(self, name).to_string()
    }
}

impl fmt::Debug for Formula {
    /// The derived form, `And([Con(..), Not(..)])`, on one line also under `{:#?}`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        show(self, f, true, as_is)
    }
}

//! The operations on [`Formula`] that follow its nesting: the fold that the maps of a formula
//! are written with, and drop, compare, hash and show. Each keeps its own stack on the heap,
//! so a formula's depth is limited by the machine's memory alone.
//!
//! A part of a formula may be held by more than one parent ([`Formula`]). Each operation but
//! show reads such a part once per call: it keeps the part's result in a map keyed by the part
//! ([`Id`]), so its cost is the number of distinct parts and not the size of the tree written
//! out. A part held by one parent alone is reached once and is not kept in the map.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::mem;
use std::slice;
use std::sync::Arc;

use super::{Con, Formula, Lin, Model, Rel};

impl Con {
    /// The constraint, moved out of `c`, with `c` left the constraint `0 >= 0` of no atoms.
    pub fn take(c: &mut Con) -> Con {
        Con {
            lin: mem::take(&mut c.lin),
            rel: c.rel,
        }
    }
}

/// A compound part of a formula, held, so that it lives as long as the key, and compared and
/// hashed as the one part it is, not by its content. Two keys are equal when they hold the
/// same part, so a part that two parents hold is found by either.
pub(super) struct Id(Formula);

impl Clone for Id {
    fn clone(&self) -> Id {
        Id(self.0.clone())
    }
}

impl Id {
    /// The key of `f`, a compound part.
    fn any(f: &Formula) -> Id {
        debug_assert!(!matches!(f, Formula::Con(_)), "a compound part");
        Id(f.clone())
    }

    /// The key of `f` when another holder shares it, so that a pass may reach it again, or
    /// `None` for a constraint or a part held by its parent alone.
    pub(super) fn of(f: &Formula) -> Option<Id> {
        f.is_shared().then(|| Id::any(f))
    }

    /// The key of `f` when `f` is one of `twice` ([`Id::reached_twice`]), or `None`.
    pub(super) fn among(f: &Formula, twice: &HashSet<Id>) -> Option<Id> {
        if matches!(f, Formula::Con(_)) {
            return None;
        }
        let id = Id::any(f);
        twice.contains(&id).then_some(id)
    }

    /// The compound parts of `f` that `f` reaches through more than one parent, found in one
    /// walk with a visited set, so in time near the number of distinct parts. A pass that
    /// treats these parts apart reads `f`'s own sharing, not the handles held outside it.
    pub(super) fn reached_twice(f: &Formula) -> HashSet<Id> {
        let mut seen: HashSet<Id> = HashSet::new();
        let mut twice: HashSet<Id> = HashSet::new();
        let mut stack = vec![f];
        while let Some(g) = stack.pop() {
            for h in g.kids() {
                if matches!(h, Formula::Con(_)) {
                    continue;
                }
                let id = Id::any(h);
                if seen.contains(&id) {
                    twice.insert(id);
                } else {
                    seen.insert(id);
                    stack.push(h);
                }
            }
        }
        twice
    }

    /// Where the part is kept, which names it while the key holds it.
    fn at(&self) -> *const () {
        match &self.0 {
            Formula::Con(_) => unreachable!("a key holds a compound part"),
            Formula::Not(g) => Arc::as_ptr(g).cast(),
            Formula::And(gs) | Formula::Or(gs) => Arc::as_ptr(gs).cast(),
        }
    }
}

impl PartialEq for Id {
    fn eq(&self, other: &Id) -> bool {
        self.at() == other.at()
    }
}

impl Eq for Id {}

impl Hash for Id {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.at().hash(state)
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
    /// Whether `self` is a conjunction or disjunction of the variant `kind`, so that it is read
    /// as flattened into a parent of that variant ([`Flat`]).
    fn flattens_into(&self, kind: u8) -> bool {
        matches!(self, Formula::And(_) | Formula::Or(_)) && self.rank() == kind
    }

    /// The formulas directly under `self`, in order.
    fn kids(&self) -> &[Formula] {
        match self {
            Formula::Con(_) => &[],
            Formula::Not(g) => slice::from_ref(&**g),
            Formula::And(gs) | Formula::Or(gs) => gs,
        }
    }

    /// Whether another holder shares the part, so that a pass may reach it twice.
    pub(super) fn is_shared(&self) -> bool {
        match self {
            Formula::Con(_) => false,
            Formula::Not(g) => Arc::strong_count(g) > 1,
            Formula::And(gs) | Formula::Or(gs) => Arc::strong_count(gs) > 1,
        }
    }

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
    pub(super) fn chooses(&self) -> bool {
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
            Formula::And(gs) | Formula::Or(gs) => Some(match Arc::get_mut(gs) {
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
            Formula::Not(g) => Some(match Arc::get_mut(g) {
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
                if let Some(h) = Arc::get_mut(g) {
                    out.push(mem::replace(h, hole()));
                }
            }
            Formula::And(gs) | Formula::Or(gs) => {
                if let Some(v) = Arc::get_mut(gs) {
                    out.append(v);
                }
            }
        }
    }

    /// The rank of the variant, in the order in which [`Ord`] puts them.
    fn rank(&self) -> u8 {
        match self {
            Formula::Con(_) => 0,
            Formula::Not(_) => 1,
            Formula::And(_) => 2,
            Formula::Or(_) => 3,
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
            (Formula::Not(a), Formula::Not(b)) => Arc::ptr_eq(a, b),
            (Formula::And(a), Formula::And(b)) | (Formula::Or(a), Formula::Or(b)) => {
                Arc::ptr_eq(a, b)
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
            Formula::Not(g) => Formula::Not(Arc::clone(g)),
            Formula::And(gs) => Formula::And(Arc::clone(gs)),
            Formula::Or(gs) => Formula::Or(Arc::clone(gs)),
        }
    }
}

/// One side of a pair of nodes being compared: the parts left at each level of the node's own
/// kind, the innermost last, as in [`Flat`], each with the number of the entry it was entered
/// with when the other side entered its partner at the same point ([`Formula::cmp`]).
struct Side<'a> {
    left: Vec<(slice::Iter<'a, Formula>, Option<usize>)>,
}

impl<'a> Side<'a> {
    fn of(g: &'a Formula) -> Side<'a> {
        Side {
            left: vec![(g.kids().iter(), None)],
        }
    }

    /// The next part at the innermost level, not read through.
    fn peek(&self) -> Option<&'a Formula> {
        self.left.last().and_then(|(it, _)| it.as_slice().first())
    }

    fn advance(&mut self) {
        if let Some((it, _)) = self.left.last_mut() {
            it.next();
        }
    }

    fn enter(&mut self, g: &'a Formula, entry: Option<usize>) {
        self.left.push((g.kids().iter(), entry));
    }

    /// The entry of the innermost level if it has no parts left: `Some(None)` for a level
    /// entered alone.
    fn done(&self) -> Option<Option<usize>> {
        self.left
            .last()
            .filter(|(it, _)| it.as_slice().is_empty())
            .map(|&(_, e)| e)
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
    /// ([`Flat`]): the variants in the order they are declared, then the constraints, or the
    /// parts in order with a prefix first. A conjunction that [`Formula::and`] keeps whole,
    /// since it is shared, is then equal to the one written out. A part compared with itself is
    /// equal at once (COMPLEXITY.md S31), and a pair of parts one of which is shared is
    /// compared once per call: a pair found equal is kept. Two kept parts of the level's own
    /// kind met at one point of the two flattened sequences are entered together, and kept as
    /// equal when their parts run out together, so a pair met again is passed over.
    // Complexity tradeoff: a kept part entered on one side alone, against a part of the other
    // side that is not kept, or entered with a partner whose parts run out at another place, is
    // read through at each place it is met, since its parts are then compared against parts
    // grouped otherwise. No answer is given up; the cost is. Two formulas whose kept parts line
    // up (a named chain against an equal one or one extended at either end, built apart, or
    // pairs whose inner parts end apart inside outer ones that end together) are compared at a
    // cost linear in their distinct parts (`l01_38_presburger::shared`, the two scaling tests
    // of chains). Two that group one sequence at other places on each side, at many shared
    // places, cost the size of the sequence written out: exponential in the depth of sharing,
    // 211 ms at d = 20 for 2^21 - 1 constraints (`shared::shifted_chains`, checked for order
    // at d up to 9; COMPLEXITY.md S31b). A complete solution compares the sequences as
    // compressed strings (a hash of each part's sequence and its prefixes, searched for the
    // first difference), which no program seen so far needs.
    fn cmp(&self, other: &Formula) -> Ordering {
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
        let mut level = Level::of(self, other, None);
        let mut above: Vec<Level> = Vec::new();
        loop {
            level.settle(&mut equal, &mut entries);
            let (x, y) = (level.a.peek(), level.b.peek());
            let kind = level.kind;
            match (x, y) {
                (Some(x), Some(y)) if x.flattens_into(kind) && y.flattens_into(kind) => {
                    level.a.advance();
                    level.b.advance();
                    if x.same(y) {
                        continue;
                    }
                    let key = (Id::any(x), Id::any(y));
                    if equal.contains(&key) {
                        continue;
                    }
                    entries.push(Some(key));
                    level.a.enter(x, Some(entries.len() - 1));
                    level.b.enter(y, Some(entries.len() - 1));
                }
                (Some(x), _) if x.flattens_into(kind) => {
                    level.a.advance();
                    level.a.enter(x, None);
                }
                (_, Some(y)) if y.flattens_into(kind) => {
                    level.b.advance();
                    level.b.enter(y, None);
                }
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
    fn eq(&self, other: &Formula) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Formula {}

impl Hash for Formula {
    /// Writes one number made from the tree bottom up: each node's number is the hash of its
    /// variant and its constraint, or of its parts' numbers read as flattened ([`Flat`]), so
    /// that formulas equal under [`Ord`] write equal numbers. A shared part's number is found
    /// once per call.
    fn hash<H: Hasher>(&self, state: &mut H) {
        /// An odd multiplier, 2^64 divided by (1 + √5) / 2.
        const BASE: u64 = 0x9e37_79b9_7f4a_7c15;
        // Each node's number, and for a conjunction or disjunction its parts' numbers as one
        // polynomial in `BASE` and `BASE` to the count of its parts. A part of the node's own
        // kind adds its polynomial in its place, so that it is hashed as flattened at the cost
        // of its own parts.
        let (n, _, _) = self.fold(
            (),
            |_, ()| (),
            |g, (), parts: Vec<(u64, u64, u64)>| {
                // A fixed hasher, so that the number of a formula does not change between runs.
                let mut h = DefaultHasher::new();
                h.write_u8(g.rank());
                let (mut seq, mut pow) = (0u64, 1u64);
                match g {
                    Formula::Con(c) => c.hash(&mut h),
                    Formula::Not(_) => h.write_u64(parts[0].0),
                    Formula::And(_) | Formula::Or(_) => {
                        for (k, (n, s, p)) in g.kids().iter().zip(parts) {
                            if k.flattens_into(g.rank()) {
                                seq = seq.wrapping_mul(p).wrapping_add(s);
                                pow = pow.wrapping_mul(p);
                            } else {
                                seq = seq.wrapping_mul(BASE).wrapping_add(n);
                                pow = pow.wrapping_mul(BASE);
                            }
                        }
                        h.write_u64(seq);
                        h.write_u64(pow);
                    }
                }
                (h.finish(), seq, pow)
            },
        );
        state.write_u64(n);
    }
}

/// A piece of the text of a formula: a formula yet to be shown, or text.
enum Piece<'a> {
    Formula(&'a Formula),
    Text(&'static str),
}

/// Shows the formula with `show` for each node, as the derived form does when `debug`; each
/// node pushes the pieces it is made of, in reverse, onto one list. A shared part is written
/// out at each place it is held, so the text is as long as the tree written out.
fn show(root: &Formula, f: &mut fmt::Formatter<'_>, debug: bool) -> fmt::Result {
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
            Formula::Con(c) => write!(f, "{c}")?,
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
        show(self, f, false)
    }
}

impl fmt::Debug for Formula {
    /// The derived form, `And([Con(..), Not(..)])`, on one line also under `{:#?}`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        show(self, f, true)
    }
}

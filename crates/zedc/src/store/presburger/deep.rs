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

impl Formula {
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

impl Ord for Formula {
    /// The order the derived one would give: the variants in the order they are declared,
    /// then the constraints, or the parts in order with a prefix first. A part compared with
    /// itself is equal at once (COMPLEXITY.md S31), and a pair of parts one of which is
    /// shared is compared once per call: a pair found equal is kept.
    fn cmp(&self, other: &Formula) -> Ordering {
        match self.cmp_node(other) {
            Ordering::Equal => {}
            o => return o,
        }
        if self.same(other) {
            return Ordering::Equal;
        }
        let mut equal: HashSet<(Id, Id)> = HashSet::new();
        // The parts left at the level being read, with the key of the pair whose parts they
        // are when one of the two is shared, and above it those of the levels around it.
        type Level<'a> = (
            slice::Iter<'a, Formula>,
            slice::Iter<'a, Formula>,
            Option<(Id, Id)>,
        );
        let mut level: Level = (self.kids().iter(), other.kids().iter(), None);
        let mut above: Vec<Level> = Vec::new();
        loop {
            match (level.0.next(), level.1.next()) {
                (Some(x), Some(y)) => match x.cmp_node(y) {
                    Ordering::Equal if x.kids().is_empty() && y.kids().is_empty() => {}
                    Ordering::Equal if x.same(y) => {}
                    Ordering::Equal => {
                        let key =
                            (x.is_shared() || y.is_shared()).then(|| (Id::any(x), Id::any(y)));
                        if key.as_ref().is_some_and(|k| equal.contains(k)) {
                            continue;
                        }
                        above.push(mem::replace(
                            &mut level,
                            (x.kids().iter(), y.kids().iter(), key),
                        ));
                    }
                    o => return o,
                },
                (Some(_), None) => return Ordering::Greater,
                (None, Some(_)) => return Ordering::Less,
                (None, None) => match above.pop() {
                    Some(l) => {
                        if let Some(k) = mem::replace(&mut level, l).2 {
                            equal.insert(k);
                        }
                    }
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
    /// variant and its constraint, or of its count of parts and their numbers, so that equal
    /// formulas write equal numbers. A shared part's number is found once per call.
    fn hash<H: Hasher>(&self, state: &mut H) {
        let n = self.fold(
            (),
            |_, ()| (),
            |g, (), parts: Vec<u64>| {
                // A fixed hasher, so that the number of a formula does not change between runs.
                let mut h = DefaultHasher::new();
                h.write_u8(g.rank());
                match g {
                    Formula::Con(c) => c.hash(&mut h),
                    Formula::Not(_) | Formula::And(_) | Formula::Or(_) => {
                        h.write_usize(parts.len());
                        for p in parts {
                            h.write_u64(p);
                        }
                    }
                }
                h.finish()
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
                Formula::And(gs) | Formula::Or(gs) => {
                    f.write_str(if matches!(g, Formula::And(_)) {
                        "And(["
                    } else {
                        "Or(["
                    })?;
                    stack.push(Piece::Text("])"));
                    for (i, h) in gs.iter().enumerate().rev() {
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
            Formula::And(gs) | Formula::Or(gs) if gs.is_empty() => {
                write!(f, "{}", matches!(g, Formula::And(_)))?
            }
            Formula::And(gs) | Formula::Or(gs) => {
                let sep = if matches!(g, Formula::And(_)) {
                    " && "
                } else {
                    " || "
                };
                for (i, h) in gs.iter().enumerate().rev() {
                    // A conjunction or disjunction of two or more parts is in parentheses.
                    let wrap = matches!(h, Formula::And(hs) | Formula::Or(hs) if hs.len() > 1);
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

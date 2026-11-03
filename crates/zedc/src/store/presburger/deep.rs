//! The operations on [`Formula`] that follow its nesting: the fold that the maps of a formula
//! are written with, and drop, copy, compare, hash and show. Each keeps its own stack on the
//! heap, so a formula's depth is limited by the machine's memory alone, and each costs O(size).

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::slice;

use super::{Con, Formula, Model};

impl Con {
    /// The constraint, moved out of `c`, with `c` left the constraint `0 >= 0` of no atoms.
    pub fn take(c: &mut Con) -> Con {
        Con {
            lin: mem::take(&mut c.lin),
            rel: c.rel,
        }
    }
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

    /// The fold of the formula from its constraints up. Each part is reached with a context:
    /// `ctx` at the root, and `down(node, c)` at each part directly under a node reached with
    /// `c`. `up(node, c, results)` gives a node's result from its parts' results, in order.
    pub(super) fn fold<C: Copy, R>(
        &self,
        ctx: C,
        down: impl Fn(&Formula, C) -> C,
        mut up: impl FnMut(&Formula, C, Vec<R>) -> R,
    ) -> R {
        /// A node whose parts are being folded, the parts left, and where its parts' results
        /// start in the list of results.
        struct Frame<'a, C> {
            node: &'a Formula,
            ctx: C,
            left: slice::Iter<'a, Formula>,
            start: usize,
        }
        // A constraint, the commonest root, needs no list.
        if let Formula::Con(_) = self {
            return up(self, ctx, Vec::new());
        }
        let mut results: Vec<R> = Vec::new();
        let mut stack = vec![Frame {
            node: self,
            ctx,
            left: self.kids().iter(),
            start: 0,
        }];
        while let Some(top) = stack.last_mut() {
            match top.left.next() {
                Some(g) => {
                    let ctx = down(top.node, top.ctx);
                    stack.push(Frame {
                        node: g,
                        ctx,
                        left: g.kids().iter(),
                        start: results.len(),
                    });
                }
                None => {
                    let Frame {
                        node, ctx, start, ..
                    } = stack.pop().expect("the top frame");
                    let parts = results.split_off(start);
                    results.push(up(node, ctx, parts));
                }
            }
        }
        results.pop().expect("the root's result")
    }

    /// [`Formula::holds`]: a conjunction is read up to its first part that fails and a
    /// disjunction up to its first part that holds, so a part decided early is not walked
    /// through.
    pub(super) fn holds_as(&self, vs: &Model) -> bool {
        if let Formula::Con(c) = self {
            return c.holds(vs);
        }
        // The nodes being read, each with the parts left, and the value of the part just read.
        let mut stack = vec![(self, self.kids().iter())];
        let mut value: Option<bool> = None;
        while let Some((node, left)) = stack.last_mut() {
            if let Some(v) = value.take() {
                let decided = match node {
                    Formula::And(_) => !v,
                    Formula::Or(_) => v,
                    Formula::Not(_) => true,
                    Formula::Con(_) => unreachable!("a constraint has no parts"),
                };
                if decided {
                    value = Some(if matches!(node, Formula::Not(_)) {
                        !v
                    } else {
                        v
                    });
                    stack.pop();
                    continue;
                }
            }
            match left.next() {
                Some(Formula::Con(c)) => value = Some(c.holds(vs)),
                Some(g) => stack.push((g, g.kids().iter())),
                // Every part read and none decided: a conjunction holds, a disjunction fails.
                None => {
                    value = Some(matches!(node, Formula::And(_)));
                    stack.pop();
                }
            }
        }
        value.expect("the root's value")
    }

    /// Calls `f` on each constraint, in order.
    pub(super) fn walk<'a>(&'a self, f: &mut dyn FnMut(&'a Con)) {
        let mut stack = vec![slice::from_ref(self).iter()];
        while let Some(top) = stack.last_mut() {
            match top.next() {
                Some(Formula::Con(c)) => f(c),
                Some(g) => stack.push(g.kids().iter()),
                None => {
                    stack.pop();
                }
            }
        }
    }

    /// The parts directly under `self`, moved out, with `self` left a leaf.
    pub(super) fn take_kids(&mut self) -> Vec<Formula> {
        match self {
            Formula::Con(_) => Vec::new(),
            Formula::Not(g) => vec![mem::replace(&mut **g, Formula::top())],
            Formula::And(gs) | Formula::Or(gs) => mem::take(gs),
        }
    }

    /// The parts of a conjunction or a disjunction, moved out, or `None` for another formula.
    pub fn into_parts(mut self) -> Option<Vec<Formula>> {
        match &mut self {
            Formula::And(gs) | Formula::Or(gs) => Some(mem::take(gs)),
            Formula::Con(_) | Formula::Not(_) => None,
        }
    }

    /// The formula under a negation, moved out, or `None` for another formula.
    pub fn into_negated(mut self) -> Option<Formula> {
        match &mut self {
            Formula::Not(g) => Some(mem::replace(&mut **g, Formula::top())),
            Formula::Con(_) | Formula::And(_) | Formula::Or(_) => None,
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
}

impl Drop for Formula {
    fn drop(&mut self) {
        // Each part is moved to the list before its parent goes, and the parts of a part
        // before it goes in turn, so a part dropped here has no parts and this recursion is
        // one level deep.
        let mut stack = self.take_kids();
        while let Some(mut g) = stack.pop() {
            match &mut g {
                Formula::Con(_) => {}
                Formula::Not(h) => stack.push(mem::replace(&mut **h, Formula::top())),
                Formula::And(gs) | Formula::Or(gs) => stack.append(gs),
            }
        }
    }
}

impl Clone for Formula {
    fn clone(&self) -> Formula {
        self.fold(
            (),
            |_, ()| (),
            |node, (), mut parts| match node {
                Formula::Con(c) => Formula::Con(c.clone()),
                Formula::Not(_) => Formula::Not(Box::new(parts.pop().expect("one part"))),
                Formula::And(_) => Formula::And(parts),
                Formula::Or(_) => Formula::Or(parts),
            },
        )
    }
}

impl Ord for Formula {
    /// The order the derived one would give: the variants in the order they are declared,
    /// then the constraints, or the parts in order with a prefix first.
    fn cmp(&self, other: &Formula) -> Ordering {
        // A formula compared with itself is equal at once (COMPLEXITY.md S31).
        if std::ptr::eq(self, other) {
            return Ordering::Equal;
        }
        match self.cmp_node(other) {
            Ordering::Equal => {}
            o => return o,
        }
        // The parts left at the level being read, and above it those of the levels around it;
        // the list is made only when a level has a level under it.
        let mut level = (self.kids().iter(), other.kids().iter());
        let mut above = Vec::new();
        loop {
            match (level.0.next(), level.1.next()) {
                (Some(x), Some(y)) => match x.cmp_node(y) {
                    Ordering::Equal if x.kids().is_empty() && y.kids().is_empty() => {}
                    Ordering::Equal => {
                        above.push(mem::replace(&mut level, (x.kids().iter(), y.kids().iter())))
                    }
                    o => return o,
                },
                (Some(_), None) => return Ordering::Greater,
                (None, Some(_)) => return Ordering::Less,
                (None, None) => match above.pop() {
                    Some(l) => level = l,
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
        // A formula compared with itself is equal at once (COMPLEXITY.md S31).
        if std::ptr::eq(self, other) {
            return true;
        }
        let mut stack = Vec::new();
        let (mut a, mut b) = (self, other);
        loop {
            let same = match (a, b) {
                (Formula::Con(x), Formula::Con(y)) => x == y,
                _ => a.rank() == b.rank() && a.kids().len() == b.kids().len(),
            };
            if !same {
                return false;
            }
            stack.extend(a.kids().iter().zip(b.kids()));
            match stack.pop() {
                Some((x, y)) => (a, b) = (x, y),
                None => return true,
            }
        }
    }
}

impl Eq for Formula {}

impl Hash for Formula {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Each node writes its variant, and its constraint or its count of parts, so that
        // equal formulas write equal sequences and the sequence reads back as one tree.
        let mut stack = Vec::new();
        let mut g = self;
        loop {
            state.write_u8(g.rank());
            match g {
                Formula::Con(c) => c.hash(state),
                Formula::Not(_) => {}
                Formula::And(gs) | Formula::Or(gs) => state.write_usize(gs.len()),
            }
            stack.extend(g.kids().iter().rev());
            match stack.pop() {
                Some(h) => g = h,
                None => return,
            }
        }
    }
}

/// A piece of the text of a formula: a formula yet to be shown, or text.
enum Piece<'a> {
    Formula(&'a Formula),
    Text(&'static str),
}

/// Shows the formula with `show` for each node, as the derived form does when `debug`; each
/// node pushes the pieces it is made of, in reverse, onto one list.
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

//! Questions over shared conjunctions, each decided from the answers of the conjunction it
//! extends (LOAD-chain-share). The relation of a test `p(x) = q(x: x) && x > 3` is the
//! conjunction of `q`'s relation, kept whole as one part ([`Formula::and_keeping`]), and the
//! new constraint; the relation of a chain of n such tests so holds each callee's relation
//! once, shared, and not n²/2 copies. [`Extending`] remembers the answers of each conjunction
//! it decides, by the part it is (`Id`), and decides a conjunction that holds a decided one
//! from those answers and its other parts.

use std::collections::HashMap;
use std::rc::Rc;

use super::formula::Id;
use super::{Formula, Model, Refusal, decide, satisfiable};

/// Whether a formula holds somewhere and whether its negation does, each with the refusal that
/// left it undecided.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Answers {
    /// Whether the formula holds somewhere.
    pub holds: Result<bool, Refusal>,
    /// Whether its negation holds somewhere.
    pub fails: Result<bool, Refusal>,
}

/// What is remembered of a decided conjunction: its answers, and a point where it holds when it
/// holds and the solver gave one.
struct Known {
    answers: Answers,
    point: Option<Rc<Model>>,
}

/// The answers of conjunctions decided so far, by the part each is.
#[derive(Default)]
pub struct Extending {
    known: HashMap<Id, Known>,
}

impl Extending {
    /// An empty memory.
    pub fn new() -> Extending {
        Extending::default()
    }

    /// Whether `f` holds somewhere and whether `!f` does: [`decide`] of each, but a
    /// conjunction one of whose parts is a conjunction kept whole is decided from that part's
    /// answers, which are found first and remembered, and its other parts:
    ///
    /// - it holds nowhere when the part holds nowhere; it holds where the part's point meets
    ///   every other part; otherwise it is decided whole;
    /// - its negation holds somewhere when the part's negation does; when the part holds
    ///   everywhere, it is the negation of the other parts that is decided; otherwise it is
    ///   decided whole.
    ///
    /// Each answer is the one [`decide`] gives the whole, where [`decide`] answers it: a
    /// conjunction that holds nowhere because a part does, or holds at a point, holds there.
    /// The answer of a conjunction does not depend on the order in which conjunctions are asked,
    /// since its kept part is always decided first, the same way. The time is that of the parts
    /// beside each kept part, for a chain of conjunctions each extending the one before whose
    /// point meets the next part and whose negation holds or never holds; a conjunction decided
    /// whole costs what [`decide`] costs on it.
    // Complexity tradeoff: a conjunction whose new parts exclude the point found for the part it
    // extends, or whose part's question was refused, is decided whole, in time of the whole
    // conjunction and not of its new parts; the answer is [`decide`]'s. Why: deciding integer
    // feasibility after adding a constraint has no procedure in time of the constraint alone
    // (an added constraint may move every point, and the elimination the solver does is not
    // kept). Trigger: a chain of tests whose constraints each exclude the point of the test it
    // calls. Test `l01_38_presburger::extend::a_chain_whose_points_move_is_decided_whole`, which
    // measures it, and `l01_38_presburger::one_scope::the_questions_of_a_chain_of_tests_scale`
    // for the chain whose points serve. COMPLEXITY.md row LOAD-chain-share. A complete
    // solution needs an incremental integer procedure: a simplex kept from the callee, with
    // its basis, to which the new rows are added, and the branch of an integer search redone
    // only where the new rows cut it.
    pub fn answers(&mut self, f: &Formula) -> Answers {
        // The chain of kept conjunctions from `f` down to the first one known or with no kept
        // part, each decided after the one it holds: an explicit stack, since the chain is as
        // deep as the chain of calls.
        let mut chain: Vec<Formula> = Vec::new();
        let mut g = f.clone();
        while matches!(g, Formula::And(_)) && !self.known.contains_key(&Id::any(&g)) {
            let next = kept(&g).cloned();
            chain.push(g);
            match next {
                Some(h) => g = h,
                None => break,
            }
        }
        while let Some(g) = chain.pop() {
            let k = self.extend(&g);
            self.known.insert(Id::any(&g), k);
        }
        match f {
            Formula::And(_) => self.known[&Id::any(f)].answers.clone(),
            _ => Answers {
                holds: decide(f),
                fails: decide(&Formula::negate(f.clone())),
            },
        }
    }

    /// The answers of the conjunction `g`, its kept part's answers known when it has one.
    fn extend(&self, g: &Formula) -> Known {
        let Some(at) = kept_at(g) else {
            return whole(g);
        };
        let kids = g.kids();
        let Some(part) = self.known.get(&Id::any(&kids[at])) else {
            return whole(g);
        };
        // The other parts, O(their number); a refusal on them is answered by deciding the whole,
        // so a refused question prints the refusal it printed before.
        let rest = || {
            let others = kids.iter().enumerate().filter(|&(i, _)| i != at);
            Formula::and(others.map(|(_, h)| h.clone()).collect())
        };
        let (holds, point) = match (&part.answers.holds, &part.point) {
            (Ok(false), _) => (Ok(false), None),
            (Ok(true), Some(m)) if rest().holds(m) => (Ok(true), Some(m.clone())),
            _ => holds_whole(g),
        };
        let fails = match part.answers.fails {
            Ok(true) => Ok(true),
            Ok(false) => match decide(&Formula::negate(rest())) {
                Ok(b) => Ok(b),
                Err(_) => decide(&Formula::negate(g.clone())),
            },
            Err(_) => decide(&Formula::negate(g.clone())),
        };
        Known {
            answers: Answers { holds, fails },
            point,
        }
    }
}

/// Where the first part of the conjunction `g` that is a conjunction kept whole lies among
/// its parts.
fn kept_at(g: &Formula) -> Option<usize> {
    g.kids().iter().position(|h| matches!(h, Formula::And(_)))
}

/// The first part of the conjunction `g` that is a conjunction kept whole.
fn kept(g: &Formula) -> Option<&Formula> {
    kept_at(g).map(|i| &g.kids()[i])
}

/// Whether `g` holds somewhere, decided whole, with a point when it holds and the solver
/// gives one.
fn holds_whole(g: &Formula) -> (Result<bool, Refusal>, Option<Rc<Model>>) {
    match decide(g) {
        Ok(true) => (Ok(true), satisfiable(g).ok().flatten().map(Rc::new)),
        other => (other, None),
    }
}

/// The answers of `g`, decided whole.
fn whole(g: &Formula) -> Known {
    let (holds, point) = holds_whole(g);
    Known {
        answers: Answers {
            holds,
            fails: decide(&Formula::negate(g.clone())),
        },
        point,
    }
}

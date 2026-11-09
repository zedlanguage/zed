//! Where a refused check points and, for a member of a recursive group that the group's decider
//! refuses, why (DESIGN.md L1.23, sec:diagnostics; items GROUP-refusal and REFUSE-group-site):
//! the member being decided, the definitions that take part and how they refer to each other,
//! the number of independent cycles they make, the tuple whose two undecided components stopped
//! the decider, and a repair that a re-check confirms.
//!
//! Every choice follows the definitions' names and the order of a tuple's components, never the
//! numbers of the decider's nodes or the order the definitions are listed in, so a group with
//! its definitions listed in another order gets the same message.

use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::Arc;

use super::super::bes::{Answer, Bes, Decision, Kind, decide};
use super::super::rec::{self, Env, Group};
use super::super::{Node, Refusal, Type};

/// What a refused member's message reads, kept with its group's judgment ([`super::Judgment`]).
pub(in crate::types) struct Why {
    /// The decider's system, as it was built, its leaves last set `Top`.
    graph: Bes,
    /// The definition and the expression each node stands for, by its number.
    origin: Vec<(usize, Arc<rec::Node>)>,
    /// The parts the decider does not take, each a node with no children ([`super::judge`]).
    leaves: Vec<u32>,
    /// The decisions: with the leaves `Bot`, and, when there are leaves, with them `Top`.
    runs: Vec<Decision>,
    /// For each run, the refusal whose component holds each node it refused for its shape.
    of: Vec<HashMap<u32, usize>>,
    /// The number of members, whose nodes come first.
    members: u32,
}

impl Why {
    pub(super) fn new(
        members: usize,
        graph: Bes,
        origin: Vec<(usize, Arc<rec::Node>)>,
        leaves: Vec<u32>,
        runs: Vec<Decision>,
    ) -> Why {
        let of = (runs.iter())
            .map(|d| {
                (d.refusals.iter().enumerate())
                    .flat_map(|(k, c)| c.component.iter().map(move |&v| (v, k)))
                    .collect()
            })
            .collect();
        Why {
            members: members as u32,
            graph,
            origin,
            leaves,
            runs,
            of,
        }
    }

    /// Whether the decider decides member `i` once the case `| #end` is added to each member
    /// of `which`: the system of the nodes `i` reaches, each of `which` made a union of its old
    /// node and `Top`, decided as `judge` decides, the leaves `Bot` and then `Top`. What `i`
    /// reaches is all its answer reads, so this is what `judge` gives the group so written.
    fn decides_with_end(&self, i: u32, which: &BTreeSet<usize>) -> bool {
        let mut local: HashMap<u32, u32> = HashMap::from([(i, 0)]);
        let mut order = vec![i];
        let mut k = 0;
        while k < order.len() {
            for &w in self.graph.children(order[k]) {
                if let Entry::Vacant(e) = local.entry(w) {
                    e.insert(order.len() as u32);
                    order.push(w);
                }
            }
            k += 1;
        }
        let leaf: HashSet<u32> = self.leaves.iter().copied().collect();
        let mut b = Bes::new();
        for &v in &order {
            let children = self.graph.children(v).iter().map(|w| local[w]).collect();
            b.add(self.graph.kind(v), children);
        }
        // The leaves, by their new numbers: a member's node given `| #end` keeps its old node
        // under the new union.
        let mut leaves = Vec::new();
        for &v in &order {
            let mut at = local[&v];
            if v < self.members && which.contains(&(v as usize)) {
                let old = b.add(self.graph.kind(v), b.children(at).to_vec());
                let end = b.add(Kind::Top, vec![]);
                b.set(at, Kind::Or, vec![old, end]);
                at = old;
            }
            if leaf.contains(&v) {
                leaves.push(at);
            }
        }
        b.seal();
        let mut answers = Vec::new();
        for kind in [Kind::Bot, Kind::Top] {
            // A leaf has no children either way, so the parents `seal` filled stay right.
            for &v in &leaves {
                b.set(v, kind, vec![]);
            }
            answers.push(decide(&b).answers[0]);
        }
        answers[0] == Answer::Inhabited || answers[1] == Answer::Empty
    }
}

/// Where a refused check points, when it rests on a recursive group.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct GroupSite {
    /// The definition the refusal points at: the member whose answer was being decided.
    pub head: String,
    /// Each definition that takes part, as `type name = body`: the head first, then by name.
    pub defs: Vec<String>,
    /// For a refusal by the group's decider (`Refusal::Group`), the whole reason, written to
    /// follow "because".
    pub detail: Option<String>,
}

impl Type {
    /// Where a check of `self` refused for `cause` points, when it rests on a recursive group.
    /// For `Refusal::Group`, the member its group's decider refuses that `self` is or reads
    /// first, with the reason ([`GroupSite::detail`]); for another cause, the first member on a
    /// cycle of its group that `self` is or reads, with its group's definitions. `None` when
    /// `self` reads no such member. The members are met in a walk of the parts of `self` from
    /// the top, a function of `self` alone. Time linear in the parts walked, and for
    /// `Refusal::Group` in the group, which is built again at most twice to confirm a repair.
    pub fn refusal_site(&self, cause: Refusal) -> Option<GroupSite> {
        let group = cause == Refusal::Group;
        let m = first_member(self, |t| {
            if group {
                t.refused_by_group()
            } else {
                t.on_cycle()
            }
        })?;
        let Node::Rec(r) = &*m.0 else {
            unreachable!("a member is a recursive node")
        };
        let (env, i) = r.key.member_at().expect("a member");
        Some(if group {
            refused_site(env, i)
        } else {
            let defs = env.group().defs();
            let mut part: Vec<usize> = (0..defs.len()).filter(|&j| j != i).collect();
            part.sort_by(|&a, &b| defs[a].name.cmp(&defs[b].name));
            part.insert(0, i);
            GroupSite {
                head: defs[i].name.clone(),
                defs: part.iter().map(|&j| written(env.group(), j)).collect(),
                detail: None,
            }
        })
    }

    /// [`Type::refusal_site`] of the check `self <: other`, which decides `self - other`.
    pub fn subtype_refusal_site(&self, other: &Type, cause: Refusal) -> Option<GroupSite> {
        (self - other).refusal_site(cause)
    }
}

/// The first recursive member for which `want` holds, in a walk of the parts of `t` from the
/// top, breadth first, each node once.
fn first_member(t: &Type, want: impl Fn(&Type) -> bool) -> Option<Type> {
    // Each node met, held for the walk, so that its address names no other node meanwhile.
    let mut seen: HashSet<usize> = HashSet::new();
    let mut held: Vec<Type> = Vec::new();
    let mut queue = VecDeque::from([t.clone()]);
    seen.insert(t.node_addr());
    let mut visit = |x: &Type, queue: &mut VecDeque<Type>| {
        if seen.insert(x.node_addr()) {
            queue.push_back(x.clone());
        }
    };
    while let Some(t) = queue.pop_front() {
        if t.is_member() && want(&t) {
            return Some(t);
        }
        let p = t.p();
        for a in p.atoms.names.values() {
            visit(&a.payload, &mut queue);
        }
        p.tuples.atoms(&mut |row| {
            row.iter().for_each(|x| visit(x, &mut queue));
            true
        });
        p.morphisms.atoms(&mut |m| {
            for x in [&m.guarantee, &m.permission, &m.value] {
                visit(x, &mut queue);
            }
            true
        });
        held.push(t);
    }
    None
}

/// Definition `j` of `group` as written: `type name(params) = body`.
fn written(group: &Group, j: usize) -> String {
    let d = &group.defs()[j];
    let params = if d.params.is_empty() {
        String::new()
    } else {
        format!("({})", d.params.join(", "))
    };
    format!(
        "type {}{params} = {}",
        d.name,
        group.text(j, &group.0.bodies[j])
    )
}

/// `a`, `b` and `c`.
fn listed(names: &[String]) -> String {
    match names {
        [] => String::new(),
        [a] => a.clone(),
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
    }
}

/// The site of member `i` of `env`, which its group's decider refuses. Time linear in the part
/// of the group's system that member `i` reaches, and in the texts written.
// Complexity tradeoff: each message walks, and decides again with the repair, the part of the
// group the member reaches, so the messages of m refused members that all reach one part of n
// nodes cost O(m n), where a table shared by the members could cost O(m + n). Why: a message is
// written only for a check that was refused and is reported, and the walk keeps the decider
// itself linear and free of any per-message table. Trigger: a message asked for each of many
// refused members of one group. Tests: `l01_23_subtyping::group_refusal`. COMPLEXITY.md K85. A
// complete solution keeps the reached parts and their re-check per refused component.
fn refused_site(env: &Arc<Env>, i: usize) -> GroupSite {
    let judgment = env.judged.get().expect("the decider ran");
    let why = judgment.why.as_ref().expect("a member is refused");
    let group = env.group();
    let defs = group.defs();
    let name = |j: usize| format!("`{}`", defs[j].name);
    let r = (why.runs.iter())
        .position(|d| d.answers[i] == Answer::Refused)
        .expect("a run refused the member");
    let (run, of) = (&why.runs[r], &why.of[r]);
    // The refused nodes the member reaches, and the refusals for shape among them, which its
    // answer rests on.
    let mut seen: HashSet<u32> = HashSet::from([i as u32]);
    let mut reached_nodes = vec![i as u32];
    let mut k = 0;
    while k < reached_nodes.len() {
        for &w in why.graph.children(reached_nodes[k]) {
            if run.answers[w as usize] == Answer::Refused && seen.insert(w) {
                reached_nodes.push(w);
            }
        }
        k += 1;
    }
    let reached: BTreeSet<usize> = reached_nodes
        .iter()
        .filter_map(|v| of.get(v))
        .copied()
        .collect();
    // The definitions that take part: the member's and those of the nodes reached.
    let taking: BTreeSet<usize> = (reached_nodes.iter())
        .map(|&v| why.origin[v as usize].0)
        .collect();
    let mut part: Vec<usize> = taking.iter().copied().filter(|&j| j != i).collect();
    part.sort_by(|&a, &b| defs[a].name.cmp(&defs[b].name));
    part.insert(0, i);
    // How they refer to each other: an edge from a node of one to the member node of another.
    let mut refs: BTreeSet<(usize, usize)> = BTreeSet::new();
    for &v in &reached_nodes {
        for &w in why.graph.children(v) {
            if w < why.members && taking.contains(&(w as usize)) {
                refs.insert((why.origin[v as usize].0, w as usize));
            }
        }
    }
    let referring: Vec<String> = (part.iter())
        .filter_map(|&a| {
            let mut to: Vec<usize> = (refs.range((a, 0)..=(a, usize::MAX)))
                .map(|&(_, b)| b)
                .filter(|&b| b != a)
                .collect();
            to.sort_by(|&x, &y| defs[x].name.cmp(&defs[y].name));
            let mut to: Vec<String> = to.into_iter().map(name).collect();
            if refs.contains(&(a, a)) {
                to.push("itself".into());
            }
            (!to.is_empty()).then(|| format!("{} refers to {}", name(a), listed(&to)))
        })
        .collect();
    let cycles = refs.len() + connected(&taking, &refs) - taking.len();
    // The tuple: the least by its definition's name and its text among the tuples with two
    // undecided components on the refused cycles.
    let tuple = (reached.iter())
        .flat_map(|&k| run.refusals[k].tuples.iter().copied())
        .map(|v| {
            let (def, e) = &why.origin[v as usize];
            (defs[*def].name.clone(), group.text(*def, e), v)
        })
        .min();
    let mut text = format!(
        "deciding whether {} has a value needs the definitions {} together; {}; these references make {}; \
         some of these cycles pass through a tuple, which no value can go around forever since \
         a value is finite, and some through the result of a function type, which a value can, \
         since a function can return without calling itself",
        name(i),
        listed(&part.iter().map(|&j| name(j)).collect::<Vec<_>>()),
        referring.join("; "),
        if cycles == 1 {
            "one cycle".to_owned()
        } else {
            format!("{cycles} independent cycles")
        },
    );
    let mut fixes: Vec<BTreeSet<usize>> = vec![taking.clone()];
    if let Some((owner, t, v)) = &tuple {
        let def = why.origin[*v as usize].0;
        let parts = match &why.origin[*v as usize].1.e {
            rec::Shape::Tuple(xs) | rec::Shape::Atom(_, xs) => xs.as_slice(),
            _ => &[],
        };
        let open: Vec<String> = (why.graph.children(*v).iter().zip(parts))
            .filter(|(w, _)| run.answers[**w as usize] == Answer::Refused)
            .map(|(_, x)| format!("`{}`", group.text(def, x)))
            .take(2)
            .collect();
        text += &format!(
            "; the tuple `{t}` in `{owner}` needs a value of both {}, and whether they have one \
             is still open",
            listed(&open)
        );
        fixes.insert(0, BTreeSet::from([def]));
    }
    text += &format!(
        "; the known ways to settle such a group take time that grows with the square of its \
         size, while the checker decides each group in time linear in it, so it stops here and \
         counts {} as possibly having a value",
        name(i)
    );
    // A repair is offered only when the decider, run again with it, decides the member.
    let repaired = fixes.iter().find(|w| why.decides_with_end(i as u32, w));
    text += &match repaired.map(|w| w.iter().copied().collect::<Vec<_>>()) {
        Some(w) if w.len() == 1 => format!(
            "; adding the case `| #end` to {}, as in `{} | #end`, lets the checker decide it",
            name(w[0]),
            written(group, w[0])
        ),
        Some(mut w) => {
            w.sort_by(|&a, &b| defs[a].name.cmp(&defs[b].name));
            format!(
                "; adding the case `| #end` to each of {} lets the checker decide it",
                listed(&w.into_iter().map(name).collect::<Vec<_>>())
            )
        }
        None => "; adding the case `| #end` to these definitions does not settle it either, so \
                 the tuple's components must be written so that they do not both lead back into \
                 the group"
            .to_owned(),
    };
    GroupSite {
        head: defs[i].name.clone(),
        defs: part.iter().map(|&j| written(group, j)).collect(),
        detail: Some(text),
    }
}

/// The number of connected parts of the graph on `nodes` with the edges `refs`, their
/// directions ignored: a union-find with path halving.
fn connected(nodes: &BTreeSet<usize>, refs: &BTreeSet<(usize, usize)>) -> usize {
    let index: Vec<usize> = nodes.iter().copied().collect();
    let at = |d: usize| index.binary_search(&d).expect("a node of the set");
    let mut up: Vec<usize> = (0..index.len()).collect();
    let find = |up: &mut Vec<usize>, mut x: usize| {
        while up[x] != x {
            up[x] = up[up[x]];
            x = up[x];
        }
        x
    };
    let mut parts = index.len();
    for &(a, b) in refs {
        let (ra, rb) = (find(&mut up, at(a)), find(&mut up, at(b)));
        if ra != rb {
            up[ra] = rb;
            parts -= 1;
        }
    }
    parts
}

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
use std::sync::{Arc, PoisonError};

use super::super::bes::{Answer, Bes, Kind, decide};
use super::super::rec::{self, Env, Group, Recheck, Rechecked, Why};
use super::super::{GroupSite, Node, Refusal, Type, Verdict, defs};
use super::settled;

// `Why` and `Recheck` are defined in module `rec`, with the group's instance that keeps them, and
// `Why` is made by `judge`; how a refused member's message reads it is written here.
impl Why {
    /// What the decider makes of member `i` once the case `| #end` is added to each member of
    /// `which`: the system of the nodes `i` reaches, each of `which` made a union of its old
    /// node and `Top`, decided as `judge` decides, the leaves `Bot` and then `Top`, and read as
    /// `judge` reads it ([`settled`]). What `i` reaches is all its answer reads, so this is what
    /// `judge` gives the group so written. The repair adds no meet or difference, so whether a
    /// node reaches one is as it was.
    ///
    /// The re-check is shared. A node that reaches no refused node is not walked: it stands as
    /// `Top` or `Bot`, its answer in each run, since its answer reads only nodes the repair does
    /// not change (each member of `which` reaches a refused node of its own). Every member the
    /// re-check from `i` reaches gets its answers kept, under `which`, since all it reaches lies
    /// inside what `i` reaches and the decider decides each component from the components below
    /// it alone; a later message for that member reads them from there. A later re-check under
    /// `which` does not walk such a member again when it is decided in both runs: it stands as
    /// `Top` or `Bot` as above (GROUP-refusal-reach). A node on a cycle with it is reached only
    /// through a member on that cycle, kept with it and so a leaf too, unless refused in a run;
    /// a walk that meets a member kept refused is made again with no member a leaf.
    fn recheck(&self, i: u32, which: &BTreeSet<usize>) -> Recheck {
        let key: Vec<usize> = which.iter().copied().collect();
        let mut checked = self.checked.lock().unwrap_or_else(PoisonError::into_inner);
        let kept = checked.entry(key).or_default();
        if let Some(&answers) = kept.get(&i) {
            return self.read(i, answers);
        }
        debug_assert!(
            which.iter().all(|&d| self.open[d]),
            "each member given `| #end` reaches a refused node"
        );
        // The answers a re-check under `which` kept for member `v`, when decided in both runs.
        let decided = |kept: &Rechecked, v: u32| {
            (kept.get(&v))
                .filter(|a| a.iter().all(|&x| x != Answer::Refused))
                .copied()
        };
        // The nodes `i` reaches through nodes that reach a refused node, by their new numbers,
        // with the kept members decided in both runs as leaves when `cut`; `None` when a cut
        // walk meets a kept member refused in a run, which may share a cycle with a leaf.
        let walk = |cut: bool| {
            let mut local: HashMap<u32, u32> = HashMap::from([(i, 0)]);
            let mut order = vec![i];
            let mut k = 0;
            while k < order.len() {
                let v = order[k];
                let leaf = cut && decided(kept, v).is_some();
                if cut && !leaf && kept.contains_key(&v) {
                    return None;
                }
                if self.open[v as usize] && !leaf {
                    for &w in self.graph.children(v) {
                        if let Entry::Vacant(e) = local.entry(w) {
                            e.insert(order.len() as u32);
                            order.push(w);
                        }
                    }
                }
                k += 1;
            }
            Some((local, order))
        };
        // Complexity tradeoff: a walk with cuts that meets a member kept refused is made again
        // whole, O(nodes reached) for this message alone; m refused members whose re-checks
        // under one repair each meet such a member, and reach n nodes, cost O(m n) together.
        // Cutting there too needs the decider's cycles of the whole system, kept with `Why`.
        // Naive version: every re-check walks the whole system, O(n) each, O(m n) for m refused
        // members; used: the walk with cuts, O(nodes reached) each, falling back to the whole walk
        // only where it meets a member kept refused (COMPLEXITY.md K85).
        let (cut, (local, order)) = match walk(true) {
            Some(w) => (true, w),
            None => (
                false,
                walk(false).expect("a walk without cuts is never stopped"),
            ),
        };
        let leaf = |v: u32| if cut { decided(kept, v) } else { None };
        // The nodes walked, by their new numbers; each node not walked into stands as a node
        // with no children, set to its answer in each run below.
        let mut b = Bes::new();
        let mut fixed: Vec<(u32, [Answer; 2])> = Vec::new();
        for &v in &order {
            if let Some(a) = leaf(v) {
                fixed.push((b.add(Kind::Bot, vec![]), a));
            } else if self.open[v as usize] {
                let children = self.graph.children(v).iter().map(|w| local[w]).collect();
                b.add(self.graph.kind(v), children);
            } else {
                let a = [0, 1]
                    .map(|run: usize| self.runs[run.min(self.runs.len() - 1)].answers[v as usize]);
                fixed.push((b.add(Kind::Bot, vec![]), a));
            }
        }
        for &v in &order {
            if v < self.members && which.contains(&(v as usize)) && leaf(v).is_none() {
                let at = local[&v];
                let old = b.add(self.graph.kind(v), b.children(at).to_vec());
                let end = b.add(Kind::Top, vec![]);
                b.set(at, Kind::Or, vec![old, end]);
            }
        }
        b.seal();
        let mut answers = Vec::new();
        for run in 0..2 {
            // A node set here has no children either way, so the parents `seal` filled stay
            // right.
            for &(at, a) in &fixed {
                let kind = if a[run] == Answer::Inhabited {
                    Kind::Top
                } else {
                    Kind::Bot
                };
                b.set(at, kind, vec![]);
            }
            answers.push(decide(&b).answers);
        }
        for &v in order.iter().filter(|&&v| v < self.members) {
            let at = local[&v] as usize;
            kept.entry(v).or_insert([answers[0][at], answers[1][at]]);
        }
        self.read(i, kept[&i])
    }

    /// What the answers of member `i` in the two runs of a re-check make of it.
    fn read(&self, i: u32, [low, high]: [Answer; 2]) -> Recheck {
        if settled(low, high, self.wide[i as usize]).is_some() {
            Recheck::Decided
        } else if low == Answer::Refused || high == Answer::Refused {
            Recheck::Refused
        } else {
            Recheck::Searched
        }
    }
}

impl Type {
    /// Where a check of `self` refused for `cause` points, when it rests on a recursive group.
    /// For `Refusal::Group`, the member that `self` is or reads first whose group's decider
    /// refuses it and whose search for a value leaves it undecided, with the reason
    /// ([`GroupSite::detail`]); for another cause, the first member on a cycle of its group that
    /// `self` is or reads, with its group's definitions. `None` when `self` reads no such member. The members are met in a walk of the parts of `self` from
    /// the top, a function of `self` alone. Time linear in the parts walked, and for
    /// `Refusal::Group` in the group, which is built again at most twice to confirm a repair.
    ///
    /// Each definition is written as a user declares it, `type name = body;`. Outside a
    /// checker's message, a part written more than once among them is declared once more
    /// after them, as `type T1 = …;`, and named by `T1` where it stands; inside one, the
    /// message around the site lays it out (module `defs`). Time linear in the texts.
    pub fn refusal_site(&self, cause: Refusal) -> Option<GroupSite> {
        let local = defs::local();
        let mut site = self.site(cause)?;
        if local.is_some() {
            let mut texts: Vec<&mut String> =
                site.defs.iter_mut().chain(&mut site.detail).collect();
            let shared = defs::lift(&mut texts, &|_| false);
            (site.defs).extend(
                shared
                    .iter()
                    .map(|(name, body)| defs::Declaration(name, body).to_string()),
            );
        }
        Some(site)
    }

    /// [`Type::refusal_site`], with each part written more than once left to the printer's
    /// table.
    fn site(&self, cause: Refusal) -> Option<GroupSite> {
        let group = cause == Refusal::Group;
        let m = first_member(self, |t| {
            if group {
                t.refused_by_group() && t.verdict() == Verdict::Refused(Refusal::Group)
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
                defs: part
                    .iter()
                    .map(|&j| format!("{};", written(env.group(), j)))
                    .collect(),
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

/// The site of member `i` of `env`, which its group's decider refuses. Time linear in the texts
/// written and in the nodes member `i` reaches that reach a refused node, with their edges.
// The re-check of a repair is shared by the members of the group: it walks only the nodes that
// reach a refused node, so a decided part that many refused members read is not walked at all,
// and it keeps the answer of every member it reaches, so the other members of a
// refused component read theirs from it (`Why::recheck`). The messages of m refused
// members that read one decided part of n nodes cost O(m + n) together. COMPLEXITY.md K85.
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
    // undecided components on the refused cycles. A meet with a recursive occurrence in it is
    // read as a tuple of its operands, and is named only when no tuple is.
    let tuple = (reached.iter())
        .flat_map(|&k| run.refusals[k].tuples.iter().copied())
        .map(|v| {
            let (def, e) = &why.origin[v as usize];
            let meet = matches!(e.e, rec::Shape::And(_));
            (meet, defs[*def].name.clone(), group.text(*def, e), v)
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
    if let Some((meet, owner, t, v)) = &tuple {
        let def = why.origin[*v as usize].0;
        let parts = match &why.origin[*v as usize].1.e {
            rec::Shape::Tuple(xs) | rec::Shape::Atom(_, xs) | rec::Shape::And(xs) => xs.as_slice(),
            _ => &[],
        };
        let open: Vec<String> = (why.graph.children(*v).iter().zip(parts))
            .filter(|(w, _)| run.answers[**w as usize] == Answer::Refused)
            .map(|(_, x)| format!("`{}`", group.text(def, x)))
            .take(2)
            .collect();
        let (what, needs) = if *meet {
            ("meet", "a value in each of")
        } else {
            ("tuple", "a value of both")
        };
        text += &format!(
            "; the {what} `{t}` in `{owner}` needs {needs} {}, and whether they have one is still \
             open",
            listed(&open)
        );
        fixes.insert(0, BTreeSet::from([def]));
    }
    text += &format!(
        "; the known ways to settle such a group take time that grows with the square of its \
         size, while the checker decides each group in time linear in it, so it does not settle \
         this one; a search for a value of {0} then neither finds one nor shows that there is \
         none, so the checker counts {0} as possibly having a value",
        name(i)
    );
    // A repair is offered when the decider, run again with it, decides the member; failing
    // that, one with which it no longer refuses the member, said to leave it to the search. The
    // last repair adds `| #end` to every definition taking part, the member's among them, which
    // makes the member a union with a case that has a value: inhabited in both runs, so decided,
    // or left to the search when it reaches a meet or a difference, and never refused
    // ([`Why::recheck`], [`settled`]). So a repair is always offered.
    // The repairs are re-checked in turn up to the first decided, since the last, which holds
    // this member, is re-checked under a key of its own (GROUP-refusal-reach). For a member that
    // reaches a meet or a difference, a repair holding it leaves it to the search, as above, so
    // once an earlier repair does that too, the one holding it is not re-checked: re-checked,
    // m such members, each reaching n nodes, cost O(m n) together under their own keys.
    // Complexity tradeoff (COMPLEXITY.md K95): the naive version re-checks every repair up to
    // the first decided, the last under a key holding the member, so m members that each reach
    // a meet or a difference and n nodes cost O(m n). Used: once an earlier repair left such a
    // member to the search, the repair holding it is skipped, so the shared re-checks cost
    // O(m + n) together. Given up: nothing; the skipped re-check could only leave the member
    // to the search too, and the message names the earlier repair.
    let mut searched = None;
    let decided = fixes.iter().find(|&w| {
        if searched.is_some() && why.wide[i] && w.contains(&i) {
            return false;
        }
        match why.recheck(i as u32, w) {
            Recheck::Decided => true,
            Recheck::Searched => {
                searched.get_or_insert(w);
                false
            }
            Recheck::Refused => false,
        }
    });
    let set = |w: &BTreeSet<usize>| w.iter().copied().collect::<Vec<_>>();
    let (mut w, effect) = match decided {
        Some(w) => (set(w), "lets the checker decide it".to_owned()),
        None => (
            set(searched.expect("adding `| #end` to the member never leaves it refused")),
            format!(
                "removes this obstacle, and whether {} has a value is then left to the search \
                 for one",
                name(i)
            ),
        ),
    };
    text += &if let [d] = w[..] {
        format!(
            "; adding the case `| #end` to {}, as in `{} | #end`, {effect}",
            name(d),
            written(group, d)
        )
    } else {
        w.sort_by(|&a, &b| defs[a].name.cmp(&defs[b].name));
        format!(
            "; adding the case `| #end` to each of {} {effect}",
            listed(&w.into_iter().map(name).collect::<Vec<_>>())
        )
    };
    GroupSite {
        head: defs[i].name.clone(),
        defs: part
            .iter()
            .map(|&j| format!("{};", written(group, j)))
            .collect(),
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

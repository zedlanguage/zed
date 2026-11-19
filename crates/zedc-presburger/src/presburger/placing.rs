//! The definitions of a relation's auxiliary variables, each placed in the part of the
//! relation's body that reads its variables, in place of the conjunction of all of them beside
//! the body (FAIL-relational-if-chain-growth).
//!
//! The projection splits a formula disjunction by disjunction, and each level of a nest of
//! disjunctions keeps the rows of the level above that mention the atoms of the nest below
//! (`project_parts`). A definition written beside the body is such a row at every level above
//! the disjunct that reads its variable: in a chain of k `if`s with a `min` in each arm, each of
//! the k levels held the rows of the definitions of the arms below it, Θ(k²) rows in all. Placed
//! in the arm that reads it, a definition is met only when that arm is.
//!
//! Soundness. Let `D` be a definition of the variables `m`, total: for every value of every
//! other atom some value of `m` satisfies `D`. Let `F` be a formula whose every occurrence of `m`
//! lies under one of the parts `P1..Pr` of `F`, each reached from the root of `F` through
//! conjunctions and disjunctions alone, and let `F'` be `F` with each `Pi` replaced by
//! `Pi && D`. Then `∃m. F'` and `∃m. (D && F)` hold at the same values of the other atoms.
//! (1) Where `D(m)` holds, each `Pi && D` is `Pi`, so `F'(m)` is `F(m)`. Hence a point of
//! `D && F` is a point of `F'`. (2) Let `F'(m0)` hold. If `D(m0)` holds, `F(m0)` holds by (1).
//! Otherwise each `Pi && D` is false at `m0`, so `F'` holds with each of them replaced by
//! `false`, a formula that does not mention `m`. It is reached through conjunctions and
//! disjunctions alone, so it is monotone in each `Pi && D`, and `F'` holds at any `m1`. Take
//! `m1` with `D(m1)`, which exists since `D` is total: `F(m1)` holds by (1), so `D && F` holds
//! at `m1`. Each auxiliary variable is existential in the projection and in `decide`, so the
//! two formulas give the same answers. A part held by two parents, or under a negation, is
//! never one of the `Pi`: a definition that a part under it reads is placed at a part above
//! all the places that hold it ([`placed`]).
//!
//! Definitions are placed from the last to the first, and a definition reads only variables
//! made before it, so a definition's own place counts as an occurrence of each variable it
//! reads, and is known when that variable is placed. Where a definition reads a later variable,
//! or a variable is defined twice, nothing is placed and the definitions go beside the body,
//! as before.

use std::collections::HashMap;

use super::formula::{Atom, Factor, Formula, Id};

/// A definition for [`placed`]: the auxiliary variables it fixes, its formula, and whether it is
/// total, so that for every value of every other atom some value of its variables satisfies it.
pub struct Placing {
    /// The variables it fixes.
    pub own: Vec<u32>,
    /// Its formula.
    pub def: Formula,
    /// Whether it is total. A definition that is not stays beside the body.
    pub total: bool,
}

/// The definitions `defs` with the body `body`, as two formulas whose conjunction has, with each
/// auxiliary variable existential, the points of `defs` beside `body`: the definitions left
/// beside the body, and the body with each total definition conjoined to the deepest part that
/// holds every occurrence of its variables, reached from the root through conjunctions and
/// disjunctions held by one parent (the module's comment proves the two alike). A total
/// definition no part reads stays beside the body, as does each when `body` is not a
/// conjunction or a disjunction.
// Complexity tradeoff: naive version, each definition beside the body, which costs nothing
// here and makes each level of a nest of k disjunctions keep the definitions of the levels below
// it, Θ(k²) rows (FAIL-relational-if-chain-growth: the chain of k `if`s with a `min` in each arm
// took 22.9 times the instructions at 8k). Placing them: the distinct compound parts are walked
// once, the deepest common part of the places of each variable is found by binary lifting on
// the tree of the parts held by one parent, O(log d) per occurrence for d the depth, and only
// the parts above a placed definition are rebuilt, O((n + a) log d) in all for n the distinct
// parts and a the occurrences of auxiliary variables. Test
// `l01_25_preimage_catalog::bench::s22::relational_equal_guards_scale`, COMPLEXITY.md row
// ST-placed-definitions.
pub fn placed(body: &Formula, defs: &[Placing]) -> (Formula, Formula) {
    let beside = || {
        let all = defs.iter().map(|d| d.def.clone()).collect();
        (Formula::and(all), body.clone())
    };
    if !matches!(body, Formula::And(_) | Formula::Or(_)) || !defs.iter().any(|d| d.total) {
        return beside();
    }
    let mut owner: HashMap<u32, usize> = HashMap::new();
    for (i, d) in defs.iter().enumerate() {
        for &a in &d.own {
            if owner.insert(a, i).is_some() {
                return beside();
            }
        }
    }
    let parts = Parts::of(body);
    let n = parts.nodes.len();
    // `place[i]`: the deepest part that holds every occurrence of the variables of `defs[i]`
    // seen so far, or `None` for none.
    let mut place: Vec<Option<usize>> = vec![None; defs.len()];
    let meet = |place: &mut Vec<Option<usize>>, i: usize, at: usize| {
        place[i] = Some(match place[i] {
            Some(p) => parts.tree.lca(p, at),
            None => at,
        });
    };
    for v in 0..n {
        // A constraint directly under `v` is reached from `v`, or, below a part that is not
        // on the tree, from that part's anchor.
        let at = parts.anchor[v];
        for k in parts.nodes[v].kids() {
            if let Formula::Con(c) = k {
                for a in c.lin.terms.keys() {
                    auxes(a, |x| {
                        if let Some(&i) = owner.get(&x) {
                            meet(&mut place, i, at);
                        }
                    });
                }
            }
        }
    }
    // Each definition's part, the last first; `None` beside the body.
    let mut at: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut top = Vec::new();
    for i in (0..defs.len()).rev() {
        let d = &defs[i];
        let target = if d.total { place[i] } else { None };
        match target {
            Some(p) => at[p].push(i),
            None => top.push(i),
        }
        // The variables it reads occur at its part; beside the body is above the root.
        let mut later = false;
        for a in d.def.atoms() {
            auxes(&a, |x| match owner.get(&x) {
                Some(&j) if j == i => {}
                Some(&j) if j > i => later = true,
                Some(&j) => meet(&mut place, j, target.unwrap_or(0)),
                None => {}
            });
        }
        if later {
            return beside();
        }
    }
    top.reverse();
    let top = Formula::and(top.iter().map(|&i| defs[i].def.clone()).collect());
    (top, parts.rebuilt(&at, defs))
}

/// Calls `f` with each auxiliary variable of the atom `a`: itself, or a factor of a product.
fn auxes(a: &Atom, mut f: impl FnMut(u32)) {
    match a {
        Atom::Aux(x) => f(*x),
        Atom::Product(x, y) => {
            for g in [x, y] {
                if let Factor::Aux(x) = g {
                    f(*x)
                }
            }
        }
        Atom::Sym(_) => {}
    }
}

/// The distinct compound parts of a formula, the root first, with the tree of the
/// conjunctions and disjunctions reached from the root through parts each held by one parent.
struct Parts<'f> {
    nodes: Vec<&'f Formula>,
    /// For each part, the place of each of its compound parts in `nodes`, in order, `None` for
    /// a constraint.
    kids: Vec<Vec<Option<usize>>>,
    /// Whether the part is on the tree.
    on_tree: Vec<bool>,
    /// For each part, the deepest part of the tree that holds every place it is held at: the
    /// part itself on the tree.
    anchor: Vec<usize>,
    /// The tree, by binary lifting, its own root above part 0; only the parts on the tree are
    /// attached.
    tree: zed_graph::Lift,
    /// The parts, each after every part that holds it.
    order: Vec<usize>,
}

impl<'f> Parts<'f> {
    /// The parts of `body`, a conjunction or disjunction. O(n log d) for n the distinct parts
    /// and d the depth of the tree.
    fn of(body: &'f Formula) -> Parts<'f> {
        let mut index: HashMap<Id, usize> = HashMap::new();
        index.insert(Id::any(body), 0);
        let mut nodes = vec![body];
        let mut kids: Vec<Vec<Option<usize>>> = vec![Vec::new()];
        let mut parents: Vec<Vec<usize>> = vec![Vec::new()];
        let mut stack = vec![0];
        // Each part walked once, by its id (a visited set, as for any walk of a DAG).
        while let Some(v) = stack.pop() {
            let mut mine = Vec::with_capacity(nodes[v].kids().len());
            for k in nodes[v].kids() {
                if matches!(k, Formula::Con(_)) {
                    mine.push(None);
                    continue;
                }
                let c = *index.entry(Id::any(k)).or_insert_with(|| {
                    nodes.push(k);
                    kids.push(Vec::new());
                    parents.push(Vec::new());
                    stack.push(nodes.len() - 1);
                    nodes.len() - 1
                });
                parents[c].push(v);
                mine.push(Some(c));
            }
            kids[v] = mine;
        }
        let n = nodes.len();
        // Each part after all that hold it (Kahn's order, last ready first).
        let mut left: Vec<usize> = parents.iter().map(Vec::len).collect();
        let mut order = Vec::with_capacity(n);
        zed_graph::kahn(
            &mut left,
            &mut vec![0],
            |v| kids[v].iter().flatten().copied(),
            |v| order.push(v),
        );
        // The tree's own root is `n`, above part 0 (`zed_graph::Lift`); a part off the tree is
        // not attached and never asked about.
        let mut on_tree = vec![false; n];
        let mut tree_parent: Vec<usize> = vec![n; n];
        let mut depth: Vec<usize> = vec![0; n];
        on_tree[0] = true;
        for &v in &order[1..] {
            let compound = matches!(nodes[v], Formula::And(_) | Formula::Or(_));
            if let [p] = parents[v][..]
                && compound
                && on_tree[p]
            {
                on_tree[v] = true;
                depth[v] = depth[p] + 1;
                tree_parent[v] = p;
            }
        }
        // Part 0 is at depth 1 below the tree's root, so the deepest part at one more.
        let mut tree = zed_graph::Lift::with_depth(n, depth.iter().max().map_or(1, |d| d + 1));
        for &v in &order {
            if on_tree[v] {
                tree.attach(v, tree_parent[v]);
            }
        }
        let mut parts = Parts {
            nodes,
            kids,
            on_tree,
            anchor: vec![0; n],
            tree,
            order,
        };
        for i in 0..n {
            let v = parts.order[i];
            parts.anchor[v] = if parts.on_tree[v] {
                v
            } else {
                // Every place it is held at: a parent on the tree holds it there, any other
                // parent at that parent's anchor, known since parents come first.
                let mut a: Option<usize> = None;
                for &p in &parents[v] {
                    let at = parts.anchor[p];
                    a = Some(a.map_or(at, |a| parts.tree.lca(a, at)));
                }
                a.unwrap_or(0)
            };
        }
        parts
    }

    /// The root with the definitions `at[v]` of `defs` conjoined to each part `v` of the tree,
    /// each part above one rebuilt once ([`Formula::rebuild`] keeps its kept parts kept), every
    /// other part shared as it is. O(n) parts and the parts of the rebuilt ones.
    fn rebuilt(&self, at: &[Vec<usize>], defs: &[Placing]) -> Formula {
        let n = self.nodes.len();
        let mut need = vec![false; n];
        for (v, here) in at.iter().enumerate().take(n) {
            if here.is_empty() {
                continue;
            }
            // Up the tree to the first part already marked: each part marked once.
            let mut u = v;
            while !need[u] {
                need[u] = true;
                if u == 0 {
                    break;
                }
                u = self.tree.parent(u);
            }
        }
        let mut built: Vec<Option<Formula>> = vec![None; n];
        for &v in self.order.iter().rev() {
            if !need[v] {
                continue;
            }
            let node = self.nodes[v];
            let mut parts = Vec::with_capacity(node.kids().len());
            for (k, c) in node.kids().iter().zip(&self.kids[v]) {
                parts.push(match c {
                    // A part on the tree is held by `v` alone, so it is taken once.
                    Some(c) if need[*c] => built[*c].take().expect("a rebuilt part"),
                    _ => k.clone(),
                });
            }
            let mut f = node.rebuild(parts);
            if !at[v].is_empty() {
                let mut all = vec![f];
                // In the order of the definitions.
                all.extend(at[v].iter().rev().map(|&i| defs[i].def.clone()));
                f = Formula::and(all);
            }
            built[v] = Some(f);
        }
        built[0].take().unwrap_or_else(|| self.nodes[0].clone())
    }
}

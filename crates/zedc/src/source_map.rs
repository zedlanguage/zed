//! The map between ZIR nodes and source nodes (DESIGN.md step L1.33a; sec:introspection,
//! `sources` and `zirOf`; sec:incremental, "The compiler's own stages are derived the same
//! way", item 2): each node of a lowered graph has every source node it was lowered from, and
//! each source node the graph nodes lowered from it.
//!
//! A source node is a node of the unit's parse tree, a statement or an expression, named by
//! the top-level declaration it lies in and its path from there, the place among its
//! parent's children at each step, never by byte offsets: text inserted above a declaration
//! changes no entry. A statement's children are its expressions, as
//! `stmts_exprs` of zedc-syntax's `ast::walk` lists them; a block's are its statements; any
//! other expression's are those `expr_kids` there lists.
//!
//! The lowering gives each node the spans of the terms it was lowered for
//! ([`crate::zir::lower::Sited::sources`]); a span is the source node whose text it is, the
//! innermost when nested nodes have the same text, or, for a send `p <- v`, which the
//! elaborator places at its head, the port and `<-`, the send's statement.
//
// Complexity tradeoff: the tree is kept as a parent, a place and a list of children for each
// node, numbered in preorder, and a path is rebuilt when asked for, O(depth); storing each
// source's path would cost O(depth) memory per entry, O(n · depth) for a deep program, where
// the spec asks for one entry per pair of node and source. The reverse map is a list of
// pairs sorted by source node, as the spec's `zirOf` is ordered: O(p log p) to build for p
// pairs, O(log p + k) a look-up, where a hash map would cost O(p) to build but give no order.
// Test: `l01_33a_zir_sources::bench`.

use std::collections::HashMap;
use std::sync::Arc;

use crate::ast::{Blocks, Expr, ExprKind, Stmt, StmtKind, expr_kids, stmts_exprs};
use zed_kernel::sites::Span;

/// The top-level declaration a source node lies in: the name it declares, `None` for one that
/// declares none, and how many top-level statements before it have that name (or none), so
/// that two methods of one name, or two tests, are told apart.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Declaration {
    /// The name declared, if any.
    pub name: Option<Arc<str>>,
    /// The number of earlier top-level statements with the same `name`.
    pub nth: u32,
}

/// A node of the unit's parse tree: its declaration and its path there, the place among its
/// parent's children at each step from the declaration's statement, which has the empty path.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SourceNode {
    /// The top-level declaration.
    pub declaration: Declaration,
    /// The path from the declaration's statement.
    pub path: Vec<u32>,
}

/// The map of a lowered graph's nodes to their source nodes and back ([`SourceMap::new`]).
#[derive(Clone, Debug, Default)]
pub struct SourceMap {
    /// Each tree node's parent, `u32::MAX` for a top-level statement, by preorder number.
    parent: Vec<u32>,
    /// Each tree node's place among its parent's children, or, for a top-level statement,
    /// its place among the top-level statements.
    place: Vec<u32>,
    /// Each tree node's text, by preorder number.
    spans: Vec<Span>,
    /// Where each tree node's children begin in `kids`; one more entry than nodes.
    first: Vec<u32>,
    /// The children of every tree node, those of node 0 first.
    kids: Vec<u32>,
    /// The tree node of each top-level statement.
    roots: Vec<u32>,
    /// Each top-level statement's declaration.
    declarations: Vec<Declaration>,
    /// The top-level statement of each declaration.
    by_declaration: HashMap<Declaration, u32>,
    /// The tree nodes of each graph node, in source order, by graph node number in preorder.
    of: Vec<Vec<u32>>,
    /// Each pair of tree node and graph node, sorted.
    back: Vec<(u32, u32)>,
    /// How many spans the lowering gave are no source node's.
    missed: usize,
}

/// A parse tree node to number.
enum Item<'a> {
    Stmt(&'a Stmt),
    Expr(&'a Expr),
}

impl SourceMap {
    /// The map for the graph whose nodes have `sources`, by node number in preorder
    /// ([`crate::zir::lower::Sited::sources`]), lowered from the unit whose top-level
    /// statements, as parsed, are `stmts`. O(t + p log p) for t parse tree nodes and p pairs
    /// of graph node and source; the tree is walked on a heap stack, as deep as the program.
    pub fn new(stmts: &[Stmt], sources: &[Vec<Span>]) -> SourceMap {
        let mut m = SourceMap::default();
        let mut counts: HashMap<Option<&str>, u32> = HashMap::new();
        for s in stmts {
            let name = crate::suppress::declared(s);
            let nth = counts.entry(name).or_default();
            m.declarations.push(Declaration {
                name: name.map(Arc::from),
                nth: *nth,
            });
            *nth += 1;
        }
        for (i, d) in m.declarations.iter().enumerate() {
            m.by_declaration.insert(d.clone(), i as u32);
        }
        // Numbered in preorder: a node, then each child's subtree in order. A later node
        // with the same text is inside the earlier one, so it takes the span.
        let mut at: HashMap<(usize, usize), u32> = HashMap::new();
        let mut todo: Vec<(u32, u32, Item)> = (stmts.iter().enumerate().rev())
            .map(|(i, s)| (u32::MAX, i as u32, Item::Stmt(s)))
            .collect();
        let mut kids: Vec<Item> = Vec::new();
        while let Some((parent, place, item)) = todo.pop() {
            let n = m.parent.len() as u32;
            m.parent.push(parent);
            m.place.push(place);
            if parent == u32::MAX {
                m.roots.push(n);
            }
            match item {
                Item::Stmt(s) => {
                    m.spans.push(Span {
                        start: s.span.start,
                        end: s.span.end,
                    });
                    at.insert((s.span.start, s.span.end), n);
                    let b = s.bare();
                    if let StmtKind::Push { value, .. } = &b.kind {
                        at.insert((b.span.start, value.span.start.max(b.span.start)), n);
                    }
                    stmts_exprs(std::slice::from_ref(s), &mut |e| kids.push(Item::Expr(e)));
                }
                Item::Expr(e) => {
                    m.spans.push(Span {
                        start: e.span.start,
                        end: e.span.end,
                    });
                    at.insert((e.span.start, e.span.end), n);
                    match &e.kind {
                        ExprKind::Block(stmts) => kids.extend(stmts.iter().map(Item::Stmt)),
                        kind => expr_kids(kind, Blocks::Skip, &mut |e| kids.push(Item::Expr(e))),
                    }
                }
            }
            todo.extend((kids.drain(..).enumerate().rev()).map(|(i, c)| (n, i as u32, c)));
        }
        // The children of each node, by counting: a node's children follow its number.
        let t = m.parent.len();
        m.first = vec![0; t + 1];
        for &p in &m.parent {
            if p != u32::MAX {
                m.first[p as usize + 1] += 1;
            }
        }
        for i in 0..t {
            m.first[i + 1] += m.first[i];
        }
        m.kids = vec![0; m.first[t] as usize];
        for (n, &p) in m.parent.iter().enumerate() {
            if p != u32::MAX {
                let slot = m.first[p as usize] + m.place[n];
                m.kids[slot as usize] = n as u32;
            }
        }
        for (x, spans) in sources.iter().enumerate() {
            let mut tree: Vec<u32> = Vec::with_capacity(spans.len());
            for s in spans {
                match at.get(&(s.start, s.end)) {
                    Some(&n) => tree.push(n),
                    None => m.missed += 1,
                }
            }
            tree.sort_unstable();
            tree.dedup();
            m.back.extend(tree.iter().map(|&n| (n, x as u32)));
            m.of.push(tree);
        }
        m.back.sort_unstable();
        m
    }

    /// The source nodes of graph node `x`, in source order; none for a node lowered for no
    /// term with a site, or out of range. O(k · depth) for its k sources.
    pub fn sources(&self, x: usize) -> Vec<SourceNode> {
        (self.of.get(x).into_iter().flatten())
            .map(|&n| self.node(n))
            .collect()
    }

    /// The graph nodes lowered from the source node `s`, in node order: the reverse of
    /// [`SourceMap::sources`]. O(depth + log p + k).
    pub fn zir_of(&self, s: &SourceNode) -> Vec<usize> {
        let Some(n) = self.find(s) else {
            return Vec::new();
        };
        let from = self.back.partition_point(|&(m, _)| m < n);
        (self.back[from..].iter())
            .take_while(|&&(m, _)| m == n)
            .map(|&(_, x)| x as usize)
            .collect()
    }

    /// The text of the source node `s` in the unit the map was built from, if it has the node:
    /// where a message about it is placed. O(depth).
    pub fn span(&self, s: &SourceNode) -> Option<Span> {
        self.find(s).map(|n| self.spans[n as usize])
    }

    /// How many pairs of graph node and source node the map holds.
    pub fn len(&self) -> usize {
        self.back.len()
    }

    /// Whether the map holds no pair.
    pub fn is_empty(&self) -> bool {
        self.back.is_empty()
    }

    /// How many spans the lowering gave are no source node's text: none for a graph lowered
    /// from the unit the statements are of.
    pub fn missed(&self) -> usize {
        self.missed
    }

    /// The name of tree node `n`. O(depth).
    fn node(&self, mut n: u32) -> SourceNode {
        let mut path = Vec::new();
        while self.parent[n as usize] != u32::MAX {
            path.push(self.place[n as usize]);
            n = self.parent[n as usize];
        }
        path.reverse();
        SourceNode {
            declaration: self.declarations[self.place[n as usize] as usize].clone(),
            path,
        }
    }

    /// The tree node `s` names, if the unit has it. O(depth).
    fn find(&self, s: &SourceNode) -> Option<u32> {
        let top = *self.by_declaration.get(&s.declaration)?;
        let mut n = self.roots[top as usize];
        for &i in &s.path {
            let (from, to) = (self.first[n as usize], self.first[n as usize + 1]);
            n = *self.kids.get((from..to).nth(i as usize)? as usize)?;
        }
        Some(n)
    }
}

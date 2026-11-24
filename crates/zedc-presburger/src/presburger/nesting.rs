//! The nesting of a formula's conjunctions, disjunctions and negations, as vertices that
//! `stable_colors` adds to the graph of a system, so that two atoms whose rows are alike but
//! stand beside different rows in a disjunct get different colors (PREIMAGE-tie-indep-let).
//!
//! In `(b1 <= 0 && z == q0 - 2) || (b1 >= 1 && z == q0)` beside
//! `(b2 <= 0 && q0 == q1 - 4) || (b2 >= 1 && q0 == q1)`, read as one system of rows, `b1` and
//! `b2` each have the rows `-b >= 0` and `b - 1 >= 0` and no others, so color refinement over
//! the rows alone gives them one color, though no exchange of the two maps the formula onto
//! itself: the disjunct that holds `b1 <= 0` holds a row of constant 2, the one that holds
//! `b2 <= 0` a row of constant 4. With a vertex for each disjunct joined to its rows, the two
//! guards are told apart.

use std::collections::HashMap;
use std::slice;

use super::formula::{Con, Formula, Id};

/// A conjunction, disjunction or negation of a formula, as a vertex of the graph that
/// `stable_colors` colors: its variant (`Formula::rank`) and its parts, sorted.
#[derive(PartialEq, Eq, Hash)]
pub(super) struct Group {
    pub(super) kind: u8,
    pub(super) parts: Vec<Part>,
}

/// A part of a [`Group`]: a row of the system, or another group, by its place.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Part {
    Row(usize),
    Group(usize),
}

/// The distinct constraints of `f`, then those of `joins` not among them, and the groups of
/// `f`, each distinct group once. Two parts equal as formulas are one vertex, wherever they
/// stand and whether or not they are shared, and a group's parts are sorted, so the graph
/// depends on what `f` says and not on its sharing, the order of its parts or the names of its
/// atoms: a renaming of the atoms maps the graph onto the graph of the renamed formula.
// Complexity tradeoff: naive version, a vertex for each place in the formula written out, as
// many as the tree has nodes, exponential in the depth of a formula whose parts are shared.
// Used: a post-order walk on a heap stack that reads a shared part once (a map by `Id`), and
// joins equal groups by a map keyed by (variant, sorted parts), O(L log L) for L links from a
// part to its parent among the distinct parts, with the hashes of the constraints. Tradeoffs:
// the maps take O(L) memory; equal parts are joined, which can only make the coloring coarser
// than one of the tree written out, never finer, so no exchange of atoms that maps the formula
// onto itself is broken. Tests:
// `l01_38_omega_test::names::guards_alike_as_rows_are_told_apart_by_their_nesting` and
// `l01_38_omega_test::bench::names::decide_scales_over_guards_told_apart_by_their_nesting`
// (T(8n)/T(n) 9.6 in instructions, 100 to 800 steps).
pub(super) fn nesting<'a>(f: &'a Formula, joins: &'a [Con]) -> (Vec<&'a Con>, Vec<Group>) {
    let mut rows: Vec<&'a Con> = Vec::new();
    let mut row_of: HashMap<&'a Con, usize> = HashMap::new();
    let mut row = |c: &'a Con| {
        *row_of.entry(c).or_insert_with(|| {
            rows.push(c);
            rows.len() - 1
        })
    };
    let mut group_of: HashMap<Group, usize> = HashMap::new();
    let mut shared: HashMap<Id, Part> = HashMap::new();
    /// A group whose parts are being read: the node, its parts left, its parts read, and its
    /// key when shared.
    struct Frame<'a> {
        node: &'a Formula,
        left: slice::Iter<'a, Formula>,
        parts: Vec<Part>,
        id: Option<Id>,
    }
    let mut stack: Vec<Frame<'a>> = Vec::new();
    // A call node is read as its clauses, at the root and below (the generic route, META3
    // H7): as one part with no parts, its term's atoms would be read nowhere.
    let f = f.opened();
    match f {
        Formula::Con(c) => {
            row(c);
        }
        Formula::Holes(_) => unreachable!("an opened formula is no call node"),
        Formula::Not(_) | Formula::And(_) | Formula::Or(_) => stack.push(Frame {
            node: f,
            left: f.kids().iter(),
            parts: Vec::new(),
            id: None,
        }),
    }
    while let Some(top) = stack.last_mut() {
        match top.left.next() {
            Some(Formula::Con(c)) => top.parts.push(Part::Row(row(c))),
            Some(g) => {
                let id = Id::of(g);
                let g = g.opened();
                match id.and_then(|id| shared.get(&id)) {
                    Some(&p) => top.parts.push(p),
                    None => stack.push(Frame {
                        node: g,
                        left: g.kids().iter(),
                        parts: Vec::new(),
                        id,
                    }),
                }
            }
            None => {
                let Frame {
                    node,
                    mut parts,
                    id,
                    ..
                } = stack.pop().expect("the top frame");
                parts.sort_unstable();
                let next = group_of.len();
                let key = Group {
                    kind: node.rank(),
                    parts,
                };
                let p = Part::Group(*group_of.entry(key).or_insert(next));
                if let Some(id) = id {
                    shared.insert(id, p);
                }
                if let Some(parent) = stack.last_mut() {
                    parent.parts.push(p);
                }
            }
        }
    }
    for c in joins {
        row(c);
    }
    let mut groups: Vec<Option<Group>> = (0..group_of.len()).map(|_| None).collect();
    for (g, at) in group_of {
        groups[at] = Some(g);
    }
    let groups = groups
        .into_iter()
        .map(|g| g.expect("each place given a group"))
        .collect();
    (rows, groups)
}

//! Where the binders of a match are in its scrutinee, and the parts on the way to those a
//! fused release keeps (step L1.34). The runtime's heap (`zed_rt::Heap::matches` and
//! `release`) and the compiler's counting machine (`zedc::zir::memory`) both read them, so they
//! are here, in the crate both depend on (HEAP-paths-shared).

/// A tree of the parts a match entered, each node its parent node and its part index there,
/// with node [`Paths::ROOT`] the whole scrutinee. A binder's path is one node, so no binder
/// copies the path above it: a binder at each of `d` levels costs `d` nodes, not `d²/2` part
/// indices (HEAP-binder-paths, HEAP-binder-memory).
// Complexity tradeoff: the naive form copies the path from the scrutinee to each binder
// (`at.to_vec()`), and a release reads each kept path from the top and filters the kept paths
// at each freed cell: O(d²) time and bytes for a binder at each of d levels (COMPLEXITY.md
// HEAP-binder-paths, HEAP-binder-memory; 61.0 to 63.8 times the bytes for 8 times the depth).
// Here each part entered is one node with its parent, a binder records its node, and a release
// builds the tree of nodes on the way to the kept binders once (`Kept`): O(nodes + kept).
// Tradeoff: a binder's path as a list of indices costs O(depth) to read back (`path`), which
// only messages do. Nothing is refused. Tests
// `l01_36_cranelift::bench::scaling::a_binder_at_every_level_of_a_deep_pattern_scales`,
// `releasing_a_binder_at_every_level_scales` and
// `l01_34_memory::bench::a_binder_at_every_level_of_a_deep_match_held_once_scales`.
#[derive(Debug)]
pub struct Paths {
    /// Each node's parent node and part index, in the order entered, which is preorder;
    /// node 0, the root, is its own parent.
    nodes: Vec<(usize, usize)>,
}

impl Default for Paths {
    fn default() -> Self {
        Paths {
            nodes: vec![(Self::ROOT, 0)],
        }
    }
}

impl Paths {
    /// The node of the whole scrutinee, the empty path.
    pub const ROOT: usize = 0;

    /// The node of part `part` of the word at node `parent`.
    pub fn push(&mut self, parent: usize, part: usize) -> usize {
        self.nodes.push((parent, part));
        self.nodes.len() - 1
    }

    /// The parent of node `n`, which is not the root.
    pub fn parent(&self, n: usize) -> usize {
        self.nodes[n].0
    }

    /// Each node below the root, its parent and its part index, in the order entered: node
    /// `n` is item `n - 1`, and a parent comes before its children.
    pub fn below(&self) -> &[(usize, usize)] {
        &self.nodes[1..]
    }

    /// The part indices from the scrutinee to node `n`, in O(depth of `n`).
    pub fn path(&self, mut n: usize) -> Vec<usize> {
        let mut p = Vec::new();
        while n != Self::ROOT {
            let (up, i) = self.nodes[n];
            p.push(i);
            n = up;
        }
        p.reverse();
        p
    }

    /// Whether no part was entered: the root is the only node.
    pub fn is_empty(&self) -> bool {
        self.nodes.len() == 1
    }

    /// Removes every node but the root, keeping the buffer.
    pub fn clear(&mut self) {
        self.nodes.truncate(1);
    }
}

/// A node of [`Kept`]: links to its first child and its next sibling (0 for none: the root is
/// no one's child), whether a kept binder is there, and whether it is on the way to one.
#[derive(Clone, Default)]
struct Link {
    first: usize,
    next: usize,
    kept: bool,
    on: bool,
}

/// The nodes of a [`Paths`] on the way to the kept binders of a fused release, each with its
/// children in preorder, by the nodes' numbers in the [`Paths`].
pub struct Kept<'a> {
    paths: &'a Paths,
    links: Vec<Link>,
}

impl<'a> Kept<'a> {
    /// The tree of the nodes of `paths` on the way to the nodes `kept`. O(nodes + kept): each
    /// node is marked once, a walk up stopping at a marked node, and the marked ones are
    /// linked to their parents in one pass from the last; with nothing kept, O(1).
    pub fn new(paths: &'a Paths, kept: &[usize]) -> Self {
        let size = if kept.is_empty() {
            1
        } else {
            paths.nodes.len()
        };
        let mut links = vec![Link::default(); size];
        for &k in kept {
            links[k].kept = true;
            let mut x = k;
            while !links[x].on {
                links[x].on = true;
                if x == Paths::ROOT {
                    break;
                }
                x = paths.nodes[x].0;
            }
        }
        for x in (1..size).rev() {
            if links[x].on {
                let up = paths.nodes[x].0;
                links[x].next = links[up].first;
                links[up].first = x;
            }
        }
        Kept { paths, links }
    }

    /// The children of node `x` on the way to a kept binder, in preorder.
    pub fn kids(&self, x: usize) -> impl Iterator<Item = usize> + '_ {
        let mut k = self.links[x].first;
        std::iter::from_fn(move || {
            (k != 0).then(|| {
                let at = k;
                k = self.links[k].next;
                at
            })
        })
    }

    /// Whether a kept binder is at node `x`.
    pub fn kept(&self, x: usize) -> bool {
        self.links[x].kept
    }

    /// The part index of node `x`, which is not the root.
    pub fn part(&self, x: usize) -> usize {
        self.paths.nodes[x].1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The tree of `(a, (b, c))` read by `(x, (_, z))` keeping `z`: the root, part 1 and its
    /// part 1, and nothing on the way to `x`.
    #[test]
    fn the_tree_holds_only_the_nodes_on_the_way_to_a_kept_binder() {
        let mut p = Paths::default();
        let x = p.push(Paths::ROOT, 0);
        let pair = p.push(Paths::ROOT, 1);
        let z = p.push(pair, 1);
        assert_eq!(p.path(z), vec![1, 1]);
        assert_eq!(p.parent(z), pair);
        assert_eq!(p.below(), &[(0, 0), (0, 1), (pair, 1)]);
        let t = Kept::new(&p, &[z]);
        assert_eq!(t.kids(Paths::ROOT).collect::<Vec<_>>(), vec![pair]);
        assert_eq!(t.kids(pair).collect::<Vec<_>>(), vec![z]);
        assert_eq!((t.kept(x), t.kept(pair), t.kept(z)), (false, false, true));
        assert_eq!(t.part(z), 1);
        // Both binders kept: the root's children in preorder.
        let t = Kept::new(&p, &[z, x]);
        assert_eq!(t.kids(Paths::ROOT).collect::<Vec<_>>(), vec![x, pair]);
        // Nothing kept: no child anywhere.
        assert_eq!(Kept::new(&p, &[]).kids(Paths::ROOT).count(), 0);
        assert!(!p.is_empty());
        p.clear();
        assert!(p.is_empty());
        assert_eq!(p.below(), &[]);
        // The whole scrutinee kept: the root is kept, with no child.
        let t = Kept::new(&p, &[Paths::ROOT]);
        assert!(t.kept(Paths::ROOT));
        assert_eq!(t.kids(Paths::ROOT).count(), 0);
    }
}

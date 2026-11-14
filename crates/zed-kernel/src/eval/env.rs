//! The names in scope during a run: a persistent AVL tree of bindings, ordered by name.

use std::cmp::Ordering;
use std::rc::Rc;

use super::Binding;

/// The names in scope, in a persistent ordered map: binding a name and looking one up cost
/// `O(log n)` in the names in scope, and a closure's copy of its environment costs `O(1)`.
/// A binding replaces an outer one of the same name.
// Complexity tradeoff (COMPLEXITY.md K8): the naive environment is a list of frames walked on
// each lookup, O(depth), so O(n·depth) for `n` reads, and a closure copies it, O(names). Used:
// a persistent ordered map, O(log n) per binding and lookup and O(1) per closure. Tradeoff:
// memory, since the environments of a chain of `let`s stay live and each shares all but
// O(log n) nodes with the last, O(n log n) in all.
// Complexity tradeoff (KERNEL-eval-step-cost): the map was `imbl::OrdMap`, a B+ tree whose
// leaves hold 16 entries behind atomic counts. Most environments hold a few names, so a
// binding allocated a whole 16-entry leaf (about 1.2 KB) for an empty environment, or copied
// the leaf with each of its entries for a shared one: about 650 instructions a binding and,
// with dropping the leaves, 15% of a law test (callgrind, law_04). Used: an AVL tree of one
// binding per node behind `Rc` (Adelson-Velsky and Landis 1962; path copying as in Driscoll,
// Sarnak, Sleator and Tarjan 1989): a binding copies the O(log n) nodes on its path, each one
// entry, and updates in place the nodes no other environment shares (`Rc::make_mut`). The
// bounds are those of the B+ tree, O(log n) a binding or lookup and O(1) a copy; the constant
// is smaller for the small environments a run makes, and an environment of many names
// allocates more, smaller nodes per binding (log2 n against log16 n).
pub(super) type Env<'t> = Option<Rc<Node<'t>>>;

/// A node of an [`Env`]: one binding, the names before it to the left and after it to the
/// right, and the height of the tree it roots.
#[derive(Clone)]
pub(super) struct Node<'t> {
    name: &'t str,
    binding: Binding<'t>,
    height: u8,
    left: Env<'t>,
    right: Env<'t>,
}

fn height(env: &Env<'_>) -> u8 {
    env.as_ref().map_or(0, |n| n.height)
}

/// `env` with `name` bound to `binding`, replacing a binding of the same name.
pub(super) fn insert<'t>(env: Env<'t>, name: &'t str, binding: Binding<'t>) -> Env<'t> {
    Some(insert_node(env, name, binding))
}

fn insert_node<'t>(env: Env<'t>, name: &'t str, binding: Binding<'t>) -> Rc<Node<'t>> {
    let Some(mut rc) = env else {
        return Rc::new(Node {
            name,
            binding,
            height: 1,
            left: None,
            right: None,
        });
    };
    let node = Rc::make_mut(&mut rc);
    match name.cmp(node.name) {
        Ordering::Equal => {
            node.binding = binding;
            return rc;
        }
        Ordering::Less => node.left = Some(insert_node(node.left.take(), name, binding)),
        Ordering::Greater => node.right = Some(insert_node(node.right.take(), name, binding)),
    }
    balance(rc)
}

/// Sets the height of `rc`, whose subtrees are balanced and differ in height by at most 2, and
/// rotates it so that they differ by at most 1.
fn balance(mut rc: Rc<Node<'_>>) -> Rc<Node<'_>> {
    let node = Rc::make_mut(&mut rc);
    let (l, r) = (height(&node.left), height(&node.right));
    if l > r + 1 {
        let left = node
            .left
            .as_mut()
            .expect("a left subtree taller than the right");
        let left = Rc::make_mut(left);
        if height(&left.left) < height(&left.right) {
            left.left_rotate();
        }
        node.right_rotate();
    } else if r > l + 1 {
        let right = node
            .right
            .as_mut()
            .expect("a right subtree taller than the left");
        let right = Rc::make_mut(right);
        if height(&right.right) < height(&right.left) {
            right.right_rotate();
        }
        node.left_rotate();
    } else {
        node.height = l.max(r) + 1;
    }
    rc
}

impl<'t> Node<'t> {
    fn fix_height(&mut self) {
        self.height = height(&self.left).max(height(&self.right)) + 1;
    }

    /// Rotates the tree rooted here to the right: the left child's binding moves up here and
    /// this node's binding moves down as its right child.
    fn right_rotate(&mut self) {
        let mut left = self.left.take().expect("a right rotation has a left child");
        let child = Rc::make_mut(&mut left);
        std::mem::swap(&mut self.name, &mut child.name);
        std::mem::swap(&mut self.binding, &mut child.binding);
        // `child` now holds this node's old binding, between the left child's right subtree and
        // this node's right subtree.
        self.left = child.left.take();
        child.left = child.right.take();
        child.right = self.right.take();
        child.fix_height();
        self.right = Some(left);
        self.fix_height();
    }

    /// The mirror of [`Node::right_rotate`].
    fn left_rotate(&mut self) {
        let mut right = self
            .right
            .take()
            .expect("a left rotation has a right child");
        let child = Rc::make_mut(&mut right);
        std::mem::swap(&mut self.name, &mut child.name);
        std::mem::swap(&mut self.binding, &mut child.binding);
        self.right = child.right.take();
        child.right = child.left.take();
        child.left = self.left.take();
        child.fix_height();
        self.left = Some(right);
        self.fix_height();
    }
}

/// The binding of `name` in `env`.
pub(super) fn get<'e, 't>(env: &'e Env<'t>, name: &str) -> Option<&'e Binding<'t>> {
    let mut at = env.as_deref();
    while let Some(node) = at {
        at = match name.cmp(node.name) {
            Ordering::Equal => return Some(&node.binding),
            Ordering::Less => node.left.as_deref(),
            Ordering::Greater => node.right.as_deref(),
        };
    }
    None
}

#[cfg(test)]
mod tests {
    use super::super::{Slot, V};
    use super::*;
    use crate::term::Prim;

    fn b(fact: usize) -> Binding<'static> {
        Binding {
            value: Slot::Is(V::Prim(Prim::Add)),
            fact: Some(fact),
        }
    }

    /// The names of `env` in order, checking on the way that every node is ordered, balanced
    /// and of the height it records.
    fn walk(env: &Env<'static>, out: &mut Vec<(&'static str, usize)>) -> u8 {
        let Some(n) = env else { return 0 };
        let l = walk(&n.left, out);
        out.push((n.name, n.binding.fact.expect("a test binding has a fact")));
        let r = walk(&n.right, out);
        assert!(l.abs_diff(r) <= 1, "unbalanced at {}", n.name);
        assert_eq!(n.height, l.max(r) + 1, "height at {}", n.name);
        n.height
    }

    fn contents(env: &Env<'static>) -> Vec<(&'static str, usize)> {
        let mut out = Vec::new();
        walk(env, &mut out);
        assert!(out.windows(2).all(|w| w[0].0 < w[1].0), "out of order");
        out
    }

    const NAMES: [&str; 12] = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l"];

    #[test]
    fn insertion_in_any_order_keeps_the_tree_ordered_and_balanced() {
        // Ascending, descending and interleaved orders take each rotation and double rotation.
        let orders: [Vec<usize>; 3] = [
            (0..12).collect(),
            (0..12).rev().collect(),
            vec![5, 2, 8, 0, 11, 3, 7, 1, 10, 4, 9, 6],
        ];
        for order in orders {
            let mut env = None;
            for &i in &order {
                env = insert(env, NAMES[i], b(i));
            }
            let want: Vec<_> = (0..12).map(|i| (NAMES[i], i)).collect();
            assert_eq!(contents(&env), want);
            for (i, name) in NAMES.iter().enumerate() {
                assert_eq!(get(&env, name).and_then(|b| b.fact), Some(i));
            }
            assert!(get(&env, "zz").is_none() && get(&env, "").is_none());
            // 12 names fit in an AVL tree of height 4 or 5.
            assert!(height(&env) <= 5);
        }
        assert!(get(&None, "a").is_none());
    }

    #[test]
    fn a_binding_replaces_one_of_its_name_and_leaves_shared_environments_as_they_were() {
        let mut env = None;
        for (i, name) in NAMES.iter().enumerate() {
            env = insert(env, name, b(i));
        }
        let before = env.clone();
        let shadowed = insert(env.clone(), "e", b(100));
        let grown = insert(env, "ee", b(200));
        assert_eq!(get(&shadowed, "e").and_then(|b| b.fact), Some(100));
        assert_eq!(contents(&shadowed).len(), 12);
        assert_eq!(get(&grown, "ee").and_then(|b| b.fact), Some(200));
        assert_eq!(contents(&grown).len(), 13);
        // The shared environment is unchanged by either.
        let want: Vec<_> = (0..12).map(|i| (NAMES[i], i)).collect();
        assert_eq!(contents(&before), want);
    }

    #[test]
    fn many_bindings_stay_logarithmic() {
        let names: Vec<String> = (0..4096).map(|i| format!("x{i:05}")).collect();
        let names: &'static [String] = Box::leak(names.into_boxed_slice());
        let mut env = None;
        for (i, name) in names.iter().enumerate() {
            env = insert(env, name, b(i));
        }
        // An AVL tree of n nodes has height below 1.4405 log2(n + 2).
        assert!(height(&env) <= 17, "height {}", height(&env));
        assert_eq!(get(&env, "x02048").and_then(|b| b.fact), Some(2048));
        assert_eq!(contents(&env).len(), 4096);
    }
}

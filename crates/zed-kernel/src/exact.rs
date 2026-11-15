//! Float reductions that read no evaluation order: the canonical tree (DESIGN.md
//! sec:reduction). An exact float sum is no kernel operation: DESIGN writes it as a `rat` fold
//! rounded once, so the exact accumulator this module once held (DEAD-exact-sum) is gone.

/// A nonempty sequence being reduced on the canonical tree of (sec:reduction), whose shape
/// depends on its length alone: one element is itself; a power-of-two length reduces its two
/// halves; any other length `n`, with `p` the largest power of two dividing `n`, reduces the
/// first `n - p` elements and the last `p`. The left result is always combined with the right.
///
/// The caller drives it: [`CanonicalTree::advance`] asks for one combination, and
/// [`CanonicalTree::give`] hands back its result, so the combining can run anywhere.
pub struct CanonicalTree<T> {
    xs: std::vec::IntoIter<T>,
    todo: Vec<Task>,
    results: Vec<T>,
}

/// What is left to do on a [`CanonicalTree`], last first.
enum Task {
    /// Reduce the next `n` elements.
    Reduce(usize),
    /// Combine the last two results.
    Combine,
}

/// What a [`CanonicalTree`] asks for next.
pub enum TreeStep<T> {
    /// Combine these, left then right, and give back the result.
    Join(T, T),
    /// The reduction is over, with this result.
    Done(T),
}

impl<T> CanonicalTree<T> {
    /// The reduction of `xs`, not yet begun.
    pub fn new(xs: Vec<T>) -> Self {
        assert!(
            !xs.is_empty(),
            "the canonical tree of an empty level is the empty-fold rule's business"
        );
        CanonicalTree {
            todo: vec![Task::Reduce(xs.len())],
            xs: xs.into_iter(),
            results: Vec::new(),
        }
    }

    /// The next combination, or the result when none is left.
    pub fn advance(&mut self) -> TreeStep<T> {
        let pop = |results: &mut Vec<T>| results.pop().expect("a result of the tree");
        while let Some(task) = self.todo.pop() {
            match task {
                Task::Combine => {
                    let right = pop(&mut self.results);
                    return TreeStep::Join(pop(&mut self.results), right);
                }
                Task::Reduce(1) => self
                    .results
                    .push(self.xs.next().expect("an element of the level")),
                Task::Reduce(n) => {
                    let p = 1 << n.trailing_zeros();
                    let split = if p == n { n / 2 } else { n - p };
                    self.todo.push(Task::Combine);
                    self.todo.push(Task::Reduce(n - split));
                    self.todo.push(Task::Reduce(split));
                }
            }
        }
        TreeStep::Done(pop(&mut self.results))
    }

    /// Hands back the result of the combination [`CanonicalTree::advance`] asked for.
    pub fn give(&mut self, result: T) {
        self.results.push(result);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Reduces `xs` on the canonical tree with `op`.
    fn canonical_tree<T: Clone, E>(
        xs: &[T],
        op: &mut impl FnMut(T, T) -> Result<T, E>,
    ) -> Result<T, E> {
        let mut tree = CanonicalTree::new(xs.to_vec());
        loop {
            match tree.advance() {
                TreeStep::Join(a, b) => tree.give(op(a, b)?),
                TreeStep::Done(v) => return Ok(v),
            }
        }
    }

    fn shape(n: usize) -> String {
        let leaves: Vec<String> = (0..n).map(|i| format!("e{i}")).collect();
        canonical_tree(&leaves, &mut |a, b| Ok::<_, ()>(format!("({a} ⊕ {b})"))).unwrap()
    }

    #[test]
    fn canonical_tree_shapes() {
        assert_eq!(shape(1), "e0");
        assert_eq!(shape(3), "((e0 ⊕ e1) ⊕ e2)");
        // The example of (sec:reduction).
        assert_eq!(shape(6), "(((e0 ⊕ e1) ⊕ (e2 ⊕ e3)) ⊕ (e4 ⊕ e5))");
        assert_eq!(shape(7), "((((e0 ⊕ e1) ⊕ (e2 ⊕ e3)) ⊕ (e4 ⊕ e5)) ⊕ e6)");
    }

    #[test]
    fn canonical_tree_depth_is_floor_log_plus_popcount_minus_one() {
        fn depth(n: usize) -> usize {
            let leaves = vec![0usize; n];
            canonical_tree(&leaves, &mut |a: usize, b: usize| Ok::<_, ()>(a.max(b) + 1)).unwrap()
        }
        for n in 1..200usize {
            let expected = n.ilog2() as usize + n.count_ones() as usize - 1;
            assert_eq!(depth(n), expected, "n = {n}");
        }
    }
}

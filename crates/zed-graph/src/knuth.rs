//! The least values of a system of rules `v[node] ≤ add + max(v[children])`, by Knuth's
//! generalization of Dijkstra's algorithm: the least height of a derivation of each nonterminal
//! of a grammar, of each type of the kernel's emptiness search (zed-kernel types/empty.rs
//! `least_height_node`), of each rule of the fuzzer's grammar (zed-tools fuzz.rs `Depths`).
//!
//! D. E. Knuth, "A generalization of Dijkstra's algorithm", Information Processing Letters
//! 6(1), 1-5, 1977, doi:10.1016/0020-0190(77)90002-3, read 2026-11-21 (scanned PDF from LibGen,
//! verification only; Crossref checked 2026-11-20). Sec. 1, p. 1: g is a "superior function if
//! it is monotone nondecreasing in each variable" and g(x_1, ..., x_k) ≥ max(x_1, ..., x_k);
//! `add + max(...)` with `add ≥ 0` is one. Sec. 2 (B), p. 2: with g(x_1, ..., x_k) =
//! max(x_1, ..., x_k) + 1, "m(Y) is the minimum height of a parse tree" of Y. Sec. 3, p. 3, the
//! algorithm: compute v\[Y\] = min g(μ\[X_1\], ..., μ\[X_k\]) over the productions whose parts
//! are all in D, "Choose Y ∉ D such that v\[Y\] is minimum", set μ\[Y\] = v\[Y\], add Y to D;
//! with a priority queue it runs in O(m log n + t) for m productions, n nonterminals and total
//! length t. Sec. 4, p. 3, proves μ\[Y\] = m(Y) at each choice from monotonicity and superiority
//! alone. Departure, the priority-queue form the paper's remark describes: a rule's value is
//! computed once, when its last child is settled (each rule counts the children it still waits
//! on, as Kahn's order counts the edges into a node, zed-graph order.rs), and pushed on the
//! heap; the least popped value of a node not settled settles it, and its later entries are
//! dropped. So each rule and child is handled once, `O(t + m log m)` for the `m` rules (each
//! pushes at most one entry) and their `t` children. Tests: `knuth_settles_least_heights` and
//! `knuth_agrees_with_the_naive_fixed_point` below; empty.rs and fuzz.rs keep their own.

use crate::MinHeap;

/// A child of a rule given to [`Knuth::add_rule`]: one whose least value the caller knows
/// already, or a node of this system still to be settled.
pub enum Child {
    /// A child whose least value, given here, the caller knows already.
    Settled(u64),
    /// A child that is a node of this system, settled by [`Knuth::run`].
    Waits(usize),
}

/// A rule of `node`: `base` is `add` more than the highest child settled so far, `waiting` the
/// children not yet settled.
struct Rule {
    node: usize,
    add: u64,
    base: u64,
    waiting: usize,
}

/// A system of rules over nodes `0..n`, each node's value the least that any of its rules
/// gives, `u64::MAX` for a node no rule derives. The nodes are numbered by the caller and
/// need not be declared: a node named by a rule or by [`Knuth::ready`] is one.
#[derive(Default)]
pub struct Knuth {
    users: Vec<Vec<usize>>,
    rules: Vec<Rule>,
    ready: MinHeap<(u64, usize)>,
}

impl Knuth {
    /// A system with no rule.
    pub fn new() -> Knuth {
        Knuth::default()
    }

    /// A rule that gives `node` the value `value` (a rule with no child).
    pub fn ready(&mut self, node: usize, value: u64) {
        self.ready.push((value, node));
    }

    /// A rule that gives `node` `add` more than the highest of the values of `children`, once
    /// each is settled; a rule with a child of value `u64::MAX` (no derivation) gives none.
    pub fn add_rule(&mut self, node: usize, add: u64, children: impl IntoIterator<Item = Child>) {
        let r = self.rules.len();
        let mut rule = Rule {
            node,
            add,
            base: add,
            waiting: 0,
        };
        for c in children {
            match c {
                Child::Settled(h) => rule.base = rule.base.max(h.saturating_add(add)),
                Child::Waits(i) => {
                    if self.users.len() <= i {
                        self.users.resize_with(i + 1, Vec::new);
                    }
                    self.users[i].push(r);
                    rule.waiting += 1;
                }
            }
        }
        if rule.waiting == 0 && rule.base != u64::MAX {
            self.ready.push((rule.base, node));
        }
        self.rules.push(rule);
    }

    /// The value of each node of `0..n`: the least its rules give, `u64::MAX` when none
    /// derives it. Every node the rules name must be below `n`.
    pub fn run(mut self, n: usize) -> Vec<u64> {
        self.users.resize_with(n.max(self.users.len()), Vec::new);
        let mut height = vec![u64::MAX; n];
        while let Some((h, v)) = self.ready.pop() {
            if height[v] != u64::MAX {
                continue;
            }
            height[v] = h;
            for &r in &self.users[v] {
                let rule = &mut self.rules[r];
                rule.base = rule.base.max(h.saturating_add(rule.add));
                rule.waiting -= 1;
                if rule.waiting == 0 && rule.base != u64::MAX && height[rule.node] == u64::MAX {
                    self.ready.push((rule.base, rule.node));
                }
            }
        }
        height
    }
}

#[cfg(test)]
mod tests {
    use super::{Child, Knuth};

    #[test]
    fn knuth_settles_least_heights() {
        // 0 is a leaf; 1 = 1 + 0; 2 = 1 + max(1, 3) or 1 + 0; 3 waits on itself only.
        let mut k = Knuth::new();
        k.ready(0, 0);
        k.add_rule(1, 1, [Child::Waits(0)]);
        k.add_rule(2, 1, [Child::Waits(1), Child::Waits(3)]);
        k.add_rule(2, 1, [Child::Settled(4)]);
        k.add_rule(3, 1, [Child::Waits(3)]);
        assert_eq!(k.run(4), vec![0, 1, 5, u64::MAX]);
        // A child with no derivation derives nothing.
        let mut k = Knuth::new();
        k.add_rule(0, 0, [Child::Settled(u64::MAX)]);
        assert_eq!(k.run(1), vec![u64::MAX]);
    }

    /// On random systems, the values are those that rounds of every rule reach from
    /// `u64::MAX` (the naive version: a value is lowered only to that of a derivation, and
    /// rounds stop when none is lowered), cycles and rules sharing a node included.
    #[test]
    fn knuth_agrees_with_the_naive_fixed_point() {
        let (mut rng, seed) = crate::seed::Rng::fresh("knuth_agrees_with_the_naive_fixed_point");
        for _ in 0..2000 {
            let n = 1 + rng.below(8);
            let rules: Vec<(usize, u64, Vec<usize>)> = (0..rng.below(3 * n))
                .map(|_| {
                    let kids = (0..rng.below(3)).map(|_| rng.below(n)).collect();
                    (rng.below(n), rng.below(3) as u64, kids)
                })
                .collect();
            let mut want = vec![u64::MAX; n];
            loop {
                let mut changed = false;
                for (v, add, kids) in &rules {
                    let h = kids
                        .iter()
                        .fold(*add, |m, &c| m.max(want[c].saturating_add(*add)));
                    if h < want[*v] {
                        want[*v] = h;
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            let mut k = Knuth::new();
            for (v, add, kids) in &rules {
                k.add_rule(*v, *add, kids.iter().map(|&c| Child::Waits(c)));
            }
            assert_eq!(k.run(n), want, "seed {seed}: rules {rules:?}");
        }
    }
}

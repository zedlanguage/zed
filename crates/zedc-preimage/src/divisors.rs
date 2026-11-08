//! Sets of divisors, as the condition that a term's value is not an atom holds them
//! (`preimage::Defined`, RUNG2-definedness): canonical treaps whose nodes are each made once.
//! A node's priority is a hash of its divisor, so a set has one shape whatever order its
//! divisors were added in, and a node is found by its divisor and its two subtrees before it is
//! made, so equal sets are one node, compared in O(1). A union ([`Sets::union`]) splits one
//! set by the other's root and joins the parts; equal subtrees end it at once, and each pair of
//! sets is joined once, so a union costs O(m log(n/m + 1)) for sets of m ≤ n divisors that
//! share nothing, and O(1) for each subtree the two share.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};

use zedc_presburger::presburger::Lin;

/// A set of divisors: the number of its root node, [`EMPTY`] for none.
pub(crate) type Set = u32;

/// The empty set.
pub(crate) const EMPTY: Set = 0;

/// A node of a treap: a divisor, by its number among the divisors met, and the sets of the
/// divisors before it and after it.
struct Node {
    key: u32,
    size: u32,
    left: Set,
    right: Set,
}

/// The divisors met and the nodes made, each once, and the unions made.
pub(crate) struct Sets {
    /// Each divisor and its priority, by its number.
    keys: Vec<(Lin, u64)>,
    numbers: HashMap<Lin, u32>,
    /// The nodes; the first stands for [`EMPTY`] and is never read.
    nodes: Vec<Node>,
    made: HashMap<(u32, Set, Set), Set>,
    /// Each union by its two sets, the smaller number first.
    unions: HashMap<(Set, Set), Set>,
}

impl Default for Sets {
    fn default() -> Self {
        Sets {
            keys: Vec::new(),
            numbers: HashMap::new(),
            nodes: vec![Node {
                key: 0,
                size: 0,
                left: EMPTY,
                right: EMPTY,
            }],
            made: HashMap::new(),
            unions: HashMap::new(),
        }
    }
}

impl Sets {
    /// The number of the divisor `d`, given it when it is first met. O(the size of `d`).
    fn number(&mut self, d: &Lin) -> u32 {
        if let Some(&k) = self.numbers.get(d) {
            return k;
        }
        let k = self.keys.len() as u32;
        // A hash of fixed keys, so that one set has one shape on every run.
        let priority = BuildHasherDefault::<DefaultHasher>::default().hash_one(d);
        self.keys.push((d.clone(), priority));
        self.numbers.insert(d.clone(), k);
        k
    }

    fn divisor(&self, k: u32) -> &Lin {
        &self.keys[k as usize].0
    }

    fn node(&self, s: Set) -> &Node {
        &self.nodes[s as usize]
    }

    /// The set of the divisor `k` with `left` before it and `right` after it, made once.
    fn make(&mut self, key: u32, left: Set, right: Set) -> Set {
        if let Some(&s) = self.made.get(&(key, left, right)) {
            return s;
        }
        let size = 1 + self.len(left) + self.len(right);
        let s = self.nodes.len() as Set;
        self.nodes.push(Node {
            key,
            size,
            left,
            right,
        });
        self.made.insert((key, left, right), s);
        s
    }

    /// Whether the divisor `a` is above `b` in a treap: the higher priority, ties broken by
    /// the divisors' order, so that every set has one shape.
    fn above(&self, a: u32, b: u32) -> bool {
        let ((x, p), (y, q)) = (&self.keys[a as usize], &self.keys[b as usize]);
        (p, x) > (q, y)
    }

    /// The number of divisors of `s`. O(1).
    pub(crate) fn len(&self, s: Set) -> u32 {
        self.node(s).size
    }

    /// `{d}`.
    pub(crate) fn single(&mut self, d: &Lin) -> Set {
        let k = self.number(d);
        self.make(k, EMPTY, EMPTY)
    }

    /// Whether `s` holds `d`. O(log n) comparisons.
    pub(crate) fn contains(&self, mut s: Set, d: &Lin) -> bool {
        while s != EMPTY {
            let n = self.node(s);
            s = match d.cmp(self.divisor(n.key)) {
                Ordering::Less => n.left,
                Ordering::Greater => n.right,
                Ordering::Equal => return true,
            };
        }
        false
    }

    /// The divisors of `s` before the divisor `k`, whether `s` holds it, and those after it.
    fn split(&mut self, s: Set, k: u32) -> (Set, bool, Set) {
        if s == EMPTY {
            return (EMPTY, false, EMPTY);
        }
        let Node {
            key, left, right, ..
        } = *self.node(s);
        match self.divisor(k).cmp(self.divisor(key)) {
            Ordering::Equal => (left, true, right),
            Ordering::Less => {
                let (l, found, r) = self.split(left, k);
                (l, found, self.make(key, r, right))
            }
            Ordering::Greater => {
                let (l, found, r) = self.split(right, k);
                (self.make(key, left, l), found, r)
            }
        }
    }

    /// The divisors of `a` and of `b`. The root of higher priority is the union's root; the
    /// other set is split by it and each side joined with its side, each pair once. Recursion
    /// as deep as the treaps, O(log n) expected.
    pub(crate) fn union(&mut self, a: Set, b: Set) -> Set {
        if a == b || b == EMPTY {
            return a;
        }
        if a == EMPTY {
            return b;
        }
        let pair = (a.min(b), a.max(b));
        if let Some(&u) = self.unions.get(&pair) {
            return u;
        }
        let (top, other) = match self.above(self.node(a).key, self.node(b).key) {
            true => (a, b),
            false => (b, a),
        };
        let Node {
            key, left, right, ..
        } = *self.node(top);
        let (l, _, r) = self.split(other, key);
        let (l, r) = (self.union(left, l), self.union(right, r));
        let u = self.make(key, l, r);
        self.unions.insert(pair, u);
        u
    }

    /// Calls `f` on each divisor of `s`, in their order. Recursion as deep as the treap.
    pub(crate) fn each(&self, s: Set, f: &mut impl FnMut(&Lin)) {
        if s == EMPTY {
            return;
        }
        let n = self.node(s);
        self.each(n.left, f);
        f(self.divisor(n.key));
        self.each(n.right, f);
    }

    /// The divisors of `s` from `from` up, in order, while `more` holds of them. O(log n) and
    /// the divisors found.
    pub(crate) fn up(&self, s: Set, from: &Lin, more: &impl Fn(&Lin) -> bool, out: &mut Vec<Lin>) {
        self.up_from(s, from, more, out);
    }

    /// [`Sets::up`]; `false` once a divisor fails `more`.
    fn up_from(
        &self,
        s: Set,
        from: &Lin,
        more: &impl Fn(&Lin) -> bool,
        out: &mut Vec<Lin>,
    ) -> bool {
        if s == EMPTY {
            return true;
        }
        let n = self.node(s);
        let d = self.divisor(n.key);
        if d < from {
            return self.up_from(n.right, from, more, out);
        }
        if !self.up_from(n.left, from, more, out) {
            return false;
        }
        if !more(d) {
            return false;
        }
        out.push(d.clone());
        self.up_from(n.right, from, more, out)
    }

    /// The divisors of `s` from `to` down, in reverse order, while `more` holds of them.
    /// O(log n) and the divisors found.
    pub(crate) fn down(&self, s: Set, to: &Lin, more: &impl Fn(&Lin) -> bool, out: &mut Vec<Lin>) {
        self.down_from(s, to, more, out);
    }

    /// [`Sets::down`]; `false` once a divisor fails `more`.
    fn down_from(
        &self,
        s: Set,
        to: &Lin,
        more: &impl Fn(&Lin) -> bool,
        out: &mut Vec<Lin>,
    ) -> bool {
        if s == EMPTY {
            return true;
        }
        let n = self.node(s);
        let d = self.divisor(n.key);
        if d > to {
            return self.down_from(n.left, to, more, out);
        }
        if !self.down_from(n.right, to, more, out) {
            return false;
        }
        if !more(d) {
            return false;
        }
        out.push(d.clone());
        self.down_from(n.left, to, more, out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zedc_presburger::presburger::Atom;

    fn d(i: i64) -> Lin {
        Lin::atom(Atom::Sym("n".into())).plus(&Lin::constant(i))
    }

    fn of(sets: &mut Sets, xs: impl IntoIterator<Item = i64>) -> Set {
        xs.into_iter().fold(EMPTY, |s, i| {
            let one = sets.single(&d(i));
            sets.union(s, one)
        })
    }

    fn listed(sets: &Sets, s: Set) -> Vec<Lin> {
        let mut out = Vec::new();
        sets.each(s, &mut |l| out.push(l.clone()));
        out
    }

    #[test]
    fn a_set_has_one_node_whatever_order_its_divisors_came_in() {
        let mut sets = Sets::default();
        let a = of(&mut sets, 0..50);
        let b = of(&mut sets, (0..50).rev());
        let c = of(&mut sets, (0..50).map(|i| (i * 17) % 50));
        assert_eq!(a, b);
        assert_eq!(a, c);
        assert_eq!(sets.len(a), 50);
        assert_eq!(listed(&sets, a), (0..50).map(d).collect::<Vec<_>>());
        // A divisor added twice is one.
        let one = sets.single(&d(7));
        assert_eq!(sets.union(a, one), a);
    }

    #[test]
    fn a_union_holds_the_divisors_of_both_and_no_other() {
        let mut sets = Sets::default();
        let a = of(&mut sets, (0..40).filter(|i| i % 3 == 0));
        let b = of(&mut sets, (0..40).filter(|i| i % 5 == 0));
        let u = sets.union(a, b);
        let want: Vec<Lin> = (0..40)
            .filter(|i| i % 3 == 0 || i % 5 == 0)
            .map(d)
            .collect();
        assert_eq!(listed(&sets, u), want);
        assert_eq!(
            u,
            of(&mut sets, (0..40).filter(|i| i % 3 == 0 || i % 5 == 0))
        );
        assert_eq!(sets.union(b, a), u);
        assert_eq!(sets.union(u, EMPTY), u);
        assert_eq!(sets.union(EMPTY, u), u);
        for i in 0..40 {
            assert_eq!(sets.contains(u, &d(i)), i % 3 == 0 || i % 5 == 0, "{i}");
        }
        assert!(!sets.contains(EMPTY, &d(0)));
    }

    #[test]
    fn a_search_finds_the_divisors_of_one_variable_part_from_a_bound() {
        let mut sets = Sets::default();
        let m = Lin::atom(Atom::Sym("m".into()));
        let ms = sets.single(&m);
        let ns = of(&mut sets, [-3, -1, 0, 2, 5]);
        let s = sets.union(ns, ms);
        let terms = d(0).terms;
        let same = |l: &Lin| l.terms == terms;
        let mut out = Vec::new();
        sets.up(s, &d(1), &same, &mut out);
        assert_eq!(out, vec![d(2), d(5)]);
        out.clear();
        sets.down(s, &d(-1), &same, &mut out);
        assert_eq!(out, vec![d(-1), d(-3)]);
        out.clear();
        sets.up(s, &d(6), &same, &mut out);
        assert!(out.is_empty());
    }
}

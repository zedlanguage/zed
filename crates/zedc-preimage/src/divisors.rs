//! Sets of divisors, as the condition that a term's value is not an atom holds them
//! (`preimage::Defined`, RUNG2-definedness): canonical treaps whose nodes are each made once.
//! A node's priority is drawn at random once per run from its divisor, so in a run a set has
//! one shape whatever order its divisors were added in, and a node is found by its divisor and
//! its two subtrees before it is made, so equal sets are one node, compared in O(1). A union
//! ([`Sets::union`]) splits one set by the other's root and joins the parts; equal subtrees end
//! it at once, and each pair of sets is joined once, so a union costs O(m log(n/m + 1)) for sets
//! of m ≤ n divisors that share nothing, and O(1) for each subtree the two share.
//!
//! Proof that equal sets are one node (the claim `Defined::meet`, `Defined::arm`,
//! `Shown::arm` and the call keys of `Walk::shared_call_key` in preimage.rs rely on when they
//! compare two `Set`s with `==`). Write `a ≻ b` for [`Sets::above`]: priority first, then the
//! divisors' order, a strict total order on distinct divisors since `numbers` gives each
//! divisor one number and one priority. Invariant: every `Set` made is a treap, its keys in
//! order to the left and right (search order) and its root `≻` every other key of it (heap
//! order). It holds of [`EMPTY`] and of [`Sets::single`]; of [`Sets::split`], whose pieces
//! keep the search order and put `key` above keys of its own old subtree only, so the heap
//! order too; and of [`Sets::union`], whose root `key` is `≻` both roots and so every key of
//! both (heap order of each), and whose two sides are unions of keys below and above `key`.
//! A treap on a set `S` of keys is unique: its root is the `≻`-greatest key of `S`, and its
//! subtrees are the treaps on the keys of `S` before and after it. So, by induction on the
//! size, two `Set`s with the same keys have the same root key and, by the induction
//! hypothesis, the same numbers for their two subtrees, and [`Sets::make`] gives one number
//! for one `(key, left, right)` (`made`). A number is a set only of the `Sets` that made it:
//! each `preimage::Tr` holds one, and every table that holds a number (`Memo::defined`,
//! `Memo::defined_calls`, the third part of a `CallKey`) is filled under that one `Tr`
//! (`Scoped::relation` puts tables back only with the `Tr` they were made under, a new
//! `Tr::new` comes with a new run's empty tables, `Tx::start`, and `Tx::relation` clears them).
//! Tests: `a_set_has_one_node_whatever_order_its_divisors_came_in` (three orders of 50
//! divisors give one number) and `a_union_holds_the_divisors_of_both_and_no_other`; they cannot
//! catch a heap-order break that one of these shapes does not reach.
//!
//! The cost of a union is that of Blelloch and Reid-Miller's treap union (G. E. Blelloch and
//! M. Reid-Miller, "Fast set operations using treaps", SPAA 1998, doi:10.1145/277651.277660;
//! G. E. Blelloch, D. Ferizovic and Y. Sun, "Just join for parallel ordered sets", SPAA 2016,
//! doi:10.1145/2935764.2935768, section 4 and Theorem 4: split one tree at the other's root
//! and join the two recursive unions, `O(m log(n/m + 1))` expected work for sizes `m <= n`).
//! The full citation, how it was checked and the quote are at `zed_kernel::treap_set`'s module
//! comment (the 1998 text was not obtained; the bound is read from the 2016 paper's
//! Theorem 4, whose text was checked). The bound needs the priorities random (`PRIORITIES`, below). The departures: the
//! recursion stops at `a == b` and at a pair met before (`unions`), and both give the
//! union itself, so the calls made are a subset of the cited recursion's, plus a hash lookup
//! for each; and `make` looks each node up before making it, O(1) expected for each.
//! "O(1) for each subtree the two share", in the sense used here: the call on the keys of
//! `a` and `b` in a range of keys returns at once when the two hold the same keys there, so
//! the calls made are at the nodes of the union's treap above a key of one set and not the
//! other. That this count and the splits it makes stay within `O(m log(n/m + 1))` for `m`
//! such keys is Not proved here: it is the cited analysis applied to those paths, which was
//! not checked step by step; the test `ladder::the_conditions_of_shared_divisors_scale`
//! (l01_38_presburger bench) measures the families of RUNG2-definedness at k and 8k.

use std::cmp::Ordering;
use std::collections::HashMap;

use zed_kernel::priority::Priorities;
use zedc_presburger::presburger::Lin;

/// The priorities of the divisors, drawn once per run ([`zed_kernel::priority`]): the run's
/// random polynomial of degree 4 at a random polynomial hash of the divisor's `Hash` stream
/// ([`Priorities::hash`]). A `Lin`'s stream is its terms and constant, so distinct divisors
/// have distinct streams and tie with probability at most `(S + 1)/p` a pair for streams of
/// `S` symbols; the priorities are otherwise 5-wise independent and uniform, and every
/// node's depth is `O(log n)` in expectation for every set of divisors (Seidel and Aragon,
/// "Randomized search trees", Algorithmica 16, 1996, doi:10.1007/BF01940876, Theorem 3.3 and
/// section 6; the full comment and the proof are in module [`zed_kernel::priority`]), where
/// the fixed hash this replaces had no bound for chosen divisors (COMPLEXITY.md K123). A set's
/// number depends on the shape, and so on the draw, and is only compared for equality, never
/// ordered or shown.
static PRIORITIES: Priorities = Priorities::new(5);

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
    /// [`Lin::aux_end`] of the divisors of the set: the largest of its divisor's and its two
    /// subtrees', made with the node, so O(1) (`Sets::aux_end`).
    aux_end: u32,
}

/// The divisors met and the nodes made, each once, and the unions made.
pub(crate) struct Sets {
    /// Each divisor and its priority, by its number.
    keys: Vec<(Lin, u64)>,
    /// [`Lin::aux_end`] of each divisor, by its number, found once when it is numbered.
    aux_ends: Vec<u32>,
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
            aux_ends: Vec::new(),
            numbers: HashMap::new(),
            nodes: vec![Node {
                key: 0,
                size: 0,
                left: EMPTY,
                right: EMPTY,
                aux_end: 0,
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
        let k = zed_collections::index::to_u32(self.keys.len(), "divisors");
        // The run's random priority of `d` (`PRIORITIES`): one set has one shape in a run.
        let priority = PRIORITIES.hash(d);
        self.keys.push((d.clone(), priority));
        self.aux_ends.push(d.aux_end());
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
        let aux_end = (self.aux_ends[key as usize])
            .max(self.aux_end(left))
            .max(self.aux_end(right));
        let s = self.nodes.len() as Set;
        self.nodes.push(Node {
            key,
            size,
            left,
            right,
            aux_end,
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

    /// One more than the largest auxiliary variable a divisor of `s` names, 0 for none
    /// ([`Lin::aux_end`]). Sets are never undone, so a set made before an attempt was undone
    /// may name atoms the undo took away; `Tx::forget` reads this to drop what such a set
    /// keys. O(1).
    pub(crate) fn aux_end(&self, s: Set) -> u32 {
        self.node(s).aux_end
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
    ///
    /// Proof that `out` gets, in order, the divisors `d >= from` of `s` up to the first that
    /// fails `more`, and that the call visits O(depth + found) nodes. The walk is an in-order
    /// walk that skips a node below `from` and its left subtree (all below it, so below `from`)
    /// and stops everything at the first `false`; so it pushes the divisors `>= from` in order
    /// until one fails `more`. A node below `from` is reached only on the search path of
    /// `from` (a right subtree of a pushed node holds only keys above it). A node `>= from` that
    /// is not pushed either fails `more` or waits on a left subtree that returned `false`, so
    /// it is the failing node or one of its ancestors: at most depth + 1 of them. So
    /// `O(depth + found)`, `O(log n)` expected depth (`PRIORITIES`). The callers
    /// (`Defined::shown_nonzero` in preimage.rs) pass a `more` that holds on one run of
    /// consecutive divisors from `from` (one variable part, `Lin`'s order is terms first), so
    /// stopping at the first failure loses nothing. Test:
    /// `a_search_finds_the_divisors_of_one_variable_part_from_a_bound`.
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

    /// [`Sets::down`]; `false` once a divisor fails `more`. The proof of [`Sets::up_from`]
    /// with the order reversed.
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

    /// `Sets::aux_end` of every set made, from singles, unions and the splits they make,
    /// against the largest auxiliary variable its divisors name, listed (PROOF-preimage-forget-callkey).
    #[test]
    fn a_set_knows_the_newest_auxiliary_variable_its_divisors_name() {
        use zedc_presburger::presburger::Factor;
        let mut sets = Sets::default();
        assert_eq!(sets.aux_end(EMPTY), 0);
        // n + i, q_i + 1, and n * q_(2i): no variable, the atom itself, the factor of a product.
        let divisor = |i: u32| match i % 3 {
            0 => d(i64::from(i)),
            1 => Lin::atom(Atom::Aux(i)).plus(&Lin::constant(1)),
            _ => Lin::atom(Atom::product_of(
                Factor::Sym("n".into()),
                Factor::Aux(2 * i),
            )),
        };
        let mut s = EMPTY;
        for i in (0..30).rev() {
            let one = sets.single(&divisor(i));
            s = sets.union(s, one);
            let mut end = 0;
            sets.each(s, &mut |l| end = end.max(l.aux_end()));
            assert_eq!(sets.aux_end(s), end, "after {i}");
        }
        // 29 % 3 == 2: the divisor n * q58.
        assert_eq!(sets.aux_end(s), 59);
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

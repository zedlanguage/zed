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
//! comment. The 1998 text was read 2026-11-21 (PDF, LibGen, verification only): its abstract
//! gives union, intersection and difference of sets of sizes `m <= n` "in expected
//! O(m lg(n/m)) work", and its Theorem 2.4 (sec. 2, p. 21) proves it for union: the work is
//! a sum of split costs, each logarithmic in the part of the larger treap that falls between
//! two keys of the smaller, and the sum of those logarithms is greatest when the `n` keys are
//! spread evenly over the `m + 1` gaps (Lemma 2.2), which gives `O(m lg(n/m))`. The `+ 1`
//! written here keeps the bound positive at `m = n`, where the paper's form reads 0. The
//! bound needs the priorities random (`PRIORITIES`, below).
//! The departures: the recursion stops at `a == b` and at a pair met before (`unions`), and both
//! give the union itself, so the calls made are a subset of the cited recursion's, plus a hash
//! lookup for each; and `make` looks each node up before making it, O(1) expected for each.
//! "O(1) for each subtree the two share", in the sense used here: the call on the keys of
//! `a` and `b` in a range of keys returns at once when the two hold the same keys there, so
//! the calls made are at the nodes of the union's treap above a key of one set and not the
//! other.
//!
//! Proof of that count (PROOF-divisors-shared-subtree-cost). Write `T(S)` for the treap on
//! the keys `S`, unique by the proof above, and `A`, `B` for the keys of `a`, `b`. (1) Every
//! call of the recursion of `union(a, b)` is `union(T(A ∩ I), T(B ∩ I))` for `I` the range of
//! keys of a subtree of `T(A ∪ B)` (all keys at the first call). By induction: the root kept
//! is the `≻`-greatest key of `(A ∪ B) ∩ I`, the root of that subtree; the other set's
//! pieces from [`Sets::split`] are treaps (the invariant above), so they are `T` of their
//! keys and, `make` looking each node up, their numbers are those; and the root's own
//! subtrees are `T` of its keys before and after it. So the two calls below are on the
//! ranges of the two subtrees of that node. (2) A call goes past its first tests only when
//! `T(A ∩ I) != T(B ∩ I)`, so `A ∩ I != B ∩ I` (one set, one number), so `I` holds a key
//! of `A Δ B`; a range of a subtree holds `x` exactly when its root is `x` or above `x`. So
//! the calls that recurse are at most the nodes on the paths from the root of `T(A ∪ B)` to
//! the keys of `A Δ B`, `R <= Σ_{x ∈ A Δ B} (depth(x) + 1)`; each makes two calls, so
//! `1 + 2R` calls in all, and each adds at most one entry to `unions`. With the priorities
//! of `PRIORITIES`, each depth is `O(log |A ∪ B|)` in expectation (Seidel and Aragon, as
//! cited there), so `E[R] = O(k log n)` for `k` keys in `A Δ B` and `n` in `A ∪ B`. (3) A
//! call's split walks `T(other ∩ I)` along the search path of the root key, which is the
//! part in `I` of its search path in `T(B)` or `T(A)`: a key `y` is on the search path of
//! `k` exactly when it is `≻` every key of the set between `y` and `k`, and for `y` and `k`
//! in `I` those keys are the same in the set and in its part in `I`. So a split costs at
//! most `1 +` the height of `T(A)` or `T(B)`. (4) The splits sum to `O(k log n)` expected
//! (proofdoc5f). Take a call that recurses, with root key `r`, the `≻`-greatest key of
//! `(A ∪ B) ∩ I` by (1). If `r` is in both `A` and `B`, it is in the other set's part in
//! `I` and `≻` every key of it, so it is that part's root (heap order), and
//! [`Sets::split`] meets it at its first node and returns (`Ordering::Equal`): one step. If
//! `r` is in `A Δ B`, the split walks the part in `I` of `r`'s search path in the other set,
//! by (3); that path, in `T(B)` for `r` in `A \ B` and in `T(A)` for `r` in `B \ A`, ends
//! at an empty child of its last node, and that node is `r`'s predecessor or successor in
//! that set (an empty child of `y` is reached for `r` only when no key of the set lies
//! between `y` and `r`); every node of a search path is an ancestor of the last, so the path
//! has at most `depth(pred) + depth(succ) + 2` nodes, a depth of a key that does not exist
//! read as 0. Each key is the root of at most one call, since by (1) the calls are at
//! distinct subtrees of `T(A ∪ B)`, a call met again ends at `unions` before its split. So
//! the split steps are at most `R + Σ_{r ∈ A Δ B} (depth(pred(r)) + depth(succ(r)) + 2)`,
//! a bound that holds for every draw of the priorities. Its expectation is a sum of single
//! depths, each `O(log n)` by Seidel and Aragon under the priorities of `PRIORITIES`, so by
//! linearity of expectation, with no independence between `R` and the depths needed,
//! `E[split steps] <= E[R] + 2k·O(log n) = O(k log n)`, and the union's work, `O(1)` per
//! call plus a `make` per split step (one hash lookup each), is `O(k log n)` expected.
//! `O(k log(n/k + 1))` was not proved and is not claimed. Deterministically the work is at
//! most `(1 + 2R)(1 + h)` for `h` the greater height.
//! Tests: `tests::a_union_of_sets_that_differ_in_two_divisors_recurses_only_above_them`
//! checks the bound of (2) on the entries made and the bound of (4) on the split steps
//! (counted under `cfg(test)`), over 32 pairs at `n = 256` and `8n`, and both ratios, under
//! 2 against the `log` ratio 1.375; it cannot show the expectation, which rests on the
//! priorities, and its pairs share all but two keys. The
//! test `ladder::the_conditions_of_shared_divisors_scale` (l01_38_presburger bench) measures
//! the families of RUNG2-definedness at k and 8k.

use std::cmp::Ordering;
use std::collections::HashMap;

use zed_collections::priority::Priorities;
use zed_collections::treap::DEEP;
use zedc_presburger::presburger::Lin;

/// The priorities of the divisors, drawn once per run ([`zed_collections::priority`]): the run's
/// random polynomial of degree 4 at a random polynomial hash of the divisor's `Hash` stream
/// ([`Priorities::hash`]). A `Lin`'s stream is its terms and constant, so distinct divisors
/// have distinct streams and tie with probability at most `(S + 1)/p` a pair for streams of
/// `S` symbols; the priorities are otherwise 5-wise independent and uniform, and every
/// node's depth is `O(log n)` in expectation for every set of divisors (Seidel and Aragon,
/// "Randomized search trees", Algorithmica 16, 1996, doi:10.1007/BF01940876, Theorem 3.3 and
/// section 6; the full comment and the proof are in module [`zed_collections::priority`]), where
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

/// A step of [`Sets::union`].
enum UnionStep {
    /// The union, known at once: one set empty, the sets equal, or the pair met before.
    Known(Set),
    /// The union of `pair` is the divisor `key` over the unions of the pairs `left` and
    /// `right`: the root of higher priority's children, each with its side of the other set.
    Split {
        key: u32,
        pair: (Set, Set),
        left: (Set, Set),
        right: (Set, Set),
    },
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
    /// The nodes [`Sets::split`] has visited, for the test of the cost of a union.
    #[cfg(test)]
    split_steps: u64,
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
            #[cfg(test)]
            split_steps: 0,
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

    /// The divisors of `s` before the divisor `k`, whether `s` holds it, and those after it:
    /// one walk down the search path of `k`, kept on a vector, then the two sides made from the
    /// bottom up, in the order a recursion makes them. A loop, so its depth is not the stack's:
    /// the priorities of a run are random but known to a run that sets `ZED_TREAP_SEED`, and
    /// divisors chosen against them make a path (FAIL-treap-inplace-recursion-depth). Test:
    /// `deep_sets_take_no_deep_recursion`.
    fn split(&mut self, mut s: Set, k: u32) -> (Set, bool, Set) {
        // The nodes passed, as their divisor and the child off the path, and whether `k` is
        // before each.
        let mut path: Vec<(u32, Set, bool)> = Vec::new();
        let (mut l, mut found, mut r) = (EMPTY, false, EMPTY);
        while s != EMPTY {
            #[cfg(test)]
            {
                self.split_steps += 1;
            }
            let Node {
                key, left, right, ..
            } = *self.node(s);
            match self.divisor(k).cmp(self.divisor(key)) {
                Ordering::Equal => {
                    (l, found, r) = (left, true, right);
                    break;
                }
                Ordering::Less => {
                    s = left;
                    path.push((key, right, true));
                }
                Ordering::Greater => {
                    s = right;
                    path.push((key, left, false));
                }
            }
        }
        for (key, off, before) in path.into_iter().rev() {
            if before {
                r = self.make(key, r, off);
            } else {
                l = self.make(key, off, l);
            }
        }
        (l, found, r)
    }

    /// The divisors of `a` and of `b`. The root of higher priority is the union's root; the
    /// other set is split by it and each side joined with its side, each pair once. A
    /// recursion as deep as the treaps, `O(log n)` expected, to [`DEEP`] calls, past which
    /// [`Sets::union_loop`] goes on with the pairs it has reached (the comment at `DEEP`).
    pub(crate) fn union(&mut self, a: Set, b: Set) -> Set {
        self.union_at(a, b, 0)
    }

    /// [`Sets::union`], `depth` calls below the first.
    fn union_at(&mut self, a: Set, b: Set, depth: usize) -> Set {
        if depth >= DEEP {
            return self.union_loop(a, b);
        }
        match self.union_step(a, b) {
            UnionStep::Known(u) => u,
            UnionStep::Split {
                key,
                pair,
                left,
                right,
            } => {
                let (l, r) = (
                    self.union_at(left.0, left.1, depth + 1),
                    self.union_at(right.0, right.1, depth + 1),
                );
                self.union_made(key, pair, l, r)
            }
        }
    }

    /// One step of [`Sets::union`] of `a` and `b`: the union if it is known at once, else the
    /// root's split done.
    fn union_step(&mut self, a: Set, b: Set) -> UnionStep {
        if a == b || b == EMPTY {
            return UnionStep::Known(a);
        }
        if a == EMPTY {
            return UnionStep::Known(b);
        }
        let pair = (a.min(b), a.max(b));
        if let Some(&u) = self.unions.get(&pair) {
            return UnionStep::Known(u);
        }
        let (top, other) = match self.above(self.node(a).key, self.node(b).key) {
            true => (a, b),
            false => (b, a),
        };
        let Node {
            key, left, right, ..
        } = *self.node(top);
        let (l, _, r) = self.split(other, key);
        UnionStep::Split {
            key,
            pair,
            left: (left, l),
            right: (right, r),
        }
    }

    /// The union of the pair `pair`, of root `key` and children `l` and `r`, made and kept.
    fn union_made(&mut self, key: u32, pair: (Set, Set), l: Set, r: Set) -> Set {
        let u = self.make(key, l, r);
        self.unions.insert(pair, u);
        u
    }

    /// [`Sets::union`] by a loop: the steps of the recursion kept on a vector, the unions made
    /// on another, so the same splits, nodes and unions are made in the same order.
    fn union_loop(&mut self, a: Set, b: Set) -> Set {
        enum Step {
            /// The union of a pair, to find.
            Union(Set, Set),
            /// The union of `pair` of root `key`, its two children the last two unions found.
            Made(u32, (Set, Set)),
        }
        let (mut todo, mut done) = (vec![Step::Union(a, b)], Vec::new());
        while let Some(step) = todo.pop() {
            match step {
                Step::Union(a, b) => match self.union_step(a, b) {
                    UnionStep::Known(u) => done.push(u),
                    UnionStep::Split {
                        key,
                        pair,
                        left,
                        right,
                    } => {
                        // The left pair is found first, as in the recursion.
                        todo.push(Step::Made(key, pair));
                        todo.push(Step::Union(right.0, right.1));
                        todo.push(Step::Union(left.0, left.1));
                    }
                },
                Step::Made(key, pair) => {
                    let r = done.pop().expect("the right child's union");
                    let l = done.pop().expect("the left child's union");
                    let u = self.union_made(key, pair, l, r);
                    done.push(u);
                }
            }
        }
        done.pop().expect("the union")
    }

    /// Calls `f` on each divisor of `s`, in their order: an in-order walk by a stack.
    pub(crate) fn each(&self, s: Set, f: &mut impl FnMut(&Lin)) {
        let (mut stack, mut at) = (Vec::new(), s);
        loop {
            while at != EMPTY {
                stack.push(at);
                at = self.node(at).left;
            }
            let Some(s) = stack.pop() else { return };
            let n = self.node(s);
            f(self.divisor(n.key));
            at = n.right;
        }
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
    ///
    /// The walk is a loop: `stack` holds the nodes `>= from` whose left subtree is being
    /// walked, nearest last, so it is the recursion's stack of pending nodes, kept on the heap
    /// (FAIL-treap-inplace-recursion-depth, test `deep_sets_take_no_deep_recursion`). In the
    /// right subtree of a pushed node every divisor is above it, so `>= from`, as in the
    /// recursion.
    fn up_from(
        &self,
        s: Set,
        from: &Lin,
        more: &impl Fn(&Lin) -> bool,
        out: &mut Vec<Lin>,
    ) -> bool {
        let (mut stack, mut at) = (Vec::new(), s);
        loop {
            while at != EMPTY {
                let n = self.node(at);
                if self.divisor(n.key) < from {
                    at = n.right;
                } else {
                    stack.push(at);
                    at = n.left;
                }
            }
            let Some(s) = stack.pop() else { return true };
            let n = self.node(s);
            let d = self.divisor(n.key);
            if !more(d) {
                return false;
            }
            out.push(d.clone());
            at = n.right;
        }
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
        let (mut stack, mut at) = (Vec::new(), s);
        loop {
            while at != EMPTY {
                let n = self.node(at);
                if self.divisor(n.key) > to {
                    at = n.left;
                } else {
                    stack.push(at);
                    at = n.right;
                }
            }
            let Some(s) = stack.pop() else { return true };
            let n = self.node(s);
            let d = self.divisor(n.key);
            if !more(d) {
                return false;
            }
            out.push(d.clone());
            at = n.left;
        }
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

    /// `Sets::aux_end` of every set made, from singles, unions and the splits they make, against
    /// the largest auxiliary variable its divisors name, listed (PROOF-preimage-forget-callkey).
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

    /// PROOF-divisors-shared-subtree-cost. Two sets that share `n` divisors and differ in one
    /// each: the calls of `union` that recurse (each adds one pair to `unions`, or hits it)
    /// are at most the nodes on the paths of the union's treap from its root to the two
    /// divisors not shared, the bound the proof at the module comment gives; and over 32 such
    /// pairs at `n` and `8n` their number grows as those paths, `O(log n)`, not as `n`. The
    /// split steps of those calls (`Sets::split_steps`) are at most the calls plus the search
    /// path of `x` in `b` and of `y` in `a`, the bound of step (4) of that proof, and grow as
    /// those paths too.
    #[test]
    fn a_union_of_sets_that_differ_in_two_divisors_recurses_only_above_them() {
        /// The nodes from the root of `s` down to the divisor `x`, both counted, or down to
        /// an empty subtree when `s` does not hold `x` (its search path).
        fn path(sets: &Sets, mut s: Set, x: &Lin) -> u64 {
            let mut nodes = 0;
            while s != EMPTY {
                nodes += 1;
                let n = sets.node(s);
                s = match x.cmp(sets.divisor(n.key)) {
                    Ordering::Less => n.left,
                    Ordering::Greater => n.right,
                    Ordering::Equal => return nodes,
                };
            }
            nodes
        }
        let (mut calls, mut steps) = (Vec::new(), Vec::new());
        for n in [256i64, 2048] {
            let mut sets = Sets::default();
            let shared = of(&mut sets, (0..n).map(|i| 2 * i));
            let (mut total, mut split_total) = (0, 0);
            for j in 0..32 {
                let (x, y) = (2 * ((j * 37) % n) + 1, 2 * ((j * 53 + 11) % n) + 1);
                let one = sets.single(&d(x));
                let a = sets.union(shared, one);
                let one = sets.single(&d(y));
                let b = sets.union(shared, one);
                let (before, split_before) = (sets.unions.len(), sets.split_steps);
                let u = sets.union(a, b);
                let made = (sets.unions.len() - before) as u64;
                let split = sets.split_steps - split_before;
                let bound = path(&sets, u, &d(x)) + path(&sets, u, &d(y));
                assert!(
                    made <= bound,
                    "n = {n}, {x} and {y}: {made} calls, paths {bound}"
                );
                let split_bound = made + path(&sets, b, &d(x)) + path(&sets, a, &d(y));
                assert!(
                    split <= split_bound,
                    "n = {n}, {x} and {y}: {split} split steps, bound {split_bound}"
                );
                assert_eq!(sets.len(u), n as u32 + 1 + u32::from(x != y));
                total += made;
                split_total += split;
            }
            calls.push(total);
            steps.push(split_total);
        }
        let ratio = calls[1] as f64 / calls[0] as f64;
        let split_ratio = steps[1] as f64 / steps[0] as f64;
        eprintln!(
            "over 32 pairs at n and 8n: unions made {calls:?}, ratio {ratio:.2}; split steps \
             {steps:?}, ratio {split_ratio:.2}"
        );
        assert!(ratio < 2.0, "calls {calls:?}: ratio {ratio:.2} at 8n");
        assert!(
            split_ratio < 2.0,
            "split steps {steps:?}: ratio {split_ratio:.2} at 8n"
        );
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

    /// FAIL-treap-inplace-recursion-depth: a set whose treap is a path of 100,000 divisors, the
    /// priorities the test's (set on the divisors once numbered, as divisors chosen against a
    /// known draw would give), in a thread of a 1 MiB stack, which a recursion one call a node
    /// of the path overflows. A split, a union, `each`, `up` and `down` walk the whole path.
    #[test]
    fn deep_sets_take_no_deep_recursion() {
        std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                const M: i64 = 100_000;
                let mut sets = Sets::default();
                // The set of the divisor `d(i)`, given the priority `priority`.
                let one = |sets: &mut Sets, i: i64, priority: u64| {
                    let k = sets.number(&d(i));
                    sets.keys[k as usize].1 = priority;
                    sets.make(k, EMPTY, EMPTY)
                };
                // `d(2i)` of priority `M - i + 2`: the priorities fall as the divisors rise, so
                // the treap is a path to the right. Each divisor comes in as the new root, the
                // smallest so far, so each union is O(1).
                let mut a = EMPTY;
                for i in (0..M).rev() {
                    let s = one(&mut sets, 2 * i, (M - i + 2) as u64);
                    a = sets.union(a, s);
                }
                let want: Vec<Lin> = (0..M).map(|i| d(2 * i)).collect();
                assert_eq!(sets.len(a), M as u32);
                assert_eq!(listed(&sets, a), want);
                let mut out = Vec::new();
                sets.up(a, &d(0), &|_| true, &mut out);
                assert_eq!(out, want);
                out.clear();
                sets.down(a, &d(2 * M), &|_| true, &mut out);
                assert!(out.iter().eq(want.iter().rev()));
                // A divisor above all, of the highest priority: the union's root, so the path is
                // split by it, every node on the walk.
                let top = one(&mut sets, 2 * M, u64::MAX);
                let v = sets.union(a, top);
                // One set has one node, however made: the divisors put in under `top`, each
                // the new root below it, O(1) each.
                let mut again = top;
                for i in (0..M).rev() {
                    let s = sets.single(&d(2 * i));
                    again = sets.union(again, s);
                }
                assert_eq!(again, v);
                // A divisor of the lowest priority at the bottom of the path: the union walks
                // down to it, one call a node.
                let low = one(&mut sets, 2 * M - 1, 1);
                let w = sets.union(v, low);
                assert_eq!(sets.len(w), M as u32 + 2);
                let mut all = want;
                all.extend([d(2 * M - 1), d(2 * M)]);
                assert_eq!(listed(&sets, w), all);
            })
            .expect("a thread")
            .join()
            .expect("no stack overflow and no failed check");
    }
}

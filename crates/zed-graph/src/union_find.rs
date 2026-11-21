//! Disjoint sets over the numbers `0..n` (union-find), written once for every crate
//! (DRY-union-find-generic).
//!
//! One structure, [`UnionFind`], with each choice made by its caller at [`UnionFind::new`]:
//! - [`Compression`]: what a find does to the path it walks: nothing, halving (each element
//!   passed is pointed at its grandparent) or full compression (each is pointed at the root);
//! - [`Linking`]: which root stays when [`Keep::Rule`] links two classes: the one of higher
//!   rank, or the one of the larger class;
//! - an optional value per class (`V`), held at its root and merged at a union by the
//!   caller's function;
//! - an optional offset per edge (`O`, an [`Offset`]): an element's value as a function of
//!   its parent's, such as `x_v = x_p + d` ([`Diff`]), `x_v = s·x_p + d` with `s` = ±1
//!   ([`Signed`]) or `x_v = x_p xor b` ([`Parity`]). A find also gives the element's value
//!   as a function of its root's, and a union of two elements of one class gives the
//!   relation the class already holds between them.
//!
//! A caller that must choose which root stays (because the root is the class's printed or
//! ordered name) passes [`Keep::First`], [`Keep::Second`] or [`Keep::Least`] in place of
//! [`Keep::Rule`]; the rank or size is still kept, as a guide or for the caller to read
//! ([`UnionFind::size`]). A caller whose parents live in a structure of its own (a record per
//! class, a persistent map) walks them with [`root_of`] over the [`Parents`] trait.
//!
//! Bounds, for m finds and unions on n elements (R. E. Tarjan and J. van Leeuwen,
//! "Worst-case analysis of set union algorithms", JACM 31(2), 245-281, 1984,
//! doi:10.1145/62.2160; read 2026-11-20 in the copy cached by OpenAlex, since the ACM site
//! answered with a challenge page, and again 2026-11-21 in a PDF (LibGen, verification only;
//! title and authors checked on the copy); each quote below was compared with that text):
//! - [`Linking::Rank`] or [`Linking::Size`] with [`Compression::None`]: no path is longer
//!   than log2 n, so a find is O(log n) and the whole O(n + m log n). Corollary 2: "In a
//!   forest built from single nodes by a sequence of links by size, no path has length
//!   exceeding log n"; Lemma 2: "Lemma 1 holds for linking by rank. That is, size(x) ≥
//!   2^rank(x)"; Theorem 2: "With either linking by size or linking by rank, the set union
//!   algorithm runs in O(n + m log n) time in the worst case."
//! - Rank or size with [`Compression::Halving`] or [`Compression::Full`]: O(n + m α(m + n,
//!   n)), α a functional inverse of Ackermann's function. Theorem 3 (p. 258): "The set union
//!   algorithm with either linking by rank or linking by size and either compression,
//!   splitting, or halving runs in O(n + mα(m + n, n)) time and thus is asymptotically
//!   optimal." Its proof for halving counts only every other node of a find path (the
//!   "essential" nodes, exactly those whose parent changes), bounds those by the
//!   multiple-partition charge of Lemma 6 used for compression, and doubles it, since at
//!   least half of each path is essential. The same paper: "Perhaps the best is linking by rank with halving, since it
//!   saves space over linking by size and uses only one pass over each find path." The
//!   matching lower bound is Tarjan's earlier paper ("Efficiency of a good but not linear
//!   set union algorithm", JACM 22(2), 215-225, 1975, doi:10.1145/321879.321884; read
//!   2026-11-20 in the OpenAlex copy): for "a sequence of m ≥ n FINDs and n - 1 intermixed
//!   UNIONs, then k1·mα(m, n) ≤ t(m, n) ≤ k2·mα(m, n)".
//! - Roots chosen by the caller (any [`Keep`] but `Rule`, the paper's "naive linking") with
//!   full compression: Theorem 4, "The set union algorithm with compression and naive
//!   linking runs in O(n + m log_(2+m/n) n) time"; with halving: Theorem 6 (p. 268), "The set
//!   union algorithm with halving and naive union runs in O((n + m) log_(2+m/n)(min{m, n}))
//!   time". For m ≥ n both are O(m log_(1+m/n) n) (Table I, p. 280), which is O(log n) per
//!   operation at worst and O(1) amortized once m ≥ n^(1+ε). Naive linking gives up the
//!   freedom sec. 2 (p. 249) names, "we are free either to make f point to e or to make e
//!   point to f", so the caller picks which root stays.
//! - Roots chosen by the caller with no compression: no bound beyond n per find, the depth
//!   of a chain; a caller that does this says why at its call (a tree it walks itself).
//!
//! The rank is a byte: by Lemma 2 a rank-linked rank is at most log2 n < 64 (the paper:
//! linking by rank "needs only log log n bits per node"); once roots are chosen it is kept
//! saturating at 255, as a guide only. A size is a `usize`, the exact count of the class.
//!
//! Variants measured before the rank-and-halving default of the old `UnionFind` was chosen
//! (DRY-graph-shared, release build, 2,000,000 elements, 4,000,000 unions of random pairs
//! then a find of each, best of 5, at load 30 and 41 on 32 cores): halving with rank 158 and
//! 242 ms; halving with size 335 and 448 ms; halving with no rule (the shape of most of the
//! inline copies this replaced) 461 and 593 ms; full compression in two passes with size 409
//! and 378 ms, with rank 523 and 316 ms, with no rule 1,269 and 683 ms. A rank is one byte,
//! a size a word, so the rank array is an eighth of the memory, which is the likely cause of
//! its lead.
//!
//! Tests: `union_find_classes_match_a_plain_labeling` (every compression and linking, every
//! [`Keep`], against a plain labeling), `offsets_match_plain_values` (each [`Offset`] under
//! each compression), `values_merge_by_the_callers_function`,
//! `rank_and_size_bound_the_height_without_compression` and
//! `a_chosen_root_without_compression_makes_a_chain` (the negative control: a height the rule
//! would have kept at log2 n); `union_find_takes_near_linear_time` and
//! `union_into_a_chain_takes_n_log_n_time` check the growth of the time, which catches a lost
//! rank or halving but cannot tell α from a slowly growing log.

use std::ops::{Add, Sub};

/// What a find does to the path it walks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Compression {
    /// Nothing: the tree keeps its shape, for a caller that walks it itself or reads it
    /// shared.
    None,
    /// Each element passed is pointed at its grandparent: one pass, no stack.
    Halving,
    /// Each element on the path is pointed at the root: two passes, no stack.
    Full,
}

/// Which root stays when [`Keep::Rule`] joins two classes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Linking {
    /// The root of higher rank (on equal ranks, the first element's); a byte per element.
    Rank,
    /// The root of the larger class (on equal sizes, the first element's); a word per
    /// element, and [`UnionFind::size`] reads it.
    Size,
}

/// Which root stays at a union of the classes of `a` and `b`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Keep {
    /// The one [`Linking`] picks.
    Rule,
    /// The root of `a`'s class.
    First,
    /// The root of `b`'s class.
    Second,
    /// The lesser of the two roots, so that, when every union is by this rule, each class's
    /// root is its least element.
    Least,
}

/// An element's value as a function of its parent's, closed under composition and inverse
/// (a group): `compose(f, g)` is `f ∘ g`, the value of `x` from that of `g`'s base when
/// `f` gives `x` from `y` and `g` gives `y` from the base.
pub trait Offset: Clone {
    /// The function that changes nothing.
    fn identity() -> Self;
    /// `self ∘ inner`.
    fn compose(&self, inner: &Self) -> Self;
    /// The function that undoes `self`.
    fn inverse(&self) -> Self;
    /// `self = self ∘ inner`, in place. An offset whose identity is common (most edges of an
    /// alias chain carry `+ 0`) overrides it to skip the work when `inner` is the identity,
    /// which keeps a long walk over such edges free of arithmetic on big numbers (the zero
    /// shortcut the unit union-find of zedc-presburger `modular.rs` had; bench
    /// `pncx_wide_affine_alias_scale`).
    #[inline]
    fn then(&mut self, inner: &Self) {
        *self = self.compose(inner);
    }
}

// The small methods here and of `UnionFind` are `#[inline]`: the workspace builds with
// `lto = "off"` (Cargo.toml), so without it a copy made for a caller's types can land in
// another codegen unit than the caller and is then never inlined. Measured 2026-11-21 before
// this was added: `UnionFind::parent`, `Signed::then`, `union_roots` and
// `find_offset_shared` stood as calls of their own in `pncx_affine_alias_chain_scale`
// (13.49G instructions at n = 320,000 with the hand-written union-find, 14.01G here), and
// `halve` in `union_find_takes_near_linear_time` (141M against 542M at n = 1,600,000).
// `find` and `find_offset` are `#[inline(always)]`: with `#[inline]` alone, `find_offset`
// still stood as a call of its own in `join`, and inlining it took that bench from 210.0M to
// 172.0M.

/// Whether a value is zero, for [`Diff`] and [`Signed`] to skip adding a zero in
/// [`Offset::then`]. A trait of its own because the test `x == T::default()` built a zero,
/// compared and dropped it on every step of a walk: `pncx_affine_alias_chain_scale` took
/// 13.66G instructions at n = 320,000 with it (13.49G with the hand-written union-find).
pub trait IsZero {
    /// Whether `self` is zero.
    fn is_zero(&self) -> bool;
}

macro_rules! is_zero_by_eq {
    ($($t:ty),*) => {$(
        impl IsZero for $t {
            #[inline]
            fn is_zero(&self) -> bool {
                *self == 0
            }
        }
    )*};
}
is_zero_by_eq!(i8, i16, i32, i64, i128, isize);

/// No offset: the plain union-find. Every operation is empty and compiles to nothing.
impl Offset for () {
    #[inline]
    fn identity() -> Self {}
    #[inline]
    fn compose(&self, _: &Self) -> Self {}
    #[inline]
    fn inverse(&self) -> Self {}
}

/// `x_v = x_p + d` in a commutative group whose `+` and `-` are those of `&T` and whose zero
/// is `T::default()` (as the integers are).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Diff<T>(pub T);

impl<T> Offset for Diff<T>
where
    T: Clone + Default + IsZero,
    for<'a> &'a T: Add<&'a T, Output = T> + Sub<&'a T, Output = T>,
{
    #[inline]
    fn identity() -> Self {
        Diff(T::default())
    }
    #[inline]
    fn compose(&self, inner: &Self) -> Self {
        Diff(&self.0 + &inner.0)
    }
    #[inline]
    fn inverse(&self) -> Self {
        Diff(&T::default() - &self.0)
    }
    #[inline(always)]
    fn then(&mut self, inner: &Self) {
        if !inner.0.is_zero() {
            self.0 = &self.0 + &inner.0;
        }
    }
}

/// `x_v = sign·x_p + d` with `sign` = ±1 (`neg` when it is -1), over `T` as for [`Diff`].
/// `(s1, d1) ∘ (s2, d2)` gives `s1·(s2·x + d2) + d1 = (s1·s2)·x + (s1·d2 + d1)`; the
/// inverse of `(s, d)` is `(s, -s·d)`, since `x = s·(y - d)`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Signed<T> {
    /// Whether the sign is -1.
    pub neg: bool,
    /// The constant added after the sign.
    pub d: T,
}

impl<T> Offset for Signed<T>
where
    T: Clone + Default + IsZero,
    for<'a> &'a T: Add<&'a T, Output = T> + Sub<&'a T, Output = T>,
{
    #[inline]
    fn identity() -> Self {
        Signed {
            neg: false,
            d: T::default(),
        }
    }
    #[inline]
    fn compose(&self, inner: &Self) -> Self {
        let d = if self.neg {
            &self.d - &inner.d
        } else {
            &self.d + &inner.d
        };
        Signed {
            neg: self.neg != inner.neg,
            d,
        }
    }
    #[inline]
    fn inverse(&self) -> Self {
        let d = if self.neg {
            self.d.clone()
        } else {
            &T::default() - &self.d
        };
        Signed { neg: self.neg, d }
    }
    #[inline(always)]
    fn then(&mut self, inner: &Self) {
        // (s1, d1) ∘ (s2, d2) = (s1·s2, s1·d2 + d1): with d2 = 0 only the sign changes.
        if !inner.d.is_zero() {
            self.d = if self.neg {
                &self.d - &inner.d
            } else {
                &self.d + &inner.d
            };
        }
        self.neg ^= inner.neg;
    }
}

/// `x_v = x_p xor b` over booleans: a parity, its own inverse.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Parity(pub bool);

impl Offset for Parity {
    #[inline]
    fn identity() -> Self {
        Parity(false)
    }
    #[inline]
    fn compose(&self, inner: &Self) -> Self {
        Parity(self.0 != inner.0)
    }
    #[inline]
    fn inverse(&self) -> Self {
        *self
    }
}

/// Parent links held in a structure of the caller's own (a record per class, a persistent
/// map), walked by [`root_of`].
pub trait Parents {
    /// The parent of `x`; `x` itself at a root.
    fn parent(&self, x: usize) -> usize;
}

/// The root of `x` in `forest`, changing nothing: O(height). The bound on the height is the
/// caller's linking, stated at its call (log2 n when it links by rank or size, Corollary 2
/// of Tarjan and van Leeuwen 1984, quoted at the head of this file).
#[inline]
pub fn root_of<P: Parents + ?Sized>(forest: &P, mut x: usize) -> usize {
    loop {
        let p = forest.parent(x);
        if p == x {
            return x;
        }
        x = p;
    }
}

/// Whether an offset of type `O` carries anything. A value of a zero-sized type holds no
/// data, so every value of it is the same value: `identity()`, and `f.then(g)` leaves `f`
/// equal to `identity()` whatever it computes. A walk may then skip the offsets, and with them
/// the bounds checks and the `split_at_mut` that reading them costs on the empty table. A
/// constant for each `O`, so the branch on it is removed at compile time.
#[inline]
const fn has_offset<O>() -> bool {
    std::mem::size_of::<O>() != 0
}

/// Disjoint sets over `0..len()`, with a value of type `V` per class and an offset of type
/// `O` per edge; the choices and their bounds are at the head of this file.
#[derive(Clone, Debug)]
pub struct UnionFind<V = (), O = ()> {
    /// Each element's parent; a root is its own parent.
    parent: Vec<usize>,
    /// Under [`Linking::Rank`], each root's rank (empty under [`Linking::Size`]).
    rank: Vec<u8>,
    /// Under [`Linking::Size`], each root's class size (empty under [`Linking::Rank`]).
    size: Vec<usize>,
    /// Each element's value as a function of its parent's; the identity at a root.
    off: Vec<O>,
    /// Each root's class value; `V::default()` at an element that is not a root.
    value: Vec<V>,
    compression: Compression,
    linking: Linking,
}

impl<V: Default, O: Offset> UnionFind<V, O> {
    /// The `n` classes `{0}, …, {n - 1}`, each with the value `V::default()`.
    pub fn new(n: usize, compression: Compression, linking: Linking) -> Self {
        // Each table made whole, at its final length, rather than by `n` pushes.
        let (rank, size) = match linking {
            Linking::Rank => (vec![0; n], Vec::new()),
            Linking::Size => (Vec::new(), vec![1; n]),
        };
        UnionFind {
            parent: (0..n).collect(),
            rank,
            size,
            off: std::iter::repeat_with(O::identity).take(n).collect(),
            value: std::iter::repeat_with(V::default).take(n).collect(),
            compression,
            linking,
        }
    }

    /// Adds the element `len()` in a class of its own, with the value `V::default()`, and
    /// returns it.
    #[inline]
    pub fn push(&mut self) -> usize {
        self.push_value(V::default())
    }
}

impl<V, O: Offset> UnionFind<V, O> {
    /// Adds the element `len()` in a class of its own with the value `value`, and returns it.
    #[inline]
    pub fn push_value(&mut self, value: V) -> usize {
        let x = self.parent.len();
        self.parent.push(x);
        match self.linking {
            Linking::Rank => self.rank.push(0),
            Linking::Size => self.size.push(1),
        }
        self.off.push(O::identity());
        self.value.push(value);
        x
    }

    /// The number of elements.
    pub fn len(&self) -> usize {
        self.parent.len()
    }

    /// Whether there is no element.
    pub fn is_empty(&self) -> bool {
        self.parent.is_empty()
    }

    /// The parent of `x` (`x` itself at a root), for a caller that walks the tree itself.
    #[inline]
    pub fn parent(&self, x: usize) -> usize {
        self.parent[x]
    }

    /// The value of `x` as a function of its parent's, for a caller that walks the tree
    /// itself.
    #[inline]
    pub fn edge(&self, x: usize) -> &O {
        &self.off[x]
    }

    /// The size of the class whose root is `root`. Panics unless the linking is
    /// [`Linking::Size`].
    #[inline]
    pub fn size(&self, root: usize) -> usize {
        self.size[root]
    }

    /// The rank of `x`, a bound on the height of its subtree. Panics unless the linking is
    /// [`Linking::Rank`].
    #[inline]
    pub fn rank(&self, x: usize) -> u8 {
        self.rank[x]
    }

    /// The value of the class whose root is `root`.
    #[inline]
    pub fn value(&self, root: usize) -> &V {
        &self.value[root]
    }

    /// The value of the class whose root is `root`, to change.
    #[inline]
    pub fn value_mut(&mut self, root: usize) -> &mut V {
        &mut self.value[root]
    }

    /// The root of `x`'s class, doing to the path what the compression says.
    #[inline(always)]
    pub fn find(&mut self, x: usize) -> usize {
        if let Some(p) = self.root_within_one(x) {
            return p;
        }
        match self.compression {
            Compression::None => self.find_shared(x),
            Compression::Halving => self.halve(x).0,
            Compression::Full => self.compress(x).0,
        }
    }

    /// `x`'s parent when it is a root, so that `x` is the root or one step under it: there
    /// every compression leaves the path as it is, so the find needs no branch on
    /// `self.compression`, and is right whatever the forest. Linking by rank or size keeps
    /// trees low (a root of rank r has at least 2^r elements, Lemmas 1 and 2 of Tarjan and van
    /// Leeuwen 1984, and compression only lowers a tree), so many finds end here; how many is
    /// measured, not proved: with it, `union_find_takes_near_linear_time` took 79.1
    /// instructions an element at n = 1,600,000 against 97.5 without it and 88.3 with the
    /// hand-written union-find it replaced (2026-11-21).
    #[inline(always)]
    fn root_within_one(&self, x: usize) -> Option<usize> {
        let p = self.parent[x];
        (self.parent[p] == p).then_some(p)
    }

    /// The root of `x`'s class and the value of `x` as a function of the root's, doing to
    /// the path what the compression says.
    #[inline(always)]
    pub fn find_offset(&mut self, x: usize) -> (usize, O) {
        if !has_offset::<O>()
            && let Some(p) = self.root_within_one(x)
        {
            return (p, O::identity());
        }
        match self.compression {
            Compression::None => self.find_offset_shared(x),
            Compression::Halving => self.halve(x),
            Compression::Full => self.compress(x),
        }
    }

    /// The root of `x`'s class, changing nothing: O(height), for a caller holding the sets
    /// shared.
    #[inline]
    pub fn find_shared(&self, x: usize) -> usize {
        root_of(self, x)
    }

    /// The root of `x`'s class and the value of `x` as a function of the root's, changing
    /// nothing: O(height).
    #[inline]
    pub fn find_offset_shared(&self, x: usize) -> (usize, O) {
        if !has_offset::<O>() {
            return (self.find_shared(x), O::identity());
        }
        let mut x = x;
        let mut acc = O::identity();
        while self.parent[x] != x {
            acc.then(&self.off[x]);
            x = self.parent[x];
        }
        (x, acc)
    }

    /// Drops the elements `n..len()`. Each kept element's parent must be kept too, which
    /// holds when every union is by [`Keep::Least`] (a parent is then less than its child),
    /// checked in debug builds; for a caller whose elements open and close as a stack. The
    /// linking must be [`Linking::Rank`] (checked in debug builds): a rank bounds the height
    /// of its subtree, and dropping elements only lowers heights, so every kept rank is still
    /// a bound; a size would still count the dropped elements. A value merged into a kept
    /// root from a dropped element stays there.
    pub fn truncate(&mut self, n: usize) {
        debug_assert!(self.linking == Linking::Rank);
        debug_assert!(self.parent[..n.min(self.len())].iter().all(|&p| p < n));
        self.parent.truncate(n);
        self.rank.truncate(n);
        self.size.truncate(n);
        self.off.truncate(n);
        self.value.truncate(n);
    }

    /// Whether `a` and `b` are in one class.
    #[inline]
    pub fn same(&mut self, a: usize, b: usize) -> bool {
        self.find(a) == self.find(b)
    }

    /// Halving: each element passed is pointed at its grandparent, its offset composed with
    /// its parent's (`f_x ∘ f_p`, the value of `x` from the grandparent's), in one pass with
    /// no stack.
    #[inline]
    fn halve(&mut self, mut x: usize) -> (usize, O) {
        if !has_offset::<O>() {
            loop {
                let p = self.parent[x];
                if p == x {
                    return (x, O::identity());
                }
                let g = self.parent[p];
                self.parent[x] = g;
                x = g;
            }
        }
        let mut acc = O::identity();
        loop {
            let p = self.parent[x];
            if p == x {
                return (x, acc);
            }
            let g = self.parent[p];
            if g != p {
                // `off[x] = off[x] ∘ off[p]`, in place: x and p are distinct elements.
                let (lo, hi) = self.off.split_at_mut(x.max(p));
                let (fx, fp) = if x < p {
                    (&mut lo[x], &hi[0])
                } else {
                    (&mut hi[0], &lo[p])
                };
                fx.then(fp);
                self.parent[x] = g;
            }
            acc.then(&self.off[x]);
            x = g;
        }
    }

    /// Full compression in two passes with no stack: the first finds the root and `f`, the
    /// value of `x` from the root's; the second points each element `y` of the path at the
    /// root with `f_y` as its offset, and gets its parent's as `f_p = f_y_old⁻¹ ∘ f_y`
    /// (since `f_y = f_y_old ∘ f_p`).
    #[inline]
    fn compress(&mut self, x: usize) -> (usize, O) {
        let (root, f) = self.find_offset_shared(x);
        if !has_offset::<O>() {
            let mut y = x;
            while y != root {
                let p = self.parent[y];
                self.parent[y] = root;
                y = p;
            }
            return (root, f);
        }
        let mut y = x;
        let mut fy = f.clone();
        while y != root && self.parent[y] != root {
            let p = self.parent[y];
            let old = std::mem::replace(&mut self.off[y], fy.clone());
            self.parent[y] = root;
            fy = old.inverse().compose(&fy);
            y = p;
        }
        (root, f)
    }

    /// Records `x_a = r(x_b)` and joins the classes of `a` and `b`, the root `keep` names
    /// staying, the class values merged by `merge(&mut kept, other, edge)`, with `edge` the
    /// function that gives the value of the root that went under from the value of the root
    /// that stayed (for a class value stated in terms of its root, such as bounds on it).
    /// `Ok(root)` when it joined two classes; `Err(c)` when they were one class already, with
    /// `c` the function that gives `x_a` from `x_b` in the class (equal to `r` exactly when
    /// the record agrees with it), and `merge` not called.
    #[inline]
    pub fn join(
        &mut self,
        a: usize,
        b: usize,
        r: &O,
        keep: Keep,
        merge: impl FnOnce(&mut V, V, &O),
    ) -> Result<usize, O>
    where
        V: Default,
    {
        let (ra, fa) = self.find_offset(a);
        let (rb, fb) = self.find_offset(b);
        if ra == rb {
            // x_a = fa(x_root), x_b = fb(x_root), so x_a = fa(fb⁻¹(x_b)).
            return Err(fa.compose(&fb.inverse()));
        }
        // x_ra = fa⁻¹(x_a) = fa⁻¹(r(x_b)) = fa⁻¹(r(fb(x_rb))).
        let ra_under_rb = fa.inverse().compose(r).compose(&fb);
        Ok(self.link_roots(ra, rb, ra_under_rb, keep, merge))
    }

    /// Joins the classes of the distinct roots `ra` and `rb`, given `x_ra = ra_under_rb(x_rb)`,
    /// the root `keep` names staying, the values merged as by [`UnionFind::join`]; gives the
    /// root that stays. For a caller that found both roots itself and handled the case of one
    /// class in its own way.
    #[inline]
    pub fn union_roots(
        &mut self,
        ra: usize,
        rb: usize,
        ra_under_rb: O,
        keep: Keep,
        merge: impl FnOnce(&mut V, V, &O),
    ) -> usize
    where
        V: Default,
    {
        debug_assert!(ra != rb && self.parent[ra] == ra && self.parent[rb] == rb);
        self.link_roots(ra, rb, ra_under_rb, keep, merge)
    }

    /// [`UnionFind::union_roots`] without its check that `ra` and `rb` are distinct roots, for
    /// [`UnionFind::join`], which has just found them so. Debug assertions are on in the dev
    /// profile the benches run in; this and storing no zero-sized edge in `link`, measured
    /// together, took `union_find_takes_near_linear_time` from 172.0M to 156.0M instructions
    /// at n = 1,600,000 (2026-11-21).
    #[inline]
    fn link_roots(
        &mut self,
        ra: usize,
        rb: usize,
        ra_under_rb: O,
        keep: Keep,
        merge: impl FnOnce(&mut V, V, &O),
    ) -> usize
    where
        V: Default,
    {
        let a_stays = match keep {
            Keep::First => true,
            Keep::Second => false,
            Keep::Least => ra < rb,
            Keep::Rule => match self.linking {
                Linking::Rank => self.rank[ra] >= self.rank[rb],
                Linking::Size => self.size[ra] >= self.size[rb],
            },
        };
        // The edge of `ra` under `rb`, or its inverse, the edge of `rb` under `ra`.
        let (root, child, edge) = if a_stays {
            (ra, rb, ra_under_rb.inverse())
        } else {
            (rb, ra, ra_under_rb)
        };
        self.link(root, child, edge, merge);
        root
    }

    /// Puts the root `child` under the root `root` with `edge` as its offset. The rank
    /// follows the height: the new tree's height is at most `max(height(root),
    /// height(child) + 1)` (saturating at 255, reached only when roots are chosen, since
    /// rank-linked ranks stay under 64, Lemma 2 of Tarjan and van Leeuwen 1984).
    #[inline]
    fn link(&mut self, root: usize, child: usize, edge: O, merge: impl FnOnce(&mut V, V, &O))
    where
        V: Default,
    {
        self.parent[child] = root;
        match self.linking {
            Linking::Rank => {
                let up = self.rank[child].saturating_add(1);
                if self.rank[root] < up {
                    self.rank[root] = up;
                }
            }
            Linking::Size => self.size[root] += self.size[child],
        }
        // The child is no longer a root, so its slot is no longer read: `V::default()` is left
        // there.
        let other = std::mem::take(&mut self.value[child]);
        merge(&mut self.value[root], other, &edge);
        // An offset of zero size holds nothing to store (see `has_offset`).
        if has_offset::<O>() {
            self.off[child] = edge;
        }
    }
}

/// The plain union-find, with no value and no offset.
impl UnionFind {
    /// Joins the classes of `a` and `b`, the root [`Linking`] picks staying; false when they
    /// were one class already.
    #[inline]
    pub fn union(&mut self, a: usize, b: usize) -> bool {
        self.join(a, b, &(), Keep::Rule, |_, _, _| {}).is_ok()
    }

    /// Joins the classes of `keep` and `other` with `keep`'s root as the root of the whole;
    /// false when they were one class already. For a caller whose class names are its roots.
    #[inline]
    pub fn union_into(&mut self, keep: usize, other: usize) -> bool {
        self.join(keep, other, &(), Keep::First, |_, _, _| {})
            .is_ok()
    }

    /// Joins the classes of `a` and `b` with the lesser of their roots as the root
    /// ([`Keep::Least`]); false when they were one class already.
    #[inline]
    pub fn union_least(&mut self, a: usize, b: usize) -> bool {
        self.join(a, b, &(), Keep::Least, |_, _, _| {}).is_ok()
    }
}

impl<V, O: Offset> Parents for UnionFind<V, O> {
    #[inline]
    fn parent(&self, x: usize) -> usize {
        self.parent[x]
    }
}

#[cfg(test)]
mod tests;

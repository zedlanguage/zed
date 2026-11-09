//! The checker's types (step L1.26): a kernel type for the scalars and atoms, structured
//! tuples, function signatures, type variables, and the unknown type `_` of a value no rule
//! has typed yet (a port's lines, a pattern's bound names).
//!
//! A type is a union of pieces: the values of one scalar carrier, the atoms, one tuple shape,
//! one function, one type variable, or the unknown. An operator or a function applies to each
//! combination of its arguments' pieces, so `int | f64` plus `int` is checked as `int + int`
//! and `f64 + int`.

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;

use zed_kernel::frames::{Deep, Stack};
pub use zed_kernel::types::names::{Names, ProgramNames, fresh_name};
use zed_kernel::types::{Refusal, TextPlace, Type as KType, Verdict};
use zed_kernel::value::Digest;
use zed_kernel::{Items, Universe, Value};

use zedc_syntax::lex::Span;

/// A type.
#[derive(Clone, Eq)]
pub struct Ty {
    /// The scalars and atoms, and the kind-wide part: every tuple or every struct as `(..)`
    /// and `{..}` write them (L1.40d), and what narrowing leaves of those. A tuple shape built
    /// from values is in `tuples`, and a function in `fns`.
    pub set: KType,
    /// The tuple shapes, each with its components.
    pub tuples: Vec<Row>,
    /// The functions.
    pub fns: Vec<Arc<Sig>>,
    /// The type variables.
    pub vars: BTreeSet<Arc<str>>,
    /// Whether the type holds the unknown `_`.
    pub dynamic: bool,
    /// The atoms of `set` that are members of a named atom family: data, which `else` keeps
    /// and an operator rejects (sec:failure). The other atoms are loose.
    pub family: KType,
    /// What the payloads of its atoms hold, by atom name: the shapes the atoms were built
    /// with, or `None` where that is not known. The payload of an atom whose name is not
    /// listed is not known.
    pub payloads: BTreeMap<Arc<str>, Option<Vec<Shape>>>,
}

/// The components of a tuple shape, kept in one shared node with what they hold at any depth,
/// found from the components' rows when the row is made. A row is copied in constant time, so
/// a type is copied in the time of its outer level; and a check that walks into tuples reads
/// a row where it would walk into it, so a tuple nested `n` deep costs `O(n)` in all, not
/// `O(n)` at each level.
#[derive(Clone)]
pub struct Row(Arc<RowData>);

struct RowData {
    cs: Vec<Ty>,
    /// The hash of the components.
    digest: u64,
    /// Whether a component holds a type variable or the unknown, outside functions, at any
    /// depth, in payloads too: whether [`Ty::closed`] fails on one.
    open: bool,
    /// Whether a component holds the unknown, outside functions, at any depth, in payloads too.
    dynamic: bool,
    /// The first function, not a family, that a component holds at any depth.
    held: Option<Arc<Sig>>,
    /// The first function, not a family, that a component holds at any depth and no tuple
    /// expression has checked as data: none for a row that [`Self::checked`] says was.
    unchecked: Option<Arc<Sig>>,
    /// Whether no component holds a type variable, a function or a payload, at any depth:
    /// replacing variables keeps the row whole.
    fixed: bool,
    /// Whether every type variable it holds outside functions, at any depth, was checked as
    /// data when the row was made: set only for the row of a tuple expression, whose
    /// components are each checked as data first.
    data: bool,
    /// Whether this row, or the row it was made from by replacing variables, is the row of a
    /// tuple expression: a function it held then was reported at that tuple, and a function
    /// that took the place of a variable since is reported by the variable's data need.
    checked: bool,
    /// The variables a component holds at any depth, inside functions and payloads too: so
    /// replacing variables keeps whole a row that holds none of them, and the variables of a
    /// type are found at the cost of its outer level.
    vars: VarFacts,
    /// The kernel type of the tuple shape ([`Row::kernel`]): none when a component holds a
    /// function, a variable or the unknown at any depth.
    kernel: Option<KType>,
    /// The kernel type of the tuple shape with its atoms' payloads read ([`Ty::exact_data`]):
    /// none where [`Self::kernel`] has none.
    exact: Option<KType>,
    /// The one value of the tuple shape, when each component is one value ([`Ty::point`]).
    point: Option<Value>,
    /// The first kind-wide part, `(..)` or `{..}`, a component holds at any depth outside
    /// functions, in payloads too: a part that may hold a function ([`Ty::held_wide`]).
    wide: Option<KType>,
    /// Whether a component lists no value ([`Ty::lists_nothing`]): the row has no value, and
    /// [`Ty::of_row`] makes the empty type of it.
    void: bool,
    /// Whether a component lists the payloads of an atom at any depth outside functions: when
    /// not, [`Self::exact`] is [`Self::kernel`].
    listed: bool,
    /// Whether a component, at any depth outside functions, in payloads too, holds the atoms
    /// of every name it does not list ([`Ty::open_atoms`]).
    open_atoms: bool,
    /// The class of each component and its value where it is one value ([`class`]), and what
    /// is read from them to file the row, found the first time the row is filed
    /// ([`Row::keys`]) and kept.
    keys: std::sync::OnceLock<Keys>,
}

impl Row {
    /// The row of `cs`.
    pub fn new(cs: Vec<Ty>) -> Row {
        Row::made(cs, false, false)
    }

    /// The row of `cs`, each checked as data.
    pub fn of_data(cs: Vec<Ty>) -> Row {
        Row::made(cs, true, true)
    }

    /// The row of `cs`, which took the place of this row's components when variables were
    /// replaced: its variables' data needs are met anew, and a function it holds is reported
    /// as this row's would be.
    fn replaced(&self, cs: Vec<Ty>) -> Row {
        Row::made(cs, false, self.0.checked)
    }

    fn made(cs: Vec<Ty>, data: bool, checked: bool) -> Row {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        let digest = BuildHasherDefault::<DefaultHasher>::default().hash_one(&cs);
        // Each component's rows and payload shapes keep what they hold at any depth, so this
        // reads the components' outer levels.
        let open = cs.iter().any(|c| !c.closed());
        let dynamic = cs.iter().any(Ty::holds_unknown);
        let held = cs.iter().find_map(|c| c.held_function().cloned());
        let unchecked = match checked {
            true => None,
            false => cs.iter().find_map(|c| c.unchecked_function().cloned()),
        };
        let mut vars = VarFacts::default();
        cs.iter().for_each(|c| vars.ty(c));
        let fixed = cs.iter().all(|c| {
            c.vars.is_empty()
                && c.fns.is_empty()
                && c.payloads.is_empty()
                && c.tuples.iter().all(|r| r.0.fixed)
        });
        // Each component's kernel type reads the kernel types its rows keep, so it costs the
        // component's outer level. A row that holds a variable or the unknown has none.
        let kernel = match open {
            true => None,
            false => (cs.iter().map(Ty::kernel))
                .collect::<Option<Vec<_>>>()
                .map(KType::tuple),
        };
        // A row with no payload listed at any depth reads no payload, so its exact kernel
        // type is its kernel type, made once.
        let listed = cs
            .iter()
            .any(|c| !c.payloads.is_empty() || c.tuples.iter().any(|r| r.0.listed));
        let exact = match (&kernel, listed) {
            (None, _) => None,
            (Some(k), false) => Some(k.clone()),
            (Some(_), true) => (cs.iter().map(Ty::exact_data))
                .collect::<Option<Vec<_>>>()
                .map(KType::tuple),
        };
        // Each component's rows keep their own, so this reads the components' outer levels.
        let point = (cs.iter().map(Ty::point))
            .collect::<Option<Vec<_>>>()
            .map(Value::tuple);
        let wide = cs.iter().find_map(Ty::held_wide);
        let open_atoms = cs.iter().any(Ty::open_atoms);
        // Complexity tradeoff: as in `KType::tuple`, only a component that lists no value
        // makes the row void; one that only the kernel's search proves empty keeps the row.
        // Why: the search costs up to the size of the component per row made; this is O(1)
        // per component. Trigger: a component empty by a meet or recursion. Tests:
        // `l01_26_type_resolution::never::a_tuple_with_an_empty_component_is_never`.
        // COMPLEXITY.md C34.
        let void = cs.iter().any(Ty::lists_nothing);
        Row(Arc::new(RowData {
            cs,
            digest,
            open,
            dynamic,
            held,
            unchecked,
            fixed,
            data,
            checked,
            vars,
            kernel,
            exact,
            point,
            wide,
            void,
            listed,
            open_atoms,
            keys: std::sync::OnceLock::new(),
        }))
    }

    /// The kernel type of the tuple shape, `(t1, …, tn)` of its components' kernel types
    /// ([`Ty::kernel`]), or none when a component holds a function, a variable or the unknown
    /// at any depth. Made with the row, from the kernel types the components' rows keep, so
    /// each row's is made once, whatever the paths to it: `d(positional x) = (x, x)` called
    /// `n` times nested gives `n` rows each holding the one below twice, `2^n` paths, which a
    /// walk into the components took `2^n` time for at each call (TUPLE-eq-dup).
    fn kernel(&self) -> Option<KType> {
        self.0.kernel.clone()
    }

    /// Whether a component holds one of the variables `binds` replaces, at any depth, inside
    /// functions and payloads too.
    fn holds_any(&self, binds: &Binds) -> bool {
        self.0.vars.holds_any(binds)
    }

    /// Whether a component holds a type variable or the unknown, outside functions, at any
    /// depth, in payloads too.
    pub fn open(&self) -> bool {
        self.0.open
    }

    /// Whether a component holds the unknown, outside functions, at any depth, in payloads too.
    pub fn dynamic(&self) -> bool {
        self.0.dynamic
    }

    /// Whether every type variable it holds outside functions was checked as data when the
    /// row was made.
    pub fn data(&self) -> bool {
        self.0.data
    }

    /// Its address: the same for each path to a shared row, so a walk visits it once.
    pub fn addr(&self) -> *const () {
        Arc::as_ptr(&self.0).cast()
    }

    /// The class of each component and its value where it is one value ([`class`]), by which
    /// tuples are filed ([`Holders`], [`Groups`], [`Choices`]). Found once per row, the first
    /// time it is asked for, and kept: filing a row again, in another walk or against another
    /// type, reads them instead of working out each component's class from its set again,
    /// which cost about 17,000 instructions a tuple of two components (TY-row-class). Filing a
    /// tuple of two components now costs about 8.4k to 9.7k instructions the first time and 1.9k
    /// to 2.9k after, the same from 16 to 4,096 tuples: the filings are hash maps (TY-row-hash).
    fn keys(&self) -> &Keys {
        self.0
            .keys
            .get_or_init(|| Keys::new(self.0.cs.iter().map(class).collect()))
    }

    /// The components, to change.
    pub fn to_vec(&self) -> Vec<Ty> {
        self.0.cs.clone()
    }
}

impl std::ops::Deref for Row {
    type Target = [Ty];
    fn deref(&self) -> &[Ty] {
        &self.0.cs
    }
}

impl<'a> IntoIterator for &'a Row {
    type Item = &'a Ty;
    type IntoIter = std::slice::Iter<'a, Ty>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.cs.iter()
    }
}

impl FromIterator<Ty> for Row {
    fn from_iter<I: IntoIterator<Item = Ty>>(it: I) -> Row {
        Row::new(it.into_iter().collect())
    }
}

impl PartialEq for Row {
    /// Compares the components as [`Ty`]'s `==` does, with no stack as deep as the row: two
    /// equal rows built apart share no node, and a comparison that recursed once a level
    /// overflowed an 8 MiB stack a few tens of thousands of levels deep (ROW-eq-deep).
    fn eq(&self, other: &Row) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || {
            let mut lazy = Lazy::default();
            let equal = self.0.alike(&other.0)
                && (self.0.cs.iter().zip(&other.0.cs)).all(|(a, b)| outer(&mut lazy, a, b));
            lazy.rest(equal)
        }
    }
}

impl RowData {
    /// Whether it and `other` have equal hashes and as many components: what [`Row`]'s `==`
    /// checks before it compares the components.
    #[inline]
    fn alike(&self, other: &RowData) -> bool {
        self.digest == other.digest && self.cs.len() == other.cs.len()
    }
}

impl PartialEq for Ty {
    /// Compares the two types at their outer level, and the rows, payload shapes and functions
    /// they hold with a `Same`, made only for a pair of these that is not one node: with no
    /// stack as deep as the types, and, for types that hold none, the common case, as cheaply
    /// as the derived `==` did. Inlined, as the derived `==` was, so a caller in another crate
    /// compares the outer level without a call.
    #[inline]
    fn eq(&self, other: &Ty) -> bool {
        let mut lazy = Lazy::default();
        let equal = outer(&mut lazy, self, other);
        lazy.rest(equal)
    }
}

impl std::hash::Hash for Ty {
    /// Hashes each part in turn; a row, payload shape or signature by the hash it keeps.
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        let Ty {
            set,
            tuples,
            fns,
            vars,
            dynamic,
            family,
            payloads,
        } = self;
        set.hash(h);
        tuples.hash(h);
        fns.hash(h);
        vars.hash(h);
        dynamic.hash(h);
        family.hash(h);
        payloads.hash(h);
    }
}

impl Ty {
    /// Whether it holds a row, a payload shape or a function, which `==` descends into.
    fn holds_nodes(&self) -> bool {
        !self.tuples.is_empty()
            || !self.fns.is_empty()
            || (!self.payloads.is_empty() && self.payloads.values().any(Option::is_some))
    }
}

/// A comparison of two types, two rows, two payload shapes or two signatures, which needs no
/// stack as deep as the types: `==` on types nested as deep as the program.
///
/// Each type is compared at its outer level, and the pairs of components of the rows, shapes
/// and signatures it holds are compared by recursion while the thread's stack has room
/// ([`Same::room`]); where it has none, they are pushed on `left`, to be compared once the
/// recursion has returned. Shallow types, the common case, are so compared as a plain
/// recursion compares them, with nothing pushed and no allocation.
///
/// Two nodes, one from each side, are assumed equal once their pair is met, and the pairs of
/// nodes found equal so are kept as classes in a union-find (Hopcroft and Karp's test of
/// equivalence): a pair whose nodes are already in one class is not compared again. Each pair
/// of recorded nodes compared joins two classes, so at most one is compared for each node, and
/// the comparison costs the size of the two types as graphs, not as trees: two types each
/// holding `n` nodes and `2^n` paths, built apart, cost `O(n)`. The assumption holds: if every
/// pair met is found equal at its outer level, the classes relate only equal nodes, as the
/// types hold no cycles; and a pair that differs makes `==` false.
///
/// A node is known by its address. Every node it records is reachable from the two operands
/// `==` borrows, so none is freed, and no address is reused, while the comparison runs.
///
/// A pair of nodes neither of which is shared (one owner each, `Arc::strong_count` 1) is not
/// recorded, so a comparison of types built once and never shared allocates no table. The cost
/// stays linear: an unshared node is reached only through its one owner, so it is compared once
/// each time the nearest recorded node above it is; each recorded node is compared again only
/// when its pair joins two classes, and the joins form a forest over the recorded nodes, so each
/// join can be charged to a node of its own (its child end), which pays for the unshared nodes
/// below it, each of which lies below one recorded node only. The records only save work: they
/// are never needed for the answer, as the types hold no cycles.
///
/// A function counts as unshared in the same way when its other owners are only the rows and
/// shapes on the path to it, which keep it as their held or unchecked function (`above`,
/// [`Same::shared_sigs`]): those are not met again below it, so a function held once, in a
/// type built once, is not recorded either.
#[derive(Default)]
struct Same<'a> {
    /// The lowest stack address the recursion descends from ([`Same::room`]), set when it first
    /// descends; 0 before.
    floor: usize,
    /// The pairs of types left to compare, pushed where the stack had no room.
    left: Vec<(&'a Ty, &'a Ty)>,
    /// The union-find forest, by address: for each node met, the node it was joined to, or
    /// itself, and, for the root of a class, the number of nodes in it. One table, so the
    /// first node recorded costs one allocation.
    ids: HashMap<*const (), (*const (), usize), std::hash::BuildHasherDefault<AddressHasher>>,
    /// The functions the rows and shapes on the path to the pair now compared keep as held or
    /// unchecked, on the left and on the right ([`Same::shared_sigs`]).
    above: [Above; 2],
}

/// The stack [`Same`]'s recursion may take, from where it first descends: a small part of the
/// 2 MiB a thread is given by default, so the caller and what the comparison calls at its
/// deepest (`==` on scalar types, sets of variables and payload maps) keep the rest.
const SAME_STACK: usize = 128 << 10;

impl<'a> Same<'a> {
    /// Whether the pairs left, and those they push, are each equal.
    fn rest(mut self) -> bool {
        // A pair pushed is compared away from its path.
        self.above = Default::default();
        while let Some((a, b)) = self.left.pop() {
            if !outer(&mut self, a, b) {
                return false;
            }
        }
        true
    }

    /// Whether either of `x` and `y` has another owner, so the comparison may meet it again.
    fn shared<T>(x: &Arc<T>, y: &Arc<T>) -> bool {
        Arc::strong_count(x) > 1 || Arc::strong_count(y) > 1
    }

    /// Whether either of the signatures `x` and `y` has an owner other than the type that
    /// holds it and the rows and shapes on the path to it that keep it as held or unchecked.
    /// Those rows and shapes keep the first function they hold, so a signature in a row is
    /// never alone; counted as shared, each would be recorded, and a comparison of types that
    /// hold functions and share no node would allocate a table. A signature no other node owns
    /// is met only through the type that holds it, as an unshared row is.
    fn shared_sigs(&self, x: &Arc<Sig>, y: &Arc<Sig>) -> bool {
        let [l, r] = self.above;
        Arc::strong_count(x) > 1 + l.keeping(x) || Arc::strong_count(y) > 1 + r.keeping(y)
    }

    /// `then` run with `above` set for a pair under rows or shapes whose held and unchecked
    /// functions are `x` on the left and `y` on the right, and restored after.
    #[inline]
    fn under(
        &mut self,
        x: [&Option<Arc<Sig>>; 2],
        y: [&Option<Arc<Sig>>; 2],
        then: impl FnOnce(&mut Self) -> bool,
    ) -> bool {
        let [l, r] = self.above;
        self.above = [l.under(x), r.under(y)];
        let equal = then(self);
        self.above = [l, r];
        equal
    }

    /// Whether the signatures `x` and `y` are equal, field by field in the order the derived
    /// `==` took; the types of their arrows are compared by [`Same::descend`]. Their needs are
    /// compared by `==` on each type they hold, each comparison a `Same` of its own: a need's
    /// types are variables of the signature, or the types of a call's arguments, which nest
    /// only as deep as the call's text. `facts` is a cache, equal to any other.
    fn sig(&mut self, x: &'a Sig, y: &'a Sig) -> bool {
        let Sig {
            params,
            arrows,
            bounds,
            data,
            word,
            needs,
            own,
            held,
            named,
            facts: _,
        } = x;
        *params == y.params
            && arrows.len() == y.arrows.len()
            && (arrows.iter().zip(&y.arrows)).all(|(p, q)| {
                p.params.len() == q.params.len()
                    && self.descend(
                        (p.params.iter().zip(&q.params)).chain([(&p.result, &q.result)]),
                    )
            })
            && *bounds == y.bounds
            && *data == y.data
            && *word == y.word
            // No needs, the common case, and the slice compare is not free.
            && ((needs.is_empty() && y.needs.is_empty()) || *needs == y.needs)
            && *own == y.own
            && *held == y.held
            && *named == y.named
    }

    /// Whether each of `pairs` is equal, or, for a pair whose left type holds a row, shape or
    /// function and where the stack has no room ([`Same::room`]), may be: such a pair is
    /// pushed on `left`. A pair whose left type holds none is compared now, as that pushes
    /// nothing.
    fn descend(&mut self, pairs: impl IntoIterator<Item = (&'a Ty, &'a Ty)>) -> bool {
        match self.room() {
            true => pairs.into_iter().all(|(a, b)| outer(self, a, b)),
            false => pairs.into_iter().all(|(a, b)| match a.holds_nodes() {
                true => {
                    self.left.push((a, b));
                    true
                }
                false => outer(self, a, b),
            }),
        }
    }

    /// Whether the stack has room to recurse a level deeper: whether the address of this frame
    /// lies above `floor`, [`SAME_STACK`] below where the recursion first descended.
    // Complexity tradeoff: none is given up. Whether a pair is compared by recursion or pushed
    // on `left` changes where it is compared, never the answer or the order of growth, which
    // is linear in the size of the two types as graphs either way; each pair pushed is compared
    // by `rest`, from the top of the stack again. Recursion is the faster: it keeps a shallow
    // type, the common case, as cheap to compare as the derived `==` was
    // (l01_26_type_resolution deep_types::shallow_types_compare_as_cheaply_as_a_plain_recursion).
    // The switch is on the stack the recursion has taken, which bounds it whatever the types'
    // depth: types 100,000 deep compare on a 2 MiB stack
    // (types_built_apart_100000_deep_compare_on_a_2_mib_stack). The stack the thread has left
    // is not read: the crates that read it (`stacker`, `libc`) cannot be linked into this
    // dylib as well as into the test binaries. COMPLEXITY F118.
    #[inline]
    fn room(&mut self) -> bool {
        let mark = 0u8;
        let here = std::ptr::addr_of!(mark) as usize;
        if self.floor == 0 {
            self.floor = here.saturating_sub(SAME_STACK).max(1);
        }
        here > self.floor
    }

    /// Whether the rows `x` and `y`, two nodes found alike, are already in one class, or equal
    /// in each component.
    fn alike_rows(&mut self, x: &'a Row, y: &'a Row) -> bool {
        let (x, y) = (&x.0, &y.0);
        (Self::shared(x, y) && self.assumed(Arc::as_ptr(x).cast(), Arc::as_ptr(y).cast()))
            || match x.held.is_some() {
                // A row that holds no function, the common case, keeps none.
                false => self.descend(x.cs.iter().zip(&y.cs)),
                true => self.under([&x.held, &x.unchecked], [&y.held, &y.unchecked], |s| {
                    s.descend(x.cs.iter().zip(&y.cs))
                }),
            }
    }

    /// Whether the payload shapes `x` and `y`, two nodes found alike, are already in one
    /// class, or equal in each component and field.
    fn alike_shapes(&mut self, x: &'a Shape, y: &'a Shape) -> bool {
        (Self::shared(&x.0, &y.0)
            && self.assumed(Arc::as_ptr(&x.0).cast(), Arc::as_ptr(&y.0).cast()))
            || {
                let named = std::cell::Cell::new(true);
                let (x, y) = (&x.0, &y.0);
                let equal = match x.held.is_some() {
                    false => self.descend(x.pairs(y, &named)),
                    true => self.under([&x.held, &x.unchecked], [&y.held, &y.unchecked], |s| {
                        s.descend(x.pairs(y, &named))
                    }),
                };
                equal && named.get()
            }
    }

    /// Whether the nodes at `x` and `y`, two nodes at least one of them shared, are already in
    /// one class; if not, their classes are joined, so the caller compares them now and no
    /// later pair does again.
    fn assumed(&mut self, x: *const (), y: *const ()) -> bool {
        let (i, j) = (self.root(x), self.root(y));
        if i == j {
            return true;
        }
        // Union by size, the smaller class under the larger.
        let (si, sj) = (self.ids[&i].1, self.ids[&j].1);
        let (small, large) = match si < sj {
            true => (i, j),
            false => (j, i),
        };
        self.ids.insert(small, (large, si.min(sj)));
        self.ids.insert(large, (large, si + sj));
        false
    }

    /// The root of the class of the node at `x`, which is met here first if it is new; the
    /// path to it is halved.
    fn root(&mut self, x: *const ()) -> *const () {
        let mut up = self.ids.entry(x).or_insert((x, 1)).0;
        let mut i = x;
        while up != i {
            let above = self.ids[&up].0;
            self.ids.insert(i, (above, 0));
            i = above;
            up = self.ids[&i].0;
        }
        i
    }
}

/// How [`outer`] compares the rows, payload shapes and functions two types hold.
trait Nodes<'a> {
    /// Whether the rows `x` and `y` are equal, or, where the comparison is put off, may be.
    fn row(&mut self, x: &'a Row, y: &'a Row) -> bool;
    /// Whether the payload shapes `x` and `y` are equal, or may be.
    fn shape(&mut self, x: &'a Shape, y: &'a Shape) -> bool;
    /// Whether the functions `x` and `y` are equal, or may be.
    fn func(&mut self, x: &'a Arc<Sig>, y: &'a Arc<Sig>) -> bool;
}

/// Whether `a` and `b` are equal at their outer level, field by field in the order the derived
/// `==` took, and in the rows, payload shapes and functions they hold, which `n` compares.
#[inline]
fn outer<'a>(n: &mut impl Nodes<'a>, a: &'a Ty, b: &'a Ty) -> bool {
    let Ty {
        set,
        tuples,
        fns,
        vars,
        dynamic,
        family,
        payloads,
    } = a;
    *set == b.set
        && tuples.len() == b.tuples.len()
        && (tuples.iter().zip(&b.tuples)).all(|(x, y)| n.row(x, y))
        && fns.len() == b.fns.len()
        && (fns.iter().zip(&b.fns)).all(|(x, y)| n.func(x, y))
        && *vars == b.vars
        && *dynamic == b.dynamic
        && *family == b.family
        && payloads.len() == b.payloads.len()
        // An empty map is the common case, and its iterator is not free.
        && (payloads.is_empty()
            || (payloads.iter().zip(&b.payloads)).all(|((k, x), (l, y))| {
                k == l
                    && match (x, y) {
                        (Some(x), Some(y)) => {
                            x.len() == y.len() && x.iter().zip(y).all(|(p, q)| n.shape(p, q))
                        }
                        (None, None) => true,
                        (Some(_), None) | (None, Some(_)) => false,
                    }
            }))
}

/// How `==` starts: a pair of rows, payload shapes or functions that is one node is equal, and
/// the first pair that is not makes the [`Same`] that compares it and the rest. Most types
/// the checker compares hold none, and no `Same` is made for them.
#[derive(Default)]
struct Lazy<'a>(Option<Same<'a>>);

impl<'a> Lazy<'a> {
    /// The `Same`, made now if it was not.
    fn same(&mut self) -> &mut Same<'a> {
        self.0.get_or_insert_with(Same::default)
    }

    /// Whether `equal`, what the comparison found before the pairs the `Same` put off, holds,
    /// and those pairs are each equal. It takes the `Lazy`, so no path drops it apart.
    #[inline]
    fn rest(self, equal: bool) -> bool {
        match self.0 {
            None => equal,
            // Nothing was put off unless the types are deep, so the call is skipped.
            Some(same) => equal && (same.left.is_empty() || same.rest()),
        }
    }
}

impl<'a> Nodes<'a> for Lazy<'a> {
    // Inlined into a caller in another crate, with `Ty`'s `==`: the checks that settle the
    // common pairs, one node or two that differ, take no call.
    #[inline]
    fn row(&mut self, x: &'a Row, y: &'a Row) -> bool {
        Arc::ptr_eq(&x.0, &y.0) || (x.0.alike(&y.0) && self.same().alike_rows(x, y))
    }

    #[inline]
    fn shape(&mut self, x: &'a Shape, y: &'a Shape) -> bool {
        Arc::ptr_eq(&x.0, &y.0) || (x.0.alike(&y.0) && self.same().alike_shapes(x, y))
    }

    #[inline]
    fn func(&mut self, x: &'a Arc<Sig>, y: &'a Arc<Sig>) -> bool {
        Arc::ptr_eq(x, y) || self.same().func(x, y)
    }
}

impl<'a> Nodes<'a> for Same<'a> {
    /// One node, already in one class, or alike and equal in each component.
    fn row(&mut self, x: &'a Row, y: &'a Row) -> bool {
        Arc::ptr_eq(&x.0, &y.0) || (x.0.alike(&y.0) && self.alike_rows(x, y))
    }

    /// One node, already in one class, or alike and equal in each component and field.
    fn shape(&mut self, x: &'a Shape, y: &'a Shape) -> bool {
        Arc::ptr_eq(&x.0, &y.0) || (x.0.alike(&y.0) && self.alike_shapes(x, y))
    }

    /// One node, already in one class, or equal as signatures ([`Same::sig`]).
    fn func(&mut self, x: &'a Arc<Sig>, y: &'a Arc<Sig>) -> bool {
        Arc::ptr_eq(x, y)
            || (self.shared_sigs(x, y)
                && self.assumed(Arc::as_ptr(x).cast(), Arc::as_ptr(y).cast()))
            || self.sig(x, y)
    }
}

/// On one side of a [`Same`], the function the row or shape just above the pair compared keeps
/// as held, by address, and how many references to it the rows and shapes in a run up to it
/// keep, as held or as unchecked: owners of a signature the comparison may meet that lie on its
/// path. A row's held function is the first its components hold, so the rows keeping a
/// function lie on the paths to it; each counted is a node of the path, and a run counts no
/// more references than there are. A function kept as unchecked only is not counted, and is
/// so taken for shared, which costs a record, never the answer.
#[derive(Clone, Copy, Default)]
struct Above {
    at: usize,
    run: usize,
}

impl Above {
    /// The same under a row or shape that keeps `held` and `unchecked`.
    #[inline]
    fn under(self, [held, unchecked]: [&Option<Arc<Sig>>; 2]) -> Above {
        let addr = |s: &Option<Arc<Sig>>| s.as_ref().map_or(0, |s| Arc::as_ptr(s).addr());
        let at = addr(held);
        let refs = usize::from(at != 0) + usize::from(at != 0 && addr(unchecked) == at);
        Above {
            at,
            run: refs + if at == self.at { self.run } else { 0 },
        }
    }

    /// How many references to `s` the rows and shapes it counts keep.
    #[inline]
    fn keeping(self, s: &Arc<Sig>) -> usize {
        if Arc::as_ptr(s).addr() == self.at {
            self.run
        } else {
            0
        }
    }
}

/// The hasher of [`Same`]'s table of nodes by address: one folded multiply of the address.
#[derive(Default)]
struct AddressHasher(u64);

impl std::hash::Hasher for AddressHasher {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.write_usize(usize::from(b));
        }
    }

    fn write_usize(&mut self, x: usize) {
        let p = u128::from(self.0 ^ x as u64) * 0x9e37_79b9_7f4a_7c15;
        self.0 = (p as u64) ^ ((p >> 64) as u64);
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

impl Eq for Row {}

impl Drop for RowData {
    /// Drops the components on a stack of its own: a type nests as deep as the program, and the
    /// drop glue would recurse once per level, through tuples, functions and payloads. A row or
    /// signature another type still holds is left to it.
    fn drop(&mut self) {
        let sigs = [self.held.take(), self.unchecked.take()];
        drop_types(std::mem::take(&mut self.cs), sigs.into_iter().flatten());
    }
}

impl std::hash::Hash for Row {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        h.write_u64(self.0.digest);
    }
}

impl fmt::Debug for Row {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_debug(Dbg::Row(self), f)
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_debug(Dbg::Ty(self), f)
    }
}

impl fmt::Debug for Sig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_debug(Dbg::Sig(self), f)
    }
}

/// A part of the `Debug` text of a type ([`write_debug`]).
enum Dbg<'a> {
    /// Text written as it is.
    Text(&'static str),
    /// A part that holds no type, written by its own `Debug`.
    Leaf(&'a dyn fmt::Debug),
    Ty(&'a Ty),
    Row(&'a Row),
    Shape(&'a Shape),
    Sig(&'a Sig),
    Need(&'a Need),
}

/// Writes `start` as a derived `Debug` writes it on one line, for `{:#?}` too. A type nests as
/// deep as the program, and the derived `Debug` recursed once a level (100,000 levels overflowed
/// a 2 MiB stack), so the writing keeps its own stack, as [`write_parts`] does: each part
/// expands to the parts it is made of, pushed so that they pop in order.
fn write_debug(start: Dbg, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut stack = vec![start];
    let mut parts = Vec::new();
    while let Some(d) = stack.pop() {
        match d {
            Dbg::Text(s) => f.write_str(s)?,
            Dbg::Leaf(x) => write!(f, "{x:?}")?,
            Dbg::Ty(t) => debug_ty(t, &mut parts),
            Dbg::Row(r) => debug_list(&mut parts, "[", r.iter(), "]", |p, t| p.push(Dbg::Ty(t))),
            Dbg::Shape(s) => {
                parts.push(Dbg::Text("Shape { items: "));
                debug_list(&mut parts, "[", &s.items, "]", |p, t| p.push(Dbg::Ty(t)));
                parts.push(Dbg::Text(", fields: "));
                debug_map(&mut parts, &s.fields);
                parts.push(Dbg::Text(" }"));
            }
            Dbg::Sig(s) => debug_sig(s, &mut parts),
            Dbg::Need(n) => debug_need(n, &mut parts),
        }
        stack.extend(parts.drain(..).rev());
    }
    Ok(())
}

/// Pushes `open`, the parts `each` pushes for each of `items`, separated by commas, and
/// `close`.
fn debug_list<'a, T>(
    parts: &mut Vec<Dbg<'a>>,
    open: &'static str,
    items: impl IntoIterator<Item = T>,
    close: &'static str,
    mut each: impl FnMut(&mut Vec<Dbg<'a>>, T),
) {
    parts.push(Dbg::Text(open));
    for (i, x) in items.into_iter().enumerate() {
        if i > 0 {
            parts.push(Dbg::Text(", "));
        }
        each(parts, x);
    }
    parts.push(Dbg::Text(close));
}

/// Pushes the parts of a map of names to types.
fn debug_map<'a>(parts: &mut Vec<Dbg<'a>>, m: &'a BTreeMap<Arc<str>, Ty>) {
    debug_list(parts, "{", m, "}", |p, (k, t)| {
        p.extend([Dbg::Leaf(k), Dbg::Text(": "), Dbg::Ty(t)]);
    });
}

fn debug_ty<'a>(t: &'a Ty, parts: &mut Vec<Dbg<'a>>) {
    let Ty {
        set,
        tuples,
        fns,
        vars,
        dynamic,
        family,
        payloads,
    } = t;
    parts.extend([
        Dbg::Text("Ty { set: "),
        Dbg::Leaf(set),
        Dbg::Text(", tuples: "),
    ]);
    debug_list(parts, "[", tuples, "]", |p, r| p.push(Dbg::Row(r)));
    parts.push(Dbg::Text(", fns: "));
    debug_list(parts, "[", fns, "]", |p, s| p.push(Dbg::Sig(s)));
    parts.extend([
        Dbg::Text(", vars: "),
        Dbg::Leaf(vars),
        Dbg::Text(", dynamic: "),
        Dbg::Leaf(dynamic),
        Dbg::Text(", family: "),
        Dbg::Leaf(family),
        Dbg::Text(", payloads: "),
    ]);
    debug_list(parts, "{", payloads, "}", |p, (k, shapes)| {
        p.extend([Dbg::Leaf(k), Dbg::Text(": ")]);
        match shapes {
            None => p.push(Dbg::Text("None")),
            Some(shapes) => {
                p.push(Dbg::Text("Some("));
                debug_list(p, "[", shapes, "]", |p, s| p.push(Dbg::Shape(s)));
                p.push(Dbg::Text(")"));
            }
        }
    });
    parts.push(Dbg::Text(" }"));
}

fn debug_sig<'a>(s: &'a Sig, parts: &mut Vec<Dbg<'a>>) {
    let Sig {
        params,
        arrows,
        bounds,
        data,
        word,
        needs,
        own,
        held,
        named,
        facts,
    } = s;
    parts.extend([
        Dbg::Text("Sig { params: "),
        Dbg::Leaf(params),
        Dbg::Text(", arrows: "),
    ]);
    debug_list(parts, "[", arrows, "]", |p, a| {
        p.push(Dbg::Text("Arrow { params: "));
        debug_list(p, "[", &a.params, "]", |p, t| p.push(Dbg::Ty(t)));
        p.extend([Dbg::Text(", result: "), Dbg::Ty(&a.result), Dbg::Text(" }")]);
    });
    parts.extend([
        Dbg::Text(", bounds: "),
        Dbg::Leaf(bounds),
        Dbg::Text(", data: "),
        Dbg::Leaf(data),
        Dbg::Text(", word: "),
        Dbg::Leaf(word),
        Dbg::Text(", needs: "),
    ]);
    debug_list(parts, "[", needs, "]", |p, n| p.push(Dbg::Need(n)));
    parts.extend([
        Dbg::Text(", own: "),
        Dbg::Leaf(own),
        Dbg::Text(", held: "),
        Dbg::Leaf(held),
        Dbg::Text(", named: "),
        Dbg::Leaf(named),
        Dbg::Text(", facts: "),
        Dbg::Leaf(facts),
        Dbg::Text(" }"),
    ]);
}

/// Pushes the parts of a need. A kind that holds no type is written by its derived `Debug`;
/// each is named, so that a kind added with a type is written here.
fn debug_need<'a>(n: &'a Need, parts: &mut Vec<Dbg<'a>>) {
    parts.extend([
        Dbg::Text("Need { on: "),
        Dbg::Ty(&n.on),
        Dbg::Text(", kind: "),
    ]);
    match &n.kind {
        NeedKind::Component { i, key } => parts.extend([
            Dbg::Text("Component { i: "),
            Dbg::Leaf(i),
            Dbg::Text(", key: "),
            Dbg::Ty(key),
            Dbg::Text(" }"),
        ]),
        NeedKind::Index(t) => parts.extend([Dbg::Text("Index("), Dbg::Ty(t), Dbg::Text(")")]),
        NeedKind::Call {
            what,
            positional,
            named,
            curry,
        } => {
            parts.extend([Dbg::Text("Call { what: "), Dbg::Leaf(what)]);
            parts.push(Dbg::Text(", positional: "));
            debug_list(parts, "[", positional, "]", |p, t| p.push(Dbg::Ty(t)));
            parts.push(Dbg::Text(", named: "));
            debug_list(parts, "[", named, "]", |p, (k, t)| {
                p.extend([
                    Dbg::Text("("),
                    Dbg::Leaf(k),
                    Dbg::Text(", "),
                    Dbg::Ty(t),
                    Dbg::Text(")"),
                ]);
            });
            parts.extend([Dbg::Text(", curry: "), Dbg::Leaf(curry), Dbg::Text(" }")]);
        }
        NeedKind::Into { what, ty } => parts.extend([
            Dbg::Text("Into { what: "),
            Dbg::Leaf(what),
            Dbg::Text(", ty: "),
            Dbg::Ty(ty),
            Dbg::Text(" }"),
        ]),
        NeedKind::Narrow(Narrow::Not(t)) => {
            parts.extend([Dbg::Text("Narrow(Not("), Dbg::Ty(t), Dbg::Text("))")]);
        }
        NeedKind::Order {
            what,
            word,
            other,
            first,
        } => parts.extend([
            Dbg::Text("Order { what: "),
            Dbg::Leaf(what),
            Dbg::Text(", word: "),
            Dbg::Leaf(word),
            Dbg::Text(", other: "),
            Dbg::Ty(other),
            Dbg::Text(", first: "),
            Dbg::Leaf(first),
            Dbg::Text(" }"),
        ]),
        k @ (NeedKind::Destructure { .. }
        | NeedKind::Data(_)
        | NeedKind::Payload { .. }
        | NeedKind::Narrow(Narrow::Loose | Narrow::Atom(_))
        | NeedKind::NoInt(_)
        | NeedKind::Sum
        | NeedKind::InDomain { .. }) => parts.push(Dbg::Leaf(k)),
    }
    parts.push(Dbg::Text(", result: "));
    match &n.result {
        None => parts.push(Dbg::Text("None")),
        Some(t) => parts.extend([Dbg::Text("Some("), Dbg::Ty(t), Dbg::Text(")")]),
    }
    parts.extend([Dbg::Text(", span: "), Dbg::Leaf(&n.span), Dbg::Text(" }")]);
}

/// The payload an atom was built with, kept in one shared node with what it holds at any depth,
/// as a [`Row`] is: a shape is copied in constant time, so a type is copied in the time of its
/// outer level; and a walk that would enter a payload reads what the shape keeps instead, so
/// `n` atoms nested directly in atoms cost `O(n)` in all, not `O(n)` at each level
/// (ATOM-nested-sq).
#[derive(Clone)]
pub struct Shape(Arc<ShapeData>);

/// What a [`Shape`] holds.
pub struct ShapeData {
    /// Its components, by position.
    pub items: Vec<Ty>,
    /// Its fields, by name.
    pub fields: BTreeMap<Arc<str>, Ty>,
    /// The hash of the components and fields.
    digest: u64,
    /// Whether a component or field holds a type variable or the unknown, outside functions,
    /// at any depth, in payloads too.
    open: bool,
    /// Whether a component or field holds the unknown, outside functions, at any depth, in
    /// payloads too.
    dynamic: bool,
    /// The first function, not a family, that a component or field holds at any depth.
    held: Option<Arc<Sig>>,
    /// The first function, not a family, that a component or field holds at any depth and no
    /// tuple expression has checked as data.
    unchecked: Option<Arc<Sig>>,
    /// Whether no component or field holds a type variable or a function at any depth:
    /// replacing variables, or settling them, keeps the shape whole.
    fixed: bool,
    /// The variables its components and fields hold at any depth, inside functions and
    /// payloads too.
    vars: VarFacts,
    /// The payload as a kernel type, with its atoms' payloads read: a tuple of its items.
    /// None when it has fields, which only a normal form with a mark of their names tells
    /// apart ([`Forms`]), or when a component holds a function, a variable or the unknown at
    /// any depth.
    exact: Option<KType>,
    /// The first kind-wide part a component or field holds at any depth outside functions.
    wide: Option<KType>,
    /// Whether a component or field, at any depth outside functions, holds the atoms of every
    /// name it does not list ([`Ty::open_atoms`]).
    open_atoms: bool,
    /// Whether a component or field lists no value ([`Ty::lists_nothing`]): no atom has this
    /// payload, and [`Ty::atom_of`] and the rebuilding walk leave it out.
    void: bool,
}

impl std::ops::Deref for Shape {
    type Target = ShapeData;
    fn deref(&self) -> &ShapeData {
        &self.0
    }
}

impl PartialEq for Shape {
    /// Compares the components and fields as a row does.
    fn eq(&self, other: &Shape) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || {
            let mut lazy = Lazy::default();
            let named = std::cell::Cell::new(true);
            let equal = self.0.alike(&other.0)
                && (self.0.pairs(&other.0, &named)).all(|(a, b)| outer(&mut lazy, a, b))
                && named.get();
            lazy.rest(equal)
        }
    }
}

impl ShapeData {
    /// Whether it and `other` have equal hashes and as many components and fields: what
    /// [`Shape`]'s `==` checks before it compares the components and fields.
    #[inline]
    fn alike(&self, other: &ShapeData) -> bool {
        self.digest == other.digest
            && self.items.len() == other.items.len()
            && self.fields.len() == other.fields.len()
    }

    /// Its components and fields, each paired with the one in the same place in `other`, up
    /// to the first field whose name differs, where `named` is set false.
    fn pairs<'a: 'b, 'b>(
        &'a self,
        other: &'a ShapeData,
        named: &'b std::cell::Cell<bool>,
    ) -> impl Iterator<Item = (&'a Ty, &'a Ty)> + 'b {
        let fields = (self.fields.iter().zip(&other.fields)).map_while(|((k, x), (l, y))| {
            let same = k == l;
            named.set(same);
            same.then_some((x, y))
        });
        (self.items.iter().zip(&other.items)).chain(fields)
    }
}

impl Eq for Shape {}

impl std::hash::Hash for Shape {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        h.write_u64(self.0.digest);
    }
}

impl fmt::Debug for Shape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_debug(Dbg::Shape(self), f)
    }
}

impl Drop for ShapeData {
    /// Drops the components and fields on a stack of their own, as a row does: payloads
    /// nest as deep as the program.
    fn drop(&mut self) {
        let mut stack = std::mem::take(&mut self.items);
        stack.extend(std::mem::take(&mut self.fields).into_values());
        drop_types(
            stack,
            [self.held.take(), self.unchecked.take()]
                .into_iter()
                .flatten(),
        );
    }
}

/// Drops the types `tys` and the signatures `sigs` on stacks of their own: the rows,
/// signatures and payload shapes no other type holds are opened and what they hold pushed,
/// the function a row or shape keeps as held and the signature a signature was settled into
/// among it, so dropping a type nested `n` deep needs no recursion `n` deep.
fn drop_types(mut tys: Vec<Ty>, sigs: impl IntoIterator<Item = Arc<Sig>>) {
    let mut sigs: Vec<Arc<Sig>> = sigs.into_iter().collect();
    loop {
        if let Some(s) = sigs.pop() {
            if let Some(mut s) = Arc::into_inner(s) {
                s.take_parts(&mut tys, &mut sigs);
            }
            continue;
        }
        let Some(mut t) = tys.pop() else { break };
        for r in std::mem::take(&mut t.tuples) {
            if let Some(mut d) = Arc::into_inner(r.0) {
                tys.append(&mut d.cs);
                sigs.extend([d.held.take(), d.unchecked.take()].into_iter().flatten());
            }
        }
        sigs.append(&mut t.fns);
        for s in std::mem::take(&mut t.payloads)
            .into_values()
            .flatten()
            .flatten()
        {
            if let Some(mut d) = Arc::into_inner(s.0) {
                tys.append(&mut d.items);
                tys.extend(std::mem::take(&mut d.fields).into_values());
                sigs.extend([d.held.take(), d.unchecked.take()].into_iter().flatten());
            }
        }
    }
}

impl Drop for Sig {
    /// Drops its arrows, needs and settled signature on a stack of their own, as a row does:
    /// a function type nests functions as deep as the program, and the drop glue would recurse
    /// once per level through `Arc<Sig>` (8,000 nested lambdas overflowed a 2 MiB stack).
    fn drop(&mut self) {
        let (mut tys, mut sigs) = (Vec::new(), Vec::new());
        self.take_parts(&mut tys, &mut sigs);
        drop_types(tys, sigs);
    }
}

impl Sig {
    /// Moves the types and signatures it holds to `tys` and `sigs`, for [`drop_types`]: the
    /// types of its arrows and needs, and the signature it was settled into.
    fn take_parts(&mut self, tys: &mut Vec<Ty>, sigs: &mut Vec<Arc<Sig>>) {
        for a in std::mem::take(&mut self.arrows) {
            tys.extend(a.params);
            tys.push(a.result);
        }
        tys.extend(
            std::mem::take(&mut self.needs)
                .into_iter()
                .flat_map(Need::into_tys),
        );
        sigs.extend(self.facts.1.take());
    }
}

impl Shape {
    /// The payload of `items` by position and `fields` by name.
    ///
    /// What it keeps of its components and fields is read from their outer levels, and from
    /// what their rows and shapes keep, so it costs the size of their outer levels.
    pub fn new(items: Vec<Ty>, fields: BTreeMap<Arc<str>, Ty>) -> Shape {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        let digest = BuildHasherDefault::<DefaultHasher>::default().hash_one((&items, &fields));
        let cs = || items.iter().chain(fields.values());
        let open = cs().any(|c| !c.closed());
        let dynamic = cs().any(Ty::holds_unknown);
        let fixed = cs().all(|c| {
            c.vars.is_empty()
                && c.fns.is_empty()
                && c.tuples.iter().all(|r| r.0.fixed)
                && c.payload_shapes().all(|s| s.fixed)
        });
        let held = cs().find_map(|c| c.held_function().cloned());
        let unchecked = cs().find_map(|c| c.unchecked_function().cloned());
        let mut vars = VarFacts::default();
        cs().for_each(|c| vars.ty(c));
        // Each component's exact kernel type reads what its rows and shapes keep, so this
        // costs the outer levels of the components.
        let exact = match open || held.is_some() || !fields.is_empty() {
            true => None,
            false => (items.iter().map(Ty::exact_kernel))
                .collect::<Option<Vec<_>>>()
                .map(KType::tuple),
        };
        let wide = cs().find_map(Ty::held_wide);
        let open_atoms = cs().any(Ty::open_atoms);
        let void = cs().any(Ty::lists_nothing);
        Shape(Arc::new(ShapeData {
            items,
            fields,
            digest,
            held,
            unchecked,
            open,
            dynamic,
            fixed,
            vars,
            exact,
            wide,
            open_atoms,
            void,
        }))
    }

    /// Whether a component or field holds one of the variables `binds` replaces, at any depth,
    /// inside functions and payloads too.
    fn holds_any(&self, binds: &Binds) -> bool {
        self.0.vars.holds_any(binds)
    }

    /// Whether a component or field holds a type variable or the unknown, outside functions,
    /// at any depth.
    pub fn open(&self) -> bool {
        self.0.open
    }

    /// The address of what it holds, which only tells one shared shape from another.
    pub fn as_ptr(&self) -> *const ShapeData {
        Arc::as_ptr(&self.0)
    }

    /// What it holds at `slot`, if it has that place.
    pub fn at(&self, slot: &Slot) -> Option<&Ty> {
        match slot {
            Slot::Field(n) => self.fields.get(n),
            Slot::Item(i) => self.items.get(*i),
        }
    }

    /// Pushes the parts of the text of the type of the atom `#name` with this payload to
    /// `parts`, in order: `#name(int, f: String)`.
    fn parts<'a>(&'a self, name: &'a str, parts: &mut Vec<Print<'a>>) {
        parts.push(Print::Text("#"));
        parts.push(Print::Text(name));
        parts.push(Print::Text("("));
        let n = self.items.len() + self.fields.len();
        let mut first = true;
        for (i, t) in self.items.iter().enumerate() {
            between(parts, &mut first, ", ");
            let at = PrintAt::item(i + 1 < n);
            // The family of an `#errs` is written bare, `#errs(#a | #b ->? #a | #b)`.
            match &t.fns[..] {
                [s] if name == "errs" && s.is_family() && *t == Ty::func(s.clone()) => {
                    parts.push(Print::Family(s, at));
                }
                _ => parts.push(Print::Ty(t, at)),
            }
        }
        for (i, (f, t)) in self.fields.iter().enumerate() {
            between(parts, &mut first, ", ");
            parts.push(Print::Text(f));
            parts.push(Print::Text(": "));
            let at = PrintAt::item(self.items.len() + i + 1 < n);
            parts.push(Print::Ty(t, at));
        }
        parts.push(Print::Text(")"));
    }
}

/// The payloads of the union of the types `ts`: each name's shapes, once each, and a name some
/// type may hold an unknown payload of is not known. That is found in one union of what of
/// each type's scalars and atoms its payloads do not describe, so the join costs one pass over
/// the types and their shapes.
fn join_payloads(ts: &[&Ty]) -> BTreeMap<Arc<str>, Option<Vec<Shape>>> {
    let mut out: BTreeMap<Arc<str>, Option<Vec<Shape>>> = BTreeMap::new();
    let mut seen: HashSet<(&str, &Shape)> = HashSet::new();
    let mut rest = Vec::new();
    for t in ts {
        let listed = t
            .payloads
            .keys()
            .map(|n| KType::atom_with(n, &KType::top()));
        rest.push(&t.set - &KType::union_all(listed));
        for (n, ss) in &t.payloads {
            let entry = out.entry(n.clone()).or_insert_with(|| Some(Vec::new()));
            match (entry, ss) {
                (entry, None) => *entry = None,
                (Some(have), Some(ss)) => {
                    have.extend(ss.iter().filter(|s| seen.insert((n, s))).cloned());
                }
                (None, Some(_)) => {}
            }
        }
    }
    let rest = KType::union_all(rest);
    for (n, ss) in out.iter_mut() {
        if holds_payload(&rest, n) {
            *ss = None;
        }
    }
    out
}

/// Whether `set` may hold an atom named `n` with a payload.
fn holds_payload(set: &KType, n: &str) -> bool {
    !(set & &KType::atom_with(n, &KType::top())).is_empty()
}

/// A value no program writes, one for each `name`: the bare atom of a name that starts with
/// a NUL, which no atom written has. Marks of two names are apart. The normal form of payloads
/// and tuples ([`Forms`]) puts one where a payload's fields end and one for each function
/// compared, and takes the marks out of each component that holds the atoms of every name it
/// does not list ([`Forms::cut`]), so only the same mark holds a mark.
///
/// Not a function of the kernel, which no component holds either: the kernel builds no value
/// of a function type in a union of payloads, so `#a(x: 0, f: (int) -> int) | … <: #a(x: int,
/// f: (int) -> String)` was refused for want of a value, and that search grew as `n^1.6`.
fn mark(name: &str) -> KType {
    KType::atom(name)
}

/// The name of the mark of the field names of a payload with fields, in name order.
fn fields_mark(fields: &BTreeMap<Arc<str>, Ty>) -> String {
    let mut name = String::from("\u{0}fields");
    for f in fields.keys() {
        name.push(' ');
        name.push_str(f);
    }
    name
}

/// The kernel type of a payload of the components `ks`, items then fields: a tuple of them,
/// and, when it has fields, after them a mark of the fields' names, so that a payload with
/// fields is held only by one with the same names, or by a payload not known.
fn payload_form(mut ks: Vec<KType>, fields: &BTreeMap<Arc<str>, Ty>) -> KType {
    if !fields.is_empty() {
        ks.push(mark(&fields_mark(fields)));
    }
    KType::tuple(ks)
}

/// `set` with the payloads `payloads` lists read: each listed atom of `set` holds the payloads
/// `form` gives of its shapes (and none other), and an atom whose payload is not known any
/// payload. None when `form` gives none for a shape.
///
/// Each name costs a meet and a union with the payloads of its shapes, so the set costs the
/// size of its listed payloads, not the product of the names and their shapes.
fn payload_set(
    set: &KType,
    payloads: &BTreeMap<Arc<str>, Option<Vec<Shape>>>,
    mut form: impl FnMut(&Arc<str>, &Shape) -> Option<KType>,
) -> Option<KType> {
    let mut listed = Vec::new();
    let mut read = Vec::new();
    for (n, ss) in payloads {
        let Some(ss) = ss else { continue };
        let all = KType::atom_with(n, &KType::top());
        let p = ss.iter().map(|s| form(n, s)).collect::<Option<Vec<_>>>()?;
        // A payload of no value is left out, so a name whose payloads hold none is built as
        // empty: the kernel then has no union of empty rows to prove empty one by one.
        let p: Vec<KType> = p.into_iter().filter(|k| *k != KType::empty()).collect();
        if !p.is_empty() {
            read.push(&(set & &all) & &KType::atom_with(n, &KType::union_all(p)));
        }
        listed.push(all);
    }
    if listed.is_empty() {
        return Some(set.clone());
    }
    let rest = set - &KType::union_all(listed);
    Some(KType::union_all(std::iter::once(rest).chain(read)))
}

/// A walk that rebuilds the types it is given from what they hold at every depth:
/// [`Ty::subst`], [`Ty::settle`] and the replacements of [`Ty::replace_in`] each say through
/// these methods what they keep whole, what they give again from a memo and what they put in
/// the place of a variable, and [`rebuild`] walks.
trait Rebuild {
    /// What the type `t` is made into without entering it, if it is.
    fn known_ty(&mut self, t: &Ty) -> Option<Ty>;
    /// What the row `r` is made into without entering it, if it is: kept whole, or made before.
    fn known_row(&mut self, r: &Row) -> Option<Row>;
    /// Notes that the row `r`, entered, was made into `out`.
    fn made_row(&mut self, r: &Row, out: &Row);
    /// What the payload shape `s` is made into without entering it, if it is.
    fn known_shape(&mut self, s: &Shape) -> Option<Shape>;
    /// Notes that the payload shape `s`, entered, was made into `out`.
    fn made_shape(&mut self, s: &Shape, out: &Shape);
    /// What the function `s` a type holds is made into without entering it, if it is. If not,
    /// the walk enters it next and leaves it by [`Self::made_held`].
    fn known_held(&mut self, s: &Arc<Sig>) -> Option<Arc<Sig>>;
    /// The function `s`, entered, with its arrows and needs made into `arrows` and `needs`.
    fn made_held(&mut self, s: &Arc<Sig>, arrows: Vec<Arrow>, needs: Vec<Need>) -> Arc<Sig>;
    /// What the variable `v` is replaced by, if it is.
    fn binding(&self, v: &str) -> Option<Cow<'_, Ty>>;
}

/// A step of [`rebuild`]: a part to enter, or a part whose parts are made, to be made from them.
enum Step<'a> {
    Ty(&'a Ty),
    Row(&'a Row),
    Shape(&'a Shape),
    Held(&'a Arc<Sig>),
    TyDone(&'a Ty),
    RowDone(&'a Row),
    ShapeDone(&'a Shape),
    HeldDone(&'a Arc<Sig>),
}

/// What [`rebuild`] made, each kind on a stack of its own, the last made last.
#[derive(Default)]
struct Rebuilt {
    tys: Vec<Ty>,
    rows: Vec<Row>,
    shapes: Vec<Shape>,
    sigs: Vec<Arc<Sig>>,
}

/// What `w` makes of the types `roots`, in order.
fn rebuild_tys<'a>(w: &mut impl Rebuild, roots: impl IntoIterator<Item = &'a Ty>) -> Vec<Ty> {
    let mut stack: Vec<Step<'a>> = roots.into_iter().map(Step::Ty).collect();
    stack.reverse();
    let mut out = Rebuilt::default();
    rebuild(w, stack, &mut out);
    out.tys
}

/// What `w` makes of the type `t`.
fn rebuild_ty(w: &mut impl Rebuild, t: &Ty) -> Ty {
    let mut out = Rebuilt::default();
    rebuild(w, vec![Step::Ty(t)], &mut out);
    out.tys
        .pop()
        .expect("a walk makes one type of the one it is given")
}

/// What `w` makes of the function `s`, as a type holding it would have it.
fn rebuild_held(w: &mut impl Rebuild, s: &Arc<Sig>) -> Arc<Sig> {
    let mut out = Rebuilt::default();
    rebuild(w, vec![Step::Held(s)], &mut out);
    out.sigs
        .pop()
        .expect("a walk makes one signature of the one it is given")
}

/// Makes what `w` makes of each part on `stack`, the top first, and pushes it to `out`.
///
/// A type nests as deep as the program, so the walk keeps its own stack. It enters the parts
/// of a part in the order a recursive walk would (a type's rows, then its functions, then its
/// payload shapes; a function's arrows, each parameter then the result, then its needs), and
/// makes each part once its own are made, the last on top of their stacks in `out`; `w` sees
/// each part as the recursive walk did, so its memos and the variables it hides do not change.
fn rebuild<'a>(w: &mut impl Rebuild, mut stack: Vec<Step<'a>>, out: &mut Rebuilt) {
    /// Pushes `done`, then `parts` so that they pop in order.
    fn enter<'a>(stack: &mut Vec<Step<'a>>, done: Step<'a>, parts: impl Iterator<Item = Step<'a>>) {
        stack.push(done);
        let from = stack.len();
        stack.extend(parts);
        stack[from..].reverse();
    }
    while let Some(step) = stack.pop() {
        match step {
            Step::Ty(t) => match w.known_ty(t) {
                Some(done) => out.tys.push(done),
                None => {
                    let rows = t.tuples.iter().map(Step::Row);
                    let fns = t.fns.iter().map(Step::Held);
                    let shapes = t.payload_shapes().map(Step::Shape);
                    enter(&mut stack, Step::TyDone(t), rows.chain(fns).chain(shapes));
                }
            },
            Step::Row(r) => match w.known_row(r) {
                Some(done) => out.rows.push(done),
                None => enter(&mut stack, Step::RowDone(r), r.iter().map(Step::Ty)),
            },
            Step::Shape(s) => match w.known_shape(s) {
                Some(done) => out.shapes.push(done),
                None => {
                    let cs = s.items.iter().chain(s.fields.values());
                    enter(&mut stack, Step::ShapeDone(s), cs.map(Step::Ty));
                }
            },
            Step::Held(s) => match w.known_held(s) {
                Some(done) => out.sigs.push(done),
                None => enter(&mut stack, Step::HeldDone(s), sig_tys(s).map(Step::Ty)),
            },
            Step::TyDone(t) => {
                let mut tuples = out.rows.split_off(out.rows.len() - t.tuples.len());
                let fns = out.sigs.split_off(out.sigs.len() - t.fns.len());
                let from = out.shapes.len() - t.payload_shapes().count();
                let mut shapes = out.shapes.drain(from..);
                let mut payloads = t.map_payloads(|_| {
                    (shapes.next()).expect("a walk makes one shape of each payload shape")
                });
                // A variable replaced by the empty type leaves a row with no value, and a
                // payload shape with none, as `#a(g(x), 1)` once `g`'s result is `Never`; a name
                // left with no shape has no atom with a payload, which the type then drops (its
                // bare atom stays). O(1) per shape, and one difference of the set when a name
                // is dropped.
                tuples.retain(|r| !r.0.void);
                let mut gone = Vec::new();
                payloads.retain(|n, ss| {
                    let Some(ss) = ss else { return true };
                    let had = !ss.is_empty();
                    ss.retain(|s| !s.void);
                    if had && ss.is_empty() {
                        gone.push(KType::atom_with(n, &KType::top()));
                        return false;
                    }
                    true
                });
                let (set, family) = match gone.is_empty() {
                    true => (t.set.clone(), t.family.clone()),
                    false => {
                        let gone = KType::union_all(gone);
                        (&t.set - &gone, &t.family - &gone)
                    }
                };
                let mut made = Ty {
                    set,
                    tuples,
                    fns,
                    vars: BTreeSet::new(),
                    dynamic: t.dynamic,
                    family,
                    payloads,
                };
                for v in &t.vars {
                    match w.binding(v) {
                        Some(b) => made = made.union(&b),
                        None => {
                            made.vars.insert(v.clone());
                        }
                    }
                }
                out.tys.push(made);
            }
            Step::RowDone(r) => {
                let made = r.replaced(out.tys.split_off(out.tys.len() - r.len()));
                w.made_row(r, &made);
                out.rows.push(made);
            }
            Step::ShapeDone(s) => {
                let from = out.tys.len() - s.items.len() - s.fields.len();
                let mut cs = out.tys.drain(from..);
                let items = cs.by_ref().take(s.items.len()).collect();
                let fields = (s.fields.keys())
                    .map(|n| {
                        let c = cs.next().expect("a walk makes one type of each field");
                        (n.clone(), c)
                    })
                    .collect();
                let made = Shape::new(items, fields);
                w.made_shape(s, &made);
                out.shapes.push(made);
            }
            Step::HeldDone(s) => {
                let from = out.tys.len() - sig_tys(s).count();
                let (arrows, needs) = sig_parts(s, out.tys.drain(from..));
                out.sigs.push(w.made_held(s, arrows, needs));
            }
        }
    }
}

/// The types of the arrows and needs of `s` that a rebuilding walk enters, in order: each
/// arrow's parameters, then its result, then each need's types ([`Need::tys`]).
fn sig_tys(s: &Sig) -> impl Iterator<Item = &Ty> {
    (s.arrows.iter())
        .flat_map(|a| a.params.iter().chain(std::iter::once(&a.result)))
        .chain(s.needs.iter().flat_map(Need::tys))
}

/// The arrows and needs of `s` with the types [`sig_tys`] gives replaced by `tys`, in order.
fn sig_parts(s: &Sig, mut tys: impl Iterator<Item = Ty>) -> (Vec<Arrow>, Vec<Need>) {
    let mut next = || {
        tys.next()
            .expect("a walk makes one type of each type of a signature")
    };
    let arrows = (s.arrows.iter())
        .map(|a| Arrow {
            params: a.params.iter().map(|_| next()).collect(),
            result: next(),
        })
        .collect();
    let needs = s.needs.iter().map(|n| n.map_tys(|_| next())).collect();
    (arrows, needs)
}

/// One replacement of variables ([`Ty::replace_in`]) over a type, a signature or a need.
///
/// Rows, payload shapes and signatures are shared, so a type of `n` rows may have `2^n` paths
/// through them, as the result of `p(p(p(a0, a1), a2), ...)` with `p(s, v) = (s, (s, v))` has.
/// The walk keeps what it made of each row, shape and signature, by address, and gives that
/// again where it meets one once more, so each is replaced once (REPLACE-shared-rows). The
/// addresses are those of rows, shapes and signatures the input holds, which outlive the
/// walk, so no two are the same.
struct Replacer<'b> {
    binds: &'b Binds,
    mode: Mode,
    /// The variables `binds` binds that are own variables of a signature the walk is inside,
    /// each with the number of such signatures: there they are the signature's, and are kept.
    /// Looked up per variable met, so a signature that hides some costs the variables it
    /// holds, not a copy of `binds` without them.
    hidden: HashMap<Arc<str>, usize>,
    /// What each row and signature met was replaced by, under the variables hidden now: one
    /// memo for each signature entered that hides one, last entered last.
    // Complexity tradeoff: a row shared by several signatures that each hide variables is
    // made once in each of their memos, though two that hide the same variables would make
    // it alike: O(rows held times such signatures) at worst, not O(rows). Keying the memo by
    // the set hidden would share those, at the cost of hashing that set at each signature.
    memos: Vec<Memo>,
    /// The variables each signature the walk is inside hides, last entered last: none for one
    /// that hides none, which has no memo of its own.
    entered: Vec<Vec<Arc<str>>>,
}

/// The rows and payload shapes a walk that rebuilds a type met, by address, with what it made
/// of each: both are shared, so a walk without it would rebuild one once per path to it,
/// `2^n` times for `n` rows or shapes that each hold the one below twice. The addresses are
/// those of rows and shapes the input holds, which outlive the walk.
#[derive(Default)]
struct Made {
    rows: HashMap<*const RowData, Row>,
    shapes: HashMap<*const ShapeData, Shape>,
}

/// The rows, payload shapes and signatures a [`Replacer`] met under one set of hidden
/// variables, by address, with what it made of each.
#[derive(Default)]
struct Memo {
    made: Made,
    sigs: HashMap<*const Sig, Arc<Sig>>,
}

impl<'b> Replacer<'b> {
    fn new(binds: &'b Binds, mode: Mode) -> Self {
        Replacer {
            binds,
            mode,
            hidden: HashMap::new(),
            memos: vec![Memo::default()],
            entered: Vec::new(),
        }
    }

    /// The memo of the variables hidden now.
    fn memo(&mut self) -> &mut Memo {
        self.memos
            .last_mut()
            .expect("a replacer holds a memo from its start to its end")
    }

    /// What the variable `v` is replaced by here, if it is.
    fn bound(&self, v: &str) -> Option<&'b Ty> {
        self.binds.get(v).filter(|_| !self.hidden.contains_key(v))
    }

    /// Whether `f` holds a variable replaced here that `own` does not hold: read from the
    /// smaller of `binds` and `f`, so a call that binds many variables pays at each row or
    /// signature it replaces in for the variables that holds, not for every one it binds.
    fn holds(&self, f: &VarFacts, own: &BTreeSet<Arc<str>>) -> bool {
        let here = |v: &Arc<str>| !own.contains(v) && !self.hidden.contains_key(v);
        if self.binds.len() <= f.classes.len() + f.names.len() {
            self.binds.keys().any(|v| here(v) && f.holds(v))
        } else {
            (f.classes.iter().chain(&f.names)).any(|v| here(v) && self.binds.contains_key(v))
        }
    }

    /// [`Sig::replace_in`]: renamed, its own and held variables take their new names.
    fn sig(&mut self, s: &Sig) -> Sig {
        let tys = rebuild_tys(self, sig_tys(s));
        let (arrows, needs) = sig_parts(s, tys.into_iter());
        self.sig_of(s, arrows, needs)
    }

    /// The signature `s` with its arrows and needs replaced in, `arrows` and `needs`: its own
    /// and held variables and its bounds as the variables hidden now replace them.
    fn sig_of(&self, s: &Sig, arrows: Vec<Arrow>, needs: Vec<Need>) -> Sig {
        // Its own or held variable `v` under `binds`: renamed, kept, or dropped as replaced.
        let keep = |v: &Arc<str>| match self.bound(v) {
            None => Some(v.clone()),
            Some(t) if self.mode == Mode::Rename => t.vars.first().cloned(),
            Some(_) => None,
        };
        let own = s.own.iter().filter_map(keep).collect();
        let held = s.held.iter().filter_map(keep).collect();
        let mut bounds = BTreeMap::new();
        for (v, m) in &s.bounds {
            match self.bound(v) {
                None => {
                    bounds.insert(v.clone(), *m);
                }
                Some(t) => {
                    for w in &t.vars {
                        bounds.insert(w.clone(), *m);
                    }
                }
            }
        }
        Sig {
            params: s.params.clone(),
            arrows,
            bounds,
            data: s.data,
            word: s.word.clone(),
            needs,
            own,
            held,
            named: s.named,
            facts: Facts::default(),
        }
    }
}

impl Rebuild for Replacer<'_> {
    fn known_ty(&mut self, t: &Ty) -> Option<Ty> {
        // A type with no tuple, function or payload holds only its own variables; outside
        // functions, one with no tuple or payload does.
        let fns = !t.fns.is_empty() && self.mode != Mode::Outside;
        let leaf = t.tuples.is_empty() && !fns && t.payloads.is_empty();
        (leaf && !t.vars.iter().any(|v| self.bound(v).is_some())).then(|| t.clone())
    }

    fn known_row(&mut self, r: &Row) -> Option<Row> {
        if let Some(done) = self.memo().made.rows.get(&Arc::as_ptr(&r.0)) {
            return Some(done.clone());
        }
        let kept = match self.mode {
            _ if r.0.fixed => true,
            Mode::Outside if !r.open() => true,
            _ => !self.holds(&r.0.vars, &BTreeSet::new()),
        };
        kept.then(|| {
            self.made_row(r, r);
            r.clone()
        })
    }

    fn made_row(&mut self, r: &Row, out: &Row) {
        self.memo().made.rows.insert(Arc::as_ptr(&r.0), out.clone());
    }

    /// A payload shape: kept whole where it holds none of the variables replaced here.
    fn known_shape(&mut self, s: &Shape) -> Option<Shape> {
        if let Some(done) = self.memo().made.shapes.get(&s.as_ptr()) {
            return Some(done.clone());
        }
        let kept = match self.mode {
            _ if s.fixed => true,
            Mode::Outside if !s.open() => true,
            _ => !self.holds(&s.vars, &BTreeSet::new()),
        };
        kept.then(|| {
            self.made_shape(s, s);
            s.clone()
        })
    }

    fn made_shape(&mut self, s: &Shape, out: &Shape) {
        self.memo().made.shapes.insert(s.as_ptr(), out.clone());
    }

    /// A signature held in a type: replaced in, but its own variables are its own, so those
    /// `binds` binds are hidden inside it, under a memo of their own.
    fn known_held(&mut self, s: &Arc<Sig>) -> Option<Arc<Sig>> {
        if self.mode == Mode::Outside {
            return Some(s.clone());
        }
        if let Some(done) = self.memo().sigs.get(&Arc::as_ptr(s)) {
            return Some(done.clone());
        }
        // A signature that holds none of the variables replaced is kept whole.
        if self.mode != Mode::Rename && !self.holds(s.facts(), &s.own) {
            self.memo().sigs.insert(Arc::as_ptr(s), s.clone());
            return Some(s.clone());
        }
        let hide: Vec<Arc<str>> = match self.mode {
            Mode::Rename => Vec::new(),
            _ => (s.own.iter())
                .filter(|v| self.bound(v).is_some())
                .cloned()
                .collect(),
        };
        if !hide.is_empty() {
            for v in &hide {
                *self.hidden.entry(v.clone()).or_default() += 1;
            }
            self.memos.push(Memo::default());
        }
        self.entered.push(hide);
        None
    }

    fn made_held(&mut self, s: &Arc<Sig>, arrows: Vec<Arrow>, needs: Vec<Need>) -> Arc<Sig> {
        // Its own and held variables are read with its own hidden, as its arrows were.
        let out = Arc::new(self.sig_of(s, arrows, needs));
        let hide = (self.entered.pop()).expect("a signature the walk leaves is one it entered");
        if !hide.is_empty() {
            self.memos.pop();
            for v in &hide {
                if let Some(n) = self.hidden.get_mut(v) {
                    *n -= 1;
                    if *n == 0 {
                        self.hidden.remove(v);
                    }
                }
            }
        }
        self.memo().sigs.insert(Arc::as_ptr(s), out.clone());
        out
    }

    fn binding(&self, v: &str) -> Option<Cow<'_, Ty>> {
        self.bound(v).map(Cow::Borrowed)
    }
}

/// [`Ty::subst`]: the variables `binds` binds replaced outside the functions a type holds,
/// which are kept whole, as is a row or payload shape that holds none of them; each other row
/// and shape is made once, by address ([`Made`]).
struct Subst<'b> {
    binds: &'b Binds,
    made: Made,
}

impl Rebuild for Subst<'_> {
    fn known_ty(&mut self, _: &Ty) -> Option<Ty> {
        None
    }

    fn known_row(&mut self, r: &Row) -> Option<Row> {
        match r.holds_any(self.binds) {
            false => Some(r.clone()),
            true => self.made.rows.get(&Arc::as_ptr(&r.0)).cloned(),
        }
    }

    fn made_row(&mut self, r: &Row, out: &Row) {
        self.made.rows.insert(Arc::as_ptr(&r.0), out.clone());
    }

    fn known_shape(&mut self, s: &Shape) -> Option<Shape> {
        match s.holds_any(self.binds) {
            false => Some(s.clone()),
            true => self.made.shapes.get(&s.as_ptr()).cloned(),
        }
    }

    fn made_shape(&mut self, s: &Shape, out: &Shape) {
        self.made.shapes.insert(s.as_ptr(), out.clone());
    }

    fn known_held(&mut self, s: &Arc<Sig>) -> Option<Arc<Sig>> {
        Some(s.clone())
    }

    fn made_held(&mut self, _: &Arc<Sig>, _: Vec<Arrow>, _: Vec<Need>) -> Arc<Sig> {
        unreachable!("`subst` keeps each function whole, so it enters none")
    }

    fn binding(&self, v: &str) -> Option<Cow<'_, Ty>> {
        self.binds.get(v).map(Cow::Borrowed)
    }
}

/// [`Ty::settle`] and [`Sig::settle`]: each class variable `solve` gives a type replaced by
/// it at every depth. A row that holds no variable, the unknown or a function, and a payload
/// shape that holds no variable or function, are kept whole; each other is made once, by
/// address, in the memo of the signature the walk is inside, or of the type it started at;
/// each signature is settled once, and kept in its own facts.
struct Settle<'s> {
    solve: Solve<'s>,
    /// One memo for the type the walk started at, if it started at one, and one for each
    /// signature it is inside, last entered last.
    made: Vec<Made>,
}

impl Settle<'_> {
    /// The memo of the signature the walk is inside, or of the type it started at.
    fn memo(&mut self) -> &mut Made {
        self.made
            .last_mut()
            .expect("a settling walk enters a row or shape only inside a memo")
    }
}

impl Rebuild for Settle<'_> {
    fn known_ty(&mut self, _: &Ty) -> Option<Ty> {
        None
    }

    fn known_row(&mut self, r: &Row) -> Option<Row> {
        match r.open() || r.0.held.is_some() {
            false => Some(r.clone()),
            true => self.memo().rows.get(&Arc::as_ptr(&r.0)).cloned(),
        }
    }

    fn made_row(&mut self, r: &Row, out: &Row) {
        self.memo().rows.insert(Arc::as_ptr(&r.0), out.clone());
    }

    fn known_shape(&mut self, s: &Shape) -> Option<Shape> {
        match s.fixed {
            true => Some(s.clone()),
            false => self.memo().shapes.get(&s.as_ptr()).cloned(),
        }
    }

    fn made_shape(&mut self, s: &Shape, out: &Shape) {
        self.memo().shapes.insert(s.as_ptr(), out.clone());
    }

    /// A signature that holds no class variable is itself, and one settled before is what it
    /// was settled into; another is entered under a memo of its own.
    fn known_held(&mut self, s: &Arc<Sig>) -> Option<Arc<Sig>> {
        if s.facts().classes.is_empty() {
            return Some(s.clone());
        }
        if let Some(done) = s.facts.1.get() {
            return Some(done.clone());
        }
        self.made.push(Made::default());
        None
    }

    fn made_held(&mut self, s: &Arc<Sig>, arrows: Vec<Arrow>, needs: Vec<Need>) -> Arc<Sig> {
        self.made.pop();
        // A variable `solve` gives a type is replaced, so no longer bounded, own or held.
        let solve = self.solve;
        let open = |v: &&Arc<str>| solve(v).is_none();
        let settled = Sig {
            params: s.params.clone(),
            arrows,
            bounds: (s.bounds.iter())
                .filter(|(v, _)| open(v))
                .map(|(v, m)| (v.clone(), *m))
                .collect(),
            data: s.data,
            word: s.word.clone(),
            needs,
            own: s.own.iter().filter(open).cloned().collect(),
            held: s.held.iter().filter(open).cloned().collect(),
            named: s.named,
            facts: Facts::default(),
        };
        s.facts.1.get_or_init(|| Arc::new(settled)).clone()
    }

    fn binding(&self, v: &str) -> Option<Cow<'_, Ty>> {
        (self.solve)(v).map(Cow::Owned)
    }
}

/// A function's signature: its parameters' names and kinds, shared by its arrows, which
/// together are an intersection, and the carriers each bounded type variable ranges over.
#[derive(Clone, Eq)]
pub struct Sig {
    /// The parameters.
    pub params: Vec<SParam>,
    /// The arrows.
    pub arrows: Vec<Arrow>,
    /// Each bounded type variable, with the mask of the carriers it ranges over: one carrier,
    /// the same at each place the variable stands.
    pub bounds: BTreeMap<Arc<str>, u8>,
    /// Whether it is a family: a morphism held as data (sec:values_morphisms), shown, compared
    /// and put in a tuple as a value, and looked up through its arrows.
    pub data: bool,
    /// The prelude word it is, if it is one: the function itself, not its arrows. `min` and
    /// `max` take two tuples, which `+`, of the same arrows, does not (DESIGN.md
    /// sec:reduction, item 5), wherever the word is called from: by name, as a method, or
    /// through a name or parameter it was passed to.
    pub word: Option<Arc<str>>,
    /// What the body needs of the values of its type variables, in the order the body met
    /// the uses: each call checks them again with the variables bound (DESIGN.md rule 4).
    pub needs: Vec<Need>,
    /// Its own type variables, which it binds: a call binds them anew, and a substitution
    /// of the variables of a type that holds it leaves them alone. The others are those of
    /// the functions around it.
    pub own: BTreeSet<Arc<str>>,
    /// Its own bounded variables a parameter holds, at any depth, on any arrow: an argument
    /// fixes their carriers. Worked out when it is built ([`Sig::note_held`]), so a comparison
    /// does not walk its parameters again at each depth.
    pub held: BTreeSet<Arc<str>>,
    /// How many of the names `var_name` gives its own type variables and those of the
    /// functions it holds take: a function around it names its own from there on. The checker
    /// writes the own variables of a signature it solved `$k`, for the class `k` each was solved
    /// from, and gives them their names when it finishes, so a function around one does not
    /// rewrite it (CHK-curried).
    pub named: usize,
    /// The variables it holds at any depth, worked out when first asked ([`Sig::facts`]).
    /// Once they are read the signature is not changed in place: a change goes to a clone,
    /// whose facts are worked out again.
    pub facts: Facts,
}

/// The variables a signature holds at any depth, inside the functions it holds too: worked
/// out once for a signature held in a type, so that a substitution, or the naming of the
/// variables of a function around it, does not walk it again at each depth. It is not part
/// of the signature's value, and a clone, which may be changed, works it out again.
///
/// It also keeps the signature [`Sig::settle`] made of it, each solved class variable
/// replaced at every depth: made once, when the checker finishes, so a signature held in many
/// that the checker shows is settled once, not once for each.
///
/// And it keeps the signature's hash ([`Sig::digest`]), made from the hashes of the
/// functions it holds, so a set of functions hashes each at the cost of its outer level.
#[derive(Default)]
pub struct Facts(
    std::sync::OnceLock<VarFacts>,
    std::sync::OnceLock<Arc<Sig>>,
    std::sync::OnceLock<u64>,
);

impl Clone for Facts {
    fn clone(&self) -> Facts {
        Facts::default()
    }
}

impl PartialEq for Facts {
    fn eq(&self, _: &Facts) -> bool {
        true
    }
}

impl Eq for Facts {}

impl std::hash::Hash for Facts {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

impl fmt::Debug for Facts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("_")
    }
}

/// What [`Facts`] holds. Both sets are persistent and shared with the facts of the functions
/// it holds, so a function around one does not copy them: the larger set is kept and the
/// smaller one added to it.
#[derive(Default)]
pub struct VarFacts {
    /// The class variables.
    pub classes: imbl::OrdSet<Arc<str>>,
    /// The other variables, with its own, bounded and held ones.
    pub names: imbl::OrdSet<Arc<str>>,
    /// The first `n` such that `names` lacks the `n`th variable name (`var_name`).
    pub free: usize,
}

impl VarFacts {
    /// Whether it holds the variable `v`.
    pub fn holds(&self, v: &str) -> bool {
        self.classes.contains(v) || self.names.contains(v)
    }

    /// Whether it holds no variable.
    fn is_empty(&self) -> bool {
        self.classes.is_empty() && self.names.is_empty()
    }

    /// Whether it holds one of the variables `binds` replaces: each bind looked up in it, or
    /// each of its variables in `binds`, whichever has fewer.
    fn holds_any(&self, binds: &Binds) -> bool {
        match binds.len() <= self.classes.len() + self.names.len() {
            true => binds.keys().any(|v| self.holds(v)),
            false => (self.classes.iter().chain(&self.names)).any(|v| binds.contains_key(v)),
        }
    }

    /// The facts of the arrows and needs of `s`, worked out now; for a signature not yet
    /// held in a type, which may still change.
    pub fn of(s: &Sig) -> VarFacts {
        let mut g = VarFacts::default();
        for a in &s.arrows {
            a.params.iter().for_each(|p| g.ty(p));
            g.ty(&a.result);
        }
        for n in &s.needs {
            n.tys().for_each(|t| g.ty(t));
        }
        let extra = s.bounds.keys().chain(&s.own).chain(&s.held);
        extra.for_each(|v| add(&mut g.names, v));
        g.free = g.free.max(s.named);
        while g.names.contains(&*var_name(g.free)) {
            g.free += 1;
        }
        g
    }

    /// Adds the variables of `t`: those of its rows, payload shapes and functions as each
    /// keeps them, so the cost is that of its outer level.
    fn ty(&mut self, t: &Ty) {
        for v in &t.vars {
            match class_id(v) {
                Some(_) => add(&mut self.classes, v),
                None => add(&mut self.names, v),
            }
        }
        for r in &t.tuples {
            self.held(&r.0.vars);
        }
        for s in t.payload_shapes() {
            self.held(&s.vars);
        }
        for s in &t.fns {
            self.held(s.facts());
        }
    }

    /// Adds the facts of a function it holds: of each set, the larger is kept and the smaller
    /// one added to it, so each variable is copied O(log n) times over a nest of n.
    fn held(&mut self, f: &VarFacts) {
        merge(&mut self.classes, &f.classes);
        merge(&mut self.names, &f.names);
        self.free = self.free.max(f.free);
    }
}

/// Adds `other` to `set`, keeping the larger of the two and adding to it what the smaller
/// holds and it lacks.
///
/// Two ways find that, run a step each in turn until either ends: inserting each variable of
/// the smaller set, `O(m log n)` for sets of `m` and `n`, and the difference of the two
/// (`imbl`'s `diff`), which steps over the nodes they share, so that a set made from the other
/// by adding a few variables costs about the depth of the tree. Either alone fails a family:
/// the insertions merge a set into one it was made from at its full size, `O(n^2 log n)` over
/// `n` rows `t(k) = (t(k-1), (t(k-1), Vk))`, and the difference walks the larger set when the
/// two share no node.
fn merge(set: &mut imbl::OrdSet<Arc<str>>, other: &imbl::OrdSet<Arc<str>>) {
    let (large, small) = match other.len() > set.len() {
        true => (other, &*set),
        false => (&*set, other),
    };
    let mut out = large.clone();
    let mut lacks = large.diff(small);
    for v in small {
        add(&mut out, v);
        match lacks.next() {
            Some(imbl::ordset::DiffItem::Add(v)) => add(&mut out, v),
            Some(imbl::ordset::DiffItem::Remove(_)) => {}
            None => break,
        }
    }
    *set = out;
}

/// Adds `v` to `set`. A set shared with the facts of another signature is copied along the
/// path to `v` by an insertion, so a variable it already holds is not inserted again.
fn add(set: &mut imbl::OrdSet<Arc<str>>, v: &Arc<str>) {
    if !set.contains(v) {
        set.insert(v.clone());
    }
}

/// A use the body of a generic function makes of a value whose type is a variable: checked
/// again at each call, on the type the call binds the variable to.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Need {
    /// The type of the value used, a variable of the signature.
    pub on: Ty,
    /// The use.
    pub kind: NeedKind,
    /// What the use gives, a variable of the signature, if it gives a value.
    pub result: Option<Ty>,
    /// The use in the body.
    pub span: Span,
}

/// The uses a [`Need`] records.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum NeedKind {
    /// `v[i]` with a literal: a tuple's component, or a family's entry.
    Component {
        /// The component, if the literal is a component number.
        i: Option<usize>,
        /// The literal's type, a family's key.
        key: Ty,
    },
    /// `v[k]` with a key of this type: an application.
    Index(Ty),
    /// `a, b, ... = v` into `n` names: component `i` of a tuple of exactly `n`.
    Destructure {
        /// The component.
        i: usize,
        /// The number of names, the tuple's length.
        n: usize,
    },
    /// A call of `v`, named `what`, with arguments of these types.
    Call {
        /// The value's name in the call.
        what: Arc<str>,
        /// The types of the positional arguments.
        positional: Vec<Ty>,
        /// The names and types of the named arguments.
        named: Vec<(Arc<str>, Ty)>,
        /// Whether the call ends in `...`.
        curry: bool,
    },
    /// A use, `what`, that takes data: the value holds no function.
    Data(Arc<str>),
    /// An argument, of `what`, at a parameter of the closed type `ty`.
    Into {
        /// The function called.
        what: Arc<str>,
        /// The parameter's type.
        ty: Ty,
    },
    /// A name a pattern binds: what the payload of an atom named `atom` holds at `slot`.
    Payload {
        /// The atom's name.
        atom: Arc<str>,
        /// The place in its payload.
        slot: Slot,
    },
    /// A test's narrowing: what is left of the value where the test fails.
    Narrow(Narrow),
    /// `min` or `max`, the word `word`, named `what`, with the value as one operand and a
    /// value of `other` as the other, which holds a tuple: the value is the first operand
    /// if `first` (DESIGN.md sec:reduction, item 5).
    Order {
        /// The function called.
        what: Arc<str>,
        /// The word, `min` or `max`.
        word: Arc<str>,
        /// The other operand's type.
        other: Ty,
        /// Whether the value is the first operand.
        first: bool,
    },
    /// A use that takes an int in its domain, as `^`'s exponent and a bit word's operand do,
    /// of a value whose ints the body shows no bound of and which is no parameter: the value
    /// holds no int, or only ints listed in the domain (CHK-need-bound).
    NoInt(IntDomain),
    /// `sum` of the value: a tuple of numbers, whose sum the use gives (CHK-need-bound).
    Sum,
    /// A use that takes an int in its domain, of the value of the parameter at position
    /// `param` of the function whose signature holds it: each call shows the ints of its
    /// argument in the domain, or passes on a parameter of its own, whose calls then show them
    /// (CHK-need-bound). The need is on the parameter, not on a variable, so its `on` is the
    /// empty type and its `span` the use.
    InDomain {
        /// The use and its domain.
        domain: IntDomain,
        /// The parameter's position.
        param: usize,
        /// The calls that passed the parameter on, the last first.
        via: Option<Arc<Via>>,
    },
}

/// The ints a use takes, as `^`'s exponent and a bit word's operand do: those at least 0, and
/// below `2 ^ width` for an operand read as `width` binary digits (CHK-need-bound).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntDomain {
    /// The use, in words, as an error states it.
    pub what: Arc<str>,
    /// The smallest width of the use, for an operand read as that many digits.
    pub below_two_pow: Option<Width>,
}

/// The width of a bit word, an int at least 0, kept as its value: `2 ^ width` is never built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Width(pub Value);

impl std::hash::Hash for Width {
    /// A machine int hashes as itself and a wider one as nothing, which equal widths agree on.
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        if let Value::Int(n) = &self.0 {
            n.hash(h);
        }
    }
}

/// A call that passed its function's parameter on as the argument of a parameter with a
/// [`NeedKind::InDomain`] need, and the calls that passed that one on before it.
///
/// Two are compared one call at a time, and the same chain at once, and only the first call is
/// hashed, so a chain of `n` calls costs O(1) to hash, not O(n) at each of its `n` links.
#[derive(Clone, Debug)]
pub struct Via {
    /// The call.
    pub at: Span,
    /// The call, in words, as an error states it.
    pub text: Arc<str>,
    /// The call before it.
    pub next: Option<Arc<Via>>,
}

impl PartialEq for Via {
    fn eq(&self, other: &Via) -> bool {
        let (mut a, mut b) = (self, other);
        loop {
            if std::ptr::eq(a, b) {
                return true;
            }
            if a.at != b.at || a.text != b.text {
                return false;
            }
            match (&a.next, &b.next) {
                (Some(x), Some(y)) => (a, b) = (x, y),
                (None, None) => return true,
                _ => return false,
            }
        }
    }
}

impl Eq for Via {}

impl std::hash::Hash for Via {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.at.hash(h);
        self.text.hash(h);
    }
}

impl Drop for Via {
    /// Unlinks the chain one call at a time, so a chain of any length needs no stack as deep.
    fn drop(&mut self) {
        let mut next = self.next.take();
        while let Some(v) = next {
            next = match Arc::try_unwrap(v) {
                Ok(mut v) => v.next.take(),
                Err(_) => None,
            };
        }
    }
}

/// What a test leaves of a value where it fails (rule 3 of sec:type_resolution).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Narrow {
    /// `e else d`: what is not a loose atom.
    Loose,
    /// `e else #a -> d`: what is not the atom `#a`, with any payload or none.
    Atom(Arc<str>),
    /// `e is t`, where it is false: what is not in `t`. Only the scalars, atoms and tuples
    /// of `t` are subtracted, so its variables need no binding.
    Not(Ty),
}

/// A place in an atom's payload.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Slot {
    /// The field of this name.
    Field(Arc<str>),
    /// The component at this position.
    Item(usize),
}

impl Need {
    /// It with its variables replaced by `binds` at every depth.
    pub fn replace(&self, binds: &Binds) -> Need {
        self.replace_in(binds, Mode::Replace)
    }

    /// [`Need::replace`], or as `mode` says.
    fn replace_in(&self, binds: &Binds, mode: Mode) -> Need {
        let tys = rebuild_tys(&mut Replacer::new(binds, mode), self.tys());
        let mut tys = tys.into_iter();
        self.map_tys(|_| {
            tys.next()
                .expect("a walk makes one type of each type of a need")
        })
    }

    /// It with `f` applied to each of the types [`Need::tys`] gives, in that order.
    fn map_tys(&self, mut f: impl FnMut(&Ty) -> Ty) -> Need {
        Need {
            on: f(&self.on),
            kind: match &self.kind {
                NeedKind::Component { i, key } => NeedKind::Component {
                    i: *i,
                    key: key.clone(),
                },
                NeedKind::Index(k) => NeedKind::Index(f(k)),
                NeedKind::Destructure { i, n } => NeedKind::Destructure { i: *i, n: *n },
                NeedKind::Call {
                    what,
                    positional,
                    named,
                    curry,
                } => NeedKind::Call {
                    what: what.clone(),
                    positional: positional.iter().map(&mut f).collect(),
                    named: named.iter().map(|(n, t)| (n.clone(), f(t))).collect(),
                    curry: *curry,
                },
                NeedKind::Data(what) => NeedKind::Data(what.clone()),
                NeedKind::NoInt(d) => NeedKind::NoInt(d.clone()),
                NeedKind::Sum => NeedKind::Sum,
                NeedKind::InDomain { domain, param, via } => NeedKind::InDomain {
                    domain: domain.clone(),
                    param: *param,
                    via: via.clone(),
                },
                NeedKind::Into { what, ty } => NeedKind::Into {
                    what: what.clone(),
                    ty: ty.clone(),
                },
                NeedKind::Payload { atom, slot } => NeedKind::Payload {
                    atom: atom.clone(),
                    slot: slot.clone(),
                },
                NeedKind::Narrow(n) => NeedKind::Narrow(n.clone()),
                NeedKind::Order {
                    what,
                    word,
                    other,
                    first,
                } => NeedKind::Order {
                    what: what.clone(),
                    word: word.clone(),
                    other: f(other),
                    first: *first,
                },
            },
            result: self.result.as_ref().map(f),
            span: self.span,
        }
    }

    /// Every variable in it, in order of first appearance.
    pub fn vars_in(&self, out: &mut Vars) {
        self.tys().for_each(|t| t.vars_in(out));
    }

    /// The types in it that [`Need::replace`] replaces in, in order.
    pub fn tys(&self) -> impl Iterator<Item = &Ty> {
        let (index, positional, named): (_, &[Ty], &[(Arc<str>, Ty)]) = match &self.kind {
            NeedKind::Component { .. }
            | NeedKind::Destructure { .. }
            | NeedKind::Data(_)
            | NeedKind::NoInt(_)
            | NeedKind::InDomain { .. }
            | NeedKind::Sum
            | NeedKind::Into { .. }
            | NeedKind::Payload { .. }
            | NeedKind::Narrow(_) => (None, &[], &[]),
            NeedKind::Index(k) | NeedKind::Order { other: k, .. } => (Some(k), &[], &[]),
            NeedKind::Call {
                positional, named, ..
            } => (None, positional, named),
        };
        std::iter::once(&self.on)
            .chain(index)
            .chain(positional)
            .chain(named.iter().map(|(_, t)| t))
            .chain(&self.result)
    }

    /// Every type in it, those [`Need::tys`] leaves out too, as its hash reads them.
    fn every_ty(&self) -> Vec<&Ty> {
        let more: Vec<&Ty> = match &self.kind {
            NeedKind::Destructure { .. }
            | NeedKind::Data(_)
            | NeedKind::NoInt(_)
            | NeedKind::InDomain { .. }
            | NeedKind::Sum
            | NeedKind::Payload { .. }
            | NeedKind::Narrow(Narrow::Loose | Narrow::Atom(_)) => Vec::new(),
            NeedKind::Component { key: t, .. }
            | NeedKind::Index(t)
            | NeedKind::Into { ty: t, .. }
            | NeedKind::Order { other: t, .. }
            | NeedKind::Narrow(Narrow::Not(t)) => vec![t],
            NeedKind::Call {
                positional, named, ..
            } => positional
                .iter()
                .chain(named.iter().map(|(_, t)| t))
                .collect(),
        };
        std::iter::once(&self.on)
            .chain(more)
            .chain(&self.result)
            .collect()
    }

    /// Every type in it, its own, for [`drop_types`].
    fn into_tys(self) -> impl Iterator<Item = Ty> {
        let more: Vec<Ty> = match self.kind {
            NeedKind::Destructure { .. }
            | NeedKind::Data(_)
            | NeedKind::NoInt(_)
            | NeedKind::InDomain { .. }
            | NeedKind::Sum
            | NeedKind::Payload { .. }
            | NeedKind::Narrow(Narrow::Loose | Narrow::Atom(_)) => Vec::new(),
            NeedKind::Component { key: t, .. }
            | NeedKind::Index(t)
            | NeedKind::Into { ty: t, .. }
            | NeedKind::Order { other: t, .. }
            | NeedKind::Narrow(Narrow::Not(t)) => vec![t],
            NeedKind::Call {
                mut positional,
                named,
                ..
            } => {
                positional.extend(named.into_iter().map(|(_, t)| t));
                positional
            }
        };
        std::iter::once(self.on).chain(more).chain(self.result)
    }
}

/// A parameter of a signature.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SParam {
    /// Its name.
    pub name: Arc<str>,
    /// Whether it is passed by position.
    pub positional: bool,
    /// Its default, if it has one: the declaring function's binder, the parameter's index,
    /// and whether the default reads no name of the unit, so a call through a value can
    /// fill it.
    pub default: Option<(usize, usize, bool)>,
}

/// One arrow: a type for each parameter, and the result.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Arrow {
    /// The parameters' types.
    pub params: Vec<Ty>,
    /// The result.
    pub result: Ty,
}

/// A scalar carrier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Carrier {
    /// `bool`.
    Bool,
    /// `int`.
    Int,
    /// `rat`.
    Rat,
    /// `f64`.
    F64,
    /// `String`.
    Str,
}

impl Carrier {
    /// The five, in the order a class of values holding a literal tries them.
    pub const ALL: [Carrier; 5] = [
        Carrier::Int,
        Carrier::F64,
        Carrier::Rat,
        Carrier::Str,
        Carrier::Bool,
    ];

    /// Every value of the carrier.
    pub fn ty(self) -> KType {
        match self {
            Carrier::Bool => KType::bool(),
            Carrier::Int => KType::int(),
            Carrier::Rat => KType::rat(),
            Carrier::F64 => KType::f64(),
            Carrier::Str => KType::string(),
        }
    }

    /// Its place among the bases of [`zed_kernel::types::Split`].
    pub fn base(self) -> usize {
        match self {
            Carrier::Bool => 0,
            Carrier::Int => 1,
            Carrier::Rat => 2,
            Carrier::F64 => 3,
            Carrier::Str => 4,
        }
    }

    /// Its name.
    pub fn name(self) -> &'static str {
        match self {
            Carrier::Bool => "bool",
            Carrier::Int => "int",
            Carrier::Rat => "rat",
            Carrier::F64 => "f64",
            Carrier::Str => "String",
        }
    }

    /// Whether it is a number.
    pub fn numeric(self) -> bool {
        matches!(self, Carrier::Int | Carrier::Rat | Carrier::F64)
    }

    /// Its bit in a mask: its place in [`Carrier::ALL`].
    pub fn bit(self) -> u8 {
        1 << Carrier::ALL
            .iter()
            .position(|&c| c == self)
            .expect("a carrier")
    }

    /// The carriers of the mask `m`, in the order of [`Carrier::ALL`].
    pub fn of_mask(m: u8) -> impl Iterator<Item = Carrier> {
        Carrier::ALL.into_iter().filter(move |c| m & c.bit() != 0)
    }
}

/// The bit of a mask that stands for every value that is not of a carrier: a tuple, a
/// function, an atom.
pub const OTHER: u8 = 1 << 5;

/// The mask of every value.
pub const EVERY: u8 = (1 << 6) - 1;

/// The clause a message about a check that was refused ends with: the check is not proved to
/// fail, the checker could not decide it, and `why` says why (DESIGN.md sec:diagnostics).
pub fn undecided(why: &str) -> String {
    format!(
        "; this is not proved wrong: the checker could not decide whether it fits, because {why}"
    )
}

/// The mask `m` as a type, in type syntax: `_` when it holds [`OTHER`], since `int | _` is `_`
/// (DESIGN.md L1.26); otherwise its carriers joined by `|`, and `Never`, the empty type, when it
/// holds none.
pub fn mask_text(m: u8) -> String {
    if m & OTHER != 0 {
        return "_".into();
    }
    if m == 0 {
        return "Never".into();
    }
    let names: Vec<&str> = Carrier::of_mask(m).map(Carrier::name).collect();
    names.join(" | ")
}

/// Every atom.
pub fn atoms() -> KType {
    thread_local! {
        /// Made once, so that every use is one node and compares equal to another by pointer.
        static ATOMS: KType = {
            let carriers = Carrier::ALL.iter().fold(KType::empty(), |a, c| a | c.ty());
            KType::universe(Universe::Scalar) - &carriers
        };
    }
    ATOMS.with(KType::clone)
}

/// Every tuple and every struct, the kinds that `set` holds only as the kind-wide part.
pub fn wide() -> KType {
    &KType::universe(Universe::Tuple) | &KType::universe(Universe::Struct)
}

/// The atom `#errs` that two distinct failures merge into, with any payload.
pub fn errs() -> KType {
    KType::atom_with("errs", &KType::top())
}

/// The type of the failures that merge into `#errs`, each from the type `e` of the failures
/// that meet: `#errs(E ->? E)`, the family that maps each distinct failure to itself
/// (DESIGN.md sec:failure), whose exact keys are not kept. Its payload is a family, so its
/// signature is data and prints with `->?`; a lookup in it is a failure of `E` or `#notFound`,
/// as for any `K ->? V` (sec:type_language), which is how the printed type reads back.
pub fn errs_of(e: Ty) -> Ty {
    let param = SParam {
        name: "".into(),
        positional: true,
        default: None,
    };
    let found = e.union(&Ty::set(KType::atom("notFound")));
    let mut family = Sig::one(vec![param], vec![e], found);
    family.data = true;
    let mut t = Ty::set(errs());
    let shape = Shape::new(vec![Ty::func(Arc::new(family))], BTreeMap::new());
    t.payloads.insert("errs".into(), Some(vec![shape]));
    t
}

/// Whether `set` may hold an `#errs` with a payload.
pub fn holds_errs(set: &KType) -> bool {
    holds_payload(set, "errs")
}

/// The failures the `#errs` of `t` may hold, when each of its payloads is a family that
/// [`errs_of`] built: the union of their keys. `None` when `t` holds no `#errs` or an `#errs`
/// whose payload is not known; then what it holds is not known either.
pub fn errs_members(t: &Ty) -> Option<Ty> {
    if !holds_payload(&t.set, "errs") {
        return None;
    }
    let shapes = t.payloads.get("errs")?.as_ref()?;
    let mut keys = Ty::empty();
    for s in shapes {
        let [f] = &s.items[..] else { return None };
        let [sig] = &f.fns[..] else { return None };
        let only_fn = f.set.is_empty() && f.tuples.is_empty() && f.vars.is_empty() && !f.dynamic;
        let [arrow] = &sig.arrows[..] else {
            return None;
        };
        let [key] = &arrow.params[..] else {
            return None;
        };
        if !s.fields.is_empty() || !only_fn || !sig.data {
            return None;
        }
        keys = keys.union(key);
    }
    Some(keys)
}

/// Whether the failures of one application's operands can merge into `#errs`, given the
/// atoms of each operand that may carry one (DESIGN.md sec:failure): whether two of them can
/// carry different failures at once. Equal failures merge into one, and a singleton is the
/// atom itself, so they cannot exactly when fewer than two operands carry atoms, or each one
/// carries only the same payload-free atom, the one value they can all be. An atom with a
/// payload has a value per payload, so two of them can differ. One pass over the operands,
/// each compared with the first: types of different digests differ in `O(1)`, and equal ones
/// are read once (`Type::cmp`), so `O(n)` comparisons for `n` operands, each linear at most in
/// the atom types the checker already built.
pub fn merges<'k>(holding: impl IntoIterator<Item = &'k KType>) -> bool {
    let mut holding = holding.into_iter();
    let Some(first) = holding.next() else {
        return false;
    };
    let mut more = false;
    for t in holding {
        if t != first {
            return true;
        }
        more = true;
    }
    more && !one_bare_atom(first)
}

/// Whether `t` is one payload-free atom: a type of one value.
fn one_bare_atom(t: &KType) -> bool {
    let Some(mut names) = t.atom_names() else {
        return false;
    };
    match (names.next(), names.next()) {
        (Some((name, true)), None) => *t == KType::atom(name),
        _ => false,
    }
}

/// A piece of a type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Piece {
    /// Scalars: the values of one carrier, the atoms, or what is neither.
    Set(KType),
    /// A tuple shape.
    Tuple(Row),
    /// A function.
    Fn(Arc<Sig>),
    /// A type variable.
    Var(Arc<str>),
    /// The unknown.
    Dyn,
}

impl Piece {
    /// The carrier of a scalar piece.
    pub fn carrier(&self) -> Option<Carrier> {
        match self {
            Piece::Set(s) => Carrier::ALL.into_iter().find(|c| s.subtype(&c.ty())),
            _ => None,
        }
    }

    /// Whether it is a piece of atoms.
    pub fn is_atoms(&self) -> bool {
        matches!(self, Piece::Set(s) if s.subtype(&atoms()))
    }

    /// The type of this piece alone.
    pub fn ty(&self) -> Ty {
        match self {
            Piece::Set(s) => Ty::set(s.clone()),
            Piece::Tuple(cs) => Ty::of_row(cs.clone()),
            Piece::Fn(s) => Ty::func(s.clone()),
            Piece::Var(v) => Ty::var(v.clone()),
            Piece::Dyn => Ty::dynamic(),
        }
    }
}

/// The binding of type variables made while applying an arrow.
pub type Binds = BTreeMap<Arc<str>, Ty>;

/// How a comparison reads a variable of the types on one side ([`Env`]).
#[derive(Clone, Debug, PartialEq)]
enum Read {
    /// As the rigid variable of this name, in [`Cx::rigid`].
    Rigid(Arc<str>),
    /// As every value of the carriers of the mask, [`Ty::of_mask`].
    Mask(u8),
}

/// The variables of the function types around one side of a comparison that it reads as
/// something else: the own bounded variables of each expected function type around it, and
/// those of each given one that no parameter holds. Persistent, so that each function met
/// keeps the reading of its own side at the cost of a pointer.
type Env = imbl::OrdMap<Arc<str>, Read>;

/// The type a class variable the checker solved stands for, if it was solved to one that
/// holds no variable: a signature solved before the functions around it keeps such a
/// variable in the functions it holds, and is read through this (CHK-carrier).
pub type Solve<'s> = &'s dyn Fn(&str) -> Option<Ty>;

/// How the modes of [`Ty::replace_in`] replace.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// At every depth: [`Ty::replace`].
    Replace,
    /// At every depth, the own variables of functions too: [`Ty::renamed`].
    Rename,
    /// Outside functions: [`Ty::replace_outside`].
    Outside,
}

/// The state of one comparison of function types ([`fits_sig`], [`Ty::sub`]).
#[derive(Default)]
struct Cx<'s> {
    /// The bounded variables of the expected function types the comparison is inside, each
    /// with the mask of its bound: the caller of such a function picks one carrier of the
    /// bound for each, so a variable here stands for every carrier of its mask and is never
    /// bound.
    rigid: BTreeMap<Arc<str>, u8>,
    /// The functions of the types being compared, each put in its type as a variable of its
    /// own and kept here with the reading of its side: a function moved into the other side,
    /// as a binding of a variable there, is read as it was where it came from.
    fns: BTreeMap<Arc<str>, (Arc<Sig>, Env)>,
    /// The names of `rigid` and `fns` made by the comparisons open now, last made last.
    made: Vec<Arc<str>>,
    /// The number of names made: a quote is in no name a program writes, and the count keeps
    /// the names apart.
    count: usize,
    /// The types of the solved class variables, read where a function's arrows are read.
    solve: Option<Solve<'s>>,
    /// The verdict of each comparison of a function of `fns` with another, by their two
    /// names ([`Comparing::fits_read`]). A failed fit of an arrow is followed by the search for
    /// a cover, which compares the same two results again; without this, a refusal of curried
    /// function types compared each level twice for each level around it, 2^depth in all.
    fitted: HashMap<(Arc<str>, Arc<str>), bool>,
    /// When asked for, by [`why_unfit`], why the outermost comparison failed, if one of the
    /// covers rule 6 of sec:type_resolution gives is refused there: `Some(None)` until it is
    /// found. Only the outermost [`fits_in`] reads it, so a comparison inside, tried and
    /// dropped, gives no reason.
    why: Option<Option<String>>,
    /// Why the comparison was refused, if two members of one side each needed a shape that
    /// [`Choices`] could not single out ([`Comparing::search`]): the first such refusal. A
    /// refused comparison answers false, whatever else it found ([`Cx::decided`]).
    unchosen: Option<String>,
    /// The tuple and payload shapes of each component of a row or payload shape compared, filed
    /// once for the comparison ([`Filed`]), by the address of the row or shape and the
    /// component's place, the row or shape kept so that the address is not reused.
    filed: HashMap<(usize, usize), (Pin, Arc<Filed>)>,
}

impl Cx<'_> {
    /// `ok`, the answer of the comparison this state ran, unless the comparison was refused.
    fn decided(&self, ok: bool) -> bool {
        ok && self.unchosen.is_none()
    }

    /// A new name, from `v`.
    fn fresh(&mut self, v: &str) -> Arc<str> {
        self.count += 1;
        let w: Arc<str> = format!("{v}'{}", self.count).into();
        self.made.push(w.clone());
        w
    }

    /// `t` as the comparison reads it on a side read by `env`: each variable `env` maps
    /// replaced, and each function, outside other functions, replaced by a new variable that
    /// `fns` maps to it and `env`. The payloads stay as they are, since no comparison reads
    /// them. The cost is that of `t` outside its functions, so each function type is read once
    /// for each comparison of it. A class variable `solve` gives a type is read as that type.
    ///
    /// The tuples are read on an explicit stack, each component before the type that holds it
    /// and in order, as the recursive form read them, so the new names are made in the same
    /// order, and a tuple nested to any depth needs no more of the thread's stack.
    fn read(&mut self, t: &Ty, env: &Env) -> Ty {
        /// A type whose tuples are being read: the rows read, and the components read of the
        /// next row.
        struct Reading<'t> {
            t: &'t Ty,
            rows: Vec<Row>,
            row: Vec<Ty>,
        }
        let start = |t| Reading {
            t,
            rows: Vec::new(),
            row: Vec::new(),
        };
        let mut stack = vec![start(t)];
        loop {
            let top = stack
                .last_mut()
                .expect("the type being read is on the stack");
            if let Some(cs) = top.t.tuples.get(top.rows.len()) {
                match cs.get(top.row.len()) {
                    Some(c) => stack.push(start(c)),
                    None => {
                        let row = std::mem::take(&mut top.row).into_iter().collect();
                        top.rows.push(row);
                    }
                }
                continue;
            }
            let Reading { t, rows, .. } = stack.pop().expect("the type being read is on the stack");
            let out = self.read_outer(t, rows, env);
            match stack.last_mut() {
                Some(up) => up.row.push(out),
                None => return out,
            }
        }
    }

    /// [`Self::read`] of `t` whose tuples read as `tuples`: its functions and variables.
    fn read_outer(&mut self, t: &Ty, mut tuples: Vec<Row>, env: &Env) -> Ty {
        // A variable read as the empty type leaves a row with no value.
        tuples.retain(|r| !r.0.void);
        let mut out = Ty {
            set: t.set.clone(),
            tuples,
            fns: Vec::new(),
            vars: BTreeSet::new(),
            dynamic: t.dynamic,
            family: t.family.clone(),
            payloads: t.payloads.clone(),
        };
        for s in &t.fns {
            let w = self.fresh("");
            self.fns.insert(w.clone(), (s.clone(), env.clone()));
            out.vars.insert(w);
        }
        let mut solved = Vec::new();
        for v in &t.vars {
            match env.get(v) {
                None => match self.solve.and_then(|f| f(v)) {
                    Some(u) => solved.push(u),
                    None => {
                        out.vars.insert(v.clone());
                    }
                },
                Some(Read::Rigid(w)) => {
                    out.vars.insert(w.clone());
                }
                Some(&Read::Mask(m)) if m & OTHER != 0 => out.dynamic = true,
                Some(&Read::Mask(m)) => {
                    out.set = Carrier::of_mask(m).fold(out.set, |s, c| &s | &c.ty());
                }
            }
        }
        solved.iter().fold(out, |o, u| o.union(u))
    }

    /// Forgets the names made since `mark`.
    fn forget(&mut self, mark: usize) {
        for w in self.made.drain(mark..) {
            self.rigid.remove(&w);
            self.fns.remove(&w);
        }
    }
}

/// A comparison of function types running on an explicit stack on the heap
/// ([`zed_kernel::frames`]). The comparisons that call each other through the parts of the
/// types compared ([`Comparing::sub_in`], [`accepts`], [`fits_in`], [`every_arrow_fits`],
/// [`arrow_fits`], [`result_within`], and [`covered`], [`part_of`], [`met`], [`meet_within`]
/// and [`refused_cover`]) are `async`, awaited in the frame that calls them; a cycle among
/// them passes through [`accepts`], which starts a frame of its own ([`Comparing::fits`],
/// [`Comparing::rows`]) for a function or a tuple. So types nested to any depth are compared
/// with no more of the thread's stack than shallow ones. Calls are made in the order of the
/// recursive form, with its short-circuits, so the answers and the names made are the same.
///
/// Complexity tradeoff: each frame is a boxed future and each use of the state a check of the
/// `RefCell`, a constant factor over the recursive form, for an O(depth) heap in place of the
/// thread's stack; the order of the work is unchanged. Measured on a fit of curried types
/// 8,000 deep: 60.8 ms and 14.4 G instructions against 59.0 ms and 13.6 G recursive (both runs
/// with building and dropping the types; perf stat, TY-sub-stack, 2026-11-07).
struct Comparing<'m, 's> {
    stack: Stack<'m>,
    /// The comparison's state, borrowed by one statement at a time, never across an `await`,
    /// since the call awaited borrows it too.
    cx: &'m RefCell<Cx<'s>>,
}

/// Runs `$body`, which reads the comparison `$c`, on a stack of its own over the state `$cx`, a
/// `&mut Cx`, which it leaves as the comparison left it.
macro_rules! comparing {
    ($cx:expr, |$c:ident| $body:expr) => {{
        let cx: &mut Cx = $cx;
        let cell = RefCell::new(std::mem::take(cx));
        let v = {
            let $c = Comparing {
                stack: Stack::default(),
                cx: &cell,
            };
            $c.stack.run($body)
        };
        *cx = cell.into_inner();
        v
    }};
}

/// A row or payload shape whose components' shapes are filed in [`Cx::filed`], kept there.
#[expect(
    dead_code,
    reason = "a row or shape is held only so that its address is not reused"
)]
enum Pin {
    Row(Row),
    Shape(Shape),
}

/// Where the type a comparison holds pieces against sits: a component of a row or payload shape
/// of the expected side, at its place (items, then fields), or elsewhere.
#[derive(Clone, Copy)]
enum Site<'a> {
    In(Holder<'a>, usize),
    Other,
}

/// A row or payload shape that holds the type a comparison holds pieces against.
#[derive(Clone, Copy)]
enum Holder<'a> {
    Row(&'a Row),
    Shape(&'a Shape),
}

impl Holder<'_> {
    /// Its address, a key of [`Cx::filed`] with the place.
    fn addr(self) -> usize {
        match self {
            Holder::Row(r) => Arc::as_ptr(&r.0) as usize,
            Holder::Shape(s) => Arc::as_ptr(&s.0) as usize,
        }
    }

    /// It, kept in [`Cx::filed`] while its address is a key.
    fn pin(self) -> Pin {
        match self {
            Holder::Row(r) => Pin::Row(r.clone()),
            Holder::Shape(s) => Pin::Shape(s.clone()),
        }
    }
}

/// What a component of a shape of the expected side holds, for [`Choices`]: one value, the
/// values of one carrier, atoms of one name, or tuples of one length, and nothing else.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ShapeKey {
    /// One scalar literal, or one tuple of such values at any depth ([`Ty::point`]).
    Point(Value),
    /// The values of one carrier.
    Carrier(Carrier),
    /// Atoms named this, bare or with payloads.
    Atom(Arc<str>),
    /// Tuples of this length.
    Row(usize),
}

/// The shapes of one [`Group`] a member is tried against: those filed under a key, or every
/// shape of the group (`None`).
type Bucket = Option<Vec<ShapeKey>>;

/// Where a component of a member may be held, at a place a [`Group`] files.
enum Member {
    /// By no shape: what it holds is held by no component filed there.
    Nowhere,
    /// By any shape: it holds nothing that a component must hold, or the checker does not
    /// find what it holds.
    Anywhere,
    /// By the shapes filed under the key.
    At(ShapeKey),
}

/// The class of a scalar set: the carrier its values are all of, or the one name of its atoms;
/// none for an empty set, which has no part. It is read from the parts of `s` by universe
/// ([`KType::universes`]): a carrier's part is there only when it holds a value, and the atoms
/// and the rest only when they are not empty, so `s` is within a carrier exactly when that
/// carrier's part is its only one, and within the atoms when they are its only part, with no
/// comparison of types.
fn class_of(s: &KType) -> Option<ShapeKey> {
    let split = s.universes();
    let mut carriers = Carrier::ALL.into_iter().filter(|c| split.bases[c.base()]);
    match (carriers.next(), carriers.next(), split.atoms, split.rest) {
        (Some(c), None, false, false) => return Some(ShapeKey::Carrier(c)),
        (None, _, true, false) => {}
        _ => return None,
    }
    let mut names = s.atom_names()?;
    let (n, _) = names.next()?;
    names.next().is_none().then(|| ShapeKey::Atom(n.into()))
}

/// The class of `y`, a component of a shape of the expected side, and its value when it is one
/// value ([`Ty::point`]): a non-empty set of one class ([`class_of`]) that holds no tuple,
/// function, variable or unknown, or tuples of one length and nothing else, of the class of
/// that length. Such a component holds a component of a member only when the member's holds
/// values of its class alone ([`member`]), so the shapes can be filed by it.
fn class(y: &Ty) -> Option<(ShapeKey, Option<Value>)> {
    if y.dynamic || !y.vars.is_empty() || !y.fns.is_empty() {
        return None;
    }
    if let Some(r) = y.tuples.first() {
        let rows_only = y.set.is_empty() && y.family.is_empty();
        let one_length = y.tuples.iter().all(|s| s.len() == r.len());
        return (rows_only && one_length).then(|| (ShapeKey::Row(r.len()), y.point()));
    }
    let k = class_of(&y.set)?;
    Some((k, y.point()))
}

/// Where `x`, a component of a member, may be held at a place a [`Group`] files, by value or by
/// class, as [`accepts`] decides each piece of `x` against a component there ([`class`]):
/// - A function, the unknown or a variable not rigid is held by none, since no such component
///   holds a function or a variable. A rigid variable is held by those that hold each carrier
///   of its bound: by none of one value, and by the class of the carrier for one carrier.
/// - A set is held by the shapes of its value or class.
/// - Tuples are held by those of their length, by class, and by value by those of their value
///   when they are one value. Tuples that are not one value are looked for in every shape filed
///   by value, since a component of no value is in any.
fn member(x: &Ty, by_value: bool, rigid: &BTreeMap<Arc<str>, u8>) -> Member {
    if x.dynamic || !x.fns.is_empty() {
        return Member::Nowhere;
    }
    let mut carrier = None;
    for v in &x.vars {
        let Some(&m) = rigid.get(v) else {
            return Member::Nowhere;
        };
        let mut cs = Carrier::of_mask(m);
        match (cs.next(), cs.next()) {
            (None, _) => {}
            (Some(c), None) if !by_value && carrier.is_none_or(|d| d == c) => carrier = Some(c),
            _ => return Member::Nowhere,
        }
    }
    if let Some(r) = x.tuples.first() {
        if !x.set.is_empty() || carrier.is_some() {
            return Member::Nowhere;
        }
        return match by_value {
            true => match x.point() {
                Some(v) => Member::At(ShapeKey::Point(v)),
                None => Member::Anywhere,
            },
            false => match x.tuples.iter().all(|s| s.len() == r.len()) {
                true => Member::At(ShapeKey::Row(r.len())),
                false => Member::Nowhere,
            },
        };
    }
    if x.set.is_empty() {
        return match carrier {
            Some(c) => Member::At(ShapeKey::Carrier(c)),
            None => Member::Anywhere,
        };
    }
    if by_value {
        return match x.set.scalar() {
            Some(v) => Member::At(ShapeKey::Point(v)),
            None => Member::Nowhere,
        };
    }
    match class_of(&x.set) {
        Some(k) if carrier.is_none_or(|c| k == ShapeKey::Carrier(c)) => Member::At(k),
        _ => Member::Nowhere,
    }
}

/// The shapes of a group of [`Choices`] whose components have a class ([`class`]) at the same
/// places, and are one value at the same places of those, filed by their components there: by
/// value where they are one value, else by class. A shape filed under another key than a
/// member's holds no component of the member's there ([`member`]).
struct Group {
    /// The places filed, each with whether it is filed by value.
    places: Vec<(usize, bool)>,
    /// The shapes under each key, by their index in the list of shapes, in order.
    buckets: BTreeMap<Vec<ShapeKey>, Vec<usize>>,
    /// Every shape of the group, in order.
    all: Vec<usize>,
}

impl Group {
    /// The bucket of the member whose components are `xs`, read with the rigid variables
    /// `rigid`: `None` when no shape of the group holds it.
    fn lookup(&self, xs: &[&Ty], rigid: &BTreeMap<Arc<str>, u8>) -> Option<Bucket> {
        let mut key = Vec::with_capacity(self.places.len());
        let mut anywhere = false;
        for &(j, by_value) in &self.places {
            match member(xs[j], by_value, rigid) {
                Member::Nowhere => return None,
                Member::Anywhere => anywhere = true,
                Member::At(k) => key.push(k),
            }
        }
        if anywhere {
            return Some(None);
        }
        self.buckets.contains_key(&key).then_some(Some(key))
    }

    /// The shapes of the bucket `id`, in order.
    fn bucket(&self, id: &Bucket) -> &[usize] {
        match id {
            None => &self.all,
            Some(k) => &self.buckets[k],
        }
    }
}

/// The shapes of one group of the expected side, its tuples of one length or its payloads of one
/// atom with one length and field names, in [`Group`]s by the places where their components
/// have a class and are one value: a shape with a variable at a place leaves the place filed for
/// the others. The shapes that may hold a member are those of its bucket in each group, and
/// trying them in written order finds the shape the rule of one shape finds, with the same
/// bindings.
struct Choices {
    groups: Vec<Group>,
}

/// The shapes a member may be in: a bucket of each of some groups of [`Choices`], by the
/// group's index.
type Buckets = Vec<(usize, Bucket)>;

impl Choices {
    /// The shapes, each by its index in its list and the keys of its components ([`class`]),
    /// all of one width.
    fn new<'k>(shapes: impl IntoIterator<Item = (usize, &'k [CompKey])>) -> Choices {
        // The groups by the places where a shape's components have a class, each with whether
        // it is one value there; each group's places are set once all are filed.
        let mut by_places: BTreeMap<Vec<(usize, bool)>, Group> = BTreeMap::new();
        for (i, keys) in shapes {
            let mut places = Vec::new();
            let mut key = Vec::new();
            for (j, c) in keys.iter().enumerate() {
                if let Some((k, point)) = c {
                    places.push((j, point.is_some()));
                    key.push(point.clone().map_or_else(|| k.clone(), ShapeKey::Point));
                }
            }
            let group = by_places.entry(places).or_insert_with(|| Group {
                places: Vec::new(),
                buckets: BTreeMap::new(),
                all: Vec::new(),
            });
            group.buckets.entry(key).or_default().push(i);
            group.all.push(i);
        }
        let groups = (by_places.into_iter())
            .map(|(places, group)| Group { places, ..group })
            .collect();
        Choices { groups }
    }

    /// The buckets of the member whose components are `xs`, read with the rigid variables
    /// `rigid`, one for each group that may hold it.
    fn lookup(&self, xs: &[&Ty], rigid: &BTreeMap<Arc<str>, u8>) -> Buckets {
        (self.groups.iter().enumerate())
            .filter_map(|(g, group)| Some((g, group.lookup(xs, rigid)?)))
            .collect()
    }

    /// The shapes of the bucket `id` of the group `g`, in order.
    fn bucket(&self, g: usize, id: &Bucket) -> &[usize] {
        self.groups[g].bucket(id)
    }

    /// The shapes of `buckets`, merged in written order, each with the index in `buckets` of
    /// its bucket and its place in that bucket.
    fn merged<'c>(
        &'c self,
        buckets: &'c Buckets,
    ) -> impl Iterator<Item = (usize, usize, usize)> + 'c {
        use std::cmp::Reverse;
        let shapes: Vec<&[usize]> = (buckets.iter())
            .map(|(g, id)| self.bucket(*g, id))
            .collect();
        // Each bucket's next shape, by the shape first, so the heap yields written order.
        let mut heads: std::collections::BinaryHeap<Reverse<(usize, usize, usize)>> =
            (shapes.iter().enumerate())
                .filter_map(|(k, s)| Some(Reverse((*s.first()?, k, 0))))
                .collect();
        std::iter::from_fn(move || {
            let Reverse((r, k, at)) = heads.pop()?;
            if let Some(&next) = shapes[k].get(at + 1) {
                heads.push(Reverse((next, k, at + 1)));
            }
            Some((k, at, r))
        })
    }

    /// Why the shapes of the bucket `id` of group `g` may each hold the members found in it,
    /// for a message: the members have `items` items, then the fields `names`.
    fn apart(&self, g: usize, id: &Bucket, items: usize, names: &[&Arc<str>]) -> String {
        let places: Vec<String> = (self.groups[g].places.iter())
            .map(|&(j, _)| match j.checked_sub(items) {
                None => format!("component {}", j + 1),
                Some(f) => format!("field {}", names[f]),
            })
            .collect();
        match (id, &places[..]) {
            (_, []) => "have no component that is one value, of one carrier, of one atom name or \
                        of one tuple length"
                .to_string(),
            (None, _) => format!(
                "are told apart only at {}, where each of the two has a component that any of \
                 them may hold",
                places.join(", ")
            ),
            (Some(_), _) => format!(
                "are told apart only at {}, where they agree with both",
                places.join(", ")
            ),
        }
    }
}

/// The components of a payload shape, items then fields, as [`Comparing::shape_in`] pairs them.
fn comps(s: &Shape) -> Vec<&Ty> {
    s.items.iter().chain(s.fields.values()).collect()
}

/// The group of a payload shape: its number of items and its field names.
type ShapeGroup = (usize, Vec<Arc<str>>);

fn shape_group(s: &Shape) -> ShapeGroup {
    (s.items.len(), s.fields.keys().cloned().collect())
}

/// The tuple and payload shapes of a type of the expected side, grouped and filed ([`Choices`]):
/// the tuples by length, the payloads of each atom it lists by [`ShapeGroup`].
struct Filed {
    rows: HashMap<usize, Choices>,
    payloads: HashMap<Arc<str>, HashMap<ShapeGroup, Choices>>,
}

impl Filed {
    /// In the size of `t`'s tuples and payloads. The keys of the tuples are those each row
    /// keeps ([`Row::keys`]); those of a payload shape are found here.
    fn new(t: &Ty) -> Filed {
        let mut rows: HashMap<usize, Vec<(usize, &[CompKey])>> = HashMap::new();
        for (i, r) in t.tuples.iter().enumerate() {
            rows.entry(r.len()).or_default().push((i, &r.keys().comps));
        }
        let mut payloads = HashMap::new();
        for (n, rs) in &t.payloads {
            let Some(rs) = rs else { continue };
            let mut groups: HashMap<ShapeGroup, Vec<(usize, Vec<CompKey>)>> = HashMap::new();
            for (i, r) in rs.iter().enumerate() {
                let keys = comps(r).into_iter().map(class).collect();
                groups.entry(shape_group(r)).or_default().push((i, keys));
            }
            let groups = groups.into_iter();
            payloads.insert(
                n.clone(),
                groups
                    .map(|(g, s)| (g, Choices::new(s.iter().map(|(i, k)| (*i, &k[..])))))
                    .collect(),
            );
        }
        Filed {
            rows: rows
                .into_iter()
                .map(|(n, s)| (n, Choices::new(s)))
                .collect(),
            payloads,
        }
    }
}

/// A component's class and its value when it is one value ([`class`]); none when it has no
/// class.
type CompKey = Option<(ShapeKey, Option<Value>)>;

/// What a component of a tuple holds, as [`near_pairs`] groups tuples by it: no class, a class
/// and more than one value, or one value.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Kind {
    Open,
    Class,
    Point,
}

fn kind(k: &CompKey) -> Kind {
    match k {
        None => Kind::Open,
        Some((_, None)) => Kind::Class,
        Some((_, Some(_))) => Kind::Point,
    }
}

/// What a row keeps to be filed ([`Row::keys`]): the keys of its components, and what each
/// filing reads from them, shared so that filing the row again copies no key.
struct Keys {
    /// The class of each component and its value where it is one value ([`class`]).
    comps: Box<[CompKey]>,
    /// The [`Kind`] of each component, by which [`near_pairs`] groups tuples.
    kinds: Box<[Kind]>,
    /// The [`Kind`] at each place as [`Holders`] groups tuples, and the key it files the tuple
    /// under in its group.
    held: (Arc<[Kind]>, HeldKey),
}

/// The key of a tuple in its group of [`Holders`]: the class at each place where the group has
/// one, with the value where it has one value.
type HeldKey = Arc<[(ShapeKey, Option<Value>)]>;

impl Keys {
    fn new(comps: Box<[CompKey]>) -> Keys {
        let kinds = comps.iter().map(kind).collect();
        let mut held = Vec::with_capacity(comps.len());
        let mut key = Vec::new();
        for c in &comps {
            match c {
                None => held.push(Kind::Open),
                // A component that is one tuple value is filed by its length only ([`Holders`]).
                Some((k @ ShapeKey::Row(_), _)) | Some((k, None)) => {
                    held.push(Kind::Class);
                    key.push((k.clone(), None));
                }
                Some((k, Some(v))) => {
                    held.push(Kind::Point);
                    key.push((k.clone(), Some(v.clone())));
                }
            }
        }
        Keys {
            comps,
            kinds,
            held: (held.into(), key.into()),
        }
    }
}

/// The tuples of one length and one [`Kind`] at each place, each by its index in its list and
/// the keys of its components, which its row keeps ([`Row::keys`]).
type Pattern<'r> = (usize, Cow<'r, [Kind]>);
type Keyed<'r> = Vec<(usize, &'r [CompKey])>;
/// One group of the right side of [`Groups`]: the kind at each place and its tuples.
type RightGroup<'r> = (Cow<'r, [Kind]>, Keyed<'r>);

/// The tuples of `rows`, each with the keys of its components, by length and [`Kind`] at each
/// place, each list in written order.
fn by_pattern(rows: &[Row]) -> FMap<Pattern<'_>, Keyed<'_>> {
    let mut out: FMap<Pattern<'_>, Keyed<'_>> = FMap::default();
    for (i, r) in rows.iter().enumerate() {
        let Keys { comps, kinds, .. } = r.keys();
        let kinds = Cow::Borrowed(&kinds[..]);
        // With every place open every tuple of a length is one group, no key is read
        // ([`project`]), and every tuple of the other side of that length is near it.
        #[cfg(test)]
        let kinds = match NEAR_ALL.get() {
            true => Cow::Owned(vec![Kind::Open; r.len()]),
            false => kinds,
        };
        out.entry((r.len(), kinds)).or_default().push((i, comps));
    }
    out
}

/// For each tuple of `left`, the tuples of `right` of its length that may share a value with
/// it, by their indices, in written order ([`Near`]). A tuple of `right` left out shares no
/// value with the tuple of `left`: their meet is empty ([`Ty::meet`] gives an empty component
/// at the place), and the union of `right` holds the tuple exactly when the union of the tuples
/// given holds it.
fn near_pairs(left: &[Row], right: &[Row]) -> Vec<Vec<usize>> {
    let groups = Groups::new(left, right);
    let mut near = Near::new(&groups);
    let mut sorted = |l| {
        let mut is: Vec<usize> = near.of(l).collect();
        is.sort_unstable();
        is
    };
    (0..left.len()).map(&mut sorted).collect()
}

/// The tuples of two lists `left` and `right` grouped for [`Near`]: by length and [`Kind`] at
/// each place, each with the keys of its components.
struct Groups<'r> {
    /// The groups of `right`, by length.
    right: FMap<usize, Vec<RightGroup<'r>>>,
    /// The groups of `left`, each its length and kinds.
    left: Vec<Pattern<'r>>,
    /// For each tuple of `left`, its group and the keys of its components; none when `right` has
    /// no tuple.
    of: Vec<Option<(usize, &'r [CompKey])>>,
}

impl<'r> Groups<'r> {
    fn new(left: &'r [Row], right: &'r [Row]) -> Groups<'r> {
        let mut groups = Groups {
            right: FMap::default(),
            left: Vec::new(),
            of: vec![None; left.len()],
        };
        if left.is_empty() || right.is_empty() {
            return groups;
        }
        for ((len, kinds), rows) in by_pattern(right) {
            groups.right.entry(len).or_default().push((kinds, rows));
        }
        for (pattern, members) in by_pattern(left) {
            for (l, keys) in members {
                groups.of[l] = Some((groups.left.len(), keys));
            }
            groups.left.push(pattern);
        }
        groups
    }
}

/// The right tuples of the groups of one length, each group filed by the keys a group of the
/// left side reads ([`Near`]).
type Filing<'g> = Vec<FMap<Vec<(&'g ShapeKey, Option<&'g Value>)>, Vec<usize>>>;

/// For each tuple of a list `left`, the tuples of a list `right` of its length that may share
/// a value with it ([`Groups`]). Two components share no value when both have a class
/// ([`class`]) and the classes differ, or both are one value and the values differ: the
/// carriers, the atoms of each name and the tuples of each length are disjoint, and two values
/// the kernel tells apart are unequal [`Value`]s. Any two other components may share one, so a
/// tuple of `right` not given for a tuple of `left` shares no value with it.
///
/// For a group of each side, a tuple of one may share a value with a tuple of the other exactly
/// when they agree at each place where both have a class: on the class, and on the value where
/// both are one value. So the tuples of each right group are filed by those keys, and each
/// tuple of the left group finds its own by one lookup. The right groups are filed for a left
/// group when the first tuple of the left group is read, so a reader that stops at the first
/// pair it wants ([`Ty::meets`]) files only the groups read before it.
///
/// Complexity tradeoff: each group of one side is filed or looked up once for each group of
/// the other of its length. What is given up: the cost is expected O((l·G + r·H)·w + l·G·log G)
/// (hash maps; the log G sorts the buckets found into one order) for `l` and `r` tuples of width `w` in `H` and `G` groups, and a reader pays for each pair it
/// reads, up to `l·r`, so `n` tuples in about `n` groups on each side cost about `n^2`. Why: a
/// tuple of points and wildcards encodes a vector of bits (1 as the point `1` on one side and
/// `0` on the other, 0 as `int`), so that two such tuples share a value exactly when the vectors
/// are orthogonal; finding whether any of `n` vectors of about `c·log n` bits is orthogonal to
/// another, which is what `meets` decides on them, takes `n^(2-o(1))` time unless the strong
/// exponential time hypothesis fails, even when no pair is found, and the groups of such tuples
/// are then as many as the tuples. In a written union the groups are few. Structure: `n` tuples
/// of width `2·log2 n`, each a different arrangement of points and `int`. Tests:
/// `tests/steps/l01_22_type_representation/kinds.rs`,
/// `meeting_and_subtracting_tuples_of_many_patterns_costs_the_patterns` and
/// `meets_of_tuples_of_many_patterns_costs_the_patterns`; COMPLEXITY.md F127 and F132. A
/// complete solution does not exist under that hypothesis; one could only refuse such unions,
/// which would change the answers of narrowing that are found today.
struct Near<'g> {
    groups: &'g Groups<'g>,
    /// For each group of `left` once one of its tuples is read, the right groups of its length
    /// filed by its keys, in the order of `groups.right`.
    filed: Vec<Option<Filing<'g>>>,
}

impl<'g> Near<'g> {
    fn new(groups: &'g Groups<'g>) -> Near<'g> {
        Near {
            groups,
            filed: (0..groups.left.len()).map(|_| None).collect(),
        }
    }

    /// The tuples of `right` that may share a value with the tuple `l` of `left`, bucket by
    /// bucket, the buckets in the order of their first tuples, each in written order.
    fn of(&mut self, l: usize) -> impl Iterator<Item = usize> + '_ {
        let groups = self.groups;
        let mut buckets: Vec<&[usize]> = Vec::new();
        if let Some((q, keys)) = &groups.of[l] {
            let (len, kinds) = &groups.left[*q];
            let right = groups.right.get(len).map_or(&[][..], Vec::as_slice);
            let filed = self.filed[*q].get_or_insert_with(|| {
                let file = |(p, rows): &'g RightGroup<'g>| {
                    let mut f: FMap<_, Vec<usize>> = FMap::default();
                    for (i, ks) in rows {
                        f.entry(project(ks, p, kinds)).or_default().push(*i);
                    }
                    f
                };
                right.iter().map(file).collect()
            });
            for (f, (p, _)) in filed.iter().zip(right) {
                if let Some(b) = f.get(&project(keys, kinds, p)) {
                    buckets.push(b);
                }
            }
            // The groups of `right` come in no fixed order; their buckets, which hold no tuple
            // twice, are read by first tuple, so that a reader tries the pairs in one order on
            // every run.
            buckets.sort_unstable_by_key(|b| b[0]);
        }
        buckets.into_iter().flatten().copied()
    }
}

/// The keys of the components `keys` of a tuple of the group `p` at the places where the tuples
/// of the group `q` of the other side have a class too, with the value where both are one value.
fn project<'k>(
    keys: &'k [CompKey],
    q: &[Kind],
    p: &[Kind],
) -> Vec<(&'k ShapeKey, Option<&'k Value>)> {
    (keys.iter().zip(q.iter().zip(p)))
        .filter_map(|(key, (&q, &p))| {
            let (k, v) = key.as_ref()?;
            match (q, p) {
                (Kind::Open, _) | (_, Kind::Open) => None,
                (Kind::Point, Kind::Point) => Some((k, v.as_ref())),
                _ => Some((k, None)),
            }
        })
        .collect()
}

/// The class of a value, as [`class`] gives the class of a component that holds it: the
/// carrier of a boolean, number or string, the name of an atom, the length of a tuple. None
/// for a keypath or a family, which no component with a class holds: such a component holds
/// no function, and its set is within one carrier, within the atoms of one name, or empty
/// beside its tuples.
fn value_class(x: &Value) -> Option<ShapeKey> {
    Some(match x {
        Value::Bool(_) => ShapeKey::Carrier(Carrier::Bool),
        Value::Int(_) | Value::Big(_) => ShapeKey::Carrier(Carrier::Int),
        Value::Rat(_) => ShapeKey::Carrier(Carrier::Rat),
        Value::Float(_) => ShapeKey::Carrier(Carrier::F64),
        Value::Str(_) => ShapeKey::Carrier(Carrier::Str),
        Value::Atom(a) => ShapeKey::Atom(a.name.clone()),
        Value::Tuple(xs) => ShapeKey::Row(xs.len()),
        Value::Path(_) | Value::Family(_) => return None,
    })
}

/// The tuples of one length of a type, filed for the tuple values [`Ty::contains`] looks for
/// in them ([`Pairs::contains`]): in groups by [`Kind`] at each place, and in each group by
/// their classes at the places where they have one and their values where they are one
/// scalar value. A tuple holds a value only when, at each such place, the value's component
/// is of that class ([`value_class`]) and, where the tuple's component is one value, equal to
/// it; so each group is looked up once by the value's own key, and a tuple of no group's
/// bucket does not hold the value.
///
/// A component that is one tuple value is filed by its length only: comparing a value's
/// component with it would read the two whole, and a value compared with many types would be
/// read once for each, where the walk of the pair compares them through the memo of pairs.
///
/// Complexity tradeoff: each group is looked up once for each value. What is given up: the
/// cost is expected O(l·w + G·log G) to file `l` tuples of width `w` (hash maps; the groups are
/// sorted into one order) and O(g·w + p) per value
/// for the `g` groups looked up (at most `G`, the groups) and `p` tuples found before one
/// holds the value, so `l` tuples in about `l` groups, against `r` values,
/// cost about `l·r`. Why: a tuple of points and `int` encodes a vector of bits (1 as the point
/// `0`, 0 as `int`), and a tuple value of zeros and ones holds in it exactly when the two
/// vectors are orthogonal; deciding for each of `r` vectors of about `c·log n` bits whether one
/// of `l` such vectors is orthogonal to it is the orthogonal vectors problem, `n^(2-o(1))`
/// unless the strong exponential time hypothesis fails. In a written union the groups are
/// few. Structure: `n` tuples of width `2·log2 n`, each a different arrangement of points and
/// `int`. Test: `tests/steps/l01_22_type_representation/kinds.rs`,
/// `contains_of_tuples_of_many_patterns_costs_the_patterns`; COMPLEXITY.md F133. A complete
/// solution does not exist under that hypothesis; one could only refuse such unions, which
/// would refuse values the type holds.
struct Holders {
    /// Each group's kinds, and its tuples under each key, by their index in the type's tuples,
    /// in written order; the groups in the order of their first tuple.
    groups: Vec<(Arc<[Kind]>, ByKey)>,
}

/// The tuples of one group of [`Holders`] under their key ([`HeldKey`]).
type ByKey = FMap<HeldKey, Vec<usize>>;

/// A hash map of the filings of tuples ([`Holders`], [`Groups`], [`Near`]), hashed by
/// [`Digest`]: with no seed, so the same on every run, though no result depends on its order.
/// Each filing puts what it finds in written order itself.
type FMap<K, V> = HashMap<K, V, FilingHash>;

/// The hasher of [`FMap`]: [`Digest`] from no seed, or in a test from `SEED` when it is set.
#[derive(Clone, Copy, Default)]
struct FilingHash;

impl std::hash::BuildHasher for FilingHash {
    type Hasher = Digest;

    #[cfg(not(test))]
    fn build_hasher(&self) -> Digest {
        Digest::default()
    }

    #[cfg(test)]
    fn build_hasher(&self) -> Digest {
        let mut h = Digest::default();
        if SEED.get() != 0 {
            std::hash::Hasher::write_u64(&mut h, SEED.get());
        }
        h
    }
}

#[cfg(test)]
thread_local! {
    /// The seed of the hasher of the filings ([`FilingHash`]), for the test that their results do
    /// not depend on it.
    static SEED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

impl Holders {
    /// The tuples `rows` of `t`, by their indices, filed.
    fn new(t: &Ty, rows: &[usize]) -> Holders {
        // Each group's first tuple, by which the groups are put in order.
        let mut groups: FMap<Arc<[Kind]>, (usize, ByKey)> = FMap::default();
        for &i in rows {
            let (kinds, key) = &t.tuples[i].keys().held;
            let (_, filed) = (groups.entry(kinds.clone())).or_insert_with(|| (i, FMap::default()));
            filed.entry(key.clone()).or_default().push(i);
        }
        let mut groups: Vec<_> = groups.into_iter().collect();
        groups.sort_unstable_by_key(|(_, (first, _))| *first);
        Holders {
            groups: groups
                .into_iter()
                .map(|(kinds, (_, filed))| (kinds, filed))
                .collect(),
        }
    }

    /// The tuples that may hold the tuple value of `items`, group by group, each looked up
    /// only when the tuples before it have been read, so that a value held by a tuple of an
    /// early group costs the lookups up to that group only. The order is the same on every run.
    fn of<'h>(&'h self, items: &'h Items) -> impl Iterator<Item = usize> + 'h {
        let classes: Vec<Option<ShapeKey>> = items.iter().map(value_class).collect();
        let mut key = Vec::with_capacity(items.len());
        self.groups.iter().flat_map(move |(kinds, filed)| {
            // A group of one key, as each group is when every tuple is its own arrangement, is
            // compared with the value place by place, stopping at the first that differs,
            // instead of building and hashing the value's whole key: the same answer, since
            // the lookup also compares the keys for equality.
            let one = (filed.len() == 1).then(|| filed.iter().next()).flatten();
            let mut places = one.map(|(held, _)| held.iter());
            key.clear();
            for ((k, x), kind) in classes.iter().zip(items.iter()).zip(kinds.iter()) {
                if *kind == Kind::Open {
                    continue;
                }
                let Some(k) = k else {
                    return [].iter().copied();
                };
                // The group's tuples are one scalar value here ([`Keys::new`]), so a value's
                // atom or tuple, which may be large, is in none of them and is not hashed.
                if *kind == Kind::Point && !matches!(k, ShapeKey::Carrier(_)) {
                    return [].iter().copied();
                }
                let point = (*kind == Kind::Point).then_some(x);
                match places.as_mut().map(Iterator::next) {
                    Some(Some((hk, hx))) if hk == k && hx.as_ref() == point => {}
                    Some(_) => return [].iter().copied(),
                    None => key.push((k.clone(), point.cloned())),
                }
            }
            match one {
                Some((_, found)) => found.as_slice(),
                None => filed.get(&key[..]).map_or(&[][..], Vec::as_slice),
            }
            .iter()
            .copied()
        })
    }
}

/// How the tuples of one length of a type are read for the values [`Pairs::contains`] looks
/// for in them, by the number of values read so far.
enum Visits {
    /// One value read, by a scan of all the type's tuples, which lists none of them.
    Once,
    /// `n` values read, each by a scan of `rows`, the tuples of the length, which the walk of
    /// each value shares.
    Scanned { n: usize, rows: Rc<[usize]> },
    /// Filed, and each value read by lookup.
    Filed(Rc<Holders>),
}

/// The tuples of a type to compare with one tuple value ([`Pairs::tried`]): every tuple of its
/// length, found by a scan of all the type's tuples; those of its length, listed; or those
/// [`Holders`] finds, which the walk of each value shares.
enum Tried {
    Every,
    Scanned(Rc<[usize]>),
    Found(Rc<Holders>),
}

/// The tuples of each length of each type node read by one [`Ty::contains`], by the node's
/// address, which stays put while the type is borrowed.
type Filings = HashMap<(*const Ty, usize), Visits>;

#[cfg(test)]
thread_local! {
    /// How [`Pairs::contains`] reads the tuples of a type, for the differential test: `None`
    /// as in use, `Some(false)` by a scan of every tuple of the length for each value, as
    /// before [`Holders`], and `Some(true)` filed from the first value on.
    static FILE: std::cell::Cell<Option<bool>> = const { std::cell::Cell::new(None) };
}

#[cfg(test)]
thread_local! {
    /// Whether [`near_pairs`] gives every tuple of the length, as meeting and subtracting did
    /// before it: the form the differential test compares it with.
    static NEAR_ALL: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
thread_local! {
    /// Whether [`Comparing::search`] tries every shape in written order and refuses nothing, as
    /// before the index: the form the differential test compares the index with.
    static SCAN_ALL: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// What the comparison of the pieces of one type with a type `t` of the expected side keeps
/// between the pieces: where `t` sits, its shapes filed once a piece needs them, and the
/// buckets of its tuple shapes searched past their first shape, each with the tuple that did.
struct Search<'a> {
    site: Site<'a>,
    filed: Option<Arc<Filed>>,
    searched: BTreeMap<(usize, usize, Bucket), Row>,
}

impl<'a> Search<'a> {
    fn new(site: Site<'a>) -> Search<'a> {
        Search {
            site,
            filed: None,
            searched: BTreeMap::new(),
        }
    }
}

/// A type of one payload shape or one union of payload shapes of the atom `n`, for a message.
fn payload_text(n: &str, shapes: Vec<Shape>) -> String {
    let mut t = Ty::set(KType::atom_with(n, &KType::top()));
    t.payloads.insert(n.into(), Some(shapes));
    t.to_string()
}

/// Why two members, `first` and `second`, of a union were refused ([`Comparing::search`]): each
/// may be held by a later one of the shapes `bucket`, which `apart` describes
/// ([`Choices::apart`]), and the checker looks through them for one of the two only. `own`
/// is the shape of its own [`own_shape`] gives `first`, when there is one.
fn unchosen_text(
    what: &str,
    first: &str,
    second: &str,
    bucket: &str,
    apart: &str,
    own: Option<(String, String)>,
) -> String {
    let own = match own {
        // A shape that files `first` under a key of its own is the first shape of its bucket,
        // so only `second` searches past a first shape, and the comparison is decided.
        Some((place, shape)) => format!(
            "give {first} a shape of its own, written just before the shape that should hold \
             it and the same as that shape except at {place}: `{shape}`, with that shape's \
             other components in place of each `…`; or "
        ),
        None => String::new(),
    };
    format!(
        "the {what} {first} and {second} may each be held by one of the shapes {bucket}, which \
         {apart}, and neither is held by the first of those shapes; which shape \
         holds each decides what the type variables are bound to, and the checker looks \
         through those shapes for one of the two only; to repair it, {own}test the value with \
         `is` first, so that each test meets one of the two"
    )
}

/// A shape of its own for the member whose components are `first`, for a repair: the place of
/// the first component where `first` has a class ([`class`]) that `second` does not have
/// there, and the shape with `first`'s component there and `…` elsewhere, written by `write`
/// from its components. Filed under that key, the shape holds `first` and not `second`.
/// None when no component tells the two apart so.
fn own_shape(
    first: &[&Ty],
    second: &[&Ty],
    items: usize,
    names: &[&Arc<str>],
    write: impl FnOnce(String) -> String,
) -> Option<(String, String)> {
    let key = |c: &Ty| class(c).map(|(k, point)| point.map_or(k, ShapeKey::Point));
    let j = (0..first.len()).find(|&j| key(first[j]).is_some_and(|k| key(second[j]) != Some(k)))?;
    let comps: Vec<String> = (0..first.len())
        .map(|i| {
            let c = if i == j {
                first[i].to_string()
            } else {
                "…".to_string()
            };
            match i.checked_sub(items) {
                None => c,
                Some(f) => format!("{}: {c}", names[f]),
            }
        })
        .collect();
    let place = match j.checked_sub(items) {
        None => format!("component {}, where it is {}", j + 1, first[j]),
        Some(f) => format!("field {}, where it is {}", names[f], first[j]),
    };
    Some((place, write(comps.join(", "))))
}

impl<'m, 's> Comparing<'m, 's> {
    /// [`fits_in`] in a frame of its own.
    fn fits(&'m self, s: Arc<Sig>, se: Env, q: Arc<Sig>, qe: Env) -> Deep<'m, bool> {
        self.stack
            .call(move || async move { fits_in(&s, &se, &q, &qe, self).await })
    }

    /// Whether the function read as the variable `v`, `s` read by `se`, fits the one read as
    /// `w`, if `w` is one ([`fits_in`]): compared once for each pair of names, the verdict kept
    /// in `fitted`. The verdict depends on the two signatures, their readings, the bounds of
    /// the rigid variables those readings name, made before `v` and `w` and kept while they
    /// are, and `solve`, fixed for the comparison; `why` is read only by the outermost
    /// [`fits_in`], which is not one of these. A name is never made again in one state, and
    /// [`Comparing::diff`] sets this memo aside with the names, so a kept verdict is never read
    /// for other functions. The names are keys by identity: each is one function as read.
    async fn fits_read(&'m self, v: &Arc<str>, s: &Arc<Sig>, se: &Env, w: &Arc<str>) -> bool {
        let key = (v.clone(), w.clone());
        let (q, qe) = {
            let cx = self.cx.borrow();
            if let Some(&ok) = cx.fitted.get(&key) {
                return ok;
            }
            match cx.fns.get(w) {
                Some(f) => f.clone(),
                None => return false,
            }
        };
        let ok = self.fits(s.clone(), se.clone(), q, qe).await;
        self.cx.borrow_mut().fitted.insert(key, ok);
        ok
    }

    /// Whether each component of `cs` is in the one of `ds` at its place
    /// ([`Comparing::sub_by_shape`]), in order, stopping at the first that is not, in a frame
    /// of its own: with `b` and what it binds.
    fn rows(&'m self, cs: Row, ds: Row, mut b: Binds) -> Deep<'m, (bool, Binds)> {
        self.stack.call(move || async move {
            for (j, (c, d)) in cs.iter().zip(&ds).enumerate() {
                if !self
                    .sub_by_shape(c, d, &mut b, Site::In(Holder::Row(&ds), j))
                    .await
                {
                    return (false, b);
                }
            }
            (true, b)
        })
    }

    /// [`Ty::sub`] of `t` and `other` inside the comparisons of function types the state holds.
    async fn sub_in(&'m self, t: &Ty, other: &Ty, binds: &mut Binds) -> bool {
        self.sub_near(t, other, None, binds).await
    }

    /// [`Comparing::sub_in`]. When `t` is one tuple, `near` may give the part of `other` that
    /// may share a value with it ([`near_pairs`]), what is read once of `other` ([`Whole`]) and
    /// its shapes filed: the kernel then decides on that part ([`Comparing::near_form`]), and
    /// the rule of one shape reads `other` through the shapes filed.
    async fn sub_near(
        &'m self,
        t: &Ty,
        other: &Ty,
        near: Option<(&Ty, &Whole, &Arc<Filed>)>,
        binds: &mut Binds,
    ) -> bool {
        // The scalars, atoms with their payloads, kind-wide part and tuples of `t` are decided
        // together, once, by the kernel on their normal forms ([`Comparing::by_form`]), which
        // sees shapes that hold a piece only together. Trying each shape of `other` in turn
        // cost every shape times the components; the kernel splits the components once. Where
        // the normal form is not made (a variable, which a shape of `other` may bind) or the
        // kernel refused, each piece is tried by the rule of one shape, which is sound.
        let mut form: Option<Option<bool>> = None;
        let mut search = Search::new(Site::Other);
        if let Some((_, _, filed)) = near {
            search.filed = Some(filed.clone());
        }
        for p in t.pieces() {
            // A set piece with no kind-wide part, of a `t` that lists no payload, is decided by
            // the set alone ([`accepts`]): building both sides' kernel types for it cost each
            // comparison of a large set its size again, with a value built when it fails.
            let plain = |s: &KType| t.payloads.is_empty() && (s & &wide()).is_empty();
            let decided = match &p {
                Piece::Set(s) if plain(s) => None,
                Piece::Set(_) | Piece::Tuple(_) => match form {
                    Some(d) => d,
                    None => *form.insert(match near {
                        Some((near, whole, _)) => self.near_form(t, near, whole).await,
                        None => self.by_form(t, other).await,
                    }),
                },
                _ => None,
            };
            let ok = match decided {
                Some(ok) => ok,
                None => accepts(other, &p, t, binds, &mut search, self).await,
            };
            if !ok {
                return false;
            }
        }
        true
    }

    /// Whether the scalars, atoms with their payloads, kind-wide part and tuples of `t` are all
    /// in `other`, decided by the kernel on the normal forms of the two sides ([`Forms`]), or
    /// nothing where the forms are not made or the kernel refused. False, with no pair tried,
    /// for the class [`Forms::tie`] names.
    async fn by_form(&'m self, t: &Ty, other: &Ty) -> Option<bool> {
        if other.dynamic {
            return Some(true);
        }
        // A variable of `other` may be bound to a piece, which the forms do not do.
        if !other.vars.is_empty() {
            return None;
        }
        let verdict = match (t.exact_data(), other.exact_data()) {
            (Some(a), Some(b)) => a.subtype_verdict(&b),
            _ => {
                let right = Right::of(other)?;
                self.form_verdict(t, other, &right.fns, &right).await?
            }
        };
        held(verdict)
    }

    /// [`Comparing::by_form`] of the tuple `t` and the type `whole` reads, from `near`: `whole`
    /// with only its tuples that may share a value with `t` ([`near_pairs`]). The kernel holds
    /// `t` in `near` exactly when it holds it in `whole`; which way is taken, and which
    /// functions are compared, is read from `whole`, as [`Comparing::by_form`] reads it.
    async fn near_form(&'m self, t: &Ty, near: &Ty, whole: &Whole) -> Option<bool> {
        if near.dynamic {
            return Some(true);
        }
        if !near.vars.is_empty() {
            return None;
        }
        let verdict = match (t.exact_data(), &whole.rest) {
            (Some(a), Some(rest)) => {
                let rows = near.tuples.iter().map(|r| r.0.exact.clone());
                let rows = rows.collect::<Option<Vec<_>>>()?;
                a.subtype_verdict(&KType::union_all(std::iter::once(rest.clone()).chain(rows)))
            }
            _ => {
                let right = whole.right.as_ref()?;
                let near_fns = Forms::fns(near, false, &mut HashSet::new())?;
                self.form_verdict(t, near, &near_fns, right).await?
            }
        };
        held(verdict)
    }

    /// The kernel's verdict on the normal forms of `t` and `other` ([`Forms`]), or nothing
    /// where they are not made; [`Verdict::Inhabited`], with no pair tried, for the class
    /// [`Forms::tied`] names. `other` is the type compared with, or the part of it that may
    /// share a value with `t`, whose functions at each place are `fns`; `whole` reads the type
    /// compared with.
    async fn form_verdict(
        &'m self,
        t: &Ty,
        other: &Ty,
        fns: &PlaceFns,
        whole: &Right,
    ) -> Option<Verdict> {
        let mut forms = Forms::default();
        let left = Forms::fns(t, true, &mut forms.fields)?;
        forms.fields.extend(whole.fields.iter().cloned());
        if forms.tied(&left, &whole.fns).is_some() {
            return Some(Verdict::Inhabited);
        }
        for f in left.values().flatten() {
            forms.id(f);
        }
        forms.number_marks();
        // Each function of `t` not on the same place of `other` is compared with each of
        // `other` there: by [`Forms::tied`], one side has at most one, so the pairs are as many
        // as the functions.
        for (place, gs) in fns {
            let Some(fs) = left.get(place) else { continue };
            let all = whole.fns.get(place).unwrap_or(gs);
            let unlike: Vec<&Arc<Sig>> = fs.iter().filter(|f| !all.contains(*f)).collect();
            for g in gs {
                let mut fit = Vec::new();
                if fs.contains(g) {
                    fit.push(forms.id(g));
                }
                for f in &unlike {
                    let (f, g) = ((*f).clone(), g.clone());
                    if self.fits(f.clone(), Env::new(), g, Env::new()).await {
                        fit.push(forms.id(&f));
                    }
                }
                forms.fits.insert((place.clone(), g.clone()), fit);
            }
        }
        let a = forms.form(t, true);
        let b = forms.form(other, false);
        Some(a.subtype_verdict(&b))
    }

    /// Whether each component and field of the payload `a` is in the one of `b` at its place
    /// ([`Comparing::sub_by_shape`]), `b` of as many items and the same field names, in a
    /// frame of its own: with `b` and what it binds.
    fn shape_in(&'m self, a: Shape, b: Shape, mut binds: Binds) -> Deep<'m, (bool, Binds)> {
        self.stack.call(move || async move {
            let pairs =
                (a.items.iter().zip(&b.items)).chain(a.fields.values().zip(b.fields.values()));
            for (j, (x, y)) in pairs.enumerate() {
                if !self
                    .sub_by_shape(x, y, &mut binds, Site::In(Holder::Shape(&b), j))
                    .await
                {
                    return (false, binds);
                }
            }
            (true, binds)
        })
    }

    /// The tuple and payload shapes of `t`, the type `search` compares pieces with, filed
    /// ([`Filed`]): once for the pieces of one type, and once for the whole comparison where `t`
    /// is a component of a row or payload shape, which a comparison may meet once for each
    /// member of a union on the other side.
    fn filed(&self, t: &Ty, search: &mut Search<'_>) -> Arc<Filed> {
        if let Some(f) = &search.filed {
            return f.clone();
        }
        let f = match search.site {
            Site::Other => Arc::new(Filed::new(t)),
            Site::In(h, j) => {
                let mut cx = self.cx.borrow_mut();
                let (_, f) = (cx.filed.entry((h.addr(), j)))
                    .or_insert_with(|| (h.pin(), Arc::new(Filed::new(t))));
                f.clone()
            }
        };
        search.filed = Some(f.clone());
        f
    }

    /// Records why the comparison is refused, the first time; `why` is made only then.
    fn refuse(&self, why: impl FnOnce() -> String) {
        let mut cx = self.cx.borrow_mut();
        if cx.unchosen.is_none() {
            cx.unchosen = Some(why());
        }
    }

    /// The search for the shape of `choices`'s group that holds the member `member.1`, of the
    /// group `member.0`, whose components are `xs`: the shapes of its buckets
    /// ([`Choices::lookup`]), merged in written order, each tried by `fit` with the bindings so
    /// far, the first that holds it keeping what it binds. The rule of one shape tries every
    /// shape of the group in order; a shape outside the buckets holds no member of them, so the
    /// shape found and the bindings are the same. `Ok(false)` when none holds it, and at once
    /// when the comparison was refused, since it then answers false.
    ///
    /// Complexity tradeoff: a bucket is searched past its first shape for one member of a union
    /// only; the next member of the same union that needs a later shape of the same bucket is
    /// refused (`Err`, with the member that searched it, the group of [`Choices`] and the
    /// bucket), and the comparison answers false ([`Cx::decided`]) with the reason
    /// [`Ty::refused`] gives. What is given up: the verdict of the rule of one shape where two
    /// members each need a later shape of one bucket, such as two members that the first shape
    /// of a bucket does not hold, in a bucket of shapes that agree at every place filed. Why:
    /// whether a shape holds a member is a comparison of their components, which binds
    /// variables, with no order among shapes to search by; searching the shapes for each member
    /// cost the members times the shapes, the n² of `#a(String, 1) | … <: #a(T, 1) | …` before
    /// the index. With the refusal each bucket is searched past its first shape once, so a
    /// member costs a lookup in each group, the first shape of each of its buckets and the
    /// buckets it alone searches, and the members and shapes cost n log n times the groups. The
    /// groups are the sets of places at which shapes have a class and are one value, a few in a
    /// written union; shapes with variables or values at many different sets of places make as
    /// many groups, up to the shapes, and then each member costs a lookup in each. Measured on
    /// 20,000 random comparisons of unions of up to four shapes of width two against the rule
    /// of one shape: the same verdict and bindings wherever not refused, and 6 refused
    /// (`shapes_found_by_the_index_are_those_of_the_rule_of_one_shape`). Structure refused:
    /// `#a(3, 5) | #a(4, 6) <: #a(1 | 2, T) | #a(int, U)`, where component 1 files both shapes
    /// under `int` and `1 | 2` holds neither payload. Tests:
    /// `tests/steps/l01_22_type_representation/kinds.rs`,
    /// `payloads_with_a_variable_are_searched_by_their_keys` and the tests after it;
    /// COMPLEXITY.md F124. A complete solution would search a bucket once for all its members,
    /// by keys of the components that are not one value too (a tuple of a carrier, a payload),
    /// at any depth, as the kernel files its rows (`RowIndex`), and would find the groups that
    /// may hold a member by a partial-match index rather than one lookup in each.
    async fn search<G: Ord + Clone, M: Clone>(
        &'m self,
        choices: &Choices,
        xs: &[&Ty],
        member: (G, &M),
        searched: &mut BTreeMap<(G, usize, Bucket), M>,
        binds: &mut Binds,
        fit: impl Fn(usize, Binds) -> Deep<'m, (bool, Binds)>,
    ) -> Result<bool, (M, usize, Bucket)> {
        let buckets = {
            let cx = self.cx.borrow();
            if cx.unchosen.is_some() {
                return Ok(false);
            }
            choices.lookup(xs, &cx.rigid)
        };
        #[cfg(test)]
        let (buckets, scan_all) = match SCAN_ALL.get() {
            true => ((0..choices.groups.len()).map(|g| (g, None)).collect(), true),
            false => (buckets, false),
        };
        #[cfg(not(test))]
        let scan_all = false;
        let (group, m) = member;
        // The buckets this member has searched past their first shape.
        let mut past = vec![false; buckets.len()];
        for (k, at, r) in choices.merged(&buckets) {
            if at > 0 && !past[k] && !scan_all {
                let (g, id) = &buckets[k];
                match searched.entry((group.clone(), *g, id.clone())) {
                    Entry::Occupied(e) => return Err((e.get().clone(), *g, id.clone())),
                    Entry::Vacant(e) => e.insert(m.clone()),
                };
                past[k] = true;
            }
            let (ok, b) = fit(r, binds.clone()).await;
            if ok {
                *binds = b;
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Whether the payloads `of` gives the atoms of `s` are in those `t` gives them, where the
    /// normal forms were not made ([`Comparing::by_form`]): a payload not known is in a payload
    /// not known only, and each payload shape is in one of `t`'s shapes of the same length and
    /// field names, by the rule of one shape, binding `t`'s variables. The shapes tried for each
    /// are found by [`Comparing::search`], which refuses where the rule would search one bucket
    /// for two payloads.
    async fn payloads_in(
        &'m self,
        s: &KType,
        of: &Ty,
        t: &Ty,
        binds: &mut Binds,
        search: &mut Search<'_>,
    ) -> bool {
        // Called once `s` is in `t`'s set, with no carrier holding an atom: an atom of `s`
        // whose payloads `t` does not list is one whose payloads `t` holds all of. So only the
        // names `t` lists are read, not each name of `s`, which may be many more.
        for (n, rs) in &t.payloads {
            // A payload `t` does not know holds any payload.
            let Some(rs) = rs else { continue };
            if !holds_payload(s, n) {
                continue;
            }
            let Some(ls) = of.shapes(n) else { return false };
            if ls.is_empty() {
                continue;
            }
            let filed = self.filed(t, search);
            let groups = (filed.payloads.get(n)).expect("each payload union `t` lists is filed");
            let mut searched = BTreeMap::new();
            for l in ls {
                let g = shape_group(l);
                let Some(choices) = groups.get(&g) else {
                    return false;
                };
                let fit = |r: usize, b| self.shape_in(l.clone(), rs[r].clone(), b);
                let xs = comps(l);
                let found = self.search(choices, &xs, (g, l), &mut searched, binds, fit);
                match found.await {
                    Ok(true) => {}
                    Ok(false) => return false,
                    Err((first, k, id)) => {
                        self.refuse(|| {
                            let shapes = choices.bucket(k, &id).iter().map(|&r| rs[r].clone());
                            let second = payload_text(n, vec![l.clone()]);
                            let names: Vec<&Arc<str>> = l.fields.keys().collect();
                            let apart = choices.apart(k, &id, l.items.len(), &names);
                            let own =
                                own_shape(&comps(&first), &comps(l), l.items.len(), &names, |cs| {
                                    format!("#{n}({cs})")
                                });
                            unchosen_text(
                                "payloads",
                                &payload_text(n, vec![first]),
                                &second,
                                &payload_text(n, shapes.collect()),
                                &apart,
                                own,
                            )
                        });
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Whether the tuple piece `cs` of a type is in one of the tuple shapes of `t` of its
    /// length, the first in written order that holds it, binding `t`'s variables, of those
    /// [`Comparing::search`] tries; `search` holds `t`'s shapes filed and the buckets the
    /// other tuple pieces of the type searched.
    async fn row_in(
        &'m self,
        cs: &Row,
        t: &Ty,
        search: &mut Search<'_>,
        binds: &mut Binds,
    ) -> bool {
        let filed = self.filed(t, search);
        let Some(choices) = filed.rows.get(&cs.len()) else {
            return false;
        };
        let xs: Vec<&Ty> = cs.iter().collect();
        let fit = |r: usize, b| self.rows(cs.clone(), t.tuples[r].clone(), b);
        let found = self.search(
            choices,
            &xs,
            (cs.len(), cs),
            &mut search.searched,
            binds,
            fit,
        );
        match found.await {
            Ok(ok) => ok,
            Err((first, k, id)) => {
                self.refuse(|| {
                    let shapes = choices.bucket(k, &id).iter();
                    let bucket = Ty {
                        tuples: shapes.map(|&r| t.tuples[r].clone()).collect(),
                        ..Ty::empty()
                    };
                    let second = Ty::of_row(cs.clone()).to_string();
                    let apart = choices.apart(k, &id, cs.len(), &[]);
                    let xs: Vec<&Ty> = first.iter().collect();
                    let ys: Vec<&Ty> = cs.iter().collect();
                    let own = own_shape(&xs, &ys, cs.len(), &[], |cs| format!("({cs})"));
                    unchosen_text(
                        "tuples",
                        &Ty::of_row(first.clone()).to_string(),
                        &second,
                        &bucket.to_string(),
                        &apart,
                        own,
                    )
                });
                false
            }
        }
    }

    /// [`Comparing::sub_in`] with each tuple piece held by one tuple shape of `other`: the rule
    /// for the components of a tuple, whose joint check is the kernel's on the whole tuple.
    /// `other` sits at `site`.
    async fn sub_by_shape(&'m self, t: &Ty, other: &Ty, binds: &mut Binds, site: Site<'_>) -> bool {
        let mut search = Search::new(site);
        for p in t.pieces() {
            if !accepts(other, &p, t, binds, &mut search, self).await {
                return false;
            }
        }
        true
    }

    /// [`Ty::diff`] of `t` and `u`, a tuple compared with `u` as [`Ty::sub_with`] compares, with
    /// the resolver `solve`, if any: each comparison a new one, on this stack, the state of
    /// the comparisons open set aside meanwhile.
    async fn diff(&'m self, t: &Ty, u: &Ty, solve: Option<Solve<'s>>) -> Ty {
        let open = std::mem::take(&mut *self.cx.borrow_mut());
        let tk = u.kernel();
        let mut out = t.clone();
        out.set = &t.set - tk.as_ref().unwrap_or(&u.set);
        out.family = &t.family - &u.set;
        out.prune_payloads();
        let w = &u.set & &wide();
        let within = Ty {
            set: w.clone(),
            ..u.clone()
        };
        // What each tuple is compared with is read once: its tuples that may share a value with
        // the tuple ([`near_pairs`]), its other parts and its shapes filed. Each comparison then
        // costs the tuples found, not all of `u`'s.
        let rows = std::mem::take(&mut out.tuples);
        let nears = near_pairs(&rows, &within.tuples);
        let whole = Whole::of(&within);
        let filed = Arc::new(Filed::new(&within));
        let bare = Ty {
            tuples: Vec::new(),
            ..within.clone()
        };
        let mut rest = Vec::new();
        let mut kept = Vec::with_capacity(rows.len());
        for (a, near) in rows.into_iter().zip(nears) {
            *self.cx.borrow_mut() = Cx {
                solve,
                ..Cx::default()
            };
            let row = Ty::of_row(a.clone());
            let near = Ty {
                tuples: near.into_iter().map(|j| within.tuples[j].clone()).collect(),
                ..bare.clone()
            };
            let mut b = Binds::new();
            // A refused comparison keeps the row, as a failed one does.
            let held = (self.sub_near(&row, &within, Some((&near, &whole, &filed)), &mut b)).await;
            if self.cx.borrow().decided(held) && b.is_empty() {
                continue;
            }
            match (&tk, a.kernel()) {
                (Some(tk), Some(k)) if !(&k & &w).is_empty() => rest.push(&k - tk),
                _ => kept.push(a),
            }
        }
        *self.cx.borrow_mut() = open;
        out.tuples = kept;
        out.set = KType::union_all(std::iter::once(out.set).chain(rest));
        out
    }
}

/// Where a component sits in the tuple or payload that holds it: the kernel compares a
/// component only with those at the same place, so a function is compared only with the
/// functions of the other side at its place ([`Forms`]).
#[derive(Clone, PartialEq, Eq, Hash)]
enum Place {
    /// Component `.1` of a row of `.0` components.
    Row(usize, usize),
    /// Component `.3`, items then fields, of a payload of the atom `.0` with `.1` items and
    /// fields whose names hash to `.2`.
    Payload(Arc<str>, usize, u64, usize),
}

/// The functions met at each place, each once.
type PlaceFns = HashMap<Place, HashSet<Arc<Sig>>>;

/// Whether the kernel's verdict on a difference says the one side is in the other, or nothing
/// when it refused.
fn held(verdict: Verdict) -> Option<bool> {
    match verdict {
        Verdict::Empty => Some(true),
        Verdict::Inhabited => Some(false),
        Verdict::Refused(_) => None,
    }
}

/// What [`Forms`] reads of the type of the expected side: the functions at each place of its
/// rows and payloads, and the marks of the field names of its payloads.
struct Right {
    fns: PlaceFns,
    fields: HashSet<String>,
}

impl Right {
    /// None when `t` holds a variable, or the unknown, outside functions ([`Forms::fns`]).
    fn of(t: &Ty) -> Option<Right> {
        let mut fields = HashSet::new();
        let fns = Forms::fns(t, false, &mut fields)?;
        Some(Right { fns, fields })
    }
}

/// What [`Comparing::diff`] reads once of the type each tuple is compared with, for
/// [`Comparing::near_form`].
struct Whole {
    /// Its scalars, atoms with their payloads and kind-wide part as one kernel type, when it
    /// and each of its tuples have an exact kernel type ([`Ty::exact_data`]).
    rest: Option<KType>,
    /// What [`Forms`] reads of it, when it makes its form.
    right: Option<Right>,
}

impl Whole {
    fn of(t: &Ty) -> Whole {
        let rows_exact = t.tuples.iter().all(|r| r.0.exact.is_some());
        Whole {
            rest: rows_exact
                .then(|| payload_set(&t.set, &t.payloads, |_, s| s.0.exact.clone()))
                .flatten(),
            right: Right::of(t),
        }
    }
}

/// A row, or a payload shape of the atom named, met by [`Forms`].
#[derive(Clone, Copy)]
enum Node<'a> {
    Row(&'a Row),
    Shape(&'a Arc<str>, &'a Shape),
}

impl<'a> Node<'a> {
    /// The rows and payload shapes of `c` whose form is not their exact kernel type
    /// ([`Node::kept`]).
    fn below(c: &'a Ty) -> impl Iterator<Item = Node<'a>> {
        let rows = c.tuples.iter().map(Node::Row);
        let shapes = (c.payloads.iter())
            .flat_map(|(n, ss)| ss.iter().flatten().map(move |s| Node::Shape(n, s)));
        rows.chain(shapes).filter(|n| n.kept().is_none())
    }

    /// Its exact kernel type, when that is its form: none when it holds a function, a variable,
    /// the unknown or a payload with fields at any depth, which a form marks, or a set that
    /// holds the atoms of every name it does not list, from which a form cuts the marks.
    fn kept(self) -> Option<&'a KType> {
        let (exact, open_atoms) = match self {
            Node::Row(r) => (&r.0.exact, r.0.open_atoms),
            Node::Shape(_, s) => (&s.exact, s.open_atoms),
        };
        exact.as_ref().filter(|_| !open_atoms)
    }

    /// The node on the side `left`, as [`Forms::made`] keeps it: a shape with the name of its
    /// atom, since its places name it.
    fn key(self, left: bool) -> (*const (), bool, Option<Arc<str>>) {
        match self {
            Node::Row(r) => (Arc::as_ptr(&r.0).cast(), left, None),
            Node::Shape(n, s) => (s.as_ptr().cast(), left, Some(n.clone())),
        }
    }

    /// Its components, each with its place.
    fn comps(self) -> Vec<(Place, &'a Ty)> {
        match self {
            Node::Row(r) => (r.iter().enumerate())
                .map(|(i, c)| (Place::Row(r.len(), i), c))
                .collect(),
            Node::Shape(n, s) => {
                use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
                let names = BuildHasherDefault::<DefaultHasher>::default()
                    .hash_one(s.fields.keys().collect::<Vec<_>>());
                let len = s.items.len();
                (s.items.iter().chain(s.fields.values()).enumerate())
                    .map(|(i, c)| (Place::Payload(n.clone(), len, names, i), c))
                    .collect()
            }
        }
    }
}

/// The normal forms of the two sides of a comparison of scalars, atoms with their payloads
/// and tuples, which hold functions or the unknown: kernel types the kernel decides in the
/// size of the two sides, in place of trying each tuple shape and payload of one side against
/// each of the other.
///
/// Each function of the side compared is a mark of its own ([`mark`]), one for equal
/// functions; each function of the other side holds the marks of the functions at its place
/// that are equal to it or fit it, found before the forms are made ([`Comparing::by_form`]);
/// the unknown of the side compared is a mark only the unknown of the other holds. A payload
/// with fields is its items and fields in name order, then a mark of the names
/// ([`payload_form`]). A variable on either side, or the unknown on the other, is not put in a
/// form: a shape may bind a variable, and the unknown holds any value.
#[derive(Default)]
struct Forms {
    /// The number of each function of the side compared, by equality.
    ids: HashMap<Arc<Sig>, usize>,
    /// The functions of the side compared that each function of the other side holds, at
    /// each place, by number.
    fits: HashMap<(Place, Arc<Sig>), Vec<usize>>,
    /// The form of each node of the rows and shapes met, by [`Node::key`].
    made: HashMap<(*const (), bool, Option<Arc<str>>), KType>,
    /// The names of the marks of the field names of the payloads met on either side.
    fields: HashSet<String>,
    /// Every mark the two forms may hold: of each function of the side compared, of the
    /// unknown and of each set of field names met; none until the functions are numbered.
    marks: Option<KType>,
    /// Each set that holds the atoms of every name it does not list, with the marks cut out.
    cuts: RefCell<HashMap<KType, KType>>,
}

impl Forms {
    /// The number of the function `f` of the side compared.
    fn id(&mut self, f: &Arc<Sig>) -> usize {
        let next = self.ids.len();
        *self.ids.entry(f.clone()).or_insert(next)
    }

    /// The functions at each place of the rows and payloads of `t` and of `other`, or none
    /// when either holds a variable, or `other` the unknown, outside functions.
    fn places(&mut self, t: &Ty, other: &Ty) -> Option<(PlaceFns, PlaceFns)> {
        let left = Forms::fns(t, true, &mut self.fields)?;
        Some((left, Forms::fns(other, false, &mut self.fields)?))
    }

    /// The functions at each place of the rows and payloads of `t`, met once each over a
    /// visited set, since rows and shapes are shared: none when it holds a variable outside
    /// functions, or the unknown and is not `left`. The names of the marks of the field names
    /// of its payloads go to `fields`.
    fn fns(t: &Ty, left: bool, fields: &mut HashSet<String>) -> Option<PlaceFns> {
        let mut out = PlaceFns::new();
        let mut seen = HashSet::new();
        let mut stack: Vec<Node> = Node::below(t).collect();
        while let Some(n) = stack.pop() {
            if !seen.insert(n.key(left)) {
                continue;
            }
            if let Node::Shape(_, s) = n
                && !s.fields.is_empty()
            {
                fields.insert(fields_mark(&s.fields));
            }
            for (place, c) in n.comps() {
                if !c.vars.is_empty() || (!left && c.dynamic) {
                    return None;
                }
                if !c.fns.is_empty() {
                    out.entry(place).or_default().extend(c.fns.iter().cloned());
                }
                stack.extend(Node::below(c));
            }
        }
        Some(out)
    }

    /// A place where two or more functions of the side compared, equal to none of the other
    /// side's there, meet two or more of the other side's.
    ///
    /// Complexity tradeoff: which of those fits which is not tried. What is given up: such a
    /// comparison is refused with its own clause ([`Ty::refused`]), though each pair could be
    /// compared. Why: the pairs are the product of the two sides' functions at the place, and
    /// a union of `n` shapes on each side, each with its own function there, would cost `n^2`
    /// comparisons of functions. Structure: `(f, 1) | (g, "a") <: ((int) -> int, int) |
    /// ((String) -> String, String)` with `f` and `g` of other types than those written. Test:
    /// `tests/steps/l01_22_type_representation/kinds.rs`,
    /// `functions_unlike_on_both_sides_at_one_place_are_refused`; COMPLEXITY.md F124. A
    /// complete solution would order the functions at a place by their parameters and results,
    /// so that those a function fits are found by a search in that order, not by trying each.
    fn tied(&self, left: &PlaceFns, right: &PlaceFns) -> Option<Place> {
        // The places of the side compared are looked up, since the other side may be a whole
        // union whose places are many ([`Comparing::near_form`]).
        left.iter().find_map(|(place, fs)| {
            let gs = right.get(place)?;
            let unlike = fs.iter().filter(|f| !gs.contains(*f)).count();
            (unlike >= 2 && gs.len() >= 2).then(|| place.clone())
        })
    }

    /// Why `t <: other` was refused, if it was for the class [`Forms::tied`] names.
    fn tie(t: &Ty, other: &Ty) -> Option<&'static str> {
        if other.dynamic || !other.vars.is_empty() {
            return None;
        }
        let mut forms = Forms::default();
        let (left, right) = forms.places(t, other)?;
        forms.tied(&left, &right).map(|_| {
            "two or more functions at one place of a tuple or an atom's payload are each unlike \
             two or more functions at that place of the type expected, and the checker does not \
             try every way of pairing them; give the functions at that place one function type"
        })
    }

    /// The normal form of the scalars, atoms with their payloads, kind-wide part and tuples of
    /// `t`, on the side compared if `left`. Its rows and shapes are made bottom up, each once,
    /// on a stack of its own, since they nest as deep as the program.
    fn form(&mut self, t: &Ty, left: bool) -> KType {
        let mut stack: Vec<(Node, bool)> = Node::below(t).map(|n| (n, false)).collect();
        while let Some((n, ready)) = stack.pop() {
            let key = n.key(left);
            if self.made.contains_key(&key) {
                continue;
            }
            if !ready {
                stack.push((n, true));
                for (_, c) in n.comps() {
                    stack.extend(Node::below(c).map(|n| (n, false)));
                }
                continue;
            }
            let ks: Vec<KType> = (n.comps().into_iter())
                .map(|(place, c)| self.comp(c, &place, left))
                .collect();
            // A component of no value, as a function of the other side that no function fits,
            // leaves the tuple or payload no value: built as empty, not as a row the kernel
            // would prove empty again in each comparison.
            let k = match n {
                _ if ks.contains(&KType::empty()) => KType::empty(),
                Node::Row(_) => KType::tuple(ks),
                Node::Shape(_, s) => payload_form(ks, &s.fields),
            };
            self.made.insert(key, k);
        }
        self.data(t, left)
    }

    /// The form of `t`'s scalars, atoms with their payloads, kind-wide part and tuples, its
    /// rows and shapes made, the marks cut from its set.
    fn data(&self, t: &Ty, left: bool) -> KType {
        let form = |n: Node| {
            n.kept()
                .cloned()
                .or_else(|| self.made.get(&n.key(left)).cloned())
        };
        let shape = |n: &Arc<str>, s: &Shape| form(Node::Shape(n, s));
        let set = payload_set(&self.cut(&t.set), &t.payloads, shape).expect("each shape is made");
        let rows = (t.tuples.iter()).map(|r| form(Node::Row(r)).expect("each row is made"));
        KType::union_all(std::iter::once(set).chain(rows))
    }

    /// Numbers the marks ([`Forms::marks`]), once the functions of the side compared are.
    fn number_marks(&mut self) {
        let fns = (0..self.ids.len()).map(|i| format!("\u{0}fn {i}"));
        let names = fns.chain(self.fields.iter().cloned());
        let marks = names.map(|n| mark(&n)).chain([mark("\u{0}unknown")]);
        self.marks = Some(KType::union_all(marks));
    }

    /// `set` without the marks, when it holds the atoms of every name it does not list: a
    /// component written `#_` holds no function, so its form holds no mark ([`mark`]).
    ///
    /// Complexity tradeoff: each such set is cut once per comparison, at the cost of the
    /// marks. What is given up: `k` distinct sets of that kind against `m` marks cost `k m`.
    /// Why: the kernel has no set of all atoms whose names start with a NUL, so the marks are
    /// taken out by name, and each set keeps the names it leaves out. Structure: a union of `n`
    /// tuples `(#_ - #a_i, f_i)` against one of `n` functions. Test:
    /// `tests/steps/l01_22_type_representation/kinds.rs`,
    /// `marks_are_cut_from_sets_of_all_atoms`; COMPLEXITY.md F124. A complete solution would
    /// give the kernel a part for marks, which no type written holds.
    fn cut(&self, set: &KType) -> KType {
        let Some(marks) = &self.marks else {
            return set.clone();
        };
        if set.atom_names().is_some() {
            return set.clone();
        }
        (self.cuts.borrow_mut().entry(set.clone()))
            .or_insert_with(|| set - marks)
            .clone()
    }

    /// The form of the component `c` at `place`.
    fn comp(&self, c: &Ty, place: &Place, left: bool) -> KType {
        let mut ks = vec![self.data(c, left)];
        for f in &c.fns {
            let ids = match left {
                true => std::slice::from_ref(&self.ids[f]),
                false => {
                    (self.fits.get(&(place.clone(), f.clone()))).map_or(&[][..], Vec::as_slice)
                }
            };
            ks.extend(ids.iter().map(|i| mark(&format!("\u{0}fn {i}"))));
        }
        if c.dynamic {
            ks.push(mark("\u{0}unknown"));
        }
        KType::union_all(ks)
    }
}

/// Type variables, each once, in order of first appearance.
#[derive(Default)]
pub struct Vars {
    seen: HashSet<Arc<str>>,
    /// The rows and payload shapes [`Ty::vars_outside`] entered: a shared one is entered once.
    outside: HashSet<*const ()>,
    /// The variables, in order.
    pub order: Vec<Arc<str>>,
}

impl Vars {
    /// Whether `v` is one of them.
    pub fn contains(&self, v: &str) -> bool {
        self.seen.contains(v)
    }
}

impl Ty {
    /// No value.
    pub fn empty() -> Ty {
        Ty {
            set: KType::empty(),
            tuples: Vec::new(),
            fns: Vec::new(),
            vars: BTreeSet::new(),
            dynamic: false,
            family: KType::empty(),
            payloads: BTreeMap::new(),
        }
    }

    /// The values of `s`: scalars, atoms, and a kind-wide part.
    pub fn set(s: KType) -> Ty {
        Ty {
            set: s,
            ..Ty::empty()
        }
    }

    /// Every value of `c`.
    pub fn carrier(c: Carrier) -> Ty {
        Ty::set(c.ty())
    }

    /// The values a variable bounded by the mask `m` may stand for when nothing fixes its
    /// carrier: those of each carrier of `m`, and any value with [`OTHER`].
    pub fn of_mask(m: u8) -> Ty {
        if m & OTHER != 0 {
            return Ty::dynamic();
        }
        Ty::set(Carrier::of_mask(m).fold(KType::empty(), |s, c| &s | &c.ty()))
    }

    /// The type of a scalar literal.
    pub fn lit(v: &Value) -> Ty {
        Ty::set(KType::lit(v).expect("a scalar literal"))
    }

    /// The tuple shape `(cs…)`.
    pub fn tuple(cs: Vec<Ty>) -> Ty {
        Ty::of_row(Row::new(cs))
    }

    /// The tuple shape of `row`, or the empty type when a component lists no value.
    pub fn of_row(row: Row) -> Ty {
        if row.0.void {
            return Ty::empty();
        }
        Ty {
            tuples: vec![row],
            ..Ty::empty()
        }
    }

    /// The atom `#name(items, fields)`, or the empty type when a component lists no value.
    pub fn atom_of(name: &str, items: Vec<Ty>, fields: BTreeMap<Arc<str>, Ty>) -> Ty {
        let shape = Shape::new(items, fields);
        if shape.void {
            return Ty::empty();
        }
        let mut t = Ty::set(KType::atom_with(name, &KType::top()));
        t.payloads.insert(name.into(), Some(vec![shape]));
        t
    }

    /// The function `s`.
    pub fn func(s: Arc<Sig>) -> Ty {
        Ty {
            fns: vec![s],
            ..Ty::empty()
        }
    }

    /// The type variable `v`.
    pub fn var(v: Arc<str>) -> Ty {
        let mut t = Ty::empty();
        t.vars.insert(v);
        t
    }

    /// The variable it is, when it is one type variable and nothing else.
    pub fn as_var(&self) -> Option<&Arc<str>> {
        let mut vs = self.vars.iter();
        let v = vs.next()?;
        (vs.next().is_none() && *self == Ty::var(v.clone())).then_some(v)
    }

    /// The unknown.
    pub fn dynamic() -> Ty {
        Ty {
            dynamic: true,
            ..Ty::empty()
        }
    }

    /// Whether it lists no value: the form of [`Ty::empty`], read in O(1). A type for which
    /// this is false may still be empty ([`Ty::is_empty`]).
    pub fn lists_nothing(&self) -> bool {
        self.set.lists_nothing()
            && self.tuples.is_empty()
            && self.fns.is_empty()
            && self.vars.is_empty()
            && !self.dynamic
    }

    /// Whether no value is in it.
    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
            && self.tuples.is_empty()
            && self.fns.is_empty()
            && self.vars.is_empty()
            && !self.dynamic
    }

    /// The union.
    pub fn union(&self, other: &Ty) -> Ty {
        let mut out = self.clone();
        out.set = &out.set | &other.set;
        out.family = &out.family | &other.family;
        if !self.payloads.is_empty() || !other.payloads.is_empty() {
            out.payloads = join_payloads(&[self, other]);
        }
        let have: HashSet<&Row> = self.tuples.iter().collect();
        let new: Vec<&Row> = other.tuples.iter().filter(|t| !have.contains(t)).collect();
        let mut added = HashSet::new();
        out.tuples
            .extend(new.into_iter().filter(|t| added.insert(*t)).cloned());
        let have: HashSet<&Arc<Sig>> = self.fns.iter().collect();
        let new: Vec<&Arc<Sig>> = other.fns.iter().filter(|f| !have.contains(f)).collect();
        let mut added = HashSet::new();
        out.fns
            .extend(new.into_iter().filter(|f| added.insert(*f)).cloned());
        out.vars.extend(other.vars.iter().cloned());
        out.dynamic |= other.dynamic;
        out
    }

    /// The union of `ts`, built once: joining them one at a time copied the union so far each
    /// time, `O(n²)` in the tuple shapes.
    pub fn union_all<'t>(ts: impl IntoIterator<Item = &'t Ty>) -> Ty {
        let ts: Vec<&Ty> = ts.into_iter().collect();
        let mut out = Ty::empty();
        out.set = KType::union_all(ts.iter().map(|t| t.set.clone()));
        out.family = KType::union_all(ts.iter().map(|t| t.family.clone()));
        let mut tuples = HashSet::new();
        let mut fns = HashSet::new();
        if ts.iter().any(|t| !t.payloads.is_empty()) {
            out.payloads = join_payloads(&ts);
        }
        for t in ts {
            out.tuples
                .extend(t.tuples.iter().filter(|c| tuples.insert(*c)).cloned());
            out.fns
                .extend(t.fns.iter().filter(|f| fns.insert(*f)).cloned());
            out.vars.extend(t.vars.iter().cloned());
            out.dynamic |= t.dynamic;
        }
        out
    }

    /// Its atoms.
    pub fn atoms(&self) -> KType {
        &self.set & &atoms()
    }

    /// It without its atoms.
    pub fn without_atoms(&self) -> Ty {
        Ty {
            set: &self.set - &atoms(),
            family: KType::empty(),
            ..self.clone()
        }
    }

    /// It with every atom it holds made a member of a named family, as a `type` declaration
    /// names a union.
    pub fn named(&self) -> Ty {
        Ty {
            family: self.atoms(),
            ..self.clone()
        }
    }

    /// It as a written type reads it: every atom loose, the ascription being the visible act
    /// of re-classifying (sec:failure).
    pub fn written(&self) -> Ty {
        Ty {
            family: KType::empty(),
            ..self.clone()
        }
    }

    /// Its loose atoms: those of no named family.
    pub fn loose(&self) -> KType {
        &self.atoms() - &self.family
    }

    /// What `_` would drop of a value of it (DESIGN.md sec:tour_methods): its loose atoms,
    /// less `named`, the atoms that an `else` in the bound expression writes as its default.
    /// A family's atoms are data, and `_` drops data freely.
    pub fn dropped(&self, named: &KType) -> KType {
        &self.loose() - named
    }

    /// The type of its loose atoms, with their payloads.
    pub fn loose_ty(&self) -> Ty {
        self.of_piece(&Piece::Set(self.loose()))
    }

    /// It without its loose atoms, as `e else d` narrows `e`: what is not an atom, and the
    /// family's atoms. Each step complements only a set that lists no atom names or the
    /// family's, so it costs `O(f log n)` for `f` family atoms of `n`, where `set − loose`
    /// would complement every loose atom.
    pub fn without_loose(&self) -> Ty {
        // A set that holds no atom loses none.
        let set = match self.set.may_hold_atoms() {
            true => &(&self.set - &atoms()) | &(&self.set & &self.family),
            false => self.set.clone(),
        };
        let mut out = Ty {
            set,
            ..self.clone()
        };
        out.prune_payloads();
        out
    }

    /// It without the atoms `k`, as a call passes them by (rule 6 of sec:type_resolution).
    pub fn without(&self, k: &KType) -> Ty {
        let mut out = Ty {
            set: &self.set - k,
            ..self.clone()
        };
        out.prune_payloads();
        out
    }

    /// Drops the payloads of the atoms its set no longer holds (L29-print: a type narrowed to
    /// `String` kept the payload of the `#ioError` it lost, so it differed from `String`).
    fn prune_payloads(&mut self) {
        let set = &self.set;
        self.payloads.retain(|n, _| holds_payload(set, n));
    }

    /// Its pieces: the scalars split by carrier, then the atoms, the other scalars, the
    /// kind-wide part, the tuples, the functions, the variables and the unknown.
    pub fn pieces(&self) -> Vec<Piece> {
        let mut out = Vec::new();
        let mut split = self.set.split();
        for c in Carrier::ALL {
            out.extend(split.bases[c.base()].take().map(Piece::Set));
        }
        out.extend(split.atoms.map(Piece::Set));
        // The kind-wide part follows the other scalars, as its own piece.
        if let Some(rest) = split.rest {
            let w = &rest & &wide();
            let rest = &rest - &w;
            if !rest.is_empty() {
                out.push(Piece::Set(rest));
            }
            if !w.is_empty() {
                out.push(Piece::Set(w));
            }
        }
        out.extend(self.tuples.iter().cloned().map(Piece::Tuple));
        out.extend(self.fns.iter().cloned().map(Piece::Fn));
        out.extend(self.vars.iter().cloned().map(Piece::Var));
        if self.dynamic {
            out.push(Piece::Dyn);
        }
        out
    }

    /// The numeric carrier a generic literal takes where a value of this type is expected, and
    /// the one a plain literal of another is rejected at: the one carrier its numbers are of,
    /// when it holds numbers of one carrier and no variable or unknown, which could stand for
    /// numbers of another. Its other members (atoms, strings, booleans, tuples, functions) do
    /// not count, so `1n` at `f64 | String` is `1.0`; a type with numbers of two carriers, as
    /// `f64 | rat`, gives none (`check::expected`; DESIGN.md L1.26: the carrier "an operator or
    /// a parameter expects").
    pub fn numeric_carrier(&self) -> Option<Carrier> {
        if !self.vars.is_empty() || self.dynamic {
            return None;
        }
        // Its numbers are those of one numeric carrier: read off one split, where a meet and
        // a subtype test per carrier would build each part anew.
        let s = self.set.split();
        let mut present = [Carrier::Int, Carrier::Rat, Carrier::F64]
            .into_iter()
            .filter(|c| s.bases[c.base()].is_some());
        match (present.next(), present.next()) {
            (Some(c), None) => Some(c),
            _ => None,
        }
    }

    /// Whether it holds no variable and no unknown, outside functions, at any depth, in its
    /// tuples and its atoms' payloads: read at its outer level, since each row and payload
    /// shape keeps whether it holds one.
    pub fn closed(&self) -> bool {
        self.vars.is_empty()
            && !self.dynamic
            && self.tuples.iter().all(|r| !r.open())
            && self.payload_shapes().all(|s| !s.open)
    }

    /// Whether it holds the unknown, outside functions, at any depth, in its tuples and its
    /// atoms' payloads: read at its outer level, as [`Self::closed`] is.
    fn holds_unknown(&self) -> bool {
        self.dynamic
            || self.tuples.iter().any(Row::dynamic)
            || self.payload_shapes().any(|s| s.dynamic)
    }

    /// Whether it holds no function at any depth (a variable or the unknown may still stand
    /// for one): a type whose values the differential oracle compares (step L1.37). A
    /// kind-wide part, `(..)` or `{..}`, holds tuples and structs that hold functions.
    pub fn first_order(&self) -> bool {
        self.held_function().is_none() && self.held_wide().is_none()
    }

    /// A function it may hold, at any depth, in its tuples and its atoms' payloads; a family
    /// is data, not a function.
    pub fn held_function(&self) -> Option<&Arc<Sig>> {
        self.function_in(|r| r.0.held.as_ref(), |s| s.held.as_ref())
    }

    /// Its one value, when it is one scalar literal, or one tuple shape each of whose
    /// components is one value, and nothing else: no variable, function, unknown or payload
    /// listed. Each row keeps its own, so this reads the outer level.
    fn point(&self) -> Option<Value> {
        if self.dynamic
            || !self.vars.is_empty()
            || !self.fns.is_empty()
            || !self.payloads.is_empty()
            || !self.family.is_empty()
        {
            return None;
        }
        match (self.set.is_empty(), &self.tuples[..]) {
            (false, []) => self.set.scalar(),
            (true, [r]) => r.0.point.clone(),
            _ => None,
        }
    }

    /// A function it may hold, at any depth, that no tuple expression has checked as data, so
    /// that no error has reported it yet.
    pub fn unchecked_function(&self) -> Option<&Arc<Sig>> {
        self.function_in(|r| r.0.unchecked.as_ref(), |s| s.unchecked.as_ref())
    }

    /// The first function, not a family, that it holds itself, that `row` gives of one of its
    /// tuples, or that `shape` gives of the payload of one of its atoms (DESIGN.md, `#atom(t)`:
    /// a payload may hold a function).
    ///
    /// A row and a payload shape each keep what they hold at any depth, so the walk reads them
    /// and does not enter them: it costs the size of the outer level, however deep or shared
    /// the payloads are.
    fn function_in<'a>(
        &'a self,
        row: impl Fn(&'a Row) -> Option<&'a Arc<Sig>>,
        shape: impl Fn(&'a ShapeData) -> Option<&'a Arc<Sig>>,
    ) -> Option<&'a Arc<Sig>> {
        let own = self.fns.iter().find(|s| !s.data);
        own.or_else(|| self.tuples.iter().find_map(row))
            .or_else(|| self.payload_shapes().find_map(|s| shape(&s.0)))
    }

    /// Whether every value of `self` is in `other`, binding `other`'s variables as needed.
    pub fn sub(&self, other: &Ty, binds: &mut Binds) -> bool {
        let mut cx = Cx::default();
        let ok = comparing!(&mut cx, |c| c.sub_in(self, other, binds));
        cx.decided(ok)
    }

    /// Why `self <: other` was refused, if two members of a union of `self` each needed a
    /// shape of `other` the checker does not single out ([`Comparing::search`]).
    fn unchosen(&self, other: &Ty) -> Option<String> {
        let mut cx = Cx::default();
        comparing!(&mut cx, |c| async {
            c.sub_in(self, other, &mut Binds::new()).await;
        });
        cx.unchosen
    }

    /// [`Self::sub`], each class variable `solve` gives a type read as that type inside the
    /// functions compared.
    pub fn sub_with(&self, other: &Ty, binds: &mut Binds, solve: Solve) -> bool {
        let mut cx = Cx {
            solve: Some(solve),
            ..Cx::default()
        };
        let ok = comparing!(&mut cx, |c| c.sub_in(self, other, binds));
        cx.decided(ok)
    }

    /// [`Self::subtype`], read as [`Self::sub_with`] reads.
    pub fn subtype_with(&self, other: &Ty, solve: Solve) -> bool {
        let mut b = Binds::new();
        self.sub_with(other, &mut b, solve) && b.is_empty()
    }

    /// The kernel type of its values, when it holds no function, variable or unknown at any
    /// depth: its scalars and atoms, and its tuple shapes. A tuple piece that no one shape of
    /// a union holds may still be in the union (boxes that cover a box only together); the
    /// kernel decides that, or refuses with its cause.
    pub fn kernel(&self) -> Option<KType> {
        if !self.fns.is_empty() || !self.vars.is_empty() || self.dynamic {
            return None;
        }
        // A row and a payload shape know whether they hold a variable, the unknown or a
        // function at any depth, so a type that does is refused at its outer level, not at the
        // bottom of its tuples and payloads.
        if (self.tuples.iter()).any(|r| r.open() || r.0.held.is_some())
            || self.payload_shapes().any(|s| s.open || s.held.is_some())
        {
            return None;
        }
        // Each row's kernel type is made once and kept in the row ([`Row::kernel`]).
        // Joined in pairs: one at a time costs the size of the union so far for each shape.
        let shapes = self.tuples.iter().map(Row::kernel);
        let shapes = shapes.collect::<Option<Vec<_>>>()?;
        Some(KType::union_all(
            std::iter::once(self.set.clone()).chain(shapes),
        ))
    }

    /// [`Self::kernel`] with the payloads of its atoms read: `#a(String)` is not in
    /// `#a(int, int)`, where [`Self::kernel`] holds every `#a` with a payload.
    pub fn exact_kernel(&self) -> Option<KType> {
        if !self.fns.is_empty() || !self.vars.is_empty() || self.dynamic {
            return None;
        }
        self.exact_data()
    }

    /// The kernel type of its scalars, atoms with their payloads read, kind-wide part and
    /// tuples, leaving out its own functions, variables and unknown: none when a tuple or
    /// payload holds a function, a variable, the unknown or a payload with fields at any
    /// depth, which only the normal forms of a comparison compare. Each row and shape keeps
    /// its own, so this costs the outer level.
    pub fn exact_data(&self) -> Option<KType> {
        let rows = (self.tuples.iter().map(|r| r.0.exact.clone())).collect::<Option<Vec<_>>>()?;
        let set = payload_set(&self.set, &self.payloads, |_, s| s.0.exact.clone())?;
        Some(KType::union_all(std::iter::once(set).chain(rows)))
    }

    /// A kind-wide part, `(..)` or `{..}`, it holds at any depth outside functions, in its
    /// tuples and its atoms' payloads: every tuple or struct, those that hold a function among
    /// them. Read at its outer level, since each row and shape keeps the one it holds.
    pub fn held_wide(&self) -> Option<KType> {
        let own = &self.set & &wide();
        if !own.is_empty() {
            return Some(own);
        }
        (self.tuples.iter().find_map(|r| r.0.wide.clone()))
            .or_else(|| self.payload_shapes().find_map(|s| s.wide.clone()))
    }

    /// Whether its set, or a row or payload shape at any depth outside functions, holds the
    /// atoms of every name it does not list, as `#_` does: such a set holds the marks of a
    /// normal form ([`mark`]) unless they are cut out ([`Forms::cut`]). Read at its outer level,
    /// since each row and shape keeps its own.
    fn open_atoms(&self) -> bool {
        self.set.atom_names().is_none()
            || self.tuples.iter().any(|r| r.0.open_atoms)
            || self.payload_shapes().any(|s| s.open_atoms)
    }

    /// Whether every value of `self` is in `other`, with no variable bound.
    pub fn subtype(&self, other: &Ty) -> bool {
        let mut b = Binds::new();
        self.sub(other, &mut b) && b.is_empty()
    }

    /// The kernel's verdict on `self <: other`, on what of `self` is outside `other`: `Empty`
    /// when it holds, `Inhabited` when a value outside was built. On kernel types, or on the
    /// scalar sets when either holds a function, variable, unknown or payload with fields at
    /// any depth; `Empty` when `other` is the unknown.
    pub fn verdict(&self, other: &Ty) -> Verdict {
        if other.dynamic {
            return Verdict::Empty;
        }
        match (self.exact_kernel(), other.exact_kernel()) {
            (Some(a), Some(b)) => a.subtype_verdict(&b),
            _ => self.set.subtype_verdict(&other.set),
        }
    }

    /// When `self <: other` failed: the clause that says why it was not decided, if the check of
    /// its kernel types (its scalar sets, when either holds a function, variable or unknown)
    /// was refused, or, for a function, the clause that names the cover of rule 6 the checker
    /// refuses ([`why_unfit`]), and nothing if it was decided. A refusal claims nothing about
    /// the types, so a message that reads as a counterexample would be wrong.
    pub fn refused(&self, other: &Ty) -> String {
        if let Some(why) = Forms::tie(self, other) {
            return undecided(why);
        }
        if let Some(why) = self.unchosen(other) {
            return undecided(&why);
        }
        match self.verdict(other) {
            Verdict::Refused(r) => self.refused_in_group(other, r),
            // A function that a cover the checker refuses would take ([`why_unfit`]).
            _ => self
                .fns
                .iter()
                .find_map(|s| other.fns.iter().find_map(|q| why_unfit(s, q)))
                .map_or_else(String::new, |why| format!(": {why}")),
        }
    }

    /// The clause for a check of `self <: other` refused for `cause`. When the check rests on a
    /// recursive group (`KType::refusal_site`), a second line names the definition it was
    /// deciding and lists the group's definitions; for a refusal by the group's decider the
    /// reason names the definitions, the cycles, the tuple and a repair (DESIGN.md L1.23). The
    /// definitions carry no source place until recursive `type` declarations reach the
    /// compiler (L2.5), so they are written out.
    fn refused_in_group(&self, other: &Ty, cause: Refusal) -> String {
        let site = match (self.exact_kernel(), other.exact_kernel()) {
            (Some(a), Some(b)) => a.subtype_refusal_site(&b, cause),
            _ => self.set.subtype_refusal_site(&other.set, cause),
        };
        let Some(site) = site else {
            return undecided(&cause.message());
        };
        let why = site.detail.unwrap_or_else(|| cause.message());
        let mut out = undecided(&why);
        out += &format!(
            "\n  the check reads the recursive type `{}`, defined by:",
            site.head
        );
        for d in &site.defs {
            out += &format!("\n    {d}");
        }
        out
    }

    /// The meet with `t`, as an `is` test narrows: what of `self` is also in `t`.
    pub fn meet(&self, t: &Ty) -> Ty {
        if self.tuples.is_empty() || t.tuples.is_empty() {
            return self.meet_rest(t, Vec::new());
        }
        let memo = RefCell::default();
        let pairs = Pairs {
            stack: Stack::default(),
            memo: &memo,
        };
        pairs.stack.run(pairs.meet(self, t))
    }

    /// [`Self::meet`] with `met`, the meets of the pairs of its tuples and `t`'s.
    fn meet_rest(&self, t: &Ty, mut met: Vec<Row>) -> Ty {
        if t.dynamic {
            return self.clone();
        }
        let mut out = Ty::set(&self.set & &t.set);
        out.family = &self.family & &out.set;
        out.payloads = self.payloads.clone();
        // A kind-wide part of one side keeps the other's shapes it holds whole; of a shape it
        // holds in part, the part goes to the set, where the kernel holds it exactly. A shape
        // with no kernel type is kept, which may be more than the meet.
        for (a, b) in [(self, t), (t, self)] {
            let w = &b.set & &wide();
            if w.is_empty() {
                continue;
            }
            for cs in &a.tuples {
                match cs.kernel() {
                    Some(k) if k.subtype(&w) => met.push(cs.clone()),
                    Some(k) => out.set = &out.set | &(&k & &w),
                    None => met.push(cs.clone()),
                }
            }
        }
        let mut have = HashSet::new();
        let first: Vec<bool> = met.iter().map(|cs| have.insert(cs)).collect();
        out.tuples.extend(
            met.into_iter()
                .zip(first)
                .filter_map(|(cs, f)| f.then_some(cs)),
        );
        if !t.fns.is_empty() {
            out.fns = self.fns.clone();
        }
        if self.dynamic || !self.vars.is_empty() {
            out = out.union(t);
        }
        out
    }

    /// What of `self` is not in `t`, as `is not` narrows: scalars are subtracted, and so is
    /// all of `t` from the kind-wide part when `t` has a kernel type; tuples wholly inside `t`
    /// are dropped, a tuple that `t`'s kind-wide part holds in part leaves its rest in the set,
    /// and the other tuples are kept.
    pub fn diff(&self, t: &Ty) -> Ty {
        self.diff_in(t, None)
    }

    /// [`Self::diff`], a tuple compared with `t` as [`Self::sub_with`] compares: each class
    /// variable `solve` gives a type read as that type inside the functions it holds.
    pub fn diff_with(&self, t: &Ty, solve: Solve) -> Ty {
        self.diff_in(t, Some(solve))
    }

    /// [`Self::diff`], with the resolver of the comparisons, if any.
    fn diff_in(&self, t: &Ty, solve: Option<Solve>) -> Ty {
        comparing!(&mut Cx::default(), |c| c.diff(self, t, solve))
    }

    /// `self` with its variables replaced by their bindings.
    pub fn subst(&self, binds: &Binds) -> Ty {
        match binds.is_empty() {
            true => self.clone(),
            false => {
                let made = Made::default();
                rebuild_ty(&mut Subst { binds, made }, self)
            }
        }
    }

    /// `self` with its variables replaced by `binds` at every depth, inside the functions it
    /// holds too; not inside the types it puts in their place, which may hold the variables
    /// themselves.
    pub fn replace(&self, binds: &Binds) -> Ty {
        self.replace_in(binds, Mode::Replace)
    }

    /// `self` with the variables `names` gives other names, at every depth, inside the
    /// functions it holds too, their own variables among them: each value of `names` is one
    /// variable, and no two keys share one.
    pub fn renamed(&self, names: &Binds) -> Ty {
        self.replace_in(names, Mode::Rename)
    }

    /// `self` with its variables replaced by `binds` outside the functions it holds: the
    /// functions are kept as they are, and so is a tuple that holds no variable outside them.
    pub fn replace_outside(&self, binds: &Binds) -> Ty {
        self.replace_in(binds, Mode::Outside)
    }

    /// [`Ty::replace`], or as `mode` says.
    fn replace_in(&self, binds: &Binds, mode: Mode) -> Ty {
        match binds.is_empty() {
            true => self.clone(),
            false => rebuild_ty(&mut Replacer::new(binds, mode), self),
        }
    }

    /// The type of its piece `p` alone, with the payloads of the atoms `p` holds.
    pub fn of_piece(&self, p: &Piece) -> Ty {
        let mut out = p.ty();
        if let Piece::Set(s) = p {
            out.payloads = self
                .payloads
                .iter()
                .filter(|(n, _)| holds_payload(s, n))
                .map(|(n, ss)| (n.clone(), ss.clone()))
                .collect();
        }
        out
    }

    /// Its payloads with each shape replaced by what `f` makes of it.
    fn map_payloads(
        &self,
        mut f: impl FnMut(&Shape) -> Shape,
    ) -> BTreeMap<Arc<str>, Option<Vec<Shape>>> {
        self.payloads
            .iter()
            .map(|(n, ss)| {
                let ss = ss.as_ref().map(|ss| ss.iter().map(&mut f).collect());
                (n.clone(), ss)
            })
            .collect()
    }

    /// The shapes of its atoms' payloads.
    fn payload_shapes(&self) -> impl Iterator<Item = &Shape> {
        self.payloads.values().flatten().flatten()
    }

    /// What the payloads of its known atoms named `n` hold: their shapes, or `None` where that
    /// is not known. Its type variables and the unknown are not looked at, so the caller adds
    /// what they hold. The shapes are borrowed: a pattern asks once for each of its fields, and
    /// a copy of a payload with as many fields made the pattern quadratic in them.
    pub fn shapes(&self, n: &str) -> Option<&[Shape]> {
        match self.payloads.get(n) {
            Some(s) => s.as_deref(),
            None if holds_payload(&self.set, n) => None,
            None => Some(&[]),
        }
    }

    /// Every variable in it at any depth, as sets: at the cost of its outer level, since each
    /// row, payload shape and function keeps its own.
    pub fn var_facts(&self) -> VarFacts {
        let mut f = VarFacts::default();
        f.ty(self);
        f
    }

    /// Every variable in it, in order of first appearance.
    ///
    /// A type nests as deep as the program, so the walk keeps its own stack; rows and payload
    /// shapes are shared, so it enters each once. The address of a row or shape only tells
    /// whether it was entered, and each is marked when it is entered, in the order a recursive
    /// walk would enter it: one entered once more adds no variable, so the order does not
    /// depend on the sharing.
    pub fn vars_in(&self, out: &mut Vars) {
        enum Walk<'a> {
            Ty(&'a Ty),
            Row(&'a Row),
            Shape(&'a Shape),
        }
        let mut rows = HashSet::new();
        let mut shapes = HashSet::new();
        let mut stack = vec![Walk::Ty(self)];
        while let Some(w) = stack.pop() {
            let from = stack.len();
            let t = match w {
                Walk::Row(r) => {
                    if rows.insert(Arc::as_ptr(&r.0)) {
                        stack.extend(r.iter().map(Walk::Ty));
                        stack[from..].reverse();
                    }
                    continue;
                }
                Walk::Shape(s) => {
                    if shapes.insert(Arc::as_ptr(&s.0)) {
                        stack.extend(s.items.iter().chain(s.fields.values()).map(Walk::Ty));
                        stack[from..].reverse();
                    }
                    continue;
                }
                Walk::Ty(t) => t,
            };
            for v in &t.vars {
                if out.seen.insert(v.clone()) {
                    out.order.push(v.clone());
                }
            }
            stack.extend(t.tuples.iter().filter(|r| !r.0.fixed).map(Walk::Row));
            let open = t.payload_shapes().filter(|s| !s.vars.is_empty());
            stack.extend(open.map(Walk::Shape));
            for s in &t.fns {
                for a in &s.arrows {
                    stack.extend(a.params.iter().map(Walk::Ty));
                    stack.push(Walk::Ty(&a.result));
                }
                stack.extend(s.needs.iter().flat_map(Need::tys).map(Walk::Ty));
            }
            stack[from..].reverse();
        }
    }

    /// It with each class variable `solve` gives a type replaced by that type at every depth,
    /// each signature it holds settled once ([`Sig::settle`]). A tuple that holds no variable
    /// and no function is kept whole.
    pub fn settle(&self, solve: Solve) -> Ty {
        let made = vec![Made::default()];
        rebuild_ty(&mut Settle { solve, made }, self)
    }

    /// Every variable in it outside the functions it holds, in order of first appearance: a
    /// tuple or payload that holds none there is not entered, nor is one `out` has entered.
    ///
    /// A type nests as deep as the program, so the walk keeps its own stack, and marks each
    /// row and shape when it enters it, in the order a recursive walk would.
    pub fn vars_outside(&self, out: &mut Vars) {
        enum Walk<'a> {
            Ty(&'a Ty),
            Row(&'a Row),
            Shape(&'a Shape),
        }
        let mut stack = vec![Walk::Ty(self)];
        while let Some(w) = stack.pop() {
            let from = stack.len();
            match w {
                Walk::Row(r) => {
                    if out.outside.insert(r.addr()) {
                        stack.extend(r.iter().map(Walk::Ty));
                    }
                }
                Walk::Shape(s) => {
                    if out.outside.insert(s.as_ptr().cast()) {
                        stack.extend(s.items.iter().chain(s.fields.values()).map(Walk::Ty));
                    }
                }
                Walk::Ty(t) => {
                    for v in &t.vars {
                        if out.seen.insert(v.clone()) {
                            out.order.push(v.clone());
                        }
                    }
                    stack.extend(t.tuples.iter().filter(|r| r.open()).map(Walk::Row));
                    let open = t.payload_shapes().filter(|s| s.open);
                    stack.extend(open.map(Walk::Shape));
                }
            }
            stack[from..].reverse();
        }
    }

    /// Whether the value `v` is in it; a variable or the unknown holds every value.
    pub fn contains(&self, v: &Value) -> bool {
        self.contains_here(v).unwrap_or_else(|items| {
            let memo = RefCell::default();
            let filed = RefCell::default();
            let pairs = Pairs {
                stack: Stack::default(),
                memo: &memo,
            };
            pairs.stack.run(pairs.contains(self, items, &filed))
        })
    }

    /// Whether the value `v` is in it, when that is known without reading its tuples: unless
    /// `v` is a tuple outside its set and it has a tuple of `v`'s length, whose components
    /// are given to be read.
    fn contains_here<'v>(&self, v: &'v Value) -> Result<bool, &'v Items> {
        if self.dynamic || !self.vars.is_empty() {
            return Ok(true);
        }
        Ok(match v {
            Value::Tuple(items) => {
                let here = self.set.contains(v);
                if !here && self.tuples.iter().any(|cs| cs.len() == items.len()) {
                    return Err(items);
                }
                here
            }
            Value::Family(_) => self.fns.iter().any(|s| s.data),
            Value::Path(_) => !self.fns.is_empty() || self.set.contains(v),
            _ => self.set.contains(v),
        })
    }

    /// Whether `self` and `other` may share a value.
    pub fn meets(&self, other: &Ty) -> bool {
        self.meets_here(other).unwrap_or_else(|| {
            let memo = RefCell::default();
            let pairs = Pairs {
                stack: Stack::default(),
                memo: &memo,
            };
            pairs.stack.run(pairs.meets(self, other))
        })
    }

    /// Whether `self` and `other` may share a value, when that is known without reading their
    /// tuples, which it is unless each has a tuple of a length the other has and nothing else
    /// of them meets.
    fn meets_here(&self, other: &Ty) -> Option<bool> {
        if !self.closed() || !other.closed() {
            return Some(true);
        }
        // A shape meets the other side's kind-wide part when the kernel finds a common value;
        // a shape with no kernel type may.
        let wide_meets = |a: &Ty, b: &Ty| {
            let w = &b.set & &wide();
            !w.is_empty()
                && a.tuples
                    .iter()
                    .any(|cs| cs.kernel().is_none_or(|k| !(&k & &w).is_empty()))
        };
        if !(&self.set & &other.set).is_empty()
            || wide_meets(self, other)
            || wide_meets(other, self)
            || (!self.fns.is_empty() && !other.fns.is_empty())
        {
            return Some(true);
        }
        if self.tuples.is_empty() || other.tuples.is_empty() {
            return Some(false);
        }
        let lengths: HashSet<usize> = other.tuples.iter().map(|b| b.len()).collect();
        match self.tuples.iter().any(|a| lengths.contains(&a.len())) {
            true => None,
            false => Some(false),
        }
    }
}

/// A walk of the tuples of two types, or of a type and a value, side by side: [`Ty::meet`],
/// [`Ty::meets`] and [`Ty::contains`]. Tuples nest as deep as the program, and each recursed
/// once a level (100,000 levels overflowed a 2 MiB stack), so a pair of components whose
/// answer needs their own tuples is walked in a frame of its own ([`Stack`]), in the order the
/// recursion took. A pair of nodes shared at many places is walked once: its answer is kept
/// by the addresses of the two, which stay put while both are borrowed, so a type with `2^n`
/// paths through `n` tuples costs `O(n)` pairs, not `2^n`.
struct Pairs<'m, K, V> {
    stack: Stack<'m>,
    /// The answer for each pair walked, by the addresses of the two.
    memo: &'m RefCell<HashMap<K, V>>,
}

impl<'m, K: std::hash::Hash + Eq + Copy + 'm, V: Clone + Unpin + 'm> Pairs<'m, K, V> {
    /// The answer kept for `key`, or the one `walk` makes in a frame of its own, then kept.
    fn kept<F: Future<Output = V> + 'm>(
        &'m self,
        key: K,
        walk: impl FnOnce() -> F + 'm,
    ) -> Deep<'m, V> {
        if let Some(v) = self.memo.borrow().get(&key) {
            return Stack::ready(v.clone());
        }
        self.stack.call(move || async move {
            let v = walk().await;
            self.memo.borrow_mut().insert(key, v.clone());
            v
        })
    }
}

impl<'m> Pairs<'m, (*const Ty, *const Ty), Ty> {
    /// [`Ty::meet`] of `a` and `t`, which both hold tuples.
    async fn meet(&'m self, a: &'m Ty, t: &'m Ty) -> Ty {
        if t.dynamic {
            return a.clone();
        }
        let mut met = Vec::new();
        // Only the pairs of tuples that may share a value are met ([`near_pairs`]): the meet of
        // any other pair has an empty component and is left out, so the tuples and their order
        // are those of meeting every pair of one length.
        for (r, near) in a.tuples.iter().zip(near_pairs(&a.tuples, &t.tuples)) {
            'pair: for s in near.into_iter().map(|j| &t.tuples[j]) {
                let mut cs = Vec::with_capacity(r.len());
                for (x, y) in r.iter().zip(s) {
                    let c = match x.tuples.is_empty() || y.tuples.is_empty() {
                        true => x.meet_rest(y, Vec::new()),
                        false => self.kept((x, y), move || self.meet(x, y)).await,
                    };
                    // A row with an empty component is left out, whatever the rest meet to.
                    if c.is_empty() {
                        continue 'pair;
                    }
                    cs.push(c);
                }
                met.push(Row::new(cs));
            }
        }
        a.meet_rest(t, met)
    }
}

impl<'m> Pairs<'m, (*const Ty, *const Ty), bool> {
    /// [`Ty::meets`] of `a` and `b`, whose tuples decide it. Only the pairs of tuples that may
    /// share a value are compared ([`Near`]), found by key lookup, not every pair of one length.
    /// When each side has one tuple, that one pair is compared, with the same answer.
    async fn meets(&'m self, a: &'m Ty, b: &'m Ty) -> bool {
        // Complexity tradeoff: `l` and `r` tuples are compared pair by pair, with no keys, when
        // `l·r ≤ 1`: one tuple on each side. What is given up: nothing in order, since that is
        // one pair. Why: filing costs about 20k instructions plus 10k for each tuple on a side
        // of two components and 16k of five (the classes of the components are read once per
        // tuple and kept, `Row::keys`; the rest is hashing), and a pair about 24k, so filing is
        // already cheaper at one tuple against two. Measured 2026-11-09 in instructions per
        // walk, fresh types each walk, on unions of tuples of 2 to 5 components with one point
        // each and the other components `int`, `String` or `(int, bool)`, in one pattern or
        // four, filed against by pairs, no pair meeting: (1, 1) 41k against 46k, and 53k
        // against 50k for five components; (1, 2) 50k against 70k; (2, 2) 58k against 118k;
        // (1, 16) 190k against 407k; (8, 8) 170k against 1,550k; (32, 32) 613k against 24.57M.
        // Over 72 such cases the bound 1 costs at worst 6.75 times the cheaper path (geometric
        // mean 1.12), against 6.75 (1.23) for the old `l + r`, and over the 58 where no pair
        // meets at worst 1.13 (1.006) against 2.14 (1.16). The worst case is a pair that meets
        // found among the first, (32, 32) 886k against 131k: filing reads every tuple first,
        // and no bound on `l` and `r` alone can tell which pairs meet. Both give the same
        // answer, which `tuples_compared_by_meets_through_the_index_are_those_of_every_pair`
        // checks; the crossover is measured again at the Zed port.
        // Tests: `tests/steps/l01_22_type_representation/kinds.rs`, `meets_of_many_tuples_
        // scales`; COMPLEXITY.md F132.
        let (l, r) = (a.tuples.len(), b.tuples.len());
        let few = l.saturating_mul(r) <= 1;
        let groups = (!few).then(|| Groups::new(&a.tuples, &b.tuples));
        let mut near = groups.as_ref().map(Near::new);
        for (l, r) in a.tuples.iter().enumerate() {
            let near = near.as_mut().map(|n| n.of(l));
            let every = few.then(|| (0..b.tuples.len()).filter(|&j| b.tuples[j].len() == r.len()));
            let near = near
                .into_iter()
                .flatten()
                .chain(every.into_iter().flatten());
            'pair: for s in near.map(|j| &b.tuples[j]) {
                for (x, y) in r.iter().zip(s) {
                    let met = match x.meets_here(y) {
                        Some(m) => m,
                        None => self.kept((x, y), move || self.meets(x, y)).await,
                    };
                    if !met {
                        continue 'pair;
                    }
                }
                return true;
            }
        }
        false
    }
}

impl<'m> Pairs<'m, (*const Ty, *const Value), bool> {
    /// [`Ty::contains`] of `t` and a tuple of `items`, which its tuples decide. Only the
    /// tuples of `t` that may hold the value are compared with it, found by key lookup
    /// ([`Holders`]), once `t`'s tuples of its length have been read for enough values; until
    /// then every tuple of the length is, with the same answer. `filed` keeps each type node's
    /// tuples, filed or not, for the whole walk.
    async fn contains(&'m self, t: &'m Ty, items: &'m Items, filed: &'m RefCell<Filings>) -> bool {
        let (every, scanned, found) = match self.tried(t, items, filed) {
            Tried::Every => (Some(()), None, None),
            Tried::Scanned(rows) => (None, Some(rows), None),
            Tried::Found(holders) => (None, None, Some(holders)),
        };
        let every = every
            .into_iter()
            .flat_map(|()| (0..t.tuples.len()).filter(|&i| t.tuples[i].len() == items.len()));
        let scanned = scanned
            .into_iter()
            .flat_map(|rows| (0..rows.len()).map(move |k| rows[k]));
        let found = found.as_deref().into_iter().flat_map(|h| h.of(items));
        let rows = every.chain(scanned).chain(found);
        'row: for r in rows.map(|i| &t.tuples[i]) {
            for (c, x) in r.iter().zip(items) {
                let held = match c.contains_here(x) {
                    Ok(h) => h,
                    Err(inner) => {
                        self.kept((c, x), move || self.contains(c, inner, filed))
                            .await
                    }
                };
                if !held {
                    continue 'row;
                }
            }
            return true;
        }
        false
    }

    /// The tuples of `t` to compare with the tuple value of `items`, by their indices: every
    /// tuple of its length in written order, or those [`Holders`] finds, group by group. A tuple
    /// left out does not hold the value.
    fn tried(&self, t: &Ty, items: &Items, filed: &RefCell<Filings>) -> Tried {
        // Complexity tradeoff: the `l` tuples of one length of a node are scanned for each of
        // its first `v` values and filed at the first `v` with `l·v > 16·(l + v)`: never for 16
        // tuples or fewer, at the 22nd value for 64 tuples and the 17th for 1,024. What is
        // given up: nothing in order, since the scans before filing cost at most about
        // `16·(l + v)` tuples, linear in the node and its values. Why: filing costs about 8k
        // instructions a tuple of two components and 14k of five (the classes of the
        // components, read once per tuple and kept, `Row::keys`, and hashing), where a scan
        // costs about 440 a tuple for each value; so filing pays off only for many tuples read
        // for many values, from fewer than 16 to 64 values whatever `l`. Measured 2026-11-09 in
        // instructions per walk, max(2, 256/l) walks of a union of `l` tuples of 2 to 5
        // components (one point each, the others `int`, `String` or `(int, bool)`, in one
        // pattern or four) read for `v` values each, held by tuples spread over the union,
        // filed from the start against every tuple scanned: two components, one pattern,
        // l = 1,024, v = 16 8.80M against 3.35M, v = 64 9.56M against 12.05M, v = 1,024 24.68M
        // against 229.66M; five components, four patterns, l = 1,024, v = 16 14.59M against
        // 16.30M, v = 32 15.02M against 26.64M. Over 240 such cases the constant 16 costs at
        // worst 2.25 times the cheaper of the two (geometric mean 1.033), against 2.18 (1.035)
        // for 32, 4.14 (1.064) for 8 and 3.17 (1.096) for 64; with the scans before filing
        // counted, at worst 2.50 (1.080) against 2.36 (1.083) for 32 and 2.81 (1.101) for 24.
        // The two families cross at different `v`, so no constant suits both better. The
        // constant is measured again at the Zed port. Both give the same answer, which
        // `tuples_that_hold_a_value_through_the_index_are_those_of_every_tuple` checks. Tests:
        // `tests/steps/l01_22_type_representation/kinds.rs`, `contains_of_many_tuples_scales`;
        // COMPLEXITY.md F133.
        let len = items.len();
        let mut filed = filed.borrow_mut();
        let entry = filed.entry((t, len));
        let first = matches!(entry, std::collections::hash_map::Entry::Vacant(_));
        let visits = entry.or_insert(Visits::Once);
        #[cfg(test)]
        match FILE.get() {
            Some(false) => return Tried::Every,
            Some(true) if !matches!(visits, Visits::Filed(_)) => {
                let rows: Vec<usize> = (0..t.tuples.len())
                    .filter(|&i| t.tuples[i].len() == len)
                    .collect();
                *visits = Visits::Filed(Rc::new(Holders::new(t, &rows)));
            }
            _ => {}
        }
        match visits {
            Visits::Once if first => Tried::Every,
            Visits::Once => {
                let rows: Rc<[usize]> = (0..t.tuples.len())
                    .filter(|&i| t.tuples[i].len() == len)
                    .collect();
                *visits = Visits::Scanned {
                    n: 2,
                    rows: Rc::clone(&rows),
                };
                Tried::Scanned(rows)
            }
            Visits::Scanned { n, rows } => {
                *n += 1;
                let l = rows.len();
                if l.saturating_mul(*n) <= 16 * (l + *n) {
                    return Tried::Scanned(Rc::clone(rows));
                }
                let holders = Rc::new(Holders::new(t, rows));
                *visits = Visits::Filed(Rc::clone(&holders));
                Tried::Found(holders)
            }
            Visits::Filed(holders) => Tried::Found(Rc::clone(holders)),
        }
    }
}

/// Whether the piece `p` of `of` is in `t`, binding a variable of `t` to it when nothing else
/// of `t` holds it. A variable of `cx.rigid` stands for each carrier of its mask in turn: as
/// `p`, `t` must hold each; in `t`, it holds what each carrier, with the rest of `t`, holds. A
/// variable of `cx.fns` is the function it stands for.
///
/// A tuple shape and a function are compared in a frame of their own ([`Comparing::rows`],
/// [`Comparing::fits`]), through which every cycle of the comparisons passes. The tuple and
/// payload shapes of `t` that may hold a piece are found by `search` ([`Comparing::row_in`],
/// [`Comparing::payloads_in`]), which holds them filed for all the pieces of `of`.
async fn accepts<'m>(
    t: &Ty,
    p: &Piece,
    of: &Ty,
    binds: &mut Binds,
    search: &mut Search<'_>,
    c: &'m Comparing<'m, '_>,
) -> bool {
    if t.dynamic {
        return true;
    }
    let ok =
        match p {
            Piece::Dyn => false,
            Piece::Set(s) => {
                let held = {
                    let cx = c.cx.borrow();
                    s.subtype(&t.set)
                        || t.vars.iter().any(|w| {
                            cx.rigid.get(w).is_some_and(|&m| {
                                Carrier::of_mask(m).all(|c| s.subtype(&(&t.set | &c.ty())))
                            })
                        })
                };
                held && c.payloads_in(s, of, t, binds, search).await
            }
            // A kind-wide part that holds every tuple of the length holds it, whatever it holds.
            Piece::Tuple(cs) if KType::tuple(vec![KType::top(); cs.len()]).subtype(&t.set) => true,
            Piece::Tuple(cs) => c.row_in(cs, t, search, binds).await,
            // A type outside every comparison of function types holds its functions as written.
            Piece::Fn(s) => {
                let mut ok = false;
                for q in &t.fns {
                    if c.fits(s.clone(), Env::new(), q.clone(), Env::new()).await {
                        ok = true;
                        break;
                    }
                }
                ok
            }
            Piece::Var(v) => {
                let fns = c.cx.borrow().fns.get(v).cloned();
                match fns {
                    Some((s, se)) => {
                        let mut ok = false;
                        for w in &t.vars {
                            if c.fits_read(v, &s, &se, w).await {
                                ok = true;
                                break;
                            }
                        }
                        ok
                    }
                    None => {
                        t.vars.contains(v)
                            || c.cx.borrow().rigid.get(v).is_some_and(|&m| {
                                Carrier::of_mask(m).all(|c| c.ty().subtype(&t.set))
                            })
                    }
                }
            }
        };
    if ok {
        return true;
    }
    let cx = c.cx.borrow();
    match t
        .vars
        .iter()
        .find(|v| !cx.rigid.contains_key(*v) && !cx.fns.contains_key(*v))
    {
        Some(v) => {
            let b = binds.entry(v.clone()).or_insert_with(Ty::empty);
            *b = b.union(&of.of_piece(p));
            true
        }
        None => false,
    }
}

/// Whether a function of signature `s` is a function of signature `q`: the same parameter
/// names and kinds, and on each arrow of `q`, an arrow of `s` that takes its parameters and
/// returns within its result, or arrows of `s` that do so together (`covered`).
pub fn fits_sig(s: &Sig, q: &Sig) -> bool {
    let env = Env::new();
    let mut cx = Cx::default();
    let ok = comparing!(&mut cx, |c| fits_in(s, &env, q, &env, &c));
    cx.decided(ok)
}

/// [`fits_sig`], read as [`Ty::sub_with`] reads.
pub fn fits_sig_with(s: &Sig, q: &Sig, solve: Solve) -> bool {
    let mut cx = Cx {
        solve: Some(solve),
        ..Cx::default()
    };
    let env = Env::new();
    let ok = comparing!(&mut cx, |c| fits_in(s, &env, q, &env, &c));
    cx.decided(ok)
}

/// [`fits_sig`] inside the expected function types whose bounded variables `cx.rigid` holds,
/// `s` read by `se` and `q` by `qe`. `q`'s own bounded variables that a parameter holds join
/// `cx.rigid`: the caller of a function of type `q` picks one carrier of each bound, so `s`
/// must take every carrier of it. Each gets a new name, since `s` may use the same name for a
/// variable of its own. A bounded variable no parameter holds, of `q` or of `s`, is fixed by
/// no argument, so it stands for any carrier of its bound, as at a call ([`Sig::unheld`]).
///
/// The two sides are read through their environments, not rewritten: rewriting `q` at each
/// depth cost the size of `q` at each, the square of the depth for a function type nested
/// that deep. Each depth now costs its own parameters and bounds, and a lookup for each
/// variable (COMPLEXITY.md F60).
async fn fits_in<'m>(s: &Sig, se: &Env, q: &Sig, qe: &Env, c: &'m Comparing<'m, '_>) -> bool {
    let explain = c.cx.borrow_mut().why.take().is_some();
    if !s.needs.is_empty() {
        // Compared as written: the same signature, each variable read alike on both sides,
        // each solved class variable read as its type at every depth. That walk costs what
        // the comparison of the two as written costs.
        let solved;
        let solve = c.cx.borrow().solve;
        let (s, q) = match solve {
            Some(f) => {
                solved = (s.solved_with(f), q.solved_with(f));
                (&solved.0, &solved.1)
            }
            None => (s, q),
        };
        if s != q {
            return false;
        }
        let mut vs = Vars::default();
        for a in &s.arrows {
            a.params.iter().for_each(|p| p.vars_in(&mut vs));
            a.result.vars_in(&mut vs);
        }
        s.needs.iter().for_each(|n| n.vars_in(&mut vs));
        return vs.order.iter().all(|v| se.get(v) == qe.get(v));
    }
    let same_params = s.params.len() == q.params.len()
        && s.params
            .iter()
            .zip(&q.params)
            .all(|(a, b)| a.positional == b.positional && (a.positional || a.name == b.name));
    if !same_params {
        return false;
    }
    let (mark, sas, qas) = c.cx.borrow_mut().open(s, se, q, qe);
    let fits = every_arrow_fits(s, &sas, &qas, c).await;
    if explain && !fits {
        // The first arrow of `q` not covered, compared again alone: only on the way to an
        // error, at the cost of one more comparison of each arrow of `q`.
        let mut why = None;
        for (k, qa) in qas.iter().enumerate() {
            if !every_arrow_fits(s, &sas, std::slice::from_ref(qa), c).await {
                why = refused_cover(s, q, &sas, qa, k, c).await;
                break;
            }
        }
        c.cx.borrow_mut().why = Some(why);
    }
    c.cx.borrow_mut().forget(mark);
    fits
}

impl Cx<'_> {
    /// Opens the comparison of [`fits_in`] of `s`, read by `se`, with `q`, read by `qe`: the
    /// mark of the names made for it ([`Self::forget`]), and the arrows of each as read.
    fn open(&mut self, s: &Sig, se: &Env, q: &Sig, qe: &Env) -> (usize, Vec<Arrow>, Vec<Arrow>) {
        let cx = self;
        let mark = cx.made.len();
        // Each own variable names its own binder here, so the reading of the same name around it
        // is dropped, or replaced as above.
        let mut qe = qe.clone();
        for v in &q.own {
            match q.bounds.get(v) {
                Some(&m) if q.held.contains(v) => {
                    let w = cx.fresh(v);
                    cx.rigid.insert(w.clone(), m);
                    qe.insert(v.clone(), Read::Rigid(w));
                }
                Some(&m) => {
                    qe.insert(v.clone(), Read::Mask(m));
                }
                None => {
                    qe.remove(v);
                }
            }
        }
        let mut se = se.clone();
        for v in &s.own {
            match s.bounds.get(v) {
                Some(&m) if !s.held.contains(v) => {
                    se.insert(v.clone(), Read::Mask(m));
                }
                _ => {
                    se.remove(v);
                }
            }
        }
        let read = |a: &Arrow, env: &Env, cx: &mut Cx| Arrow {
            params: a.params.iter().map(|p| cx.read(p, env)).collect(),
            result: cx.read(&a.result, env),
        };
        let sas: Vec<Arrow> = s.arrows.iter().map(|a| read(a, &se, cx)).collect();
        let qas: Vec<Arrow> = q.arrows.iter().map(|a| read(a, &qe, cx)).collect();
        (mark, sas, qas)
    }
}

/// Why a function of signature `s` is not a function of signature `q`, when the cover of an
/// arrow of `q` that rule 6 of sec:type_resolution may give is one the checker refuses
/// (`refused_cover`): the clause a message adds after what it rejects. `None` when `s`
/// fits, or does not for a plain reason, a value no arrow takes or a result outside.
pub fn why_unfit(s: &Sig, q: &Sig) -> Option<String> {
    why_unfit_in(s, q, Cx::default())
}

/// [`why_unfit`], read as [`fits_sig_with`] reads.
pub fn why_unfit_with(s: &Sig, q: &Sig, solve: Solve) -> Option<String> {
    why_unfit_in(
        s,
        q,
        Cx {
            solve: Some(solve),
            ..Cx::default()
        },
    )
}

fn why_unfit_in(s: &Sig, q: &Sig, mut cx: Cx) -> Option<String> {
    cx.why = Some(None);
    let env = Env::new();
    let ok = comparing!(&mut cx, |c| fits_in(s, &env, q, &env, &c));
    if cx.decided(ok) {
        return None;
    }
    cx.why.flatten().or(cx.unchosen)
}

#[cfg(test)]
thread_local! {
    /// How [`every_arrow_fits`] decides, when not by the index: the forms the differential
    /// tests compare the index with.
    static REFERENCE: std::cell::Cell<tests::Reference> =
        const { std::cell::Cell::new(tests::Reference::None) };
}

/// Whether each arrow `qa` of `qas`, those of `q` as read, is covered by arrows of `sas`, those
/// of `s` as read: by one arrow that takes its parameters and returns within its result
/// ([`arrow_fits`]), or, at one parameter `j`, by arrows whose parameter types there together
/// hold `qa`'s, each taking `qa`'s other parameters and returning within its result
/// ([`covered`]). Rule 6 of sec:type_resolution types an application region by region, so a
/// call of `qa` at any value of its parameters reaches an arrow of `s` that returns within
/// `qa`'s result.
async fn every_arrow_fits<'m>(
    s: &Sig,
    sas: &[Arrow],
    qas: &[Arrow],
    c: &'m Comparing<'m, '_>,
) -> bool {
    #[cfg(test)]
    if REFERENCE.get() != tests::Reference::None {
        return tests::reference(s, sas, qas, c).await;
    }
    // Each arrow of `q` is tried first on an arrow of `s` equal to it, found by hash, so that
    // an overload passed where the same overload is expected costs one comparison per arrow.
    let mut equal: HashMap<&Arrow, &Arrow> = HashMap::with_capacity(sas.len());
    for sa in sas {
        equal.entry(sa).or_insert(sa);
    }
    // Then on the arrows of `s` the index leaves, in order, until one fits: the arrows whose
    // parameter types offer, at each parameter, each carrier and bare atom that `qa`'s holds,
    // and those whose parameter type there is open, and whose result types need no key that
    // `qa`'s closed result does not offer. An arrow it leaves out does not fit, so the verdict
    // is that of trying every arrow of `s`. The index is built at the first arrow of `q` that
    // no arrow of `s` equals, in the size of the parameter and result types of `s`.
    //
    // Complexity tradeoff: none is given up for one arrow, every arrow of `q` gets the verdict
    // of comparing it with every arrow of `s`, but the comparisons are bounded by the
    // candidates, not below n·m in the worst case: the candidates come from the shortest of
    // the lists, by parameter key or by result key, and an arrow of `s` that offers every key
    // `qa` needs at each parameter and in its result and does not fit, or is open there, is
    // still compared. So `s` and `q` of n arrows that all share one parameter piece and one
    // result piece, and differ in pieces of both, cost n^2/2 comparisons; arrows that share a
    // parameter piece and differ in their results cost n (scaling test
    // l01_26_type_resolution::scaling::passing_an_overload_whose_arrows_share_a_parameter_piece_scales;
    // COMPLEXITY.md F82). A tuple, a kind-wide part, a payload-only atom or a cofinite set of
    // atoms in `qa`'s parameter needs no key, since a parameter type may hold it without
    // offering one piece of it; a result that is open (a variable, the unknown, a cofinite set
    // of atoms) filters nothing. Why no complete bound: the question "each arrow of `q` has an
    // arrow of `s` whose parameters hold its parameters and whose result its result holds" is
    // a containment join between two families of sets, quantified for all and then exists;
    // with parameter and result types unions of many distinct members it is the complement of
    // Hitting Set, for which no n^(2-e) algorithm is expected (Abboud, Vassilevska Williams and
    // Wang, SODA 2016, the Hitting Set conjecture; a conjecture, not a theorem).
    let mut index: Option<ArrowIndex> = None;
    'qas: for qa in qas {
        if let Some(sa) = equal.get(qa)
            && arrow_fits(s, sa, qa, c).await
        {
            continue;
        }
        let index = index.get_or_insert_with(|| ArrowIndex::new(sas, s.params.len()));
        for i in index.may_fit(qa) {
            if arrow_fits(s, &sas[i], qa, c).await {
                continue 'qas;
            }
        }
        if !covered(s, sas, index, qa, c).await {
            return false;
        }
    }
    true
}

/// Why the arrow `qa` of `q`, its `k`th, as read, is covered neither by one arrow of `s`, of
/// `sas` as read, nor by its arrows together ([`covered`]), when the reason is a cover the
/// checker refuses, though rule 6 of sec:type_resolution may give it: the clause a message
/// adds. In order: an arrow that takes `qa`'s parameters only with a bounded variable bound
/// to values of several carriers that it does not stand for alone ([`one_place`]); an arrow
/// that would take part only by binding a variable ([`binds_nothing`], case (2) of
/// [`covered`]); two or more arrows that take parts and return outside `qa`'s result, whose
/// intersection the checker does not build (case (3)); an arrow that takes values at every
/// parameter but misses more than one (case (1)). `None` for a plain reason: a value no arrow
/// takes, or one arrow that returns outside. One pass over the arrows, on the way to an error.
async fn refused_cover<'m>(
    s: &Sig,
    q: &Sig,
    sas: &[Arrow],
    qa: &Arrow,
    k: usize,
    c: &'m Comparing<'m, '_>,
) -> Option<String> {
    let mut shared = None;
    let mut free = None;
    let mut outside = Vec::new();
    let mut split = None;
    for (i, sa) in sas.iter().enumerate() {
        let mut b = Binds::new();
        let mut miss = Vec::new();
        for (j, (x, y)) in qa.params.iter().zip(&sa.params).enumerate() {
            if !c.sub_in(x, y, &mut b).await {
                miss.push(j);
            }
        }
        // An arrow that takes no value of `qa` at some parameter takes no part.
        if !miss.iter().all(|&j| qa.params[j].meets(&sa.params[j])) {
            continue;
        }
        // In the order of the cases, each read off the state before a comparison borrows it.
        let binds = match miss[..] {
            [j] => !binds_nothing(&sa.params[j], &c.cx.borrow()),
            _ => false,
        };
        if let [_, _, ..] = miss[..] {
            split.get_or_insert(i);
        } else if binds {
            free.get_or_insert((i, miss[0]));
        } else if !bounds_hold(s, sa, &b, &c.cx.borrow()) {
            let cx = c.cx.borrow();
            let several = s
                .bounds
                .keys()
                .filter_map(|v| Some((v, b.get(v)?)))
                .find(|(v, t)| !one_carrier(t) && !one_place(sa, v, &cx));
            if let Some((v, t)) = several {
                shared.get_or_insert((i, v.clone(), t.clone(), Places::of(sa, v, &cx)));
            }
        } else if !result_within(sa, qa, &b, c).await {
            outside.push((i, miss.is_empty().then(|| sa.result.subst(&b))));
        }
    }
    let slot = arrow_text(q, &q.arrows[k]);
    let result = text_at(&q.arrows[k].result, q, &c.cx.borrow());
    let reason = if let Some((i, v, t, places)) = shared {
        let place = match places {
            Places { taken: 1.., .. } => format!(
                "`{v}` stands where the arrow takes values of it inside a function type, which \
                 need not be of the carrier its argument fixes"
            ),
            Places { given: 0, .. } => format!(
                "no argument gives values of `{v}` outside a function type, so none fixes its \
                 carrier"
            ),
            Places { given, .. } => format!(
                "`{v}` stands at {given} places the arguments give, which could be given values \
                 of two carriers"
            ),
        };
        format!(
            "the arrow `{}` takes it only with `{v}` bound to `{}`, values of more than one \
             carrier, but a call fixes `{v}` to one carrier, and {place}",
            arrow_text(s, &s.arrows[i]),
            text_at(&t, q, &c.cx.borrow())
        )
    } else if let Some((i, j)) = free {
        format!(
            "the arrow `{}` would take part of `{}` only by binding its type variable there, \
             and arrows that cover a parameter together bind no variable: which part each \
             takes is a choice per arrow, and fixing a bounded variable to each carrier of \
             its bound multiplies the arrows by the product of the bounds",
            arrow_text(s, &s.arrows[i]),
            s.params[j].name
        )
    } else if outside.len() >= 2 {
        let arrows: Vec<String> = outside
            .iter()
            .map(|&(i, _)| format!("`{}`", arrow_text(s, &s.arrows[i])))
            .collect();
        // When each takes all of `qa`, the intersection is the result at every value: a plain
        // reason, not a refused cover, with the intersection when the results have kernel types.
        let whole: Option<Vec<&Ty>> = outside.iter().map(|(_, r)| r.as_ref()).collect();
        if let Some(whole) = whole {
            let kernels: Option<Vec<KType>> = whole.iter().map(|r| r.kernel()).collect();
            let meet = match kernels.and_then(|ks| ks.into_iter().reduce(|a, b| &a & &b)) {
                Some(k) => format!(", `{}`,", Ty::set(k)),
                // Not built value by value ([`meet_within`]): the message says how.
                None => ", as the checker builds it (a function in one result is left out where \
                          another holds no function, and a variable bounded by carriers where \
                          each carrier of its bound is missing from some other result; every \
                          other piece that holds a function, a variable or the unknown is kept \
                          whole),"
                    .into(),
            };
            return Some(format!(
                "at `{slot}`, the arrows {} each take all of it, and the intersection of their \
                 results{meet} is not within `{result}`",
                arrows.join(", "),
            ));
        }
        format!(
            "the arrows {} each return outside `{result}`; where several take one value, the \
             result is what their results share, and the checker works that out only for \
             arrows that each take all that the arrows returning within `{result}` leave of one \
             parameter, since finding the values each group of arrows shares takes time that \
             grows with the product of their number; to repair it, write the arrows so that \
             each returns within `{result}`",
            arrows.join(", ")
        )
    } else {
        let i = split?;
        format!(
            "the arrow `{}` takes a part of more than one parameter, and arrows are combined \
             only when they differ at one parameter: telling whether arrows that each split \
             several parameters cover them all can take time exponential in the number of \
             parameters, so the checker does not try; to repair it, write the arrows so that \
             they differ at one parameter",
            arrow_text(s, &s.arrows[i])
        )
    };
    Some(format!("at `{slot}`, {reason}"))
}

/// `t` as a message about a comparison with `q` prints it: the variables `q` bounds by
/// carriers by their names, and the rigid variables made from them ([`Cx::fresh`]) by the
/// names they were made from, not as `_`. Only on the way to an error.
fn text_at(t: &Ty, q: &Sig, cx: &Cx) -> String {
    let carriers = |v: &str| q.bounds.get(v).is_some_and(|&m| m & OTHER == 0);
    let own = (q.bounds.keys())
        .filter(|v| carriers(v))
        .map(|v| (v.clone(), v.clone()));
    let rigid = cx.rigid.keys().filter_map(|w| {
        let (v, _) = w.rsplit_once('\'')?;
        carriers(v).then(|| (w.clone(), Arc::from(v)))
    });
    let mut scope = Scope::default();
    for (v, name) in own.chain(rigid) {
        scope.printed.insert(name.clone());
        scope.names.entry(v).or_default().push(Some(name));
    }
    let mut out = String::new();
    t.write(&mut out, &mut scope);
    out
}

/// The arrow `a` of `s`, as a function type of one arrow is written, with the bounds of the
/// variables it holds: at the cost of `a`, not of the other arrows of `s` (a message names each
/// arrow of an overload of `n`).
fn arrow_text(s: &Sig, a: &Arrow) -> String {
    let mut vs = Vars::default();
    a.params.iter().for_each(|p| p.vars_in(&mut vs));
    a.result.vars_in(&mut vs);
    let mut one = Sig {
        params: s.params.clone(),
        arrows: vec![a.clone()],
        bounds: (vs.order.iter())
            .filter_map(|v| Some((v.clone(), *s.bounds.get(v)?)))
            .collect(),
        data: s.data,
        word: None,
        needs: Vec::new(),
        own: vs
            .order
            .iter()
            .filter(|v| s.own.contains(*v))
            .cloned()
            .collect(),
        held: BTreeSet::new(),
        named: s.named,
        facts: Facts::default(),
    };
    one.note_held();
    Ty::func(Arc::new(one)).to_string()
}

/// Whether arrows of `sas` together cover `qa`, as rule 6 of sec:type_resolution types a call:
/// at each value of `qa`'s parameters, the arrows that take it are not none, and the
/// intersection of their results is within `qa`'s result. Two forms are built, each from the
/// candidates of the index ([`ArrowIndex::covering`]), each arrow compared once, its
/// parameters in one pass ([`part_of`]), so the cost is linear in the width, not its square.
///
/// By union: at some parameter `j`, the arrows that take `qa`'s other parameters and return
/// within its result together hold `qa`'s parameter type at `j`. Each value reaches one of
/// them, which gives a result within `qa`'s, whatever other arrows it reaches.
///
/// By intersection ([`met`]): the arrows that return within `qa`'s result take a part of
/// `qa`'s parameter at `j`, and every arrow of a set `H` takes all that they leave (or all of
/// `qa`'s parameters), and the intersection of the results of `H` is within `qa`'s. A value
/// outside the part reaches every arrow of `H`, so its result is within that intersection.
///
/// A parameter type at `j` that would bind a variable takes part in neither: one that holds a
/// type variable of `s` at any depth, as `(T,)`, since the union would bind it with no check
/// of its bound. A function type (read as a variable of `cx.fns`), a rigid variable and the
/// unknown bind nothing, and take part.
///
/// Complexity tradeoff: some overloads whose arrows together cover `qa` are refused, each
/// with its own reason ([`refused_cover`]). (1) Arrows that cover `qa` only by splitting two
/// or more parameters at once: `((x: int, y: int) -> R) & ((x: bool, y: bool) -> R) & ((x:
/// int, y: bool) -> R) & ((x: bool, y: int) -> R)` covers `(x: int | bool, y: int | bool) ->
/// R`, and is refused. Whether a union of products covers a product is DNF tautology when
/// each parameter has two values, coNP-complete, so a complete check is exponential in the
/// number of parameters. (2) An arrow whose parameter type at `j` holds a type variable of
/// `s`: which part of `qa`'s parameter the variable would be bound to is a choice per arrow,
/// and fixing a bounded variable to each carrier of its bound multiplies the arrows by the
/// product of the bounds, exponential in the variables. (3) Arrows that return outside `qa`'s
/// result, overlapping so that no one set of them takes every value the arrows within leave:
/// `((x: int | bool) -> String | #a) & ((x: int) -> String | #b) & ((x: bool) -> String |
/// #c)` covers `(x: int | bool) -> String`, the intersection `String` at `int` from the first
/// two and at `bool` from the first and third, and is refused. Deciding that is the
/// all-subsets condition of semantic subtyping on arrows (Frisch, Castagna and Benzaken, J.
/// ACM 2008); it is as hard as Orthogonal Vectors even with one parameter of atoms (each
/// arrow a coordinate, each atom of the parameter a vector of the arrows that take it, each
/// atom outside the result a vector of the arrows whose results leave it out), so no
/// n^(2-e) algorithm is expected under the Strong Exponential Time Hypothesis (Williams,
/// TCS 2005; a conjecture). Tests: l01_26_type_resolution::fits (each case, its message and a
/// near miss), and the differential tests below, against every subset of arrows and against
/// the values of small types; COMPLEXITY.md F82. A complete solution would split `qa`'s
/// parameters into the regions the arrows' parameter types cut, and intersect the results per
/// region.
///
/// Complexity tradeoff: the candidates, as those of one arrow ([`every_arrow_fits`]), are not
/// below n·m in the worst case. Arrows that all offer one piece of the slot's parameter are
/// each compared with each arrow of the slot: `(x: #c | #ai) -> String` for i below n, passed
/// where `(x: #c | #ak | #a(k+1)) -> String | #zk` is expected for each k, cost n·m
/// comparisons (63.3 times the bytes at n = 100 and 800). Covering together includes fitting
/// by one arrow, so the containment join of [`every_arrow_fits`] bounds it from below; stopping
/// at the first arrow that holds each key is not exact, since a key (a carrier, an atom's name)
/// does not decide which values of it an arrow holds. The intersection takes the candidates
/// whatever their results, since the arrows of `H` return outside `qa`'s.
async fn covered<'m>(
    s: &Sig,
    sas: &[Arrow],
    index: &ArrowIndex<'_>,
    qa: &Arrow,
    c: &'m Comparing<'m, '_>,
) -> bool {
    // The parts at each parameter, by parameter; a BTreeMap, so the parameters are tried in
    // order, and only those some arrow misses are held.
    let mut parts: BTreeMap<usize, Vec<&Ty>> = BTreeMap::new();
    for i in index.covering(qa, true) {
        if let Some((Part::At(j, true), _)) = part_of(s, &sas[i], qa, c).await {
            parts.entry(j).or_default().push(&sas[i].params[j]);
        }
    }
    for (j, ps) in parts {
        if c.sub_in(&qa.params[j], &Ty::union_all(ps), &mut Binds::new())
            .await
        {
            return true;
        }
    }
    met(s, sas, &index.covering(qa, false), qa, c).await
}

/// How the arrow `sa` of `s` takes `qa`'s parameters ([`part_of`]).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Part {
    /// It takes all of them; it returns outside `qa`'s result, or it would fit alone.
    Whole,
    /// It takes all but the parameter `j`, at which its type binds nothing, and returns within
    /// `qa`'s result or not.
    At(usize, bool),
}

/// How the arrow `sa` of `s` takes the parameters of `qa`: all of them, or all but one `j`,
/// at which its type binds nothing ([`binds_nothing`]), each bounded variable of `s` it binds
/// bound as [`bounds_hold`] requires, with what it binds. [`arrow_fits`] with `j` left out: a type that binds
/// nothing, so the pass over every parameter binds what the pass without `j` binds.
async fn part_of<'m>(
    s: &Sig,
    sa: &Arrow,
    qa: &Arrow,
    c: &'m Comparing<'m, '_>,
) -> Option<(Part, Binds)> {
    let mut b = Binds::new();
    let mut miss = None;
    for (j, (x, y)) in qa.params.iter().zip(&sa.params).enumerate() {
        if !c.sub_in(x, y, &mut b).await {
            if miss.is_some() || !binds_nothing(y, &c.cx.borrow()) {
                return None;
            }
            miss = Some(j);
        }
    }
    if !bounds_hold(s, sa, &b, &c.cx.borrow()) {
        return None;
    }
    let part = match miss {
        None => Part::Whole,
        Some(j) => Part::At(j, result_within(sa, qa, &b, c).await),
    };
    Some((part, b))
}

/// Whether comparing a type with `t` binds nothing: each variable it holds outside functions,
/// at any depth, is a rigid variable or a function read as one ([`Cx::read`]). The unknown
/// binds nothing; a type variable of the given side would be bound. The tuples are walked on
/// an explicit stack, each type's variables before its components and the components in
/// order, as the recursive form walked them, stopping at the first variable that binds.
fn binds_nothing(t: &Ty, cx: &Cx) -> bool {
    let mut stack = vec![t];
    while let Some(t) = stack.pop() {
        if !t
            .vars
            .iter()
            .all(|v| cx.rigid.contains_key(v) || cx.fns.contains_key(v))
        {
            return false;
        }
        stack.extend(t.tuples.iter().rev().flat_map(|r| r.iter().rev()));
    }
    true
}

/// Whether the candidates `cands` of `sas` cover `qa` by intersection ([`covered`]): with
/// `U` the union of the parameter types at `j` of the arrows that take a part there and
/// return within `qa`'s result, and `H` the arrows that take all of `qa`'s parameters with
/// those that take, at `j`, all of `qa`'s type there outside `U`, `H` is not empty and the
/// intersection of its results is within `qa`'s; or `H` is the arrows that take all of `qa`.
/// [`Ty::diff`] keeps a part it cannot subtract, so `H` takes at least what the arrows within
/// leave. The results are intersected by [`meet_within`]. The cost is one comparison of each
/// candidate and, for each `j`, one of each arrow that takes a part there with what the others
/// leave.
async fn met<'m>(
    s: &Sig,
    sas: &[Arrow],
    cands: &[usize],
    qa: &Arrow,
    c: &'m Comparing<'m, '_>,
) -> bool {
    // An arrow of `q` that takes no value is left to one arrow and the union, as before this
    // form: the index leaves out arrows of `s` that take part of no parameter of it.
    if qa.params.iter().any(Ty::is_empty) {
        return false;
    }
    // The results of the arrows that take all of `qa`, and, at each parameter, the parameter
    // types of the arrows within and of those outside, with their results.
    let mut whole: Vec<Ty> = Vec::new();
    let mut within: BTreeMap<usize, Vec<&Ty>> = BTreeMap::new();
    let mut outside: BTreeMap<usize, Vec<(&Ty, Ty)>> = BTreeMap::new();
    for &i in cands {
        let sa = &sas[i];
        match part_of(s, sa, qa, c).await {
            Some((Part::Whole, b)) => whole.push(sa.result.subst(&b)),
            Some((Part::At(j, true), _)) => within.entry(j).or_default().push(&sa.params[j]),
            Some((Part::At(j, false), b)) => outside
                .entry(j)
                .or_default()
                .push((&sa.params[j], sa.result.subst(&b))),
            None => {}
        }
    }
    if !whole.is_empty() && meet_within(&whole, &qa.result, c).await {
        return true;
    }
    // At a parameter no arrow outside takes a part of, `H` is the arrows that take all of `qa`.
    for (&j, parts) in &outside {
        let left = match within.get(&j) {
            Some(ps) => {
                c.diff(&qa.params[j], &Ty::union_all(ps.iter().copied()), None)
                    .await
            }
            None => qa.params[j].clone(),
        };
        let mut h = whole.clone();
        for (p, r) in parts {
            if c.sub_in(&left, p, &mut Binds::new()).await {
                h.push(r.clone());
            }
        }
        if !h.is_empty() && meet_within(&h, &qa.result, c).await {
            return true;
        }
    }
    false
}

/// Whether the intersection of `results` is within `result`. Each result is split into its
/// kernel part, its scalars and atoms and the tuple shapes that hold no function, variable or
/// unknown at any depth, and the rest. The kernel parts are intersected exactly. A value in
/// every result outside that intersection is outside the kernel part of some result `i`, so
/// in a piece of the rest of `i` and in every other result: each such piece must be within
/// `result`, unless no value of it is in every other result. That is known of a function,
/// when another result holds no function, and of a rigid variable bounded by carriers, when
/// each carrier of its bound is missing from some other result, since a call fixes it to one
/// carrier. Linear in the results: the carriers every result but one may hold are read off a
/// pass from each end.
///
/// Complexity tradeoff: a piece of the rest is not intersected value by value, so some
/// intersections within `result` are refused: `(U,) | String` and `(bool,) | String` meet
/// only on `String`, but the tuple piece `(U,)` is not within `String`. Such a fit gets the
/// error [`refused_cover`] writes, "the intersection of their results, as the checker builds
/// it (...), is not within", which states the rule above (test
/// `l01_26_type_resolution::fits::results_that_hold_a_function_or_a_variable_are_intersected`,
/// COMPLEXITY.md F82). Intersecting rigid variables value by value would fix each to each
/// carrier of its bound, the product of the bounds in the variables; the tuple pieces would
/// need the intersection per component of each pair of shapes of one width, quadratic in the
/// shapes.
async fn meet_within<'m>(results: &[Ty], result: &Ty, c: &'m Comparing<'m, '_>) -> bool {
    if results.is_empty() {
        return false;
    }
    let (kernels, rest) = {
        let cx = c.cx.borrow();
        let masks: Vec<u8> = results.iter().map(|r| carriers_of(r, &cx)).collect();
        let mut after = vec![EVERY; masks.len() + 1];
        for (i, &m) in masks.iter().enumerate().rev() {
            after[i] = after[i + 1] & m;
        }
        let no_function = results.iter().any(|r| holds_no_function(r, &cx));
        let mut before = EVERY;
        let mut kernels = Vec::with_capacity(results.len());
        let mut rest = Ty::empty();
        for (i, r) in results.iter().enumerate() {
            let others = before & after[i + 1];
            before &= masks[i];
            let mut shapes = Vec::new();
            for row in &r.tuples {
                match row.iter().map(Ty::kernel).collect::<Option<Vec<_>>>() {
                    Some(cs) => shapes.push(KType::tuple(cs)),
                    None => rest.tuples.push(row.clone()),
                }
            }
            kernels.push(KType::union_all(
                std::iter::once(r.set.clone()).chain(shapes),
            ));
            if !no_function {
                rest.fns.extend(r.fns.iter().cloned());
            }
            for v in &r.vars {
                let missed = match cx.rigid.get(v) {
                    Some(&m) => m & OTHER == 0 && m & others == 0,
                    None => no_function && cx.fns.contains_key(v),
                };
                if !missed {
                    rest.vars.insert(v.clone());
                }
            }
            rest.dynamic |= r.dynamic;
        }
        (kernels, rest)
    };
    let Some(k) = kernels.into_iter().reduce(|a, b| &a & &b) else {
        return false;
    };
    let mut b = Binds::new();
    let kernel_within = match result.kernel() {
        Some(r) => k.subtype(&r),
        None => c.sub_in(&Ty::set(k), result, &mut b).await && b.is_empty(),
    };
    kernel_within && (rest.is_empty() || c.sub_in(&rest, result, &mut b).await && b.is_empty())
}

/// Results [`meet_within`] intersects and the result their intersection must be within, built
/// before a scaling test so that the test times the intersection alone and not the check of
/// the overload around it, which costs about 160,000 instructions a result: a quadratic in the
/// results that allocates nothing shows only here (COMPLEXITY.md F82, F85).
#[doc(hidden)]
pub struct Meet {
    results: Vec<Ty>,
    result: Ty,
    rigid: BTreeMap<Arc<str>, u8>,
}

impl Meet {
    /// `results` and `result`, inside expected function types whose bounded variables are
    /// `rigid`, each with the carriers of its bound.
    #[doc(hidden)]
    pub fn new(results: Vec<Ty>, result: Ty, rigid: &[(&str, &[Carrier])]) -> Self {
        let rigid = rigid
            .iter()
            .map(|&(v, cs)| (Arc::from(v), cs.iter().fold(0, |m, c| m | c.bit())))
            .collect();
        Meet {
            results,
            result,
            rigid,
        }
    }

    /// Whether the intersection of the results is within the result ([`meet_within`]).
    #[doc(hidden)]
    pub fn within(&self) -> bool {
        let mut cx = Cx {
            rigid: self.rigid.clone(),
            ..Cx::default()
        };
        let ok = comparing!(&mut cx, |c| meet_within(&self.results, &self.result, &c));
        cx.decided(ok)
    }
}

/// The carriers a value of `t`, as a comparison reads it, may be of, and [`OTHER`] if it may
/// be another value: a rigid variable stands for its bound, and a function read as a variable
/// for no carrier.
fn carriers_of(t: &Ty, cx: &Cx) -> u8 {
    if t.dynamic {
        return EVERY;
    }
    let split = t.set.split();
    let set = Carrier::ALL
        .into_iter()
        .filter(|c| split.bases[c.base()].is_some())
        .fold(0, |m, c| m | c.bit());
    t.vars.iter().fold(set, |m, v| match cx.rigid.get(v) {
        Some(&bound) => m | bound,
        None if cx.fns.contains_key(v) => m | OTHER,
        None => EVERY,
    })
}

/// Whether no value of `t`, as a comparison reads it, is a function: it holds no function, no
/// function read as a variable, no unknown, and only rigid variables bounded by carriers.
fn holds_no_function(t: &Ty, cx: &Cx) -> bool {
    t.fns.is_empty()
        && !t.dynamic
        && t.vars
            .iter()
            .all(|v| cx.rigid.get(v).is_some_and(|&m| m & OTHER == 0))
}

/// What a parameter type of an arrow must hold to hold a piece of a parameter type: the
/// values of one carrier, by [`Carrier::base`], or the bare atom of one name.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Key<'t> {
    Carrier(usize),
    Atom(&'t str),
}

/// The keys every type that holds `t` offers, unless it is open ([`offered_keys`]): the
/// carriers of its scalars and its bare atoms, of a set of atoms that lists its names. A piece
/// of `t` a key does not decide, a tuple, a kind-wide part, a function, a variable or the
/// unknown, adds none.
fn needed_keys<'t>(t: &'t Ty, out: &mut Vec<Key<'t>>) {
    let split = t.set.split();
    out.extend(
        Carrier::ALL
            .into_iter()
            .filter(|c| split.bases[c.base()].is_some())
            .map(|c| Key::Carrier(c.base())),
    );
    if let Some(names) = t.set.atom_names() {
        out.extend(names.filter(|&(_, bare)| bare).map(|(n, _)| Key::Atom(n)));
    }
}

/// The keys the parameter type `t` offers, and whether it is closed: it holds no variable and
/// no unknown, and lists the names of its atoms. A closed type holds a scalar or bare atom only
/// if it offers its key ([`accepts`]: a set piece is held by the set alone, unless `t` has a
/// variable or the unknown). An open one may hold any piece. It may offer a key it holds no
/// value of, an atom name listed with an empty payload, which makes only a candidate more.
fn offered_keys<'t>(t: &'t Ty, out: &mut Vec<Key<'t>>) -> bool {
    let Some(names) = t
        .set
        .atom_names()
        .filter(|_| !t.dynamic && t.vars.is_empty())
    else {
        return false;
    };
    out.extend(names.map(|(n, _)| Key::Atom(n)));
    let split = t.set.split();
    out.extend(
        Carrier::ALL
            .into_iter()
            .filter(|c| split.bases[c.base()].is_some())
            .map(|c| Key::Carrier(c.base())),
    );
    true
}

/// The keys of every piece of `t`, when each piece has one: the carriers of its scalars and the
/// names of its atoms. A parameter type that holds a value of `t` and is closed
/// ([`offered_keys`]) offers that value's key. False when `t` has a piece no key decides: a
/// tuple, a kind-wide part, a function, a variable, the unknown or a cofinite set of atoms.
fn piece_keys<'t>(t: &'t Ty, out: &mut Vec<Key<'t>>) -> bool {
    if t.dynamic || !t.vars.is_empty() || !t.tuples.is_empty() || !t.fns.is_empty() {
        return false;
    }
    let split = t.set.split();
    let Some(names) = t.set.atom_names().filter(|_| split.rest.is_none()) else {
        return false;
    };
    out.extend(names.map(|(n, _)| Key::Atom(n)));
    out.extend(
        Carrier::ALL
            .into_iter()
            .filter(|c| split.bases[c.base()].is_some())
            .map(|c| Key::Carrier(c.base())),
    );
    true
}

/// The arrows of a signature, as read, by what their parameter types offer and their result
/// types need: for the arrows of an expected signature, the arrows that may fit each, found
/// from the keys of its parameter and result types ([`every_arrow_fits`], [`covered`]).
struct ArrowIndex<'t> {
    /// The number of arrows.
    n: usize,
    /// For each parameter and each key, the arrows whose parameter type there is closed and
    /// offers the key, in order.
    post: HashMap<(usize, Key<'t>), Vec<usize>>,
    /// For each parameter, whether each arrow's type there is open (or missing).
    open: Vec<Vec<bool>>,
    /// For each parameter, the arrows whose type there is open, in order.
    always: Vec<Vec<usize>>,
    /// For each arrow, the keys its result type needs ([`needed_keys`]): a closed type that
    /// holds the result offers each.
    result_needs: Vec<Vec<Key<'t>>>,
    /// The arrows whose result type needs a key, each under one of them, the one the fewest
    /// results need, in order.
    by_result: HashMap<Key<'t>, Vec<usize>>,
    /// The arrows whose result type needs no key, in order.
    any_result: Vec<usize>,
}

impl<'t> ArrowIndex<'t> {
    /// The index of `sas`, arrows of `width` parameters, in the size of their parameter and
    /// result types.
    fn new(sas: &'t [Arrow], width: usize) -> ArrowIndex<'t> {
        let mut post: HashMap<(usize, Key<'t>), Vec<usize>> = HashMap::new();
        let mut open = vec![vec![false; sas.len()]; width];
        let mut keys = Vec::new();
        for (i, sa) in sas.iter().enumerate() {
            for (j, row) in open.iter_mut().enumerate() {
                keys.clear();
                match sa.params.get(j) {
                    Some(t) if offered_keys(t, &mut keys) => {
                        for &k in &keys {
                            post.entry((j, k)).or_default().push(i);
                        }
                    }
                    _ => row[i] = true,
                }
            }
        }
        let always = open
            .iter()
            .map(|row| {
                (0..)
                    .zip(row)
                    .filter(|&(_, &o)| o)
                    .map(|(i, _)| i)
                    .collect()
            })
            .collect();
        let result_needs: Vec<Vec<Key<'t>>> = sas
            .iter()
            .map(|sa| {
                let mut keys = Vec::new();
                needed_keys(&sa.result, &mut keys);
                keys
            })
            .collect();
        let mut count: HashMap<Key<'t>, usize> = HashMap::new();
        for k in result_needs.iter().flatten() {
            *count.entry(*k).or_default() += 1;
        }
        let mut by_result: HashMap<Key<'t>, Vec<usize>> = HashMap::new();
        let mut any_result = Vec::new();
        for (i, keys) in result_needs.iter().enumerate() {
            match keys.iter().min_by_key(|k| count[*k]) {
                Some(&k) => by_result.entry(k).or_default().push(i),
                None => any_result.push(i),
            }
        }
        ArrowIndex {
            n: sas.len(),
            post,
            open,
            always,
            result_needs,
            by_result,
            any_result,
        }
    }

    /// For each key `qa`'s parameters need, at each parameter: the parameter and the arrows
    /// whose closed type there offers the key.
    fn needed(&self, qa: &'t Arrow) -> Vec<(usize, &[usize])> {
        let mut need = Vec::new();
        let mut keys = Vec::new();
        for (j, t) in qa.params.iter().enumerate().take(self.open.len()) {
            keys.clear();
            needed_keys(t, &mut keys);
            need.extend(
                keys.iter()
                    .map(|k| (j, self.post.get(&(j, *k)).map_or(&[][..], Vec::as_slice))),
            );
        }
        need
    }

    /// The keys `qa`'s result type offers, when it is closed: an arrow whose result needs a
    /// key outside them returns outside it.
    fn result_keys(qa: &'t Arrow) -> Option<HashSet<Key<'t>>> {
        let mut keys = Vec::new();
        offered_keys(&qa.result, &mut keys).then(|| keys.into_iter().collect())
    }

    /// The arrows whose results may be within a closed type that offers `keys`: those filed
    /// under one of them, and those whose results need no key.
    fn by_results(&self, keys: &HashSet<Key<'t>>) -> Vec<&[usize]> {
        let mut lists: Vec<&[usize]> = keys
            .iter()
            .filter_map(|k| self.by_result.get(k).map(Vec::as_slice))
            .collect();
        lists.push(&self.any_result);
        lists
    }

    /// The arrows of the shortest of `sources`, each the union of its lists, in order, kept
    /// when, at each parameter of `need`, the arrow is open or offers the key, and when
    /// `result` is given, it offers every key the arrow's result needs. Every arrow when there
    /// is no source. The cost is the shortest source's length, times its logarithm and the
    /// keys tested.
    fn candidates(
        &self,
        need: &[(usize, &[usize])],
        result: Option<&HashSet<Key<'t>>>,
        sources: Vec<Vec<&[usize]>>,
    ) -> Vec<usize> {
        let keep = |&i: &usize| {
            need.iter()
                .all(|&(k, l)| self.open[k][i] || l.binary_search(&i).is_ok())
                && result.is_none_or(|r| self.result_needs[i].iter().all(|k| r.contains(k)))
        };
        let Some(lists) = sources
            .into_iter()
            .min_by_key(|lists| lists.iter().map(|l| l.len()).sum::<usize>())
        else {
            return (0..self.n).filter(keep).collect();
        };
        let mut out: Vec<usize> = lists.into_iter().flatten().copied().collect();
        out.sort_unstable();
        out.dedup();
        out.retain(keep);
        out
    }

    /// The arrows that may fit `qa`, in order, to be tried until one fits. The candidates come
    /// from the shortest list: the arrows that offer one key `qa`'s parameters need, with the
    /// arrows open at that parameter, or the arrows whose results may be within `qa`'s closed
    /// result. Each is kept if, at every parameter, it is open or offers every key `qa` needs
    /// there, and its result needs no key `qa`'s closed result lacks.
    fn may_fit(&self, qa: &'t Arrow) -> Vec<usize> {
        let need = self.needed(qa);
        let result = Self::result_keys(qa);
        let mut sources: Vec<Vec<&[usize]>> = need
            .iter()
            .map(|&(j, l)| vec![l, &self.always[j][..]])
            .collect();
        if let Some(r) = &result {
            sources.push(self.by_results(r));
        }
        self.candidates(&need, result.as_ref(), sources)
    }

    /// The arrows that offer one key of `qa`'s parameter at `j` there, or are open there, when
    /// each piece of it has a key ([`piece_keys`]): an arrow outside them holds no value of it.
    fn pieces_at(&self, qa: &'t Arrow, j: usize) -> Option<Vec<&[usize]>> {
        let mut keys = Vec::new();
        piece_keys(&qa.params[j], &mut keys).then(|| {
            let mut lists: Vec<&[usize]> = keys
                .iter()
                .map(|k| self.post.get(&(j, *k)).map_or(&[][..], Vec::as_slice))
                .collect();
            lists.push(&self.always[j]);
            lists
        })
    }

    /// The arrows that may take part in covering `qa` at some parameter ([`covered`]): those
    /// that, at every parameter but at most one, are open or offer every key `qa` needs there,
    /// and whose results need no key `qa`'s closed result lacks. They come from the shortest
    /// source that holds every such arrow: the arrows whose results may be within `qa`'s; or
    /// the arrows that offer the key of the shortest list, at parameter `a`, or are open there,
    /// which hold each arrow that misses another parameter, with, for the arrows that miss
    /// `a`, the shortest list at another parameter or the arrows that offer a piece of `qa`'s
    /// parameter at `a`; or, when `qa` needs no key at any parameter, the arrows that offer a
    /// piece at some parameter. Every arrow when there is no source. With `by_result` false, the
    /// results filter nothing: the arrows that may take part in covering `qa` by intersection,
    /// whose results are outside `qa`'s ([`met`]).
    fn covering(&self, qa: &'t Arrow, by_result: bool) -> Vec<usize> {
        let need = self.needed(qa);
        let result = Self::result_keys(qa).filter(|_| by_result);
        let len = |lists: &[&[usize]]| lists.iter().map(|l| l.len()).sum::<usize>();
        let mut sources: Vec<Vec<&[usize]>> = Vec::new();
        if let Some(r) = &result {
            sources.push(self.by_results(r));
        }
        // The shortest source of one needed key, at a parameter `at` admits, with its parameter.
        let shortest = |at: &dyn Fn(usize) -> bool| {
            need.iter()
                .filter(|e| at(e.0))
                .map(|&(k, l)| (k, vec![l, &self.always[k][..]]))
                .min_by_key(|(_, lists)| len(lists))
        };
        if let Some((a, first)) = shortest(&|_| true) {
            let other = [shortest(&|k| k != a).map(|e| e.1), self.pieces_at(qa, a)]
                .into_iter()
                .flatten()
                .min_by_key(|lists| len(lists));
            if let Some(other) = other {
                sources.push(first.into_iter().chain(other).collect());
            }
        } else {
            let width = qa.params.len().min(self.open.len());
            let pieces: Option<Vec<Vec<&[usize]>>> =
                (0..width).map(|j| self.pieces_at(qa, j)).collect();
            if let Some(pieces) = pieces.filter(|p| !p.is_empty()) {
                sources.push(pieces.into_iter().flatten().collect());
            }
        }
        let keep = |i: usize| {
            let mut missed = None;
            need.iter().all(|&(k, l)| {
                self.open[k][i]
                    || l.binary_search(&i).is_ok()
                    || missed.replace(k).is_none_or(|m| m == k)
            }) && result
                .as_ref()
                .is_none_or(|r| self.result_needs[i].iter().all(|k| r.contains(k)))
        };
        let mut out: Vec<usize> = match sources.into_iter().min_by_key(|lists| len(lists)) {
            Some(lists) => lists.into_iter().flatten().copied().collect(),
            None => (0..self.n).collect(),
        };
        out.sort_unstable();
        out.dedup();
        out.retain(|&i| keep(i));
        out
    }
}

impl PartialEq for Sig {
    /// Compares the types of the arrows with a `Same`, which needs no stack as deep as they
    /// are: a function type nests functions as deep as the program.
    fn eq(&self, other: &Sig) -> bool {
        let mut same = Same::default();
        same.sig(self, other) && same.rest()
    }
}

impl std::hash::Hash for Sig {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        h.write_u64(self.digest());
    }
}

/// Whether the arrow `sa` of `s` takes the parameters of the arrow `qa` and returns within its
/// result, each bounded variable of `s` bound to carriers of its bound ([`fits_in`]).
async fn arrow_fits<'m>(s: &Sig, sa: &Arrow, qa: &Arrow, c: &'m Comparing<'m, '_>) -> bool {
    let mut b = Binds::new();
    for (x, y) in qa.params.iter().zip(&sa.params) {
        if !c.sub_in(x, y, &mut b).await {
            return false;
        }
    }
    let held = bounds_hold(s, sa, &b, &c.cx.borrow());
    held && result_within(sa, qa, &b, c).await
}

/// Whether each bounded variable of `s` that `b` binds is bound to carriers of its bound, and,
/// when bound to values of more than one carrier, stands where the arrow `sa` may take them
/// ([`one_place`]). A call fixes the variable to one carrier, so `(x: T, y: T) -> T for T in
/// int | f64` bound to `int | f64` would be called with an `int` and an `f64`, which no call
/// of it is.
fn bounds_hold(s: &Sig, sa: &Arrow, b: &Binds, cx: &Cx) -> bool {
    s.bounds.iter().all(|(v, &m)| {
        b.get(v)
            .is_none_or(|t| match t.as_var().and_then(|w| cx.rigid.get(w)) {
                // Each carrier the caller of `q` may pick is one `s` takes.
                Some(&mq) => mq & !m == 0,
                // `v` is one carrier at a call, so it cannot be a rigid variable and
                // something else at once.
                None => {
                    t.pieces().iter().all(|p| match p.carrier() {
                        Some(c) => m & c.bit() != 0,
                        None => {
                            m & OTHER != 0
                                && !matches!(p, Piece::Dyn)
                                && !matches!(p, Piece::Var(w) if cx.rigid.contains_key(w))
                        }
                    }) && (one_carrier(t) || one_place(sa, v, cx))
                }
            })
    })
}

/// Whether the values of `t` are of one carrier, or of none.
fn one_carrier(t: &Ty) -> bool {
    let mut carriers = t.pieces().into_iter().map(|p| p.carrier());
    let first = carriers.next().flatten();
    carriers.all(|c| c == first)
}

/// Whether the variable `v` stands in the arrow `sa`, as read, at one place where an argument
/// gives its values, outside every function type, and elsewhere only where the arrow gives
/// values of it: in its result, or in a parameter of a function type a parameter takes. Then
/// `v` bound to values of several carriers takes, at each value of that place, the arrow at
/// that value's carrier, which returns within the arrow at all of them. A second place an
/// argument fixes, or a place the arrow takes values at inside a function type (a parameter of
/// a function it returns, the result of a function it takes), would need one carrier at both.
/// The cost is a walk of `sa`.
fn one_place(sa: &Arrow, v: &str, cx: &Cx) -> bool {
    let places = Places::of(sa, v, cx);
    places.given == 1 && places.taken == 0
}

/// The places of a variable in an arrow ([`one_place`]).
#[derive(Default)]
struct Places {
    /// Those where an argument gives its values, outside every function type.
    given: usize,
    /// Those where the arrow takes values of it, inside a function type.
    taken: usize,
}

impl Places {
    /// The places of `v` in the arrow `sa`, as read.
    fn of(sa: &Arrow, v: &str, cx: &Cx) -> Places {
        let mut places = Places::default();
        let mut stack: Vec<(&Ty, bool, bool)> =
            sa.params.iter().map(|p| (p, false, true)).collect();
        stack.push((&sa.result, true, true));
        places.walk(stack, v, cx);
        places
    }

    /// Counts the places of `v` in each type `t` of `stack`, with `(t, out, top)`: the arrow
    /// gives values of `t` when `out` and takes values of it when not, outside every function
    /// type when `top`. A function type read as a variable ([`Cx::read`]) is walked as its
    /// signature; one that binds `v` itself does not hold this `v`. The parts are walked on an
    /// explicit stack, so a type nested to any depth needs no more of the thread's stack; the
    /// counts do not depend on the order.
    fn walk<'t>(&mut self, mut stack: Vec<(&'t Ty, bool, bool)>, v: &str, cx: &'t Cx) {
        while let Some((t, out, top)) = stack.pop() {
            if !out && t.vars.contains(v) {
                match top {
                    true => self.given += 1,
                    false => self.taken += 1,
                }
            }
            for c in t.tuples.iter().flat_map(|r| r.iter()) {
                stack.push((c, out, top));
            }
            let read = t.vars.iter().filter_map(|w| cx.fns.get(w).map(|e| &e.0));
            for s in t.fns.iter().chain(read) {
                if s.own.contains(v) {
                    continue;
                }
                for a in &s.arrows {
                    for p in &a.params {
                        stack.push((p, !out, false));
                    }
                    stack.push((&a.result, out, false));
                }
            }
        }
    }
}

/// Whether the result of `sa`, its variables bound by `b`, is within `qa`'s, binding nothing.
async fn result_within<'m>(sa: &Arrow, qa: &Arrow, b: &Binds, c: &'m Comparing<'m, '_>) -> bool {
    let mut rb = Binds::new();
    c.sub_in(&sa.result.subst(b), &qa.result, &mut rb).await && rb.is_empty()
}

impl Sig {
    /// Sets [`Sig::held`] from its parameters, at any depth, on any arrow: for a signature
    /// built from parts, at the cost of a walk of its parameters.
    pub fn note_held(&mut self) {
        debug_assert!(
            self.facts.0.get().is_none() && self.facts.2.get().is_none(),
            "a signature is changed after its facts were read"
        );
        self.held.clear();
        if self.bounds.is_empty() {
            return;
        }
        let mut vs = Vars::default();
        for a in &self.arrows {
            a.params.iter().for_each(|p| p.vars_in(&mut vs));
        }
        self.held = vs
            .order
            .into_iter()
            .filter(|v| self.own.contains(v) && self.bounds.contains_key(v))
            .collect();
    }

    /// It with each class variable `solve` gives a type replaced by that type at every depth.
    pub fn solved_with(&self, solve: Solve) -> Sig {
        let mut vs = Vars::default();
        for a in &self.arrows {
            a.params.iter().for_each(|p| p.vars_in(&mut vs));
            a.result.vars_in(&mut vs);
        }
        self.needs.iter().for_each(|n| n.vars_in(&mut vs));
        let binds: Binds = (vs.order.into_iter())
            .filter_map(|v| solve(&v).map(|t| (v, t)))
            .collect();
        self.replace(&binds)
    }

    /// Its own bounded variables no parameter holds, each bound to [`Ty::of_mask`] of its
    /// bound: no argument fixes its carrier, so a call returns a value of some carrier of it.
    pub fn unheld(&self) -> Binds {
        self.bounds
            .iter()
            .filter(|(v, _)| self.own.contains(*v) && !self.held.contains(*v))
            .map(|(v, &m)| (v.clone(), Ty::of_mask(m)))
            .collect()
    }

    /// Its hash, made at the first call from its parts, each function it holds by its own
    /// hash: so it is asked of a signature held in a type, which no longer changes. Hashed
    /// whole, a set of the functions of `g(0)(1)…(n)` cost the depth of each (CHK-carrier).
    pub fn digest(&self) -> u64 {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        let hash = |s: &Sig| {
            *s.facts.2.get_or_init(|| {
                let parts = (&s.params, &s.arrows, &s.bounds, s.data, &s.word);
                let more = (&s.needs, &s.own, &s.held, s.named);
                BuildHasherDefault::<DefaultHasher>::default().hash_one((parts, more))
            })
        };
        if let Some(&d) = self.facts.2.get() {
            return d;
        }
        // The hashes of the functions it holds that lack one are made first, deepest first, as
        // for its facts ([`Sig::facts`]).
        for s in self.held_without(true, |s| s.facts.2.get().is_none()) {
            hash(s);
        }
        hash(self)
    }

    /// The variables it holds at any depth: worked out at the first call, so it is asked of
    /// a signature held in a type, which no longer changes.
    pub fn facts(&self) -> &VarFacts {
        if let Some(f) = self.facts.0.get() {
            return f;
        }
        // The facts of a signature are made from those of the functions it holds, so those
        // that lack them are worked out first, deepest first, on a stack of its own: asked of
        // the outermost of a nest of n functions, the facts would otherwise recurse n deep.
        for s in self.held_without(false, |s| s.facts.0.get().is_none()) {
            s.facts.0.get_or_init(|| VarFacts::of(s));
        }
        self.facts.0.get_or_init(|| VarFacts::of(self))
    }

    /// The signatures of the functions it holds at any depth for which `lacks` holds, each
    /// after those it holds and once: the walk stops at a signature for which `lacks` fails,
    /// so it costs the signatures returned and their parts. It looks in the types of the
    /// arrows and in those of the needs that [`Need::tys`] gives, or in every type of each
    /// need if `whole`. A row or payload keeps what it holds worked out when it is built.
    fn held_without<'s>(&'s self, whole: bool, lacks: impl Fn(&Sig) -> bool) -> Vec<&'s Sig> {
        let fns = |s: &'s Sig| -> Vec<&'s Sig> {
            let arrows = s
                .arrows
                .iter()
                .flat_map(|a| a.params.iter().chain([&a.result]));
            let needs = s.needs.iter().flat_map(|n| match whole {
                true => n.every_ty(),
                false => n.tys().collect(),
            });
            arrows
                .chain(needs)
                .flat_map(|t| t.fns.iter().map(|f| &**f))
                .collect()
        };
        let (mut seen, mut order) = (HashSet::new(), Vec::new());
        // Each signature is entered with the signatures it holds still to visit, and left
        // once they are done.
        let mut stack: Vec<(&Sig, Vec<&Sig>)> = vec![(self, fns(self))];
        while let Some((_, todo)) = stack.last_mut() {
            match todo.pop() {
                Some(s) if lacks(s) && seen.insert(s as *const Sig) => stack.push((s, fns(s))),
                Some(_) => {}
                None => order.extend(stack.pop().map(|(s, _)| s)),
            }
        }
        order.pop(); // `self`, left last.
        order
    }

    /// It with each class variable `solve` gives a type replaced by that type at every depth:
    /// made at the first call and kept, so it is asked only when no class changes after,
    /// as the checker finishes. A signature that holds no class variable is itself.
    pub fn settle(self: &Arc<Sig>, solve: Solve) -> Arc<Sig> {
        if self.facts().classes.is_empty() {
            return self.clone();
        }
        let made = Vec::new();
        rebuild_held(&mut Settle { solve, made }, self)
    }

    /// The class variables of `want` that its arrows and needs hold, in the order in which
    /// [`Ty::vars_in`] meets them. The walk enters no function whose facts hold none of those
    /// still unseen, and it stops once all are seen, so it costs no more than replacing them.
    /// A row or payload shape met again is shared and was walked whole the first time, so it
    /// is entered once.
    pub fn first_seen(&self, want: &HashSet<Arc<str>>) -> Vec<Arc<str>> {
        enum Item<'a> {
            Ty(&'a Ty),
            Row(&'a Row),
            Shape(&'a Shape),
            Sig(&'a Sig),
        }
        let mut out = Vec::new();
        let mut left = want.clone();
        let mut entered: HashSet<*const ()> = HashSet::new();
        let mut stack = vec![Item::Sig(self)];
        while let Some(item) = stack.pop()
            && !left.is_empty()
        {
            let at = stack.len();
            match item {
                Item::Sig(s) => {
                    // `self` may still change, so its facts are not kept; it is entered.
                    if !std::ptr::eq(s, self) {
                        let classes = &s.facts().classes;
                        let any = match classes.len() < left.len() {
                            true => classes.iter().any(|v| left.contains(v)),
                            false => left.iter().any(|v| classes.contains(v)),
                        };
                        if !any {
                            continue;
                        }
                    }
                    let tys = s
                        .arrows
                        .iter()
                        .flat_map(|a| a.params.iter().chain([&a.result]));
                    let needs = s.needs.iter().flat_map(Need::tys);
                    stack.extend(tys.chain(needs).map(Item::Ty));
                }
                Item::Row(r) => {
                    if entered.insert(r.addr()) {
                        stack.extend(r.iter().map(Item::Ty));
                    }
                }
                Item::Shape(s) => {
                    if entered.insert(s.as_ptr().cast()) {
                        stack.extend(s.items.iter().chain(s.fields.values()).map(Item::Ty));
                    }
                }
                Item::Ty(t) => {
                    out.extend(t.vars.iter().filter(|v| left.remove(*v)).cloned());
                    stack.extend(t.tuples.iter().map(Item::Row));
                    stack.extend(t.payloads.values().flatten().flatten().map(Item::Shape));
                    stack.extend(t.fns.iter().map(|s| Item::Sig(s)));
                }
            }
            stack[at..].reverse();
        }
        out
    }

    /// One arrow over `params` and `result`, with no bounded variable.
    pub fn one(params: Vec<SParam>, tys: Vec<Ty>, result: Ty) -> Sig {
        Sig {
            params,
            arrows: vec![Arrow {
                params: tys,
                result,
            }],
            bounds: BTreeMap::new(),
            data: false,
            word: None,
            needs: Vec::new(),
            own: BTreeSet::new(),
            held: BTreeSet::new(),
            named: 0,
            facts: Default::default(),
        }
    }

    /// It with its variables replaced by `binds` at every depth; a bounded variable replaced
    /// by another variable keeps its bound under the new name.
    pub fn replace(&self, binds: &Binds) -> Sig {
        self.replace_in(binds, Mode::Replace)
    }

    /// It with the variables `names` gives other names, as [`Ty::renamed`] does.
    pub fn renamed(&self, names: &Binds) -> Sig {
        self.replace_in(names, Mode::Rename)
    }

    /// It with its variables replaced by `binds` in its arrows and needs, outside the functions
    /// they hold ([`Ty::replace_outside`]).
    pub fn replace_outside(&self, binds: &Binds) -> Sig {
        self.replace_in(binds, Mode::Outside)
    }

    /// [`Sig::replace`], or as `mode` says: renamed, its own and held variables take their new
    /// names.
    fn replace_in(&self, binds: &Binds, mode: Mode) -> Sig {
        Replacer::new(binds, mode).sig(self)
    }

    /// Its arrows with each bounded variable fixed to each carrier of its bound: the product
    /// of the bounds, as long as that product is.
    pub fn expand(&self) -> Vec<Arrow> {
        let mut out = self.arrows.clone();
        for (v, m) in &self.bounds {
            out = out
                .iter()
                .flat_map(|a| {
                    Carrier::of_mask(*m).map(move |c| {
                        let b: Binds = [(v.clone(), Ty::carrier(c))].into();
                        Arrow {
                            params: a.params.iter().map(|p| p.replace(&b)).collect(),
                            result: a.result.replace(&b),
                        }
                    })
                })
                .collect();
        }
        out
    }

    /// For each parameter, whether every value it takes on every arrow is an `int`: its type
    /// on each arrow is `int` or a refinement of it, and each type variable it holds ranges
    /// over `int` alone. A parameter of a variable bounded by `int | f64 | rat`, of `f64` or of
    /// `rat` is not, and neither is one that may hold an atom, a tuple, a function or the
    /// unknown. Rung 2 reads `+`, `-`, `*`, `div`, `mod`, `-x` and the comparisons as integer
    /// arithmetic, so its callers pass it only these parameters (RUNG2-carrier). Without
    /// [`Sig::expand`]'s product of the bounds: O(arrows × parameters), each type's scalar set
    /// tested once.
    pub fn int_params(&self) -> Vec<bool> {
        let int = KType::int();
        let only_int = Carrier::Int.bit();
        let is_int = |p: &Ty| {
            !p.dynamic
                && p.fns.is_empty()
                && p.tuples.is_empty()
                && (p.vars.iter()).all(|v| self.bounds.get(v) == Some(&only_int))
                && p.set.subtype(&int)
        };
        (0..self.params.len())
            .map(|i| {
                !self.arrows.is_empty()
                    && (self.arrows.iter()).all(|a| a.params.get(i).is_some_and(is_int))
            })
            .collect()
    }

    /// Whether it has the same parameter names and kinds as `other`.
    pub fn same_kinds(&self, other: &Sig) -> bool {
        self.params.len() == other.params.len()
            && self
                .params
                .iter()
                .zip(&other.params)
                .all(|(a, b)| a.positional == b.positional && a.name == b.name)
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut text = String::new();
        self.write(&mut text, &mut Scope::default());
        #[cfg(feature = "printed-types")]
        printed::record(self, &text);
        f.write_str(&text)
    }
}

/// The type variables the signatures around a place being printed bind: each by its name in
/// the type, with the name it is printed with, or none when it is printed `_`. A variable no
/// signature around it bounds by carriers is printed `_`, the type of every value, since type
/// syntax writes a type variable only with its bound (DESIGN.md L1.26, sec:diagnostics).
#[derive(Default)]
struct Scope {
    /// Each variable's printed names, innermost signature last.
    names: HashMap<Arc<str>, Vec<Option<Arc<str>>>>,
    /// The printed names in scope, so a signature inside another that bounds a name already
    /// printed takes a fresh one: a bounds clause inside another's may not bound its name again.
    printed: HashSet<Arc<str>>,
    /// The index in `T`, `U`, … of the next fresh name to try. It only grows, so each name is
    /// tried once however many signatures take a fresh one.
    fresh: usize,
}

impl Scope {
    /// How the variable `v` is printed here: its printed name, or `None` for `_`.
    fn name(&self, v: &Arc<str>) -> Option<&Arc<str>> {
        self.names.get(v)?.last()?.as_ref()
    }

    /// Opens the variables `sig` binds, giving each bounded one a printed name, and returns
    /// them with their masks, in the order of `sig.bounds`. A name not printed around the
    /// signature is kept; otherwise the next of `T`, `U`, … not yet tried that is neither
    /// printed around it nor a name of its own nor one the program binds ([`fresh_name`]).
    fn open(&mut self, sig: &Sig) -> Vec<(Arc<str>, u8)> {
        let mut out = Vec::new();
        for (v, &m) in &sig.bounds {
            if m & OTHER != 0 {
                self.names.entry(v.clone()).or_default().push(None);
                continue;
            }
            let name = if self.printed.contains(v) {
                fresh_name(Names::Variables, &mut self.fresh, |name| {
                    self.printed.contains(name) || sig.bounds.contains_key(name)
                })
            } else {
                v.clone()
            };
            self.printed.insert(name.clone());
            self.names
                .entry(v.clone())
                .or_default()
                .push(Some(name.clone()));
            out.push((name, m));
        }
        for v in sig.own.iter().filter(|v| !sig.bounds.contains_key(*v)) {
            self.names.entry(v.clone()).or_default().push(None);
        }
        out
    }

    /// Closes the variables `sig` binds, which [`Scope::open`] opened.
    fn close(&mut self, sig: &Sig) {
        let own = sig.own.iter().filter(|v| !sig.bounds.contains_key(*v));
        for v in sig.bounds.keys().chain(own) {
            let names = self.names.get_mut(v).expect("opened");
            if let Some(Some(name)) = names.pop() {
                self.printed.remove(&name);
            }
        }
    }
}

/// Writes `sep` to `out` before every item but the first, which `first` tells.
fn separate(out: &mut String, first: &mut bool, sep: &str) {
    if !*first {
        out.push_str(sep);
    }
    *first = false;
}

impl Ty {
    /// Writes its text, in type syntax, to `out`. Each part is written in place, not built as a
    /// string and copied into the whole: copying cost the depth of each part, so O(n^2) for a
    /// function type n deep. A variable `scope` does not name is printed `_`, once.
    fn write(&self, out: &mut String, scope: &mut Scope) {
        write_parts(Print::Ty(self, PrintAt::Any), out, scope);
    }

    /// Its text, in type syntax, as one operand of a union: a function in it is parenthesized,
    /// as in `((int) -> int) | String`, since `->` binds looser than `|`.
    pub fn text_in_union(&self) -> String {
        let mut out = String::new();
        write_parts(
            Print::Ty(self, PrintAt::Union),
            &mut out,
            &mut Scope::default(),
        );
        out
    }

    /// Puts its kernel set in `kernel`, to be written at offset `written` of the text, and pushes
    /// the parts that follow to `parts`, in order; with `found`, without its atom `#notFound`, as
    /// the value type of a morphism type is written ([`Sig::morphism`]). It stands at `at`, which
    /// decides its parentheses; of two members or more, each stands as an operand of `|`.
    fn parts<'a>(
        &'a self,
        written: usize,
        kernel: &mut Kernel,
        parts: &mut Vec<Print<'a>>,
        found: bool,
        at: PrintAt,
    ) {
        let mut first = true;
        // An atom whose payloads are known prints each payload's type, `#ioError(op: String,
        // path: String, why: String)` (L29-print); the kernel set holds it with any payload.
        let shaped: Vec<(&Arc<str>, &Vec<Shape>)> = self
            .payloads
            .iter()
            .filter_map(|(n, ss)| Some((n, ss.as_ref()?)))
            .filter(|(n, _)| holds_payload(&self.set, n))
            .collect();
        let rest = (!shaped.is_empty()).then(|| {
            let listed = shaped
                .iter()
                .map(|(n, _)| KType::atom_with(n, &KType::top()));
            &self.set - &KType::union_all(listed)
        });
        let set = rest.as_ref().unwrap_or(&self.set);
        let kept = found.then(|| set - &KType::atom("notFound"));
        let set = kept.as_ref().unwrap_or(set);
        let members = usize::from(!set.is_empty())
            + shaped.iter().map(|(_, ss)| ss.len()).sum::<usize>()
            + self.tuples.len()
            + self.fns.len()
            + usize::from(!self.vars.is_empty() || self.dynamic);
        let at = match members {
            0 | 1 => at,
            _ => PrintAt::Union,
        };
        if !set.is_empty() {
            first = false;
            // Written once the rest is, with the other kernel sets of the text ([`write_parts`]).
            kernel.at.push(written);
            kernel.sets.push((
                set.clone(),
                match at {
                    PrintAt::Any | PrintAt::Listed | PrintAt::Result => TextPlace::Any,
                    PrintAt::Key => TextPlace::Key,
                    PrintAt::Bound => TextPlace::Bound,
                    PrintAt::Union => TextPlace::Union,
                },
            ));
        }
        for (n, ss) in shaped {
            for s in ss {
                between(parts, &mut first, " | ");
                s.parts(n, parts);
            }
        }
        for cs in &self.tuples {
            between(parts, &mut first, " | ");
            // A tuple alone as an arrow's key is parenthesized, `((int, int)) ->? V`, since
            // `(int, int) ->? V` has two parameters; `(int,) ->? V` has one.
            let wrap = at == PrintAt::Key && cs.len() != 1;
            parts.push(Print::Text(if wrap { "((" } else { "(" }));
            let mut one = true;
            for (i, c) in cs.iter().enumerate() {
                between(parts, &mut one, ", ");
                // The one component of `(T,)` is followed by a comma too.
                parts.push(Print::Ty(
                    c,
                    PrintAt::item(i + 1 < cs.len() || cs.len() == 1),
                ));
            }
            parts.push(Print::Text(match (cs.len() == 1, wrap) {
                (true, _) => ",)",
                (false, true) => "))",
                (false, false) => ")",
            }));
        }
        for s in &self.fns {
            between(parts, &mut first, " | ");
            parts.push(Print::Sig(s, at));
        }
        parts.push(Print::Vars(self, first));
    }

    /// Writes the end of its text to `out`: the variables `scope` names, then `_` for the
    /// others and the unknown, or `Never` if `first` says nothing is written yet and nothing is
    /// to be.
    fn write_vars(&self, mut first: bool, out: &mut String, scope: &Scope) {
        let mut free = false;
        for v in &self.vars {
            match scope.name(v) {
                Some(name) => {
                    separate(out, &mut first, " | ");
                    out.push_str(name);
                }
                None => free = true,
            }
        }
        if self.dynamic || free {
            separate(out, &mut first, " | ");
            out.push('_');
        }
        if first {
            out.push_str("Never");
        }
    }
}

/// A part of the text of a type still to be written, on the stack [`write_parts`] keeps.
enum Print<'a> {
    Text(&'a str),
    Ty(&'a Ty, PrintAt),
    Sig(&'a Sig, PrintAt),
    /// The value type of a morphism type, which stands as a result: a type without its atom
    /// `#notFound`.
    Found(&'a Ty),
    /// A signature written as a family ([`Sig::family_parts`]), standing as a payload.
    Family(&'a Sig, PrintAt),
    /// The end of a type's text ([`Ty::write_vars`]), and whether nothing of it is written yet.
    Vars(&'a Ty, bool),
    /// The bounds clause of a signature, which closes the variables it opened.
    Bounds(&'a Sig, Vec<(Arc<str>, u8)>),
}

/// Where the text of a type stands, which decides the parentheses it needs to read back as one
/// type (DESIGN.md sec:grammar, `Type`, `Arrow`, `TypeUnion`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum PrintAt {
    /// Where a whole `Type` stands and no comma follows: the last component of a tuple of two
    /// or more, the last parameter, the last payload, the top.
    Any,
    /// Where a whole `Type` stands followed by a comma: a component of a tuple other than the
    /// last, and the one component of `(T,)`, a parameter or a payload other than the last. A
    /// function with a bounds clause is parenthesized, `(((T) -> T for T in int), int)`, since
    /// in `((T) -> T for T in int, int)` only the token after the comma tells that it does not
    /// begin another bound, `U in f64`.
    Listed,
    /// An arrow's result, an `Arrow`: a function with a bounds clause is parenthesized.
    Result,
    /// The key of `K -> V` or `K ->? V`, a `TypeUnion`: a function is parenthesized, and so is a
    /// tuple of other than one component, which would read as the parameters.
    Key,
    /// A bound of `L .. U -> V`, a `TypeUnion`: a function is parenthesized.
    Bound,
    /// An operand of `|`: a function is parenthesized.
    Union,
}

impl PrintAt {
    /// Where an item of a comma-separated list stands: [`PrintAt::Listed`] if a comma follows
    /// it, [`PrintAt::Any`] if the list's closing bracket does.
    fn item(comma: bool) -> PrintAt {
        match comma {
            true => PrintAt::Listed,
            false => PrintAt::Any,
        }
    }
}

/// A signature written as a morphism type ([`Sig::morphism`]).
enum Morphism<'a> {
    /// `K ->? V`: the key type, and the result, `V | #notFound`.
    Partial { key: &'a Ty, value: &'a Ty },
    /// `L .. U -> V`: the guarantee, the permission and the value type.
    Bounded {
        lower: &'a Ty,
        upper: &'a Ty,
        value: &'a Ty,
    },
}

impl<'a> Morphism<'a> {
    /// Pushes the parts of its text to `parts`, in order. The key stands at [`PrintAt::Key`],
    /// so that `((int, int)) ->? V` is not read as two parameters.
    fn parts(&self, parts: &mut Vec<Print<'a>>) {
        match *self {
            Morphism::Partial { key, value } => {
                parts.extend([
                    Print::Ty(key, PrintAt::Key),
                    Print::Text(" ->? "),
                    Print::Found(value),
                ]);
            }
            Morphism::Bounded {
                lower,
                upper,
                value,
            } => {
                parts.extend([
                    Print::Ty(lower, PrintAt::Bound),
                    Print::Text(" .. "),
                    Print::Ty(upper, PrintAt::Bound),
                ]);
                parts.extend([Print::Text(" -> "), Print::Ty(value, PrintAt::Result)]);
            }
        }
    }
}

/// Writes `start` to `out`. A type nests as deep as the program, so the writing keeps its own
/// stack: each part expands to the parts it is made of, which are put on the stack so that they
/// pop in order. The time is that of the text; a signature opens its variables when it is
/// reached and closes them after its arrows, so `scope` is as a recursive walk would have it.
///
/// The kernel sets in the text are written last, all together by name
/// ([`KType::surfaces_by_name`]), each where it stands: a part used more than once among them
/// gets a definition `type Tk = …;`, written before the whole text, so the text stays linear in
/// the sets' graph.
fn write_parts<'a>(start: Print<'a>, out: &mut String, scope: &mut Scope) {
    let base = out.len();
    let mut kernel = Kernel::default();
    let mut stack = vec![start];
    while let Some(part) = stack.pop() {
        let from = stack.len();
        match part {
            Print::Text(text) => out.push_str(text),
            Print::Ty(t, at) => t.parts(out.len(), &mut kernel, &mut stack, false, at),
            Print::Found(t) => t.parts(out.len(), &mut kernel, &mut stack, true, PrintAt::Result),
            Print::Sig(s, at) => s.parts(scope, &mut stack, at),
            Print::Family(s, at) => s.family_parts(scope, &mut stack, at),
            Print::Vars(t, first) => t.write_vars(first, out, scope),
            Print::Bounds(s, bounds) => {
                for (i, (v, m)) in bounds.iter().enumerate() {
                    out.push_str(if i == 0 { " for " } else { ", " });
                    out.push_str(v);
                    out.push_str(" in ");
                    out.push_str(&mask_text(*m));
                }
                scope.close(s);
            }
        }
        stack[from..].reverse();
    }
    if kernel.sets.is_empty() {
        return;
    }
    let texts = KType::surfaces_by_name(&kernel.sets);
    let rest = out.split_off(base);
    for (name, body) in &texts.defs {
        out.push_str("type ");
        out.push_str(name);
        out.push_str(" = ");
        out.push_str(body);
        out.push_str("; ");
    }
    let mut from = 0;
    for (at, text) in kernel.at.iter().zip(&texts.roots) {
        let at = at - base;
        out.push_str(&rest[from..at]);
        out.push_str(text);
        from = at;
    }
    out.push_str(&rest[from..]);
}

/// The kernel sets of a text still to be written ([`write_parts`]): where each stands in the
/// text, and the set with its place.
#[derive(Default)]
struct Kernel {
    at: Vec<usize>,
    sets: Vec<(KType, TextPlace)>,
}

/// Pushes `sep` to `parts` before every item but the first, which `first` tells.
fn between<'a>(parts: &mut Vec<Print<'a>>, first: &mut bool, sep: &'a str) {
    if !*first {
        parts.push(Print::Text(sep));
    }
    *first = false;
}

impl fmt::Display for Sig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut text = String::new();
        self.write(&mut text, &mut Scope::default());
        #[cfg(feature = "printed-types")]
        printed::record(&Ty::func(Arc::new(self.clone())), &text);
        f.write_str(&text)
    }
}

impl Sig {
    /// Writes its text, in type syntax, to `out`: its variables bounded by carriers by name, in
    /// a bounds clause after the arrows, and the others `_`.
    fn write(&self, out: &mut String, scope: &mut Scope) {
        write_parts(Print::Sig(self, PrintAt::Any), out, scope);
    }

    /// Opens its variables in `scope` and pushes the parts of its text to `parts`, in order. It
    /// stands at `at`: a text with a bounds clause is parenthesized anywhere but where a whole
    /// type stands with no comma after it, and an arrow also as a key, a bound or an operand of
    /// `|`; an intersection of arrows, each parenthesized, binds tighter than `|` and needs
    /// nothing more.
    fn parts<'a>(&'a self, scope: &mut Scope, parts: &mut Vec<Print<'a>>, at: PrintAt) {
        let bounds = scope.open(self);
        let morphism = self.morphism();
        let several = morphism.is_none() && self.arrows.len() != 1;
        let wrap = match at {
            PrintAt::Any => false,
            PrintAt::Listed | PrintAt::Result => !bounds.is_empty(),
            PrintAt::Key | PrintAt::Bound | PrintAt::Union => !bounds.is_empty() || !several,
        };
        if wrap {
            parts.push(Print::Text("("));
        }
        if let Some(m) = morphism {
            m.parts(parts);
        } else {
            let mut first = true;
            for a in &self.arrows {
                between(parts, &mut first, " & ");
                parts.push(Print::Text(if several { "((" } else { "(" }));
                let n = self.params.len().min(a.params.len());
                let mut one = true;
                for (i, (p, t)) in self.params.iter().zip(&a.params).enumerate() {
                    between(parts, &mut one, ", ");
                    if !p.positional {
                        parts.push(Print::Text(&p.name));
                        parts.push(Print::Text(": "));
                    }
                    parts.push(Print::Ty(t, PrintAt::item(i + 1 < n)));
                }
                parts.push(Print::Text(") -> "));
                parts.push(Print::Ty(&a.result, PrintAt::Result));
                if several {
                    parts.push(Print::Text(")"));
                }
            }
        }
        parts.push(Print::Bounds(self, bounds));
        if wrap {
            parts.push(Print::Text(")"));
        }
    }

    /// The morphism type it is written as, if it is one: a function of one unnamed positional
    /// parameter whose one arrow may answer `#notFound` is `K ->? V`, and one whose arrows are
    /// `(L) -> V` and `(U) -> V | #notFound`, with `L` within `U` and not equal to it, is
    /// `L .. U -> V` (DESIGN.md sec:type_language: a message prints a morphism type in that
    /// form when its bounds differ). Each reads back to the arrows the checker denotes it by.
    fn morphism(&self) -> Option<Morphism<'_>> {
        let [p] = &self.params[..] else {
            return None;
        };
        if !p.positional || !p.name.is_empty() {
            return None;
        }
        let miss = KType::atom("notFound");
        match &self.arrows[..] {
            // A result of `#notFound` alone is written as it is, `(K) -> #notFound`.
            [a] if (&miss - &a.result.set).is_empty() && a.result != Ty::set(miss.clone()) => {
                Some(Morphism::Partial {
                    key: &a.params[0],
                    value: &a.result,
                })
            }
            [a, b] => {
                let (lower, upper) = (&a.params[0], &b.params[0]);
                let set_only = |t: &Ty| {
                    t.tuples.is_empty() && t.fns.is_empty() && t.vars.is_empty() && !t.dynamic
                };
                (set_only(lower)
                    && set_only(upper)
                    && *lower != Ty::empty()
                    && lower != upper
                    && lower.union(upper) == *upper
                    && b.result == a.result.union(&Ty::set(miss)))
                .then_some(Morphism::Bounded {
                    lower,
                    upper,
                    value: &a.result,
                })
            }
            _ => None,
        }
    }

    /// Whether it is a family that maps each key of one key type to itself, its lookup that
    /// key type or `#notFound`, as [`errs_of`] builds, with no tuple or function in that type,
    /// so that [`Sig::family_parts`] can write it bare.
    fn is_family(&self) -> bool {
        matches!((&self.params[..], &self.arrows[..]), ([p], [a])
            if self.data && p.positional && a.params[0].tuples.is_empty() && a.params[0].fns.is_empty()
                && a.result == a.params[0].union(&Ty::set(KType::atom("notFound"))))
    }

    /// Opens its variables in `scope` and pushes the parts of its text as a family, a partial
    /// map `K ->? K` (DESIGN.md sec:values_morphisms), to `parts`, in order: its key type, bare,
    /// as [`Sig::is_family`] leaves none that could be read as parameters, twice, since `->?`
    /// adds the `#notFound` of its lookup (sec:type_language). It stands as a payload at `at`:
    /// with a bounds clause and a comma after it, it is parenthesized.
    fn family_parts<'a>(&'a self, scope: &mut Scope, parts: &mut Vec<Print<'a>>, at: PrintAt) {
        let bounds = scope.open(self);
        let wrap = at == PrintAt::Listed && !bounds.is_empty();
        if wrap {
            parts.push(Print::Text("("));
        }
        let key = &self.arrows[0].params[0];
        parts.push(Print::Ty(key, PrintAt::Key));
        parts.push(Print::Text(" ->? "));
        parts.push(Print::Ty(key, PrintAt::Result));
        parts.push(Print::Bounds(self, bounds));
        if wrap {
            parts.push(Print::Text(")"));
        }
    }
}

/// The class a type variable names: `$k` is class `k`.
pub fn class_id(v: &str) -> Option<usize> {
    v.strip_prefix('$')?.parse().ok()
}

/// The `n`th name of a signature's own type variables: `T`, `U`, `V`, `W`, `T5`, ….
pub fn var_name(n: usize) -> Arc<str> {
    Names::Variables.nth(n)
}

/// The types printed on a thread while recording is on, each with the text printed (feature
/// `printed-types`, OSP-diag): a test parses each text back and compares.
#[cfg(feature = "printed-types")]
pub mod printed {
    use std::cell::RefCell;

    use super::Ty;

    thread_local! {
        static SEEN: RefCell<Option<Vec<(Ty, String)>>> = const { RefCell::new(None) };
    }

    /// Starts recording on this thread, dropping what was recorded.
    pub fn start() {
        SEEN.set(Some(Vec::new()));
    }

    /// What was recorded since `start`, in printed order; recording stops.
    pub fn take() -> Vec<(Ty, String)> {
        SEEN.take().unwrap_or_default()
    }

    /// Records that `t` was printed as `text`, if recording is on. A text of a message, which names
    /// definitions the message writes apart, is recorded with them before it, as it reads alone.
    pub fn record(t: &Ty, text: &str) {
        SEEN.with_borrow_mut(|seen| {
            if let Some(seen) = seen {
                seen.push((t.clone(), zed_kernel::types::defs::plain(text)));
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// How [`every_arrow_fits`] decides in a differential test.
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub(super) enum Reference {
        /// By the index.
        None,
        /// By every pair of arrows, as before the index, with no arrows covering together.
        Pairs,
        /// By every pair, then, at each parameter, by every set of arrows ([`together`]).
        Subsets,
    }

    /// The most arrows whose every subset [`together`] tries.
    const SUBSETS: usize = 10;

    /// The search with no index (COMPLEXITY.md F82): each arrow of `q` on an arrow of `s`
    /// equal to it, then on every arrow of `s` in order, then, under [`Reference::Subsets`],
    /// on every set of arrows of `s` ([`together`]).
    pub(super) async fn reference<'m>(
        s: &Sig,
        sas: &[Arrow],
        qas: &[Arrow],
        c: &'m Comparing<'m, '_>,
    ) -> bool {
        let wide = REFERENCE.get() == Reference::Subsets;
        let mut equal: HashMap<&Arrow, &Arrow> = HashMap::with_capacity(sas.len());
        for sa in sas {
            equal.entry(sa).or_insert(sa);
        }
        'qas: for qa in qas {
            if let Some(sa) = equal.get(qa)
                && arrow_fits(s, sa, qa, c).await
            {
                continue;
            }
            for sa in sas {
                if arrow_fits(s, sa, qa, c).await {
                    continue 'qas;
                }
            }
            if wide
                && (together(s, sas, qa, c).await
                    || met(s, sas, &(0..sas.len()).collect::<Vec<_>>(), qa, c).await)
            {
                continue;
            }
            return false;
        }
        true
    }

    /// [`arrow_fits`] with the parameter `skip` left out.
    async fn fits_but<'m>(
        s: &Sig,
        sa: &Arrow,
        qa: &Arrow,
        skip: usize,
        c: &'m Comparing<'m, '_>,
    ) -> bool {
        let mut b = Binds::new();
        for (j, (x, y)) in qa.params.iter().zip(&sa.params).enumerate() {
            if j != skip && !c.sub_in(x, y, &mut b).await {
                return false;
            }
        }
        let held = bounds_hold(s, sa, &b, &c.cx.borrow());
        held && result_within(sa, qa, &b, c).await
    }

    /// Whether, at some parameter, a set of arrows of `sas` covers `qa`: each arrow of the set
    /// has a parameter type there that binds nothing ([`binds_nothing`]), takes `qa`'s other parameters and returns within its
    /// result, and the union of their parameter types there holds `qa`'s. Every nonempty set is
    /// tried when there are at most [`SUBSETS`] arrows; with more, the set of every arrow that
    /// qualifies, which holds what any of its subsets holds.
    async fn together<'m>(s: &Sig, sas: &[Arrow], qa: &Arrow, c: &'m Comparing<'m, '_>) -> bool {
        for j in 0..qa.params.len().min(s.params.len()) {
            let mut ok = Vec::with_capacity(sas.len());
            for sa in sas {
                let p = &sa.params[j];
                let free = binds_nothing(p, &c.cx.borrow());
                ok.push(free && fits_but(s, sa, qa, j, c).await);
            }
            let holds = async |set: &dyn Fn(usize) -> bool| {
                let u = Ty::union_all(
                    (0..sas.len())
                        .filter(|&i| set(i))
                        .map(|i| &sas[i].params[j]),
                );
                c.sub_in(&qa.params[j], &u, &mut Binds::new()).await
            };
            if sas.len() <= SUBSETS {
                for m in 1u32..1 << sas.len() {
                    let has = |i: usize| m & (1 << i) != 0;
                    if (0..sas.len()).all(|i| !has(i) || ok[i]) && holds(&has).await {
                        return true;
                    }
                }
            } else if ok.contains(&true) && holds(&|i| ok[i]).await {
                return true;
            }
        }
        false
    }

    /// splitmix64, so the cases are the same on every run.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            (z ^ (z >> 31)) % n
        }
    }

    /// The bound of the variable `B` of the signatures below: `int | f64`.
    const B_MASK: u8 = 0b11;

    /// A random member: an atom of eight, a carrier, a literal, an atom with a payload, or,
    /// when `open`, a type variable, the bounded variable `B`, the unknown or a function.
    fn member(rng: &mut Rng, open: bool) -> Ty {
        match rng.below(if open { 14 } else { 10 }) {
            0..=4 => Ty::set(KType::atom(&format!("a{}", rng.below(8)))),
            5 => Ty::carrier(Carrier::Int),
            6 => Ty::carrier(Carrier::Str),
            7 => Ty::carrier(Carrier::Bool),
            8 => Ty::lit(&Value::Int(rng.below(3) as i64)),
            9 => Ty::set(KType::atom_with("p", &KType::tuple(vec![KType::int()]))),
            10 => Ty::var("T".into()),
            11 => Ty::var("B".into()),
            12 => Ty::dynamic(),
            _ => {
                let a = Arrow {
                    params: vec![Ty::set(KType::atom("a0"))],
                    result: Ty::set(KType::atom(&format!("a{}", rng.below(2)))),
                };
                Ty::func(Arc::new(sig(vec![a], 1, false)))
            }
        }
    }

    /// A union of one to three random members.
    fn union(rng: &mut Rng, open: bool) -> Ty {
        let k = 1 + rng.below(3);
        (0..k).fold(Ty::empty(), |t, _| t.union(&member(rng, open)))
    }

    /// A signature of `width` named parameters with `arrows`, its own variables `T` and `B`,
    /// `B` bounded by `int | f64` when `bounded`.
    fn sig(arrows: Vec<Arrow>, width: usize, bounded: bool) -> Sig {
        let mut s = Sig {
            params: (0..width)
                .map(|j| SParam {
                    name: format!("x{j}").into(),
                    positional: false,
                    default: None,
                })
                .collect(),
            arrows,
            bounds: BTreeMap::new(),
            data: false,
            word: None,
            needs: Vec::new(),
            own: ["T".into(), "B".into()].into_iter().collect(),
            held: BTreeSet::new(),
            named: 0,
            facts: Facts::default(),
        };
        if bounded {
            s.bounds.insert("B".into(), B_MASK);
        }
        s.note_held();
        s
    }

    /// An arrow of `q` near `sa`: each parameter type narrowed to some of its members or
    /// widened by one, the result widened or narrowed alike, so that about half fit.
    fn near(rng: &mut Rng, sa: &Arrow) -> Arrow {
        let mut vary = |t: &Ty| match rng.below(3) {
            0 => t.clone(),
            1 => t.union(&member(rng, false)),
            _ => {
                let ps = t.pieces();
                ps[rng.below(ps.len() as u64) as usize].ty()
            }
        };
        Arrow {
            params: sa.params.iter().map(&mut vary).collect(),
            result: vary(&sa.result),
        }
    }

    /// An arrow of `q` that two arrows of `s` may cover only together: at one parameter the
    /// union of theirs, at the others a piece of `a`'s, and the union of their results.
    fn joined(rng: &mut Rng, a: &Arrow, b: &Arrow) -> Arrow {
        let at = rng.below(a.params.len() as u64) as usize;
        let params = (0..a.params.len())
            .map(|j| {
                let ps = a.params[j].pieces();
                if j == at || ps.is_empty() {
                    a.params[j].union(&b.params[j])
                } else {
                    ps[rng.below(ps.len() as u64) as usize].ty()
                }
            })
            .collect();
        Arrow {
            params,
            result: a.result.union(&b.result),
        }
    }

    /// One arrow of `q` for the arrows `sas` of `s`: random, near an arrow of `s`, or joined
    /// from two.
    fn arrow_of_q(rng: &mut Rng, sas: &[Arrow], width: usize, wider: bool, open: bool) -> Arrow {
        let pick = |rng: &mut Rng| &sas[rng.below(sas.len() as u64) as usize];
        match rng.below(6) {
            0 if wider => Arrow {
                params: (0..width).map(|_| wider_union(rng, open)).collect(),
                result: wider_union(rng, false),
            },
            0 => Arrow {
                params: (0..width).map(|_| union(rng, false)).collect(),
                result: union(rng, false),
            },
            1 | 2 => {
                let (a, b) = (pick(rng), pick(rng));
                joined(rng, a, b)
            }
            _ => {
                let sa = pick(rng);
                if wider {
                    wider_near(rng, sa)
                } else {
                    near(rng, sa)
                }
            }
        }
    }

    /// `fits_sig` by the index, by every pair and by every set of arrows, on one pair of
    /// signatures.
    fn three(s: &Sig, q: &Sig) -> (bool, bool, bool) {
        let new = fits_sig(s, q);
        REFERENCE.set(Reference::Pairs);
        let pairs = fits_sig(s, q);
        REFERENCE.set(Reference::Subsets);
        let subsets = fits_sig(s, q);
        REFERENCE.set(Reference::None);
        (new, pairs, subsets)
    }

    /// Counts of verdicts: fit, do not fit, and fit only by arrows together.
    #[derive(Default)]
    struct Counts {
        fit: usize,
        unfit: usize,
        together: usize,
    }

    impl Counts {
        /// Compares the index with every set of arrows on `q` in `s`, and counts the verdict.
        fn compare(&mut self, s: &Sig, q: &Sig, what: &str) {
            let (new, pairs, subsets) = three(s, q);
            assert_eq!(new, subsets, "{what}: {q} in {s}");
            assert!(subsets || !pairs, "{what}: a fit by one arrow is a fit");
            match (new, pairs) {
                (true, false) => self.together += 1,
                (true, true) => self.fit += 1,
                _ => self.unfit += 1,
            }
        }

        /// Both verdicts occur often, and a fit by arrows together, so the comparison is not of
        /// one answer.
        fn enough(&self) {
            let Counts {
                fit,
                unfit,
                together,
            } = self;
            assert!(
                *fit > 200 && *unfit > 200 && *together > 40,
                "{fit} fit, {unfit} do not, {together} fit only together"
            );
        }
    }

    #[test]
    fn the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows() {
        // Over random overloads, with unions of atoms and carriers and some open parameter
        // types, each arrow of `q` alone and `q` whole get the verdict of comparing with every
        // arrow of `s` and then with every set of arrows of `s` (every subset of at most
        // SUBSETS arrows), every arrow of `s` that fits an arrow of `q` is a candidate, and
        // every arrow that may take part in covering one together is a candidate for it.
        let mut rng = Rng(0x5eed);
        let mut counts = Counts::default();
        for case in 0..60 {
            let n = [1, 2, 5, 8, 20, 60, 300][case % 7];
            let width = 1 + rng.below(2) as usize;
            let open = case % 3 != 0;
            let sas: Vec<Arrow> = (0..n)
                .map(|_| {
                    let params = (0..width).map(|_| union(&mut rng, open)).collect();
                    let wide = open && rng.below(4) == 0;
                    Arrow {
                        params,
                        result: union(&mut rng, wide),
                    }
                })
                .collect();
            let qas: Vec<Arrow> = (0..n.min(60))
                .map(|_| arrow_of_q(&mut rng, &sas, width, false, false))
                .collect();
            let s = sig(sas.clone(), width, case % 2 == 0);
            for qa in &qas {
                let q = sig(vec![qa.clone()], width, false);
                counts.compare(&s, &q, &format!("case {case}"));
                same_in_every_order(&s, &q, case as u64, &format!("case {case}"));
            }
            let q = sig(qas.clone(), width, false);
            counts.compare(&s, &q, &format!("case {case}, the whole of q"));
            same_in_every_order(&s, &q, case as u64, &format!("case {case}"));
            index_keeps(&s, &qas, width, &format!("case {case}"));
        }
        counts.enough();
    }

    /// Every pair and every arrow, on the arrows as written: the index never leaves out an
    /// arrow of `s` that fits an arrow of `qas`, or one that may cover one together with
    /// others, whichever key list or result list it draws from.
    fn index_keeps(s: &Sig, qas: &[Arrow], width: usize, what: &str) {
        let index = ArrowIndex::new(&s.arrows, width);
        comparing!(&mut Cx::default(), |c| async {
            let c = &c;
            for qa in qas {
                let candidates = index.may_fit(qa);
                for (i, sa) in s.arrows.iter().enumerate() {
                    if arrow_fits(s, sa, qa, c).await {
                        assert!(
                            candidates.binary_search(&i).is_ok(),
                            "{what}: arrow {i} fits but is no candidate"
                        );
                    }
                }
                let covering = index.covering(qa, true);
                let meeting = index.covering(qa, false);
                for (i, sa) in s.arrows.iter().enumerate() {
                    // An arrow that misses a parameter takes part only where it meets it there,
                    // and one that takes a parameter of no value takes no value.
                    let part = part_of(s, sa, qa, c).await.map(|p| p.0);
                    let meets = |j: usize| sa.params[j].meets(&qa.params[j]);
                    if (part == Some(Part::Whole) && qa.params.iter().all(|t| !t.is_empty()))
                        || matches!(part, Some(Part::At(j, _)) if meets(j))
                    {
                        assert!(
                            meeting.binary_search(&i).is_ok(),
                            "{what}: arrow {i} takes part of an arrow of q but is no candidate: {part:?} {:?} {:?} {:?}",
                            sa.params.iter().map(|t| t.to_string()).collect::<Vec<_>>(),
                            qa.params.iter().map(|t| t.to_string()).collect::<Vec<_>>(),
                            (sa.result.to_string(), qa.result.to_string())
                        );
                    }
                }
                for j in 0..width {
                    for (i, sa) in s.arrows.iter().enumerate() {
                        let p = &sa.params[j];
                        let free = binds_nothing(p, &c.cx.borrow());
                        if free && p.meets(&qa.params[j]) && fits_but(s, sa, qa, j, c).await {
                            assert!(
                                covering.binary_search(&i).is_ok(),
                                "{what}: arrow {i} may cover at {j} but is no candidate"
                            );
                        }
                    }
                }
            }
        })
    }

    /// The verdict on `q` in `s` is the same with the arrows of `s` reversed, rotated by one
    /// and shuffled, and with the arrows of `q` reversed: the index and the cover try arrows
    /// in their order, and the verdict must not depend on it.
    fn same_in_every_order(s: &Sig, q: &Sig, seed: u64, what: &str) {
        let verdict = fits_sig(s, q);
        let mut rng = Rng(seed ^ 0x0bde_5eed);
        let n = s.arrows.len();
        let mut shuffled = s.arrows.clone();
        for i in (1..n).rev() {
            shuffled.swap(i, rng.below(i as u64 + 1) as usize);
        }
        let mut rotated = s.arrows.clone();
        rotated.rotate_left(1.min(n));
        let reversed: Vec<Arrow> = s.arrows.iter().rev().cloned().collect();
        for (how, arrows) in [
            ("reversed", reversed),
            ("rotated", rotated),
            ("shuffled", shuffled),
        ] {
            let mut p = s.clone();
            p.arrows = arrows;
            assert_eq!(fits_sig(&p, q), verdict, "{what}: s {how}: {q} in {s}");
        }
        let mut q_reversed = q.clone();
        q_reversed.arrows.reverse();
        assert_eq!(
            fits_sig(s, &q_reversed),
            verdict,
            "{what}: q reversed: {q} in {s}"
        );
    }

    /// A random member of the wider family: those of [`member`], and a cofinite set of atoms,
    /// every atom, an atom whose payload type is empty, a `bool` literal, every `rat`
    /// and `f64`, tuples of carriers and atoms, a kind-wide part, and, when `open`, a tuple
    /// holding the variable `T` or the bounded variable `B`.
    fn wider_member(rng: &mut Rng, open: bool) -> Ty {
        match rng.below(if open { 13 } else { 12 }) {
            0..=1 => member(rng, open),
            2 => Ty::set(&atoms() - &KType::atom(&format!("a{}", rng.below(8)))),
            3 => Ty::set(atoms()),
            4 => Ty::set(KType::atom_with("e", &KType::empty())),
            5 => Ty::lit(&Value::Bool(rng.below(2) == 0)),
            6 => Ty::carrier(Carrier::Rat),
            7 => Ty::carrier(Carrier::F64),
            8 => Ty::tuple(vec![
                Ty::carrier(Carrier::Int),
                Ty::set(KType::atom(&format!("a{}", rng.below(3)))),
            ]),
            9 => Ty::tuple(vec![
                Ty::carrier(Carrier::Int).union(&Ty::carrier(Carrier::Str)),
            ]),
            10 => Ty::set(KType::tuple(vec![KType::top(); 2])),
            11 => Ty::set(wide()),
            _ => Ty::tuple(vec![Ty::var(
                if rng.below(2) == 0 { "T" } else { "B" }.into(),
            )]),
        }
    }

    /// A union of one to three members of the wider family, sometimes with a member of the
    /// first family.
    fn wider_union(rng: &mut Rng, open: bool) -> Ty {
        let k = 1 + rng.below(3);
        (0..k).fold(Ty::empty(), |t, _| t.union(&wider_member(rng, open)))
    }

    /// [`near`] with the members of the wider family, a type of no piece kept as it is.
    fn wider_near(rng: &mut Rng, sa: &Arrow) -> Arrow {
        let mut vary = |t: &Ty| match (rng.below(3), t.pieces()) {
            (1, _) => t.union(&wider_member(rng, false)),
            (2, ps) if !ps.is_empty() => ps[rng.below(ps.len() as u64) as usize].ty(),
            _ => t.clone(),
        };
        Arrow {
            params: sa.params.iter().map(&mut vary).collect(),
            result: vary(&sa.result),
        }
    }

    /// [`sig`] with `B` bounded by `mask` when given.
    fn sig_mask(arrows: Vec<Arrow>, width: usize, mask: Option<u8>) -> Sig {
        let mut s = sig(arrows, width, false);
        if let Some(m) = mask {
            s.bounds.insert("B".into(), m);
            s.note_held();
        }
        s
    }

    #[test]
    fn the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows_on_wider_shapes() {
        // As above, on cofinite and empty-payload atoms, tuples, kind-wide parts and literals,
        // with `B` of each side bounded or not: `B` of `q` that a parameter holds is a rigid
        // variable, a bound with OTHER reads `B` of `s` unheld as the unknown.
        let masks = [None, Some(B_MASK), Some(0b1001), Some(OTHER | 0b1)];
        let mut rng = Rng(0x00dd_5eed);
        let mut counts = Counts::default();
        for case in 0..150 {
            let n = [1, 3, 6, 10, 30, 90][case % 6];
            let width = 1 + rng.below(2) as usize;
            let open = case % 3 != 0;
            let sas: Vec<Arrow> = (0..n)
                .map(|_| {
                    let params = (0..width).map(|_| wider_union(&mut rng, open)).collect();
                    let wide = open && rng.below(4) == 0;
                    Arrow {
                        params,
                        result: wider_union(&mut rng, wide),
                    }
                })
                .collect();
            let qas: Vec<Arrow> = (0..n.min(30))
                .map(|_| arrow_of_q(&mut rng, &sas, width, true, open))
                .collect();
            let s = sig_mask(sas, width, masks[rng.below(4) as usize]);
            let qm = masks[rng.below(4) as usize];
            for qa in &qas {
                let q = sig_mask(vec![qa.clone()], width, qm);
                counts.compare(&s, &q, &format!("case {case}"));
                same_in_every_order(&s, &q, case as u64, &format!("case {case}"));
            }
            index_keeps(&s, &qas, width, &format!("wider case {case}"));
            let q = sig_mask(qas, width, qm);
            counts.compare(&s, &q, &format!("case {case}, the whole of q"));
            same_in_every_order(&s, &q, case as u64, &format!("case {case}, the whole of q"));
        }
        counts.enough();
    }

    /// The values of the small types below, one for each class no type of them splits: `int`,
    /// `bool`, `String`, `f64` and the atoms `#v0` to `#v2`, a bit each.
    const VALUES: usize = 7;

    /// The type of the values of the mask `m`.
    fn of_values(m: u8) -> Ty {
        let carriers = [Carrier::Int, Carrier::Bool, Carrier::Str, Carrier::F64];
        (0..VALUES)
            .filter(|&b| m & (1 << b) != 0)
            .fold(Ty::empty(), |t, b| match carriers.get(b) {
                Some(&c) => t.union(&Ty::carrier(c)),
                None => t.union(&Ty::set(KType::atom(&format!("v{}", b - carriers.len())))),
            })
    }

    /// The bits of `int` and `f64`, the bound of `B` below.
    const B_VALUES: u8 = 0b1001;

    /// A place of a small arrow: the values of a mask, alone or with the variable `B` bounded by
    /// `int | f64`.
    #[derive(Clone, Copy)]
    enum Small {
        Values(u8),
        B(u8),
    }

    impl Small {
        fn ty(self) -> Ty {
            match self {
                Small::Values(m) => of_values(m),
                Small::B(m) => Ty::var("B".into()).union(&of_values(m)),
            }
        }

        /// The mask at `B` fixed to the carrier of the bit `c`.
        fn at(self, c: u8) -> u8 {
            match self {
                Small::Values(m) => m,
                Small::B(m) => m | c,
            }
        }
    }

    /// Whether arrows of the places `arrows` cover the arrow of masks `params -> result` as
    /// rule 6 of sec:type_resolution types a call, by the values: at each value of the
    /// parameters, some arrow takes it, and the intersection of the results of every arrow
    /// that takes it is within `result`. An arrow that holds `B` is each arrow it is at a
    /// carrier of its bound ([`Sig::expand`]).
    fn covers_by_values(arrows: &[(Vec<Small>, Small)], params: &[u8], result: u8) -> bool {
        let fixed: Vec<(Vec<u8>, u8)> = arrows
            .iter()
            .flat_map(|(ps, r)| {
                let held = ps.iter().chain([r]).any(|p| matches!(p, Small::B(_)));
                let cs: Vec<u8> = match held {
                    true => (0..VALUES)
                        .map(|b| 1 << b)
                        .filter(|c| B_VALUES & c != 0)
                        .collect(),
                    false => vec![0],
                };
                cs.into_iter()
                    .map(move |c| (ps.iter().map(|p| p.at(c)).collect(), r.at(c)))
            })
            .collect();
        // Every value of the parameters, one bit at each.
        let mut values: Vec<Vec<u8>> = vec![Vec::new()];
        for &m in params {
            values = values
                .into_iter()
                .flat_map(|v| {
                    (0..VALUES)
                        .filter(move |&b| m & (1 << b) != 0)
                        .map(move |b| {
                            let mut v = v.clone();
                            v.push(1 << b);
                            v
                        })
                })
                .collect();
        }
        values.iter().all(|v| {
            let mut met: Option<u8> = None;
            for (ps, r) in &fixed {
                if ps.iter().zip(v).all(|(p, x)| p & x != 0) {
                    met = Some(met.map_or(*r, |m| m & r));
                }
            }
            met.is_some_and(|m| m & !result == 0)
        })
    }

    /// A random mask of [`VALUES`], not empty.
    fn mask(rng: &mut Rng) -> u8 {
        loop {
            let m = rng.below(1 << VALUES) as u8;
            if m != 0 {
                break m;
            }
        }
    }

    /// `B` one time in eight, else the values of a random mask; when `narrow`, of the meet of
    /// two and one of the first three values, so that results outside a slot's are common.
    fn small(rng: &mut Rng, narrow: bool) -> Small {
        if rng.below(8) == 0 {
            return Small::B(0);
        }
        Small::Values(match narrow {
            true => mask(rng) & mask(rng) | 1 << rng.below(3),
            false => mask(rng),
        })
    }

    #[test]
    fn a_fit_of_small_types_is_a_cover_of_their_values() {
        // Over random overloads of one or two parameters whose types are unions of the values
        // of [`VALUES`], some arrows with `B`: every fit `fits_sig` gives holds at every value,
        // as rule 6 types a call there, whether by one arrow, by a union at one parameter or
        // by the intersection of results ([`covered`]). The checker refuses some covers
        // (cases (1) to (3) of [`covered`]), so a cover it does not take is counted, not
        // asserted, and the counts show each form of fit occurs.
        let mut rng = Rng(0x0005_eed5);
        let (mut fit, mut cover, mut refused, mut neither) = (0, 0, 0, 0);
        for case in 0..4000 {
            let width = 1 + case % 2;
            let n = 1 + rng.below(4) as usize;
            let mut arrows: Vec<(Vec<Small>, Small)> = Vec::new();
            for _ in 0..n {
                let ps = (0..width).map(|_| small(&mut rng, false)).collect();
                arrows.push((ps, small(&mut rng, true)));
            }
            let params: Vec<u8> = (0..width)
                .map(|_| (mask(&mut rng) & mask(&mut rng)).max(1))
                .collect();
            let result = mask(&mut rng) | 1 << rng.below(3);
            let sas = arrows
                .iter()
                .map(|(ps, r)| Arrow {
                    params: ps.iter().map(|p| p.ty()).collect(),
                    result: r.ty(),
                })
                .collect();
            let mut s = sig(sas, width, false);
            s.bounds
                .insert("B".into(), Carrier::Int.bit() | Carrier::F64.bit());
            s.note_held();
            let qa = Arrow {
                params: params.iter().map(|&m| of_values(m)).collect(),
                result: of_values(result),
            };
            let q = sig(vec![qa.clone()], width, false);
            let truth = covers_by_values(&arrows, &params, result);
            let pairs = {
                REFERENCE.set(Reference::Pairs);
                let v = fits_sig(&s, &q);
                REFERENCE.set(Reference::None);
                v
            };
            match (fits_sig(&s, &q), truth) {
                (true, false) => panic!("case {case}: {q} in {s} is no cover of the values"),
                (true, true) if pairs => fit += 1,
                (true, true) => cover += 1,
                (false, true) => refused += 1,
                (false, false) => neither += 1,
            }
        }
        assert!(
            fit > 200 && cover > 100 && neither > 200,
            "{fit} fit by one arrow, {cover} together, {refused} refused, {neither} no cover"
        );
    }

    #[test]
    fn a_fit_at_a_bounded_variable_is_a_cover_of_its_values() {
        // As above, with the slot generic: `U`, bounded by `int | f64`, stands at some of its
        // parameters and in its result, and the arrows hold `B`, alone or with other values,
        // at parameters and in results, so a result may hold the rigid `U` (by `B` bound to
        // it) beside values ([`meet_within`]). A fit holds at each carrier the caller may fix
        // `U` to, at every value, as rule 6 types a call there, and the verdict is the same in
        // every order of the arrows.
        let mut rng = Rng(0x0005_eed6);
        let (mut fit, mut refused, mut neither) = (0, 0, 0);
        let place = |rng: &mut Rng, narrow: bool| match small(rng, narrow) {
            Small::B(_) if narrow && rng.below(2) == 0 => Small::B(1 << rng.below(VALUES as u64)),
            p => p,
        };
        for case in 0..4000 {
            let width = 1 + case % 2;
            let n = 1 + rng.below(4) as usize;
            let mut arrows: Vec<(Vec<Small>, Small)> = Vec::new();
            for _ in 0..n {
                let ps = (0..width).map(|_| place(&mut rng, false)).collect();
                arrows.push((ps, place(&mut rng, true)));
            }
            // A slot's place: `U`, alone or with values, one time in three, else values.
            let slot = |rng: &mut Rng, m: u8| match rng.below(3) {
                0 => (true, m & mask(rng) & mask(rng)),
                _ => (false, m.max(1)),
            };
            let params: Vec<(bool, u8)> = (0..width)
                .map(|_| {
                    let m = mask(&mut rng) & mask(&mut rng);
                    slot(&mut rng, m)
                })
                .collect();
            let m = mask(&mut rng) | 1 << rng.below(3);
            let result = slot(&mut rng, m);
            let u = |(held, m): (bool, u8)| match held {
                true => Ty::var("U".into()).union(&of_values(m)),
                false => of_values(m),
            };
            let sas = arrows
                .iter()
                .map(|(ps, r)| Arrow {
                    params: ps.iter().map(|p| p.ty()).collect(),
                    result: r.ty(),
                })
                .collect();
            let mut s = sig(sas, width, false);
            s.bounds
                .insert("B".into(), Carrier::Int.bit() | Carrier::F64.bit());
            s.note_held();
            let qa = Arrow {
                params: params.iter().map(|&p| u(p)).collect(),
                result: u(result),
            };
            let mut q = sig(vec![qa], width, false);
            q.own.insert("U".into());
            q.bounds
                .insert("U".into(), Carrier::Int.bit() | Carrier::F64.bit());
            q.note_held();
            let at = |(held, m): (bool, u8), c: u8| if held { m | c } else { m };
            // `U` that no parameter holds is no carrier a caller fixes: it is read as its bound.
            let fixed: &[u8] = match params.iter().any(|&(held, _)| held) {
                true => &[1, 1 << 3],
                false => &[1 | 1 << 3],
            };
            let truth = fixed.iter().all(|&c| {
                let ps: Vec<u8> = params.iter().map(|&p| at(p, c)).collect();
                covers_by_values(&arrows, &ps, at(result, c))
            });
            match (fits_sig(&s, &q), truth) {
                (true, false) => panic!("case {case}: {q} in {s} is no cover of the values"),
                (true, true) => fit += 1,
                (false, true) => refused += 1,
                (false, false) => neither += 1,
            }
            same_in_every_order(&s, &q, case as u64, &format!("case {case}"));
        }
        assert!(
            fit > 200 && neither > 200,
            "{fit} fit, {refused} refused, {neither} no cover"
        );
    }

    /// The values of the types of [`Place`]: `int`, `bool`, `String`, `f64`, the atoms `#v0` and
    /// `#v1`, a function of `(x0: int) -> #v0` alone, one of `(x0: int) -> #v1` alone, and one
    /// of both (it returns no value), a bit each.
    const FN_VALUES: usize = 9;

    /// A place of an arrow over [`FN_VALUES`]: the values of a mask of the first six, the
    /// function types `(x0: int) -> #v0` and `(x0: int) -> #v1`, and the own unbounded variable
    /// `T` of the arrow's signature, which a comparison binds to the slot's type there.
    #[derive(Clone, Copy, Default)]
    struct Place {
        m: u8,
        f1: bool,
        f2: bool,
        t: bool,
    }

    impl Place {
        /// The function type returning `#v<i>`.
        fn f(i: usize) -> Ty {
            let a = Arrow {
                params: vec![Ty::carrier(Carrier::Int)],
                result: Ty::set(KType::atom(&format!("v{i}"))),
            };
            Ty::func(Arc::new(sig(vec![a], 1, false)))
        }

        fn ty(self) -> Ty {
            let carriers = [Carrier::Int, Carrier::Bool, Carrier::Str, Carrier::F64];
            let mut t = (0..6)
                .filter(|&b| self.m & (1 << b) != 0)
                .fold(Ty::empty(), |t, b| match carriers.get(b) {
                    Some(&c) => t.union(&Ty::carrier(c)),
                    None => t.union(&Ty::set(KType::atom(&format!("v{}", b - 4)))),
                });
            for (held, i) in [(self.f1, 0), (self.f2, 1)] {
                if held {
                    t = t.union(&Place::f(i));
                }
            }
            if self.t {
                t = t.union(&Ty::var("T".into()));
            }
            t
        }

        /// Its values but those of `T`.
        fn values(self) -> u16 {
            let mut v = u16::from(self.m);
            if self.f1 {
                v |= 1 << 6 | 1 << 8;
            }
            if self.f2 {
                v |= 1 << 7 | 1 << 8;
            }
            v
        }

        /// A random place of values, not empty: functions one time in `f` each.
        fn random(rng: &mut Rng, narrow: bool, f: u64) -> Place {
            let m = match narrow {
                true => (rng.below(64) & rng.below(64)) as u8,
                false => rng.below(64) as u8,
            };
            let mut p = Place {
                m,
                f1: rng.below(f) == 0,
                f2: rng.below(f) == 0,
                t: false,
            };
            if p.values() == 0 {
                p.m = 1 << rng.below(6);
            }
            p
        }
    }

    /// [`covers_by_values`] over [`FN_VALUES`]: at each value of the parameters, some arrow
    /// takes it, and the intersection of the results of every arrow that takes it is within
    /// `result`. `T`, alone at a parameter, takes every value there, and in the result stands
    /// for the value it took: what an arrow generic in `T` returns at it.
    fn covers_with_fns(arrows: &[(Vec<Place>, Place)], params: &[u16], result: u16) -> bool {
        let mut values: Vec<Vec<u16>> = vec![Vec::new()];
        for &m in params {
            values = values
                .into_iter()
                .flat_map(|v| {
                    (0..FN_VALUES)
                        .filter(move |&b| m & (1 << b) != 0)
                        .map(move |b| {
                            let mut v = v.clone();
                            v.push(1 << b);
                            v
                        })
                })
                .collect();
        }
        values.iter().all(|v| {
            let mut met: Option<u16> = None;
            for (ps, r) in arrows {
                if ps.iter().zip(v).all(|(p, &x)| p.t || p.values() & x != 0) {
                    let at_t = ps.iter().zip(v).find(|(p, _)| p.t).map_or(0, |(_, &x)| x);
                    let r = r.values() | if r.t { at_t } else { 0 };
                    met = Some(met.map_or(r, |m| m & r));
                }
            }
            met.is_some_and(|m| m & !result == 0)
        })
    }

    #[test]
    fn a_fit_with_functions_in_the_results_is_a_cover_of_their_values() {
        // As above, with two function types among the values, at parameters and in results,
        // and arrows generic in their own unbounded `T`, alone at a parameter, so a result
        // holds the slot's functions by `T` bound to them ([`meet_within`]): a function piece
        // is left out of the intersection only where another result holds no function. Each
        // fit holds at every value, and the verdict is the same in every order of the arrows.
        let mut rng = Rng(0x0005_eed7);
        let (mut fit, mut cover, mut by_fns, mut refused, mut neither) = (0, 0, 0, 0, 0);
        for case in 0..4000 {
            let width = 1 + case % 2;
            let n = 2 + rng.below(3) as usize;
            let mut arrows: Vec<(Vec<Place>, Place)> = Vec::new();
            for _ in 0..n {
                let tj = (rng.below(3) == 0).then(|| rng.below(width as u64) as usize);
                let ps = (0..width)
                    .map(|j| match tj == Some(j) {
                        true => Place {
                            t: true,
                            ..Place::default()
                        },
                        false => Place::random(&mut rng, false, 3),
                    })
                    .collect();
                let mut r = Place::random(&mut rng, true, 2);
                r.t = tj.is_some() && rng.below(2) == 0;
                arrows.push((ps, r));
            }
            let params: Vec<Place> = (0..width)
                .map(|_| Place::random(&mut rng, true, 3))
                .collect();
            let mut result = Place::random(&mut rng, false, 3);
            result.m |= 1 << rng.below(3);
            let sas = arrows
                .iter()
                .map(|(ps, r)| Arrow {
                    params: ps.iter().map(|p| p.ty()).collect(),
                    result: r.ty(),
                })
                .collect();
            let s = sig(sas, width, false);
            let qa = Arrow {
                params: params.iter().map(|p| p.ty()).collect(),
                result: result.ty(),
            };
            let q = sig(vec![qa], width, false);
            let ps: Vec<u16> = params.iter().map(|p| p.values()).collect();
            let truth = covers_with_fns(&arrows, &ps, result.values());
            let pairs = {
                REFERENCE.set(Reference::Pairs);
                let v = fits_sig(&s, &q);
                REFERENCE.set(Reference::None);
                v
            };
            let fns_met = arrows.iter().any(|(_, r)| r.f1 || r.f2 || r.t);
            match (fits_sig(&s, &q), truth) {
                (true, false) => panic!("case {case}: {q} in {s} is no cover of the values"),
                (true, true) if pairs => fit += 1,
                (true, true) if fns_met => by_fns += 1,
                (true, true) => cover += 1,
                (false, true) => refused += 1,
                (false, false) => neither += 1,
            }
            same_in_every_order(&s, &q, case as u64, &format!("case {case}"));
        }
        assert!(
            fit > 200 && by_fns > 100 && neither > 200,
            "{fit} fit by one arrow, {cover} together, {by_fns} together with functions in \
             the results, {refused} refused, {neither} no cover"
        );
    }

    /// A row shared by two shapes of a union, and nested inside the first, gives its variables
    /// where a recursive walk first meets it, inside the first shape, not after it.
    #[test]
    fn vars_in_gives_a_shared_row_s_variables_where_it_first_appears() {
        let shared = Row::new(vec![Ty::var("$5".into())]);
        let first = Ty::tuple(vec![
            Ty::tuple(vec![Ty::of_row(shared.clone())]),
            Ty::var("$7".into()),
        ]);
        let t = first.union(&Ty::of_row(shared));
        let mut vars = Vars::default();
        t.vars_in(&mut vars);
        let order: Vec<&str> = vars.order.iter().map(|v| &**v).collect();
        assert_eq!(order, ["$5", "$7"]);
    }

    /// The atom `#a` with `inner` as its one payload component.
    fn atom_of(inner: Ty) -> Ty {
        let mut t = Ty::set(KType::atom_with("a", &KType::top()));
        (t.payloads).insert(
            "a".into(),
            Some(vec![Shape::new(vec![inner], BTreeMap::new())]),
        );
        t
    }

    /// A tuple whose first component is an atom whose payload holds `inner`, the second `int`.
    fn row_of_atom(inner: Ty) -> Ty {
        Ty::tuple(vec![atom_of(inner), Ty::set(KType::int())])
    }

    /// A variable or the unknown in an atom's payload, inside a tuple, is held by the tuple at
    /// any depth, as one in a component is (ATOM-payload-open): the row is open, the type is
    /// not closed and has no kernel type, and a walk outside functions reaches the variable.
    #[test]
    fn a_variable_in_a_payload_inside_a_tuple_is_held_by_the_tuple() {
        let x: Arc<str> = "$3".into();
        for t in [
            row_of_atom(Ty::var(x.clone())),
            row_of_atom(row_of_atom(Ty::var(x.clone()))),
        ] {
            assert!(t.tuples[0].open(), "{t}");
            assert!(!t.tuples[0].dynamic(), "{t}");
            assert!(!t.closed(), "{t}");
            assert!(t.kernel().is_none(), "{t}");
            let mut vars = Vars::default();
            t.vars_outside(&mut vars);
            assert_eq!(vars.order, std::slice::from_ref(&x), "{t}");
            let int = Ty::set(KType::int());
            let binds: Binds = [(x.clone(), int.clone())].into_iter().collect();
            for done in [
                t.replace_outside(&binds),
                t.settle(&|v| (v == &*x).then(|| int.clone())),
            ] {
                assert!(done.closed(), "{done}");
                assert!(done.var_facts().classes.is_empty(), "{done}");
            }
        }
        let unknown = row_of_atom(Ty::dynamic());
        assert!(
            unknown.tuples[0].open() && unknown.tuples[0].dynamic(),
            "{unknown}"
        );
        assert!(!unknown.closed() && unknown.kernel().is_none(), "{unknown}");
        let data = row_of_atom(Ty::set(KType::int()));
        assert!(!data.tuples[0].open() && data.closed() && data.kernel().is_some());
    }

    /// A function in a payload is held at any depth, so the type has no kernel type.
    #[test]
    fn a_function_in_a_payload_leaves_no_kernel_type() {
        let s = Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::set(KType::int())));
        assert!(atom_of(Ty::func(s.clone())).kernel().is_none());
        assert!(row_of_atom(Ty::func(s)).kernel().is_none());
    }

    /// A random component of a shape: a literal of three, `int`, `String`, a tuple of a
    /// literal and a component, or, when `open`, the variable `T` or `U`.
    fn component(rng: &mut Rng, open: bool, depth: u32) -> Ty {
        match rng.below(if open { 8 } else { 6 }) {
            0..=2 => Ty::lit(&Value::Int(rng.below(3) as i64)),
            3 => Ty::carrier(Carrier::Int),
            4 => Ty::carrier(Carrier::Str),
            5 if depth > 0 => Ty::carrier(Carrier::Int),
            5 => Ty::tuple(vec![
                Ty::lit(&Value::Int(rng.below(2) as i64)),
                component(rng, open, depth + 1),
            ]),
            6 => Ty::var("T".into()),
            _ => Ty::var("U".into()),
        }
    }

    /// A union of one to four random members of width two: tuples, or payloads of the atom
    /// `#p`.
    fn shapes(rng: &mut Rng, open: bool, payloads: bool) -> Ty {
        let k = 1 + rng.below(4);
        let mut ms = Vec::new();
        for _ in 0..k {
            let cs = vec![component(rng, open, 0), component(rng, open, 0)];
            ms.push(match payloads {
                false => Ty::tuple(cs),
                true => {
                    let mut t = Ty::set(KType::atom_with("p", &KType::top()));
                    let shape = Shape::new(cs, BTreeMap::new());
                    t.payloads.insert("p".into(), Some(vec![shape]));
                    t
                }
            });
        }
        Ty::union_all(&ms)
    }

    /// The shapes found through the index (COMPLEXITY.md F124) are those the rule of one shape
    /// finds by trying every shape in written order: the same verdict and the same bindings
    /// wherever the index does not refuse.
    #[test]
    fn shapes_found_by_the_index_are_those_of_the_rule_of_one_shape() {
        let mut rng = Rng(24);
        let (mut cases, mut held, mut refused, mut bound) = (0, 0, 0, 0);
        for i in 0..20_000 {
            let payloads = i % 2 == 1;
            let s = shapes(&mut rng, false, payloads);
            let t = shapes(&mut rng, true, payloads);
            let mut by_index = Binds::new();
            let ok = s.sub(&t, &mut by_index);
            SCAN_ALL.set(true);
            let mut by_scan = Binds::new();
            let want = s.sub(&t, &mut by_scan);
            SCAN_ALL.set(false);
            cases += 1;
            if s.unchosen(&t).is_some() {
                assert!(!ok, "{s} <: {t}: refused, but held");
                refused += 1;
                continue;
            }
            assert_eq!(ok, want, "{s} <: {t}");
            if ok {
                assert_eq!(by_index, by_scan, "{s} <: {t}");
                held += 1;
                bound += usize::from(!by_index.is_empty());
            }
        }
        println!("{cases} cases: {held} held ({bound} binding), {refused} refused");
        assert!(held > 1000 && bound > 500, "{held} held, {bound} binding");
    }

    /// A random component of a tuple for [`near_pairs`]: literals of three integers, of two
    /// floats and of `true`, `int`, `String`, a bare atom of two names, a tuple of a literal and
    /// a component, a union of no class, a function of three, and, when `open`, the variable
    /// `T` or the unknown.
    fn near_component(rng: &mut Rng, open: bool, depth: u32, fns: &[Arc<Sig>]) -> Ty {
        match rng.below(if open { 15 } else { 13 }) {
            0..=2 => Ty::lit(&Value::Int(rng.below(3) as i64)),
            3 => Ty::carrier(Carrier::Int),
            4 => Ty::carrier(Carrier::Str),
            5 => Ty::lit(&Value::float([0.0, -0.0][rng.below(2) as usize])),
            6 => Ty::lit(&Value::Bool(true)),
            7 => Ty::set(KType::atom(["a", "b"][rng.below(2) as usize])),
            8 if depth == 0 => Ty::tuple(vec![
                Ty::lit(&Value::Int(rng.below(2) as i64)),
                near_component(rng, open, depth + 1, fns),
            ]),
            8 => Ty::carrier(Carrier::Int),
            9 => Ty::lit(&Value::Int(1)).union(&Ty::carrier(Carrier::Str)),
            10..=12 => Ty::func(fns[rng.below(3) as usize].clone()),
            13 => Ty::var("T".into()),
            _ => Ty::dynamic(),
        }
    }

    /// A union of one to six random tuples of one to three components, with, now and then, a
    /// kind-wide part, `int`, and when `open` the variable `T`.
    fn near_union(rng: &mut Rng, open: bool, fns: &[Arc<Sig>]) -> Ty {
        let mut ms = Vec::new();
        for _ in 0..1 + rng.below(6) {
            let width = [1, 2, 2, 2, 3][rng.below(5) as usize];
            let cs = (0..width)
                .map(|_| near_component(rng, open, 0, fns))
                .collect();
            ms.push(Ty::tuple(cs));
        }
        match rng.below(12) {
            0 => ms.push(Ty::set(KType::tuple(vec![KType::int(), KType::top()]))),
            1 => ms.push(Ty::set(wide())),
            2 => ms.push(Ty::carrier(Carrier::Int)),
            3 if open => ms.push(Ty::var("T".into())),
            _ => {}
        }
        Ty::union_all(&ms)
    }

    /// Meeting and subtracting through [`near_pairs`] gives exactly what meeting and
    /// subtracting every pair of tuples of one length gives (COMPLEXITY.md F127), on random
    /// unions of tuples of points, classes, unions, functions, variables and the unknown.
    #[test]
    fn tuples_met_and_subtracted_through_the_index_are_those_of_every_pair() {
        let int = Ty::carrier(Carrier::Int);
        let fns = [
            Arc::new(Sig::one(Vec::new(), Vec::new(), int.clone())),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::lit(&Value::Int(1)))),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::carrier(Carrier::Str))),
        ];
        let mut rng = Rng(127);
        let (mut cases, mut met, mut dropped) = (0, 0, 0);
        for i in 0..20_000 {
            let s = near_union(&mut rng, i % 3 == 0, &fns);
            let t = near_union(&mut rng, i % 2 == 0, &fns);
            for (a, b) in [(&s, &t), (&t, &s)] {
                let (meet, diff) = (a.meet(b), a.diff(b));
                NEAR_ALL.set(true);
                let (want_meet, want_diff) = (a.meet(b), a.diff(b));
                NEAR_ALL.set(false);
                assert_eq!(meet, want_meet, "({a}) meet ({b})");
                assert_eq!(diff, want_diff, "({a}) \\ ({b})");
                cases += 1;
                met += usize::from(!meet.tuples.is_empty());
                dropped += usize::from(diff.tuples.len() < a.tuples.len());
            }
        }
        println!("{cases} cases: {met} meets with a tuple, {dropped} differences dropping one");
        assert!(met > 5000 && dropped > 3000, "{met} met, {dropped} dropped");
    }

    /// Whether two types share a value, decided on the pairs of tuples [`Near`] finds, is what
    /// comparing every pair of tuples of one length decides (COMPLEXITY.md F132), on random
    /// unions of tuples of points, classes, unions, functions, variables and the unknown, and
    /// on the same unions with each tuple of the other side nested as a component of a pair, so
    /// that the tuples' own tuples are compared too. Pairs of sides of more than one pair go
    /// through [`Near`]; the count of those decided by tuples is checked.
    #[test]
    fn tuples_compared_by_meets_through_the_index_are_those_of_every_pair() {
        let int = Ty::carrier(Carrier::Int);
        let fns = [
            Arc::new(Sig::one(Vec::new(), Vec::new(), int.clone())),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::lit(&Value::Int(1)))),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::carrier(Carrier::Str))),
        ];
        let mut rng = Rng(132);
        let (mut cases, mut meet, mut apart, mut filed) = (0, 0, 0, 0);
        for i in 0..20_000 {
            let s = near_union(&mut rng, i % 3 == 0, &fns);
            let t = near_union(&mut rng, i % 2 == 0, &fns);
            let nest = |u: &Ty| Ty::tuple(vec![Ty::lit(&Value::Int(0)), u.clone()]);
            let (ns, nt) = (nest(&s), nest(&t));
            for (a, b) in [(&s, &t), (&t, &s), (&ns, &nt)] {
                let by_index = a.meets(b);
                NEAR_ALL.set(true);
                let want = a.meets(b);
                NEAR_ALL.set(false);
                assert_eq!(by_index, want, "({a}) meets ({b})");
                cases += 1;
                // Those that tuples decide: neither side open, and nothing but tuples meets.
                if a.meets_here(b).is_none() {
                    let (l, r) = (a.tuples.len(), b.tuples.len());
                    filed += usize::from(l * r > 1);
                    match by_index {
                        true => meet += 1,
                        false => apart += 1,
                    }
                }
            }
        }
        println!("{cases} cases; decided by tuples: {meet} meet, {apart} apart, {filed} filed");
        assert!(
            meet > 1000 && apart > 1000 && filed > 1000,
            "{meet} meet, {apart} apart, {filed} filed"
        );
    }

    /// A random value for [`near_component`]'s tuples: integers 0 to 2, the floats 0, -0 and
    /// 1.5, both booleans, two strings, two bare atoms, an atom with a payload, a tuple of an
    /// integer and a value, a path, an integer outside 64 bits and a rational.
    fn near_value(rng: &mut Rng, depth: u32) -> Value {
        match rng.below(14) {
            0..=2 => Value::Int(rng.below(3) as i64),
            3 => Value::float([0.0, -0.0, 1.5][rng.below(3) as usize]),
            4 => Value::Bool(rng.below(2) == 0),
            5 => Value::str(["s", "t"][rng.below(2) as usize]),
            6 => Value::atom(["a", "b"][rng.below(2) as usize]),
            7 => Value::atom_with("a", vec![Value::Int(rng.below(2) as i64)]),
            8 | 9 if depth == 0 => Value::tuple(vec![
                Value::Int(rng.below(2) as i64),
                near_value(rng, depth + 1),
            ]),
            8 | 9 => Value::Int(1),
            10 => Value::path(vec![Value::str("k")]),
            11 => Value::int_text("123456789012345678901234567890", 10)
                .expect("an integer")
                .expect("an integer"),
            12 => Value::rat(
                zed_kernel::Rat::decimal("0.5")
                    .expect("a rat")
                    .expect("a rat"),
            ),
            _ => Value::tuple(Vec::new()),
        }
    }

    /// Whether a type holds a tuple value, decided on the tuples [`Holders`] finds, is what
    /// comparing the value with every tuple of its length decides (COMPLEXITY.md F133), on
    /// random unions of tuples of points, classes, unions, functions, variables and the unknown,
    /// and random tuple values of points of every kind, alone, nested as the second component
    /// of `(0, _)`, and as `k` values `(x)` in a tuple of `k` copies of `(t)`: a copy of a type copies
    /// its outer level, so through the one row of `(t)` the union is one node, read for each of
    /// the `k` values in one walk, and filed in its own course.
    #[test]
    fn tuples_that_hold_a_value_through_the_index_are_those_of_every_tuple() {
        let int = Ty::carrier(Carrier::Int);
        let fns = [
            Arc::new(Sig::one(Vec::new(), Vec::new(), int.clone())),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::lit(&Value::Int(1)))),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::carrier(Carrier::Str))),
        ];
        let mut rng = Rng(134);
        let (mut cases, mut held, mut apart) = (0, 0, 0);
        for i in 0..20_000 {
            let t = near_union(&mut rng, i % 3 == 0, &fns);
            // A value of a length that `t` has most of the time: that of one of its tuples.
            let width = match t.tuples.is_empty() || rng.below(5) == 0 {
                true => 1 + rng.below(3) as usize,
                false => t.tuples[rng.below(t.tuples.len() as u64) as usize].len(),
            };
            let tuple =
                |rng: &mut Rng| Value::tuple((0..width).map(|_| near_value(rng, 0)).collect());
            let v = tuple(&mut rng);
            let k = 1 + rng.below(12) as usize;
            let vs = Value::tuple(
                (0..k)
                    .map(|_| Value::tuple(vec![tuple(&mut rng)]))
                    .collect(),
            );
            let nest = |u: &Ty| Ty::tuple(vec![Ty::lit(&Value::Int(0)), u.clone()]);
            let nv = Value::tuple(vec![Value::Int(0), v.clone()]);
            let wide = Ty::tuple(vec![Ty::tuple(vec![t.clone()]); k]);
            for (a, x) in [(&t, &v), (&nest(&t), &nv), (&wide, &vs)] {
                let by_index = a.contains(x);
                FILE.set(Some(true));
                let filed = a.contains(x);
                FILE.set(Some(false));
                let want = a.contains(x);
                FILE.set(None);
                assert_eq!(by_index, want, "({a}) holds {x:?}");
                assert_eq!(filed, want, "({a}) holds {x:?}, filed at once");
                cases += 1;
                match want {
                    true => held += 1,
                    false => apart += 1,
                }
            }
        }
        println!("{cases} cases: {held} held, {apart} not");
        assert!(held > 5000 && apart > 5000, "{held} held, {apart} not");
    }

    /// [`class_of`], read from the parts of a set, is what comparing the set with each carrier
    /// and with the atoms gives, on random unions and differences of carriers, literals, atoms
    /// with and without payloads, atoms of no value, all atoms but one, and tuples, some empty; and
    /// [`KType::universes`] gives the parts [`KType::split`] gives.
    #[test]
    fn class_of_read_from_the_parts_is_that_of_comparing_types() {
        let by_subtype = |s: &KType| {
            if let Some(c) = Carrier::ALL.into_iter().find(|c| s.subtype(&c.ty())) {
                return Some(ShapeKey::Carrier(c));
            }
            if !s.subtype(&atoms()) {
                return None;
            }
            let mut names = s.atom_names()?;
            let (n, _) = names.next()?;
            names.next().is_none().then(|| ShapeKey::Atom(n.into()))
        };
        let piece = |rng: &mut Rng| match rng.below(15) {
            0 => KType::int(),
            1 => KType::lit(&Value::Int(rng.below(3) as i64)).expect("a literal"),
            2 => KType::f64(),
            3 => KType::lit(&Value::float(1.5)).expect("a literal"),
            4 => KType::rat(),
            5 => KType::string(),
            6 => KType::bool(),
            7 => KType::lit(&Value::Bool(false)).expect("a literal"),
            8 => KType::atom(["a", "b"][rng.below(2) as usize]),
            9 => KType::atom_with("a", &KType::int()),
            10 => KType::atom_with("c", &KType::empty()),
            11 => &atoms() - &KType::atom("a"),
            12 => KType::tuple(vec![KType::int(), KType::top()]),
            13 => KType::tuple(vec![KType::empty()]),
            _ => KType::atom_with("a", &KType::tuple(vec![KType::empty()])),
        };
        let mut rng = Rng(133);
        let (mut carriers, mut names, mut none) = (0, 0, 0);
        for _ in 0..20_000 {
            let mut s = piece(&mut rng);
            for _ in 0..rng.below(3) {
                let p = piece(&mut rng);
                s = match rng.below(4) {
                    0 => &s - &p,
                    _ => &s | &p,
                };
            }
            if s.is_empty() {
                assert!(class_of(&s).is_none(), "the class of {s:?}, empty");
                continue;
            }
            let split = s.split();
            let universes = zed_kernel::types::Universes {
                bases: split.bases.each_ref().map(Option::is_some),
                atoms: split.atoms.is_some(),
                rest: split.rest.is_some(),
            };
            assert!(s.universes() == universes, "the universes of {s:?}");
            let class = class_of(&s);
            assert!(class == by_subtype(&s), "the class of {s:?}");
            match class {
                Some(ShapeKey::Carrier(_)) => carriers += 1,
                Some(_) => names += 1,
                None => none += 1,
            }
        }
        println!("{carriers} of a carrier, {names} of one name, {none} of none");
        assert!(carriers > 1000 && names > 500 && none > 1000);
    }

    /// What the filings find ([`Near`], [`Holders`]) does not depend on the hash or on the order
    /// the tuples are filed in: with another seed of their hasher ([`SEED`]) the tuples come out
    /// the same and in the same order, and with the tuples of the filed side given in reverse
    /// the same tuples come out, on random unions and tuple values as in the tests above.
    #[test]
    fn filings_find_the_same_tuples_whatever_the_hash_and_the_order() {
        let int = Ty::carrier(Carrier::Int);
        let fns = [
            Arc::new(Sig::one(Vec::new(), Vec::new(), int.clone())),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::lit(&Value::Int(1)))),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::carrier(Carrier::Str))),
        ];
        // The tuples found for each tuple of `left` among `right`, under the seed `seed`.
        let near = |left: &[Row], right: &[Row], seed: u64| {
            SEED.set(seed);
            let groups = Groups::new(left, right);
            let mut near = Near::new(&groups);
            let found: Vec<Vec<usize>> = (0..left.len()).map(|l| near.of(l).collect()).collect();
            SEED.set(0);
            found
        };
        // The tuples of `t` among `rows` found for the tuple value of `items`.
        let holders = |t: &Ty, rows: &[usize], items: &Items, seed: u64| {
            SEED.set(seed);
            let found: Vec<usize> = Holders::new(t, rows).of(items).collect();
            SEED.set(0);
            found
        };
        let sorted = |mut is: Vec<usize>| {
            is.sort_unstable();
            is
        };
        let mut rng = Rng(135);
        let (mut found, mut several) = (0, 0);
        for i in 0..5_000 {
            let s = near_union(&mut rng, i % 3 == 0, &fns);
            let t = near_union(&mut rng, i % 2 == 0, &fns);
            let want = near(&s.tuples, &t.tuples, 0);
            assert_eq!(near(&s.tuples, &t.tuples, 1 + i), want, "({s}) near ({t})");
            let back: Vec<Row> = t.tuples.iter().rev().cloned().collect();
            let last = t.tuples.len().saturating_sub(1);
            for (got, want) in near(&s.tuples, &back, 7 + i).into_iter().zip(&want) {
                let got = sorted(got.into_iter().map(|j| last - j).collect());
                assert_eq!(&got, &sorted(want.clone()), "({s}) near ({t}) in reverse");
            }
            found += want.iter().filter(|w| !w.is_empty()).count();
            several += want.iter().filter(|w| w.len() > 1).count();

            let width = match t.tuples.is_empty() {
                true => 1 + rng.below(3) as usize,
                false => t.tuples[rng.below(t.tuples.len() as u64) as usize].len(),
            };
            let v = Value::tuple((0..width).map(|_| near_value(&mut rng, 0)).collect());
            let Value::Tuple(items) = &v else {
                unreachable!("a tuple value")
            };
            let rows: Vec<usize> = (0..t.tuples.len())
                .filter(|&j| t.tuples[j].len() == width)
                .collect();
            let want = holders(&t, &rows, items, 0);
            assert_eq!(holders(&t, &rows, items, 1 + i), want, "{t} holds {v:?}");
            let back: Vec<usize> = rows.iter().rev().copied().collect();
            assert_eq!(
                sorted(holders(&t, &back, items, 7 + i)),
                sorted(want.clone()),
                "{t} holds {v:?} in reverse"
            );
            found += usize::from(!want.is_empty());
            several += usize::from(want.len() > 1);
        }
        println!("{found} lookups found a tuple, {several} more than one");
        assert!(
            found > 5000 && several > 1000,
            "{found} found, {several} several"
        );
    }
}

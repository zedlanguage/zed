//! Recursive type definitions (step L1.23, DESIGN.md sec:type_language): a group of mutually
//! recursive definitions, checked when it is defined and instantiated at its arguments.
//!
//! A group is accepted when it is
//! - *contractive*: every cycle of recursive occurrences passes through a constructor (a tuple
//!   component, an atom payload, or a morphism bound or value), so a type unfolds to its
//!   parts in finitely many steps;
//! - *regular*: every recursive occurrence passes the group's parameters unchanged, so a type
//!   has finitely many components;
//! - *monotone in emptiness*: no recursive occurrence stands under a complement, to the right
//!   of `\`, or in the guarantee of a morphism type whose value type may be empty or mentions
//!   the group, since `type T = (T) -> (#a & #b)` is inhabited exactly when it is empty; nor
//!   in the guarantee of a morphism type whose guarantee and permission differ, or that stands
//!   under `&`, `\`, a complement or differing domain bounds, directly or through a definition
//!   named there (cross-review X14: `W = (W) -> int` is accepted, `((W) -> int) & top` and
//!   `R0 = (R1) -> int; R1 = (int, R0 & ((empty) -> int))` are not).
//!
//! A value type that mentions a parameter may be empty when that parameter is: it counts as
//! possibly empty when it is empty with every parameter empty, or has a parameter under a
//! complement or to the right of `\`, where a larger argument shrinks it.

use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, LazyLock, Mutex, OnceLock, PoisonError, Weak};

use super::bes::{Answer, Bes, Kind, decide};
use super::{Piece, Rope, Type, Verdict, bytes, mix};
use crate::deep;

mod walk;

/// A type expression in a definition's body. Its `Clone`, `==` and `Debug` are written in
/// module `walk`, each in a loop.
pub enum Expr {
    /// The definition's parameter of this index.
    Param(usize),
    /// The group's definition of this index, at these arguments.
    Ref(usize, Vec<Expr>),
    /// A type that does not mention the group.
    Type(Type),
    /// `a | b | …`.
    Union(Vec<Expr>),
    /// `a & b & …`.
    And(Vec<Expr>),
    /// `!a`.
    Not(Box<Expr>),
    /// `a \ b`.
    Diff(Box<Expr>, Box<Expr>),
    /// `(a, b, …)`.
    Tuple(Vec<Expr>),
    /// `#name(a, b, …)`, whose payload is the tuple of its items.
    Atom(String, Vec<Expr>),
    /// The morphism type with this guarantee, permission and value type.
    Morphism(Box<Expr>, Box<Expr>, Box<Expr>),
}

impl Expr {
    /// `K -> V`, exact.
    pub fn exact(key: Expr, value: Expr) -> Expr {
        Expr::Morphism(Box::new(key.clone()), Box::new(key), Box::new(value))
    }

    /// Applies `f` to `self` and every expression in it, each before its parts, from a stack.
    fn walk(&self, f: &mut impl FnMut(&Expr)) {
        let mut todo = vec![self];
        while let Some(e) = todo.pop() {
            f(e);
            todo.extend(e.kids().rev());
        }
    }
}

/// A definition `type name(params) = body`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Def {
    /// Its name.
    pub name: String,
    /// Its parameters' names.
    pub params: Vec<String>,
    /// Its body.
    pub body: Expr,
}

/// The accepted groups, one per distinct definition list, by the digest of the definitions
/// ([`digest`]). `Def` equality picks the entry, so a digest only narrows the search: equal
/// definitions get one group, and so one number, however often they were written while it lives.
/// Each group is held weakly and leaves the table when it is dropped (step TABLE-life).
static GROUPS: LazyLock<Mutex<HashMap<u64, Vec<Weak<Checked>>>>> = LazyLock::new(Mutex::default);

/// The live instances, by the unit that made them, the group's number and the arguments, each
/// held weakly.
type Instances = HashMap<(u64, u64, Vec<Type>), Weak<Env>>;

/// The live instances, by the unit that made them ([`Unit`]), the group's number and the
/// arguments: one group at equal arguments gives one set of types in a unit while they live, so
/// that equal definitions meet as equal types. Types of two units are equal types too, by their
/// keys ([`Key::order`]), but no unit finds another's instance, so the end of one unit never
/// changes the types another is reading. The arguments hash by their digests and compare
/// exactly, so a call costs time in its arguments only. An instance leaves the table when it is
/// dropped (step TABLE-life). No type is dropped while this table or [`GROUPS`] is locked, since
/// a type dropped may drop an instance or a group, which takes the lock.
static INSTANCES: LazyLock<Mutex<Instances>> = LazyLock::new(Mutex::default);

/// The units begun, over all threads.
static UNITS: AtomicU64 = AtomicU64::new(0);

/// The instances made, over all threads: each instance's number ([`Key::group`]).
static ENVS: AtomicU64 = AtomicU64::new(0);

/// A thread's unit of work under way, from the end of the last (`Type::forget_emptiness`, which
/// a unit's checker calls first, or the thread's start) to the next: its number, and the
/// instances whose recursive members it made. A recursive member's unfolding holds the member,
/// and the member holds its instance, which holds its members: a cycle of strong handles,
/// which the end of the unit breaks ([`end_unit`]). The instances a unit made are its arena.
// Complexity tradeoff: a recursive type kept past the end of its unit makes its unfolding
// again, in the size of its body, when next read, and keeps it until the end of that unit. A
// group no one holds past its unit is made, instantiated and decided again by the next unit
// that names it; before, every group was kept, since no instance was freed. A cycle collector
// would free a cycle as soon as no holder is left, but cannot see who holds a type: the maps of
// atoms (`imbl::OrdMap`) share their nodes between types (`M | x` holds the map of `M`'s
// unfolding), and those nodes' counts cannot be read, so a collector would free types still
// held, or keep every recursive type with atoms. COMPLEXITY.md K68.
struct Unit {
    number: u64,
    made: Vec<Weak<Env>>,
}

thread_local! {
    static UNIT: RefCell<Unit> = RefCell::new(Unit {
        number: UNITS.fetch_add(1, Ordering::Relaxed),
        made: Vec::new(),
    });
}

/// A thread's last unit ends when the thread does.
impl Drop for Unit {
    fn drop(&mut self) {
        forget(std::mem::take(&mut self.made));
    }
}

/// The number of this thread's unit under way.
fn unit() -> u64 {
    // Thread-locals first used after this call are dropped before the queue that frees types.
    super::hold();
    UNIT.with_borrow(|u| u.number)
}

/// Ends this thread's unit: breaks the cycle of each instance whose recursive members it made,
/// so that an instance no one holds is dropped, and begins the next unit. A type held past the
/// end still denotes what it did, and is unfolded again when read. Time linear in the instances
/// the unit made and their members, besides what is dropped.
pub(super) fn end_unit() {
    let made = UNIT.try_with(|u| {
        let mut u = u.borrow_mut();
        u.number = UNITS.fetch_add(1, Ordering::Relaxed);
        std::mem::take(&mut u.made)
    });
    if let Ok(made) = made {
        forget(made);
    }
}

/// Breaks the cycle of each instance of `made` still alive ([`Env::forget`]).
fn forget(made: Vec<Weak<Env>>) {
    for env in made.iter().filter_map(Weak::upgrade) {
        env.forget();
    }
}

/// A checked group of mutually recursive definitions.
#[derive(Clone, Debug)]
pub struct Group(Arc<Checked>);

#[derive(Debug)]
struct Checked {
    /// The group's number in [`INSTANCES`]: one per distinct definition list ([`GROUPS`]). It
    /// counts the groups the process made before, so it only finds a table entry: no digest
    /// and no order reads it (deterministic checking, repair REC-id-order).
    number: u64,
    /// The hash of the definitions ([`digest`]), from which its types' digests are made.
    digest: u64,
    defs: Vec<Def>,
    /// Each body as a shared tree.
    bodies: Vec<Arc<Node>>,
    /// Whether each definition is plain: on no cycle of the group and naming only plain
    /// definitions. A plain member is its unfolding, built as an ordinary type, so equal plain
    /// members of groups built apart are one type.
    plain: Vec<bool>,
    /// The plain definitions, each after those it names.
    order: Vec<usize>,
}

/// An expression as a shared tree, each node knowing whether it mentions the group, so that a
/// part kept unevaluated is shared rather than copied, and no node's flag is computed twice.
struct Node {
    /// A hash of the shape, from the children's: equal shapes hash alike.
    digest: u64,
    recursive: bool,
    /// Whether the node names a definition that is not plain.
    open: bool,
    /// The node's place in its group: its number in the order the bodies' nodes are left,
    /// children first, the bodies in order. A part kept unevaluated is known by it ([`Key`]).
    at: u32,
    e: Shape,
}

enum Shape {
    Param(usize),
    Ref(usize, Vec<Arc<Node>>),
    Type(Type),
    Union(Vec<Arc<Node>>),
    And(Vec<Arc<Node>>),
    Not(Arc<Node>),
    Diff(Arc<Node>, Arc<Node>),
    Tuple(Vec<Arc<Node>>),
    Atom(String, Vec<Arc<Node>>),
    Morphism(Arc<Node>, Arc<Node>, Arc<Node>),
}

impl Node {
    /// The tree of `e`, given which definitions are plain; an index outside `plain` is not.
    /// Each expression's node is built once its parts' are, from a stack. Its nodes are
    /// numbered from `next` on, in the order they are built, children first.
    fn of(e: &Expr, plain: &[bool], next: &mut u32) -> Arc<Node> {
        enum Step<'a> {
            Visit(&'a Expr),
            Build(&'a Expr),
        }
        let mut todo = vec![Step::Visit(e)];
        let mut done: Vec<Arc<Node>> = Vec::new();
        while let Some(step) = todo.pop() {
            let shape = match step {
                Step::Visit(Expr::Param(i)) => Shape::Param(*i),
                Step::Visit(Expr::Type(t)) => Shape::Type(t.clone()),
                Step::Visit(e) => {
                    todo.push(Step::Build(e));
                    todo.extend(e.kids().rev().map(Step::Visit));
                    continue;
                }
                Step::Build(e) => {
                    let mut parts = done.split_off(done.len() - e.kids().count());
                    let mut last = || parts.pop().expect("each part is built");
                    match e {
                        Expr::Not(_) => Shape::Not(last()),
                        Expr::Diff(..) => {
                            let b = last();
                            Shape::Diff(last(), b)
                        }
                        Expr::Morphism(..) => {
                            let v = last();
                            let u = last();
                            Shape::Morphism(last(), u, v)
                        }
                        Expr::Ref(i, _) => Shape::Ref(*i, parts),
                        Expr::Union(_) => Shape::Union(parts),
                        Expr::And(_) => Shape::And(parts),
                        Expr::Tuple(_) => Shape::Tuple(parts),
                        Expr::Atom(name, _) => Shape::Atom(name.clone(), parts),
                        Expr::Param(_) | Expr::Type(_) => unreachable!("a leaf is not built"),
                    }
                }
            };
            let recursive = matches!(shape, Shape::Ref(..)) || shape.kids().any(|c| c.recursive);
            let open = match &shape {
                Shape::Ref(i, _) => !plain.get(*i).copied().unwrap_or(false),
                _ => shape.kids().any(|c| c.open),
            };
            let digest = shape.kids().fold(shape.tag(), |h, c| mix(h, c.digest));
            let at = *next;
            *next += 1;
            done.push(Arc::new(Node {
                digest,
                recursive,
                open,
                at,
                e: shape,
            }));
        }
        done.pop().expect("the tree of the expression")
    }
}

impl Shape {
    /// A hash of the top of the shape, without its children.
    fn tag(&self) -> u64 {
        match self {
            Shape::Param(i) => mix(1, *i as u64),
            Shape::Ref(i, _) => mix(2, *i as u64),
            Shape::Type(t) => mix(3, t.digest()),
            Shape::Union(_) => 4,
            Shape::And(_) => 5,
            Shape::Not(_) => 6,
            Shape::Diff(..) => 7,
            Shape::Tuple(_) => 8,
            Shape::Atom(name, _) => mix(9, bytes(name.as_bytes())),
            Shape::Morphism(..) => 10,
        }
    }

    /// The top of the shape, without its children or type, for [`Checked::order`]: the kind, the
    /// index of a parameter or definition, and an atom's name.
    fn head(&self) -> (u8, usize, &str) {
        match self {
            Shape::Param(i) => (1, *i, ""),
            Shape::Ref(i, _) => (2, *i, ""),
            Shape::Type(_) => (3, 0, ""),
            Shape::Union(_) => (4, 0, ""),
            Shape::And(_) => (5, 0, ""),
            Shape::Not(_) => (6, 0, ""),
            Shape::Diff(..) => (7, 0, ""),
            Shape::Tuple(_) => (8, 0, ""),
            Shape::Atom(name, _) => (9, 0, name),
            Shape::Morphism(..) => (10, 0, ""),
        }
    }
}

/// A part of an expression or tree whose owner is being dropped (module `deep`): an expression
/// nested deep is freed in a loop, on any stack.
#[expect(dead_code, reason = "a part is held only to be dropped")]
enum Freed {
    Expr(Expr),
    Exprs(Vec<Expr>),
    Shape(Shape),
    Nodes(Vec<Arc<Node>>),
}

thread_local! {
    /// The parts of expressions and trees waiting to be dropped.
    static FREED: deep::Queue<Freed> = const { deep::Queue::new() };
}

fn free(part: Freed) {
    deep::free_in(&FREED, part);
}

/// An expression's parts are freed in a loop, not by recursion.
impl Drop for Expr {
    fn drop(&mut self) {
        match self {
            Expr::Param(_) | Expr::Type(_) => {}
            Expr::Ref(_, xs)
            | Expr::Union(xs)
            | Expr::And(xs)
            | Expr::Tuple(xs)
            | Expr::Atom(_, xs) => {
                if !xs.is_empty() {
                    free(Freed::Exprs(std::mem::take(xs)));
                }
            }
            Expr::Not(a) => free(Freed::Expr(std::mem::replace(&mut **a, Expr::Param(0)))),
            Expr::Diff(a, b) => {
                for x in [a, b] {
                    free(Freed::Expr(std::mem::replace(&mut **x, Expr::Param(0))));
                }
            }
            Expr::Morphism(l, u, v) => {
                for x in [l, u, v] {
                    free(Freed::Expr(std::mem::replace(&mut **x, Expr::Param(0))));
                }
            }
        }
    }
}

/// Queues the shape `n` holds, when `n` is its last owner.
fn free_node(n: &mut Arc<Node>) {
    if let Some(n) = Arc::get_mut(n) {
        free(Freed::Shape(std::mem::replace(&mut n.e, Shape::Param(0))));
    }
}

/// A tree's children are freed in a loop, as an expression's are.
impl Drop for Shape {
    fn drop(&mut self) {
        match self {
            Shape::Param(_) | Shape::Type(_) => {}
            Shape::Ref(_, xs)
            | Shape::Union(xs)
            | Shape::And(xs)
            | Shape::Tuple(xs)
            | Shape::Atom(_, xs) => {
                if !xs.is_empty() {
                    free(Freed::Nodes(std::mem::take(xs)));
                }
            }
            Shape::Not(a) => free_node(a),
            Shape::Diff(a, b) => {
                free_node(a);
                free_node(b);
            }
            Shape::Morphism(l, u, v) => {
                free_node(l);
                free_node(u);
                free_node(v);
            }
        }
    }
}

/// Why a group is rejected: the definition at fault and the reason.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Rejection {
    /// The index of the definition.
    pub def: usize,
    /// The reason, naming the definition.
    pub message: String,
}

impl Group {
    /// The group of `defs`, if it is contractive, regular and monotone in emptiness.
    /// Equal definitions give one group: the one accepted first.
    pub fn new(defs: Vec<Def>) -> Result<Group, Rejection> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let (plain, order) = plain(&defs);
        let mut next = 0;
        let bodies: Vec<Arc<Node>> = defs
            .iter()
            .map(|d| Node::of(&d.body, &plain, &mut next))
            .collect();
        let digest = digest(&defs, &bodies);
        let g = Group(Arc::new(Checked {
            number: NEXT.fetch_add(1, Ordering::Relaxed),
            digest,
            defs,
            bodies,
            plain,
            order,
        }));
        g.regular()?;
        g.contractive()?;
        g.monotone()?;
        // The groups looked at are dropped after the lock is released, as `g` is when an equal
        // one is found.
        let mut seen = Vec::new();
        let mut groups = GROUPS.lock().expect("no thread panics holding the groups");
        let bucket = groups.entry(digest).or_default();
        for h in bucket.iter().filter_map(Weak::upgrade) {
            if h.defs == g.0.defs {
                drop(groups);
                return Ok(Group(h));
            }
            seen.push(h);
        }
        bucket.push(Arc::downgrade(&g.0));
        drop(groups);
        drop(seen);
        Ok(g)
    }

    /// The definitions.
    pub fn defs(&self) -> &[Def] {
        &self.0.defs
    }

    fn reject(&self, def: usize, why: String) -> Rejection {
        Rejection {
            def,
            message: format!("the type `{}` {why}", self.0.defs[def].name),
        }
    }

    fn regular(&self) -> Result<(), Rejection> {
        let arity = self.0.defs[0].params.len();
        for (i, d) in self.0.defs.iter().enumerate() {
            if d.params.len() != arity {
                return Err(self.reject(
                    i,
                    "takes other parameters than the definitions it is recursive with".into(),
                ));
            }
            let mut bad = None;
            d.body.walk(&mut |e| {
                if let Expr::Ref(_, args) = e {
                    let same = args.len() == arity
                        && args.iter().enumerate().all(|(k, a)| *a == Expr::Param(k));
                    if !same && bad.is_none() {
                        bad = Some(e.clone());
                    }
                }
            });
            if let Some(e) = bad {
                return Err(self.reject(
                    i,
                    format!(
                        "is not regular: its recursive occurrence `{}` changes the parameters, \
                         so the type has no end of components",
                        self.show(i, &e)
                    ),
                ));
            }
        }
        Ok(())
    }

    fn contractive(&self) -> Result<(), Rejection> {
        // The definitions each one names outside every constructor.
        let bare: Vec<Vec<usize>> = self
            .0
            .defs
            .iter()
            .map(|d| {
                let mut out = BTreeSet::new();
                unguarded(&d.body, &mut out);
                out.into_iter().collect()
            })
            .collect();
        match first_on_cycle(&bare) {
            Some(start) => Err(self.reject(
                start,
                "is not contractive: it reaches itself with no constructor between".into(),
            )),
            None => Ok(()),
        }
    }

    fn monotone(&self) -> Result<(), Rejection> {
        let bodies = &self.0.bodies;
        // A definition is constrained when it is named under `&`, `\`, a complement or the
        // domain bounds of a morphism type whose guarantee and permission differ, or is named
        // anywhere in a constrained definition: there a domain that is exact everywhere else
        // is narrowed, so the group's emptiness can flip.
        let mut constrained = vec![false; bodies.len()];
        let mut names: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); bodies.len()];
        for (i, body) in bodies.iter().enumerate() {
            refs(body, false, &mut constrained, &mut names[i]);
        }
        let mut stack: Vec<usize> = (0..bodies.len()).filter(|&i| constrained[i]).collect();
        while let Some(i) = stack.pop() {
            for &j in &names[i] {
                if !constrained[j] {
                    constrained[j] = true;
                    stack.push(j);
                }
            }
        }
        for (i, body) in bodies.iter().enumerate() {
            if let Some(why) = self.flipped(body, constrained[i]) {
                return Err(self.reject(i, format!("is not monotone in emptiness: {why}")));
            }
        }
        Ok(())
    }

    /// Where in `e` a recursive occurrence stands at a place that makes emptiness not
    /// monotone, if one does. `constrained` says whether `e` stands under `&`, `\`, a
    /// complement or differing domain bounds, here or where its definition is named.
    /// The search is depth first from a stack, each node before its parts, so the place found
    /// is the first in the order the body is written.
    fn flipped(&self, e: &Node, constrained: bool) -> Option<String> {
        let mut todo = vec![(e, constrained)];
        while let Some((e, constrained)) = todo.pop() {
            let why = match &e.e {
            Shape::Not(a) if a.recursive => {
                Some("a recursive occurrence stands under a complement".into())
            }
            Shape::Diff(_, b) if b.recursive => {
                Some("a recursive occurrence stands to the right of `\\`".into())
            }
            Shape::Morphism(l, _, v) if l.recursive && (v.recursive || self.may_be_empty(v)) => {
                Some(
                    "a recursive occurrence stands in the guaranteed domain of a morphism type \
                     whose value type may be empty or mentions the group"
                        .into(),
                )
            }
            Shape::Morphism(l, u, _) if l.recursive && !same(l, u) => Some(
                "a recursive occurrence stands in the guaranteed domain of a morphism type \
                 whose guarantee and permission differ"
                    .into(),
            ),
            Shape::Morphism(l, ..) if l.recursive && constrained => Some(
                "a recursive occurrence stands in the domain of a morphism type that stands \
                 under `&`, `\\`, a complement or differing domain bounds, or in a definition \
                 named there"
                    .into(),
            ),
            Shape::Morphism(l, u, v) => {
                let inner = constrained || bounded(l, u);
                todo.extend([(&**v, constrained), (&**u, inner), (&**l, inner)]);
                None
            }
            Shape::And(_) | Shape::Not(_) | Shape::Diff(..) => {
                todo.extend(e.e.kids().rev().map(|c| (&**c, true)));
                None
            }
            Shape::Param(_)
            | Shape::Ref(..)
            | Shape::Type(_)
            | Shape::Union(_)
            | Shape::Tuple(_)
            | Shape::Atom(..) => {
                todo.extend(e.e.kids().rev().map(|c| (&**c, constrained)));
                None
            }
            };
            if why.is_some() {
                return why;
            }
        }
        None
    }

    /// Whether `v`, which mentions no recursive occurrence, is empty at some arguments.
    fn may_be_empty(&self, v: &Node) -> bool {
        let none = vec![Type::empty(); self.0.defs[0].params.len()];
        shrinks(v, false) || eval(v, &Arc::new(Env::ground(none))).is_empty()
    }

    /// The group's types at `args`, one per definition. Each is a recursive node that unfolds
    /// to its body, except that a plain definition is its body, built as an ordinary type.
    ///
    /// # Panics
    ///
    /// When `args` is not one type per parameter.
    pub fn instance(&self, args: Vec<Type>) -> Vec<Type> {
        assert_eq!(
            args.len(),
            self.0.defs[0].params.len(),
            "one argument per parameter"
        );
        let key = (unit(), self.0.number, args);
        let lock = || {
            INSTANCES
                .lock()
                .expect("no thread panics holding the table")
        };
        let live = lock().get(&key).and_then(Weak::upgrade);
        if let Some(env) = live {
            return env.members();
        }
        let args = key.2.clone();
        let env = Arc::new(Env {
            id: ENVS.fetch_add(1, Ordering::Relaxed),
            unit: key.0,
            registered: AtomicU64::new(u64::MAX),
            group: Some(self.clone()),
            digest: args
                .iter()
                .fold(mix(12, self.0.digest), |h, t| mix(h, t.digest())),
            args,
            members: (0..self.0.defs.len()).map(|_| Mutex::new(None)).collect(),
            judged: OnceLock::new(),
        });
        // A plain member names only plain members, each set before it. A recursive member is
        // made when first read ([`Env::member`]).
        for &i in &self.0.order {
            let t = eval(&self.0.bodies[i], &env);
            *env.cell(i) = Some(t);
        }
        // Another thread may have made the instance meanwhile: the first kept is the one.
        let mut table = lock();
        let kept = match table.entry(key) {
            Entry::Occupied(mut o) => match o.get().upgrade() {
                Some(first) => first,
                None => {
                    o.insert(Arc::downgrade(&env));
                    env.clone()
                }
            },
            Entry::Vacant(v) => {
                v.insert(Arc::downgrade(&env));
                env.clone()
            }
        };
        drop(table);
        kept.members()
    }

    /// `e`, an expression of definition `def`, in the surface syntax.
    fn show(&self, def: usize, e: &Expr) -> String {
        Show {
            defs: &self.0.defs,
            params: &self.0.defs[def].params,
            args: None,
            e: &Node::of(e, &[], &mut 0),
        }
        .to_string()
    }
}

/// A hash of the definitions, from their names, parameters and bodies' digests: equal
/// definition lists hash alike. Time linear in the names and parameters.
fn digest(defs: &[Def], bodies: &[Arc<Node>]) -> u64 {
    defs.iter().zip(bodies).fold(11, |h, (d, body)| {
        let h = d
            .params
            .iter()
            .fold(mix(h, bytes(d.name.as_bytes())), |h, p| {
                mix(h, bytes(p.as_bytes()))
            });
        mix(mix(h, d.params.len() as u64), body.digest)
    })
}

/// Records in `names` each definition `e` names, and in `out` each it names at a constrained
/// place (`Group::flipped`); `constrained` says whether `e` itself stands at one.
fn refs(e: &Node, constrained: bool, out: &mut [bool], names: &mut BTreeSet<usize>) {
    let mut todo = vec![(e, constrained)];
    while let Some((e, constrained)) = todo.pop() {
        let inner = match &e.e {
            Shape::Ref(i, _) => {
                names.insert(*i);
                out[*i] |= constrained;
                constrained
            }
            Shape::And(_) | Shape::Not(_) | Shape::Diff(..) => true,
            Shape::Morphism(l, u, v) => {
                let dom = constrained || bounded(l, u);
                todo.extend([(&**l, dom), (&**u, dom), (&**v, constrained)]);
                continue;
            }
            Shape::Param(_)
            | Shape::Type(_)
            | Shape::Union(_)
            | Shape::Tuple(_)
            | Shape::Atom(..) => constrained,
        };
        todo.extend(e.e.kids().map(|c| (&**c, inner)));
    }
}

/// Whether the domain bounds `l` and `u` are written the same.
fn same(l: &Arc<Node>, u: &Arc<Node>) -> bool {
    Arc::ptr_eq(l, u) || l == u
}

/// Whether the domain bounds `l .. u` narrow the domain: they differ, the guarantee is not
/// `empty` and the permission is not `top`.
fn bounded(l: &Arc<Node>, u: &Arc<Node>) -> bool {
    let empty = matches!(&l.e, Shape::Type(t) if t.is_empty());
    let top = matches!(&u.e, Shape::Type(t) if Type::top().subtype(t));
    !same(l, u) && !empty && !top
}

/// Whether a parameter in `e` stands under a complement or to the right of `\\`, where a larger
/// argument shrinks `e`; `under` says whether `e` itself does.
fn shrinks(e: &Node, under: bool) -> bool {
    let mut todo = vec![(e, under)];
    while let Some((e, under)) = todo.pop() {
        match &e.e {
            Shape::Param(_) if under => return true,
            Shape::Not(a) => todo.push((a, true)),
            Shape::Diff(a, b) => todo.extend([(&**a, under), (&**b, true)]),
            s => todo.extend(s.kids().map(|c| (&**c, under))),
        }
    }
    false
}

/// The lowest vertex of `edges` on a cycle, if one is.
fn first_on_cycle(edges: &[Vec<usize>]) -> Option<usize> {
    on_cycle(edges).iter().position(|&c| c)
}

/// Whether each vertex of `edges` is on a cycle: Tarjan's strongly connected components, each
/// edge read once, with an explicit stack. A search from each vertex in turn read the graph once
/// per vertex.
fn on_cycle(edges: &[Vec<usize>]) -> Vec<bool> {
    const NEW: usize = usize::MAX;
    let n = edges.len();
    let (mut index, mut low, mut on) = (vec![NEW; n], vec![0; n], vec![false; n]);
    let (mut stack, mut next, mut cyclic) = (Vec::new(), 0, vec![false; n]);
    for s in 0..n {
        if index[s] != NEW {
            continue;
        }
        let mut calls = vec![(s, 0)];
        (index[s], low[s], on[s], next) = (next, next, true, next + 1);
        stack.push(s);
        while let Some((v, k)) = calls.last_mut() {
            let v = *v;
            if let Some(&w) = edges[v].get(*k) {
                *k += 1;
                if index[w] == NEW {
                    (index[w], low[w], on[w], next) = (next, next, true, next + 1);
                    stack.push(w);
                    calls.push((w, 0));
                } else if on[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            calls.pop();
            if let Some(&(u, _)) = calls.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == index[v] {
                let mut component = Vec::new();
                while let Some(w) = stack.pop() {
                    on[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                if component.len() > 1 || edges[v].contains(&v) {
                    for w in component {
                        cyclic[w] = true;
                    }
                }
            }
        }
    }
    cyclic
}

/// Whether each of `defs` is plain: on no cycle and naming only plain definitions; and the
/// plain definitions, each after those it names. A depth-first search with an explicit stack
/// settles each definition after those it names, reading each edge once.
fn plain(defs: &[Def]) -> (Vec<bool>, Vec<usize>) {
    let edges: Vec<Vec<usize>> = defs
        .iter()
        .map(|d| {
            let mut out = BTreeSet::new();
            d.body.walk(&mut |e| {
                if let Expr::Ref(i, _) = e {
                    out.insert(*i);
                }
            });
            out.into_iter().collect()
        })
        .collect();
    let cyclic = on_cycle(&edges);
    let (mut plain, mut order) = (vec![None; defs.len()], Vec::new());
    for s in 0..defs.len() {
        let mut calls = vec![(s, 0)];
        while let Some((v, k)) = calls.last_mut() {
            let v = *v;
            if plain[v].is_some() {
                calls.pop();
                continue;
            }
            // A definition on no cycle is not on the stack of calls when its names are read.
            match edges[v].get(*k) {
                Some(&w) if !cyclic[v] => {
                    *k += 1;
                    if plain[w].is_none() {
                        calls.push((w, 0));
                    }
                }
                _ => {
                    let p = !cyclic[v] && edges[v].iter().all(|&w| plain[w] == Some(true));
                    plain[v] = Some(p);
                    if p {
                        order.push(v);
                    }
                    calls.pop();
                }
            }
        }
    }
    (plain.into_iter().map(|p| p == Some(true)).collect(), order)
}

/// The definitions `e` names outside every constructor.
fn unguarded(e: &Expr, out: &mut BTreeSet<usize>) {
    let mut todo = vec![e];
    while let Some(e) = todo.pop() {
        match e {
            Expr::Ref(i, _) => {
                out.insert(*i);
            }
            Expr::Tuple(_) | Expr::Atom(..) | Expr::Morphism(..) => {}
            _ => todo.extend(e.kids()),
        }
    }
}

/// What an expression is evaluated in: the arguments, and the group's types at them.
struct Env {
    /// The instance's number among all instances made: never another's, so a group's members
    /// are told from another instance's after this one is dropped ([`Key::group`]).
    id: u64,
    /// The unit that made it, under which it is in [`INSTANCES`].
    unit: u64,
    /// The last unit that made its recursive members, which ends them ([`Unit`]).
    registered: AtomicU64,
    group: Option<Group>,
    /// A hash of the group's definitions and the arguments' digests.
    digest: u64,
    args: Vec<Type>,
    /// Each member's type: a plain member's set when the group is instantiated, a recursive
    /// member's when first read and until the end of the unit that read it ([`Env::forget`]).
    members: Vec<Mutex<Option<Type>>>,
    /// Each member's emptiness as the group decides it ([`judge`]), when first asked.
    judged: OnceLock<Vec<Option<bool>>>,
}

/// An instance leaves [`INSTANCES`]; its arguments, and the entry's, are dropped after the lock
/// is released.
impl Drop for Env {
    fn drop(&mut self) {
        let Some(g) = &self.group else { return };
        let key = (self.unit, g.0.number, std::mem::take(&mut self.args));
        let removed = INSTANCES.lock().ok().and_then(|mut t| {
            let mine = t.get(&key).is_some_and(|w| std::ptr::eq(w.as_ptr(), self));
            mine.then(|| t.remove_entry(&key)).flatten()
        });
        drop(removed);
    }
}

/// A group leaves [`GROUPS`], with the dead entries of its bucket.
impl Drop for Checked {
    fn drop(&mut self) {
        let Ok(mut groups) = GROUPS.lock() else {
            return;
        };
        if let Some(bucket) = groups.get_mut(&self.digest) {
            // Its own handle is dead now, as are those of groups dropped before. Only weak
            // handles are dropped here, which drop no group.
            bucket.retain(|w| w.strong_count() > 0);
            if bucket.is_empty() {
                groups.remove(&self.digest);
            }
        }
    }
}

impl Env {
    fn ground(args: Vec<Type>) -> Env {
        Env {
            id: ENVS.fetch_add(1, Ordering::Relaxed),
            unit: u64::MAX,
            registered: AtomicU64::new(u64::MAX),
            group: None,
            digest: 0,
            args,
            members: Vec::new(),
            judged: OnceLock::new(),
        }
    }

    /// The members of an instance.
    fn members(self: &Arc<Env>) -> Vec<Type> {
        (0..self.members.len()).map(|i| self.member(i)).collect()
    }

    fn cell(&self, i: usize) -> std::sync::MutexGuard<'_, Option<Type>> {
        self.members[i]
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    /// Member `i`: a recursive member is a node that unfolds to its body, made when first read
    /// in a unit, and kept, by the instance, until the unit ends. Another thread that made it
    /// at the same time may have kept its own first, which is then the one.
    fn member(self: &Arc<Env>, i: usize) -> Type {
        if let Some(t) = &*self.cell(i) {
            return t.clone();
        }
        // A plain member is set when the instance is made, so this one is recursive.
        let (e, named, j) = (self.clone(), self.clone(), self.clone());
        let made = Type::rec_judged(
            Key::new(self.clone(), At::Member(i)),
            move || named.name(i),
            move || eval(&e.group().0.bodies[i], &e),
            move || j.judged.get_or_init(|| judge(&j))[i],
        );
        let kept = self.cell(i).get_or_insert_with(|| made.clone()).clone();
        if kept.node_addr() == made.node_addr() {
            self.register();
        }
        // `made` is dropped here, after the lock, when another thread kept its own.
        drop(made);
        kept
    }

    /// Puts the instance in this thread's unit, once per unit, which breaks its cycle when it
    /// ends.
    fn register(self: &Arc<Env>) {
        let number = unit();
        if self.registered.swap(number, Ordering::Relaxed) != number {
            UNIT.with_borrow_mut(|u| u.made.push(Arc::downgrade(self)));
        }
    }

    /// Drops the recursive members it keeps, and their unfoldings, which hold the members: what
    /// is not held elsewhere is dropped. A member held elsewhere unfolds again when read, to the
    /// members made again then.
    fn forget(&self) {
        let plain = &self.group().0.plain;
        let kept: Vec<Type> = (0..self.members.len())
            .filter(|&i| !plain[i])
            .filter_map(|i| self.cell(i).take())
            .collect();
        for m in &kept {
            m.forget_unfolding();
        }
        drop(kept);
    }

    fn group(&self) -> &Group {
        self.group
            .as_ref()
            .expect("a recursive occurrence is in a group")
    }

    /// The name of definition `i` at the arguments: `Tree(int)`.
    fn name(&self, i: usize) -> Rope {
        let d = &self.group().0.defs[i];
        match self.args.is_empty() {
            true => Rope::cat([Piece::from(d.name.as_str())]),
            false => Rope::joined(
                &format!("{}(", d.name),
                self.args.iter().map(Type::rope),
                ", ",
                ")",
            ),
        }
    }
}

/// What a recursive node stands for, by which it is hashed and ordered: a member of a group, or
/// a part of a body kept unevaluated (by its node's place, `Node::at`), at the group's
/// arguments. It is made of the definitions and the arguments alone, so a type's digest and its
/// place in every order do not depend on what the process built before it, and checking a
/// program alone or after another agrees (deterministic checking, repair REC-id-order). Two
/// nodes with equal keys denote one type: one group at equal arguments is one instance
/// ([`INSTANCES`]), and a part evaluates alike wherever it is made.
pub(super) struct Key {
    digest: u64,
    env: Arc<Env>,
    at: At,
}

/// Which type of an instance a key names.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum At {
    /// The member of this index.
    Member(usize),
    /// The part kept unevaluated at the body node of this number.
    Part(u32),
}

impl Key {
    fn new(env: Arc<Env>, at: At) -> Key {
        let digest = match at {
            At::Member(i) => mix(mix(4, env.digest), i as u64),
            At::Part(n) => mix(mix(13, env.digest), u64::from(n)),
        };
        Key { digest, env, at }
    }

    pub(super) fn digest(&self) -> u64 {
        self.digest
    }

    /// The group of the member the key names, by the number of the instance its members share,
    /// when the key names a member: equal for two members of one instance of a group, and never
    /// reused, so a member of an instance made after another is dropped is not taken for one of
    /// the other's.
    pub(super) fn group(&self) -> Option<u64> {
        matches!(self.at, At::Member(_)).then_some(self.env.id)
    }

    /// Whether the decider of the group (`judge`) has run, which a member's `judged` reads.
    pub(super) fn judged_known(&self) -> bool {
        self.env.judged.get().is_some()
    }

    /// The recursive members of the group, in definition order, when the key names a member.
    pub(super) fn members(&self) -> Option<Vec<Type>> {
        let At::Member(_) = self.at else {
            return None;
        };
        let plain = &self.env.group().0.plain;
        Some(
            (0..plain.len())
                .filter(|&i| !plain[i])
                .map(|i| self.env.member(i))
                .collect(),
        )
    }

    /// The order of two keys: by digest, place, the groups' definitions and the arguments. What
    /// the definitions' shapes decide is decided here; the pairs of types inside them that tie
    /// in digest, then the arguments, are pushed to `types` in the order they are to be compared
    /// when the rest ties, by the caller's loop (`bdd::order`), so that no type is compared by
    /// recursion here. Time linear in the definitions where the groups differ and tie in
    /// digest, and constant otherwise.
    pub(super) fn order<'a>(
        &'a self,
        other: &'a Key,
        types: &mut Vec<(&'a Type, &'a Type)>,
    ) -> std::cmp::Ordering {
        let c = self.digest.cmp(&other.digest).then(self.at.cmp(&other.at));
        if c.is_ne() || Arc::ptr_eq(&self.env, &other.env) {
            return c;
        }
        let (a, b) = (&self.env.group().0, &other.env.group().0);
        if !Arc::ptr_eq(a, b) {
            let c = a.order(b, types);
            if c.is_ne() {
                return c;
            }
        }
        types.extend(self.env.args.iter().zip(&other.env.args));
        std::cmp::Ordering::Equal
    }
}

impl Checked {
    /// The order of two groups' definitions, after their digests: names, parameters, then the
    /// bodies node by node in a loop of its own, each type in them by digest; the pairs of types
    /// that tie in digest are pushed to `types` ([`Key::order`]).
    fn order<'a>(
        &'a self,
        other: &'a Checked,
        types: &mut Vec<(&'a Type, &'a Type)>,
    ) -> std::cmp::Ordering {
        let c = self
            .digest
            .cmp(&other.digest)
            .then(self.defs.len().cmp(&other.defs.len()));
        if c.is_ne() {
            return c;
        }
        for (d, e) in self.defs.iter().zip(&other.defs) {
            let c = d.name.cmp(&e.name).then_with(|| d.params.cmp(&e.params));
            if c.is_ne() {
                return c;
            }
        }
        let mut stack: Vec<(&Node, &Node)> = (self.bodies.iter().zip(&other.bodies).rev())
            .map(|(x, y)| (&**x, &**y))
            .collect();
        while let Some((x, y)) = stack.pop() {
            let (p, q) = (x.e.kids(), y.e.kids());
            let c = (x.digest.cmp(&y.digest))
                .then_with(|| x.e.head().cmp(&y.e.head()))
                .then_with(|| x.e.kids().count().cmp(&y.e.kids().count()));
            if c.is_ne() {
                return c;
            }
            if let (Shape::Type(s), Shape::Type(t)) = (&x.e, &y.e) {
                match s.digest().cmp(&t.digest()) {
                    std::cmp::Ordering::Equal => types.push((s, t)),
                    c => return c,
                }
            }
            // The counts are equal, so the pairs from the ends are the pairs in reverse.
            stack.extend(p.rev().zip(q.rev()).map(|(p, q)| (&**p, &**q)));
        }
        std::cmp::Ordering::Equal
    }
}

/// The type `e` denotes in `env`. Each expression's type is built once its parts' are, from a
/// stack; a part of a constructor is evaluated as [`component`] says.
fn eval(e: &Node, env: &Arc<Env>) -> Type {
    enum Step<'a> {
        Eval(&'a Node),
        Component(&'a Arc<Node>),
        Build(&'a Node),
    }
    let mut todo = vec![Step::Eval(e)];
    let mut done: Vec<Type> = Vec::new();
    while let Some(step) = todo.pop() {
        let t = match step {
            Step::Component(e) if eager(e) => {
                todo.push(Step::Eval(e));
                continue;
            }
            Step::Component(e) => component(e, env),
            Step::Eval(e) => match &e.e {
                Shape::Param(i) => env.args[*i].clone(),
                Shape::Ref(i, _) => env.member(*i),
                Shape::Type(t) => t.clone(),
                Shape::Union(_) | Shape::And(_) | Shape::Not(_) | Shape::Diff(..) => {
                    todo.push(Step::Build(e));
                    todo.extend(e.e.kids().rev().map(|c| Step::Eval(c)));
                    continue;
                }
                Shape::Tuple(_) | Shape::Atom(..) | Shape::Morphism(..) => {
                    todo.push(Step::Build(e));
                    todo.extend(e.e.kids().rev().map(Step::Component));
                    continue;
                }
            },
            Step::Build(e) => {
                let mut parts = done.split_off(done.len() - e.e.kids().count());
                match &e.e {
                    Shape::Union(_) => Type::union_all(parts),
                    Shape::And(_) => Type::meet_all(parts),
                    Shape::Tuple(_) => Type::tuple(parts),
                    Shape::Atom(name, _) => Type::atom_with(name, &Type::tuple(parts)),
                    Shape::Not(_) => !parts.pop().expect("the part"),
                    Shape::Diff(..) => {
                        let b = parts.pop().expect("the right part");
                        parts.pop().expect("the left part") - &b
                    }
                    Shape::Morphism(..) => {
                        let v = parts.pop().expect("the value type");
                        let u = parts.pop().expect("the permission");
                        Type::morphism(parts.pop().expect("the guarantee"), u, v)
                    }
                    Shape::Param(_) | Shape::Ref(..) | Shape::Type(_) => {
                        unreachable!("a leaf is not built")
                    }
                }
            }
        };
        done.push(t);
    }
    done.pop().expect("the type of the expression")
}

/// Whether `e`, in a constructor, is evaluated now: it names a definition, or names none that
/// is not plain.
fn eager(e: &Node) -> bool {
    matches!(e.e, Shape::Ref(..)) || !e.open
}

/// `e` in a constructor: when it names a definition that is not plain and is more than one
/// occurrence, it is kept as a node evaluated on first use, since evaluating it now could need
/// the parts of the type being built.
fn component(e: &Arc<Node>, env: &Arc<Env>) -> Type {
    if eager(e) {
        return eval(e, env);
    }
    let (named, at) = (e.clone(), env.clone());
    let key = Key::new(env.clone(), At::Part(e.at));
    let (e, env) = (e.clone(), env.clone());
    Type::rec(
        key,
        move || {
            Show {
                defs: &at.group().0.defs,
                params: &[],
                args: Some(&at.args),
                e: &named,
            }
            .rope()
        },
        move || eval(&e, &env),
    )
}

/// An expression in the surface syntax, its parameters by name or, with `args`, by value.
struct Show<'a> {
    defs: &'a [Def],
    params: &'a [String],
    args: Option<&'a [Type]>,
    e: &'a Node,
}

impl Show<'_> {
    /// The text as a rope, which holds the texts of the types it names without copying them,
    /// so that the name of `Tree(Tree(..))` takes time linear in its text.
    /// Each expression's rope is built once its parts' are, from a stack.
    fn rope(&self) -> Rope {
        enum Step<'a> {
            Visit(&'a Node),
            Build(&'a Node),
        }
        let mut todo = vec![Step::Visit(self.e)];
        let mut done: Vec<Rope> = Vec::new();
        while let Some(step) = todo.pop() {
            let r = match step {
                Step::Visit(e) => match &e.e {
                    Shape::Param(i) => match self.args {
                        Some(args) => args[*i].rope(),
                        None => Rope::cat([Piece::from(self.params[*i].as_str())]),
                    },
                    Shape::Ref(i, args) if args.is_empty() => {
                        Rope::cat([Piece::from(self.defs[*i].name.as_str())])
                    }
                    Shape::Type(t) => t.rope(),
                    _ => {
                        todo.push(Step::Build(e));
                        todo.extend(e.e.kids().rev().map(|c| Step::Visit(c)));
                        continue;
                    }
                },
                Step::Build(e) => {
                    let parts = done.split_off(done.len() - e.e.kids().count());
                    if let Shape::Ref(i, _) = &e.e {
                        // An argument is written without parentheses.
                        Rope::joined(&format!("{}(", self.defs[*i].name), parts, ", ", ")")
                    } else {
                        let mut parts: Vec<Rope> = parts
                            .into_iter()
                            .zip(e.e.kids())
                            .map(|(r, c)| match c.e {
                                Shape::Union(_)
                                | Shape::And(_)
                                | Shape::Diff(..)
                                | Shape::Morphism(..) => Rope::joined("(", [r], "", ")"),
                                _ => r,
                            })
                            .collect();
                        match &e.e {
                            Shape::Union(_) => Rope::joined("", parts, " | ", ""),
                            Shape::And(_) => Rope::joined("", parts, " & ", ""),
                            Shape::Not(_) => Rope::joined("!", parts, "", ""),
                            Shape::Diff(..) => Rope::joined("", parts, " \\ ", ""),
                            Shape::Tuple(_) => Rope::joined("(", parts, ", ", ")"),
                            Shape::Atom(name, _) => {
                                Rope::joined(&format!("#{name}("), parts, ", ", ")")
                            }
                            Shape::Morphism(l, u, _) => {
                                let v = parts.pop().expect("the value type");
                                let u_rope = parts.pop().expect("the permission");
                                let l_rope = parts.pop().expect("the guarantee");
                                if l == u {
                                    Rope::joined("(", [l_rope, v], ") -> ", "")
                                } else if l.e == Shape::Type(Type::empty()) {
                                    Rope::joined("", [u_rope, v], " ->? ", "")
                                } else {
                                    Rope::cat([
                                        Piece::from("("),
                                        Piece::from(l_rope),
                                        Piece::from(" ⊆ dom ⊆ "),
                                        Piece::from(u_rope),
                                        Piece::from(") -> "),
                                        Piece::from(v),
                                    ])
                                }
                            }
                            Shape::Param(_) | Shape::Ref(..) | Shape::Type(_) => {
                                unreachable!("a leaf is not built")
                            }
                        }
                    }
                }
            };
            done.push(r);
        }
        done.pop().expect("the rope of the expression")
    }
}

impl fmt::Display for Show<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.rope().strs().try_for_each(|s| f.write_str(s))
    }
}

/// Each member's emptiness at `env`'s arguments, as the group's fixed points decide it (module
/// `bes`, cross-review X14): a union is an `Or` node, a tuple or atom payload an `And` node, a
/// morphism type whose guarantee lies within its permission and is inhabited a `Mor` node of
/// its value type, and a part that does not mention the group `Top` or `Bot` by its own
/// emptiness. A cycle through a tuple is then empty and one through a morphism's value type
/// inhabited. `None` for each member when a recursive occurrence stands under `&`, `\` or a
/// complement, which the decider does not take, and for a member the decider refuses; the
/// coinductive search of module `empty` decides those. Time linear in the bodies, besides the
/// emptiness of their closed parts.
fn judge(env: &Arc<Env>) -> Vec<Option<bool>> {
    let bodies = &env.group().0.bodies;
    let refused = || vec![None; bodies.len()];
    let mut b = Bes::new();
    let mut stack = Vec::new();
    for e in bodies {
        stack.push((b.add(Kind::Bot, vec![]), e));
    }
    // A closed part is read by its verdict, never by `is_empty`, whose "inhabited" may be a
    // check that gave up: a member judged on it could be judged empty when it is not.
    while let Some((v, e)) = stack.pop() {
        let (kind, children) = match &e.e {
            _ if !e.recursive => match eval(e, env).verdict() {
                Verdict::Empty => (Kind::Bot, vec![]),
                Verdict::Inhabited => (Kind::Top, vec![]),
                Verdict::Refused(_) => return refused(),
            },
            Shape::Ref(i, _) => (Kind::Or, vec![*i as u32]),
            Shape::Union(xs) => (Kind::Or, kids(&mut b, &mut stack, xs)),
            Shape::Tuple(xs) | Shape::Atom(_, xs) => (Kind::And, kids(&mut b, &mut stack, xs)),
            Shape::Morphism(l, u, val) if l.recursive || u.recursive => {
                // Admitted only with equal bounds and a value type that is not empty.
                if val.recursive || eval(val, env).verdict() != Verdict::Inhabited {
                    return refused();
                }
                (Kind::Top, vec![])
            }
            Shape::Morphism(l, u, val) => {
                let (l, u) = (eval(l, env), eval(u, env));
                // A key promised and not permitted leaves no morphism; with no key promised the
                // empty morphism is one.
                match (l.subtype_verdict(&u), l.verdict()) {
                    (Verdict::Refused(_), _) | (_, Verdict::Refused(_)) => return refused(),
                    (Verdict::Inhabited, _) => (Kind::Bot, vec![]),
                    (Verdict::Empty, Verdict::Empty) => (Kind::Top, vec![]),
                    (Verdict::Empty, Verdict::Inhabited) => {
                        (Kind::Mor, kids(&mut b, &mut stack, [val]))
                    }
                }
            }
            Shape::And(_) | Shape::Not(_) | Shape::Diff(..) => return refused(),
            Shape::Param(_) | Shape::Type(_) => unreachable!("a closed part is not recursive"),
        };
        b.set(v, kind, children);
    }
    b.seal();
    decide(&b).answers[..bodies.len()]
        .iter()
        .map(|a| match a {
            Answer::Empty => Some(true),
            Answer::Inhabited => Some(false),
            Answer::Refused => None,
        })
        .collect()
}

/// The node of each of `xs`: a member's own for a recursive occurrence, so that the graph has
/// the group's shape and the decider's refusals do not depend on how a body is written; else a
/// new node, queued on `stack` to be set from its expression.
fn kids<'a>(
    b: &mut Bes,
    stack: &mut Vec<(u32, &'a Arc<Node>)>,
    xs: impl IntoIterator<Item = &'a Arc<Node>>,
) -> Vec<u32> {
    xs.into_iter()
        .map(|x| {
            if let Shape::Ref(i, _) = x.e {
                return i as u32;
            }
            let c = b.add(Kind::Bot, vec![]);
            stack.push((c, x));
            c
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// One definition `name = (k, …)`, plain, or recursive as `name = () | (k, name)`.
    fn defs(name: &str, k: i64, recursive: bool) -> Vec<Def> {
        let k = Expr::Type(Type::lit(&crate::value::Value::Int(k)).expect("an int literal"));
        let body = if recursive {
            Expr::Union(vec![
                Expr::Tuple(vec![]),
                Expr::Tuple(vec![k, Expr::Ref(0, vec![])]),
            ])
        } else {
            Expr::Tuple(vec![k])
        };
        vec![Def {
            name: name.to_string(),
            params: vec![],
            body,
        }]
    }

    /// Whether [`GROUPS`] has an entry for a group of `digest`.
    fn grouped(digest: u64) -> bool {
        GROUPS
            .lock()
            .expect("no panic under the lock")
            .contains_key(&digest)
    }

    /// The instance a recursive member belongs to, held weakly.
    fn env_of(t: &Type) -> Weak<Env> {
        match &*t.0 {
            super::super::Node::Rec(r) => Arc::downgrade(&r.key.env),
            _ => panic!("a recursive member"),
        }
    }

    #[test]
    fn a_recursive_instance_no_one_holds_is_freed_at_the_end_of_its_unit() {
        // Item REC-cycle: the member's unfolding holds the member, and the instance holds its
        // members, so the instance outlives its holders until the unit ends.
        let g = Group::new(defs("RecCycleFreed", 9_003, true)).expect("a recursive group");
        let (number, digest) = (g.0.number, g.0.digest);
        let t = g.instance(vec![]);
        assert!(!t[0].is_empty());
        let env = env_of(&t[0]);
        drop((g, t));
        assert!(
            env.upgrade().is_some(),
            "held by its cycle until the unit ends"
        );
        Type::forget_emptiness();
        assert!(env.upgrade().is_none(), "freed at the end of the unit");
        assert!(!instanced(number));
        assert!(!grouped(digest));
    }

    #[test]
    fn a_member_held_past_its_unit_still_denotes_its_type() {
        // A member kept past the end of its unit unfolds again when read, to the same type.
        let g = Group::new(defs("RecCycleKept", 9_005, true)).expect("a recursive group");
        let t = g.instance(vec![]);
        let before = t[0].to_string();
        assert!(!t[0].is_empty());
        let env = env_of(&t[0]);
        Type::forget_emptiness();
        assert!(env.upgrade().is_some(), "held by `t`");
        assert!(!t[0].is_empty());
        assert_eq!(t[0].to_string(), before);
        let u = g.instance(vec![]);
        assert_eq!(t[0], u[0]);
        assert!(t[0].group().is_some());
    }

    #[test]
    fn a_group_number_is_not_taken_by_an_instance_made_after_one_is_freed() {
        // `Key::group` was the instance's address, which a later instance may be given once the
        // first is freed: then members of two instances would be taken for one group's.
        let make = || {
            let g = Group::new(defs("RecCycleKey", 9_004, true)).expect("a recursive group");
            g.instance(vec![])
        };
        let t = make();
        let first = t[0].group().expect("a member's group");
        let env = env_of(&t[0]);
        drop(t);
        Type::forget_emptiness();
        assert!(env.upgrade().is_none());
        let u = make();
        let second = u[0].group().expect("a member's group");
        assert_ne!(first, second);
        assert_eq!(
            u[0].group(),
            make()[0].group(),
            "one instance within a unit"
        );
    }

    /// Whether [`INSTANCES`] has a live instance of group `number` at no arguments.
    fn instanced(number: u64) -> bool {
        let t = INSTANCES.lock().expect("no panic under the lock");
        t.get(&(unit(), number, vec![]))
            .is_some_and(|w| w.strong_count() > 0)
    }

    #[test]
    fn a_group_is_found_again_while_it_lives_and_leaves_the_table_after() {
        // Step TABLE-life: equal definitions get one group while it lives, and a dropped group
        // leaves its entry. A plain group's instance holds nothing of the group, so it leaves
        // the instances when the call returns, and its types are built alike the next time.
        let g = Group::new(defs("TableLifePlain", 9_001, false)).expect("a plain group");
        let again = Group::new(defs("TableLifePlain", 9_001, false)).expect("a plain group");
        assert!(Arc::ptr_eq(&g.0, &again.0));
        let (number, digest) = (g.0.number, g.0.digest);
        let t = g.instance(vec![]);
        assert!(!instanced(number));
        assert_eq!(g.instance(vec![]), t);
        assert!(grouped(digest));
        drop((g, again));
        assert!(!grouped(digest));
        let made_again = Group::new(defs("TableLifePlain", 9_001, false)).expect("a plain group");
        assert_eq!(made_again.instance(vec![]), t);
    }

    #[test]
    fn a_recursive_instance_is_found_again_while_it_lives() {
        // A recursive member holds its instance, which holds the group: found again by pointer
        // while held, within a unit. The instance and its members form a cycle until the unit
        // ends (item REC-cycle; see the next test).
        let g = Group::new(defs("TableLifeRec", 9_002, true)).expect("a recursive group");
        let t = g.instance(vec![]);
        assert!(instanced(g.0.number));
        let u = g.instance(vec![]);
        assert!(Arc::ptr_eq(&t[0].0, &u[0].0));
        assert!(!t[0].is_empty());
    }
}

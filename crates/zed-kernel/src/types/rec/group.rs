//! The checks of a group of definitions (module `rec`), and the tables of its groups and
//! instances.

use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap};
use std::hash::BuildHasherDefault;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, LazyLock, Mutex, OnceLock, Weak};

use super::unfold::{ENVS, Show, eval, thread};
use super::{Checked, Def, Env, Expr, Freed, Group, Node, Rejection, Shape, free, same};
use crate::types::bdd::KeyHasher;
use crate::types::{Type, bytes, defs, mix};

/// The accepted groups, one per distinct definition list, by the digest of the definitions
/// ([`digest`]). `Def` equality picks the entry, so a digest only narrows the search: equal
/// definitions get one group, and so one number, however often they were written while it lives.
/// Each group is held weakly and leaves the table when it is dropped (step TABLE-life).
static GROUPS: LazyLock<Mutex<HashMap<u64, Vec<Weak<Checked>>>>> = LazyLock::new(Mutex::default);

/// The live instances of each thread that has any, by the thread that made them, then by the
/// group's number and the arguments, each held weakly.
type Instances = HashMap<u64, ThreadInstances, BuildHasherDefault<KeyHasher>>;

/// One thread's live instances, by the group's number and the arguments.
type ThreadInstances = HashMap<(u64, Vec<Type>), Weak<Env>, BuildHasherDefault<KeyHasher>>;

/// The live instances, by the thread that made them (`Unit::thread`), the group's number and
/// the arguments. Each thread's instances are a table of their own, removed when its last
/// instance leaves, so the table a thread adds to grows with that thread's instances only: one
/// table for all threads made the thread whose insert grew it copy every thread's entries, so the
/// bytes a run allocated depended on what tests ran beside it (`deep_types`
/// `instantiating_a_group_scales`: in 2 of 12 runs of the whole binary the run at 8,000 also
/// allocated 3,211,280 bytes, a table of 65,536 entries of 49 bytes and its 16 control bytes,
/// 14.0 times the bytes of the run at 1,000 where 7.9 is usual). One group at equal arguments gives one set of types on a thread while they
/// live, so that equal definitions meet as equal types, and a later unit finds an instance an
/// earlier one made while something holds it, with the group's decided verdicts. Types of two
/// threads are equal types too, by their keys (`Key::order`), but no thread finds another's
/// instance, so the end of one thread's unit never changes the types another is reading. The arguments hash by their digests and compare
/// exactly, so a call costs time in its arguments only. An instance leaves the table when it is
/// dropped (step TABLE-life). No type is dropped while this table or [`GROUPS`] is locked, since
/// a type dropped may drop an instance or a group, which takes the lock.
static INSTANCES: LazyLock<Mutex<Instances>> = LazyLock::new(Mutex::default);

/// The numbering of a group's nodes while its trees are built ([`Node::of`]).
#[derive(Default)]
struct Numbering {
    /// The number the next node built gets.
    next: u32,
    /// The first node built of each shape, by its digest and its place among the shapes of that
    /// digest. A node whose head equals one's and whose children are of that one's children's
    /// classes is equal to it, and takes its class.
    first: HashMap<(u64, u32), Arc<Node>, BuildHasherDefault<KeyHasher>>,
}

impl Node {
    /// The tree of `e`, given which definitions are plain; an index outside `plain` is not.
    /// Each expression's node is built once its parts' are, from a stack. Its nodes are
    /// numbered from `numbering.next` on, in the order they are built, children first, and each
    /// is given its class among the nodes `numbering` has seen, in expected O(1) a node: its
    /// head is compared with the first nodes of equal digest, and its children by class.
    fn of(e: &Expr, plain: &[bool], numbering: &mut Numbering) -> Arc<Node> {
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
            let at = numbering.next;
            numbering.next += 1;
            let equal = |c: &Node| {
                c.recursive == recursive
                    && c.open == open
                    && c.e.same_head(&shape)
                    && c.e
                        .kids()
                        .zip(shape.kids())
                        .all(|(a, b)| a.class == b.class)
            };
            // The nodes of one digest and differing shapes are at probes 0, 1, 2 and on.
            let mut probe = 0;
            let (class, vacant) = loop {
                match numbering.first.entry((digest, probe)) {
                    Entry::Occupied(c) if equal(c.get()) => break (c.get().class, None),
                    Entry::Occupied(_) => probe += 1,
                    Entry::Vacant(v) => break (at, Some(v)),
                }
            };
            let node = Arc::new(Node {
                digest,
                recursive,
                open,
                at,
                class,
                e: shape,
            });
            if let Some(v) = vacant {
                v.insert(node.clone());
            }
            done.push(node);
        }
        done.pop().expect("the tree of the expression")
    }
}

impl Group {
    /// The group of `defs`, if it is contractive, regular and monotone in emptiness.
    /// Equal definitions give one group: the one accepted first.
    pub fn new(defs: Vec<Def>) -> Result<Group, Rejection> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let (plain, order, cyclic) = plain(&defs);
        // The numbering, and its hold on the first node of each class, ends with the trees.
        let mut numbering = Numbering::default();
        let bodies: Vec<Arc<Node>> = defs
            .iter()
            .map(|d| Node::of(&d.body, &plain, &mut numbering))
            .collect();
        drop(numbering);
        let digest = digest(&defs, &bodies);
        let g = Group(Arc::new(Checked {
            number: NEXT.fetch_add(1, Ordering::Relaxed),
            digest,
            defs,
            bodies,
            plain,
            cyclic,
            order,
            canon: OnceLock::new(),
        }));
        {
            // A part a rejection writes more than once is declared after its sentence, unless
            // a message around it lays it out (module `defs`).
            let local = defs::local();
            let checked = (g.regular())
                .and_then(|()| g.contractive())
                .and_then(|()| g.monotone());
            if let Err(mut r) = checked {
                if local.is_some() {
                    defs::finish(&mut r.message);
                }
                return Err(r);
            }
        }
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

    /// The number of parameters of the first definition; 0 for a group with no definitions,
    /// which is accepted and has no types.
    fn arity(&self) -> usize {
        self.0.defs.first().map_or(0, |d| d.params.len())
    }

    fn reject(&self, def: usize, why: String) -> Rejection {
        Rejection {
            def,
            message: format!("the type `{}` {why}", self.0.defs[def].name),
        }
    }

    fn regular(&self) -> Result<(), Rejection> {
        let arity = self.arity();
        for (i, d) in self.0.defs.iter().enumerate() {
            if d.params.len() != arity {
                return Err(self.reject(
                    i,
                    "takes other parameters than the definitions it is recursive with. To repair it, \
                     give every type of the group the same parameters, in the same order"
                        .into(),
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
                let Expr::Ref(j, _) = e else {
                    unreachable!("only a recursive occurrence is kept as the bad one")
                };
                // The occurrence as it should read: the member it names, given the parameters of
                // this definition, which are in scope in its body, unchanged.
                let fixed = match d.params.is_empty() {
                    true => self.0.defs[j].name.to_string(),
                    false => format!("{}({})", self.0.defs[j].name, d.params.join(", ")),
                };
                return Err(self.reject(
                    i,
                    format!(
                        "is not regular: its recursive occurrence `{}` changes the parameters, \
                         so following it reaches a new type at each step and the type has no end \
                         of components. To repair it, pass the parameters unchanged at every \
                         recursive occurrence, as `{fixed}`",
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
                "is not contractive: it reaches itself with no tuple, atom payload or function \
                 type between, so it describes no values. To repair it, put each recursive \
                 occurrence inside a tuple, an atom's payload or a function type"
                    .into(),
            )),
            None => Ok(()),
        }
    }

    /// Whether the group has the form the admission check accepts (module comment). The check
    /// is sufficient for the group's emptiness to be monotone in its members' emptiness, not
    /// necessary, so a refusal says the type is outside that form, with the reason, its site
    /// and, for a definition narrowed where it is named, the definitions it is named through.
    fn monotone(&self) -> Result<(), Rejection> {
        let bodies = &self.0.bodies;
        // A definition is constrained when it is named under `&`, `\`, a complement or the
        // domain bounds of a morphism type whose guarantee and permission differ, or is named
        // anywhere in a constrained definition: there a domain that is exact everywhere else
        // is narrowed, so the group's emptiness can flip. `via` keeps the first reason found
        // for each, so that a rejection names the path.
        let mut via: Vec<Option<Via<'_>>> = vec![None; bodies.len()];
        let mut names: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); bodies.len()];
        for (i, body) in bodies.iter().enumerate() {
            refs(i, body, &mut via, &mut names[i]);
        }
        let mut stack: Vec<usize> = (0..bodies.len()).filter(|&i| via[i].is_some()).collect();
        while let Some(i) = stack.pop() {
            for &j in &names[i] {
                if via[j].is_none() {
                    via[j] = Some(Via::Named(i));
                    stack.push(j);
                }
            }
        }
        for (i, body) in bodies.iter().enumerate() {
            if let Some(why) = self.flipped(i, body, &via) {
                return Err(self.reject(
                    i,
                    format!(
                        "is outside the form the checker accepts: {why}; the check is \
                         sufficient, not necessary, so a type it refuses may still be monotone \
                         in emptiness. To repair it, write the type so that no \
                         recursive occurrence stands there; one inside a tuple, an atom's \
                         payload, a union or a function's value type is always accepted"
                    ),
                ));
            }
        }
        Ok(())
    }

    /// Where in `e`, the body of definition `def`, a recursive occurrence stands at a place the
    /// admission check refuses, if one does, with the reason. `via` says for each definition
    /// whether, and why, it is named where a domain may be narrowed.
    /// The search is depth first from a stack, each node before its parts, so the place found
    /// is the first in the order the body is written.
    fn flipped<'a>(&self, def: usize, e: &'a Node, via: &[Option<Via<'a>>]) -> Option<String> {
        let start = match via[def] {
            Some(_) => Under::Def,
            None => Under::No,
        };
        let mut todo = vec![(e, start)];
        while let Some((e, under)) = todo.pop() {
            let text = |n: &Node| self.text(def, n);
            let narrowed = |k| match under {
                Under::Here(..) => under,
                Under::No | Under::Def => Under::Here(k, e),
            };
            match &e.e {
                // Proved: `!a` is not monotone in `a`.
                Shape::Not(a) if a.recursive => {
                    let (n, a) = (text(e), text(a));
                    return Some(format!(
                        "a recursive occurrence stands under a complement, in `{n}`, which is \
                         not monotone in `{a}`: a larger `{a}` gives a smaller `{n}`"
                    ));
                }
                // Proved: `a \ b` is not monotone in `b`.
                Shape::Diff(_, b) if b.recursive => {
                    let (n, b) = (text(e), text(b));
                    return Some(format!(
                        "a recursive occurrence stands to the right of `\\`, in `{n}`, which \
                         is not monotone in `{b}`: a larger `{b}` gives a smaller `{n}`"
                    ));
                }
                Shape::Morphism(l, u, v) => {
                    if l.recursive {
                        let m = text(e);
                        if let Some(flaw) = self.value_flaw(v) {
                            return Some(format!(
                                "a recursive occurrence stands in the guarantee of `{m}`, whose \
                                 value type `{}` {flaw}",
                                text(v)
                            ));
                        }
                        if !same(l, u) {
                            return Some(format!(
                                "a recursive occurrence stands in the guarantee of `{m}`, whose \
                                 guarantee `{}` and permission `{}` differ",
                                text(l),
                                text(u)
                            ));
                        }
                        match under {
                            Under::Here(k, s) => {
                                return Some(format!(
                                    "a recursive occurrence stands in the guarantee of `{m}`, \
                                     which stands {}",
                                    self.narrowing(def, k, s)
                                ));
                            }
                            Under::Def => {
                                return Some(format!(
                                    "a recursive occurrence stands in the guarantee of `{m}`, \
                                     in `{}`, which is narrowed where it is named: {}",
                                    self.0.defs[def].name,
                                    self.path(def, via)
                                ));
                            }
                            Under::No => {}
                        }
                    }
                    let inner = match bounded(l, u) {
                        true => narrowed(Narrowing::Bounds),
                        false => under,
                    };
                    todo.extend([(&**v, under), (&**u, inner), (&**l, inner)]);
                }
                Shape::And(_) => {
                    let inner = narrowed(Narrowing::And);
                    todo.extend(e.e.kids().rev().map(|c| (&**c, inner)));
                }
                Shape::Not(_) => {
                    let inner = narrowed(Narrowing::Not);
                    todo.extend(e.e.kids().rev().map(|c| (&**c, inner)));
                }
                Shape::Diff(..) => {
                    let inner = narrowed(Narrowing::Diff);
                    todo.extend(e.e.kids().rev().map(|c| (&**c, inner)));
                }
                Shape::Param(_)
                | Shape::Ref(..)
                | Shape::Type(_)
                | Shape::Union(_)
                | Shape::Tuple(_)
                | Shape::Atom(..) => {
                    todo.extend(e.e.kids().rev().map(|c| (&**c, under)));
                }
            }
        }
        None
    }

    /// Why the value type `v` of a morphism type whose guarantee is recursive is refused, if it
    /// is: it mentions the group, or is empty at some arguments.
    fn value_flaw(&self, v: &Node) -> Option<&'static str> {
        if v.recursive {
            return Some("mentions the group");
        }
        if shrinks(v, false) {
            return Some(
                "has a parameter under a complement or to the right of `\\`, where a larger \
                 argument gives a smaller type, so it may be empty",
            );
        }
        let n = self.0.defs[0].params.len();
        if eval(v, &Arc::new(Env::ground(vec![Type::empty(); n]))).is_empty() {
            return Some(match n {
                0 => "is empty",
                _ => "is empty when every parameter is `empty`",
            });
        }
        None
    }

    /// Where the expression `s` of definition `def` narrows a domain within it, as `k` says.
    fn narrowing(&self, def: usize, k: Narrowing, s: &Node) -> String {
        let s = self.text(def, s);
        match k {
            Narrowing::And => format!("under `&` in `{s}`"),
            Narrowing::Not => format!("under a complement in `{s}`"),
            Narrowing::Diff => format!("in an operand of `\\` in `{s}`"),
            Narrowing::Bounds => format!("in the domain bounds of `{s}`, which differ"),
        }
    }

    /// The definitions `def` is named through, from it to one named where a domain may be
    /// narrowed. Time linear in the path's text: `via` is a forest, each definition's reason
    /// set once and after its parent's.
    fn path(&self, def: usize, via: &[Option<Via<'_>>]) -> String {
        let name = |i: usize| &self.0.defs[i].name;
        let mut parts = Vec::new();
        let mut d = def;
        loop {
            match via[d].expect("a definition on the path is constrained") {
                Via::Named(j) => {
                    parts.push(format!("`{}` is named in `{}`", name(d), name(j)));
                    d = j;
                }
                Via::Place(j, k, s) => {
                    parts.push(format!(
                        "`{}` is named in `{}`, {}",
                        name(d),
                        name(j),
                        self.narrowing(j, k, s)
                    ));
                    return parts.join("; ");
                }
            }
        }
    }

    /// The group's types at `args`, one per definition. Each is a recursive node that unfolds
    /// to its body, except that a plain definition is its body, built as an ordinary type.
    ///
    /// # Panics
    ///
    /// When `args` is not one type per parameter.
    pub fn instance(&self, args: Vec<Type>) -> Vec<Type> {
        assert_eq!(args.len(), self.arity(), "one argument per parameter");
        let made_by = thread();
        let key = (self.0.number, args);
        let lock = || {
            INSTANCES
                .lock()
                .expect("no thread panics holding the table")
        };
        let live = lock()
            .get(&made_by)
            .and_then(|mine| mine.get(&key))
            .and_then(Weak::upgrade);
        if let Some(env) = live {
            return env.members();
        }
        let args = key.1.clone();
        let env = Arc::new(Env {
            id: ENVS.fetch_add(1, Ordering::Relaxed),
            thread: made_by,
            registered: AtomicU64::new(u64::MAX),
            group: Some(self.clone()),
            digest: args
                .iter()
                .fold(mix(12, self.canon().digest), |h, t| mix(h, t.digest())),
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
        let kept = match table.entry(made_by).or_default().entry(key) {
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
        self.text(def, &Node::of(e, &[], &mut Numbering::default()))
    }

    /// `e`, a node of definition `def`'s body, in the surface syntax. Time linear in its text.
    pub(in crate::types) fn text(&self, def: usize, e: &Node) -> String {
        Show {
            defs: &self.0.defs,
            params: &self.0.defs[def].params,
            args: None,
            e,
            surface: true,
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

/// Where a domain that is exact everywhere else may be narrowed (`Group::flipped`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Narrowing {
    /// Under `&`.
    And,
    /// Under a complement.
    Not,
    /// In an operand of `\`.
    Diff,
    /// In the domain bounds of a morphism type whose guarantee and permission differ.
    Bounds,
}

/// Why a definition is constrained (`Group::monotone`).
#[derive(Clone, Copy)]
enum Via<'a> {
    /// It is named in this definition, which is constrained.
    Named(usize),
    /// It is named in this definition at a place narrowed as this, within this expression.
    Place(usize, Narrowing, &'a Node),
}

/// Whether, and why, an expression stands where a domain may be narrowed (`Group::flipped`).
#[derive(Clone, Copy)]
enum Under<'a> {
    No,
    /// Its definition is constrained.
    Def,
    /// It stands at a place narrowed as this, within this expression of its body.
    Here(Narrowing, &'a Node),
}

/// Records in `names` each definition `e`, the body of definition `def`, names, and in `via`
/// the first place, in the order the bodies are written, where each is named under `&`, `\`,
/// a complement or the domain bounds of a morphism type whose guarantee and permission differ.
fn refs<'a>(def: usize, e: &'a Node, via: &mut [Option<Via<'a>>], names: &mut BTreeSet<usize>) {
    let mut todo: Vec<(&'a Node, Option<(Narrowing, &'a Node)>)> = vec![(e, None)];
    while let Some((e, under)) = todo.pop() {
        let inner = match &e.e {
            Shape::Ref(i, _) => {
                names.insert(*i);
                if let (Some((k, s)), None) = (under, via[*i]) {
                    via[*i] = Some(Via::Place(def, k, s));
                }
                under
            }
            Shape::And(_) => under.or(Some((Narrowing::And, e))),
            Shape::Not(_) => under.or(Some((Narrowing::Not, e))),
            Shape::Diff(..) => under.or(Some((Narrowing::Diff, e))),
            Shape::Morphism(l, u, v) => {
                let dom = match bounded(l, u) {
                    true => under.or(Some((Narrowing::Bounds, e))),
                    false => under,
                };
                todo.extend([(&**v, under), (&**u, dom), (&**l, dom)]);
                continue;
            }
            Shape::Param(_)
            | Shape::Type(_)
            | Shape::Union(_)
            | Shape::Tuple(_)
            | Shape::Atom(..) => under,
        };
        todo.extend(e.e.kids().rev().map(|c| (&**c, inner)));
    }
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

/// Whether each of `defs` is plain: on no cycle and naming only plain definitions; the plain
/// definitions, each after those it names; and whether each is on a cycle. A depth-first search with an explicit stack
/// settles each definition after those it names, reading each edge once.
fn plain(defs: &[Def]) -> (Vec<bool>, Vec<usize>, Vec<bool>) {
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
    (
        plain.into_iter().map(|p| p == Some(true)).collect(),
        order,
        cyclic,
    )
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

/// An instance leaves [`INSTANCES`]. Its arguments and members, and the entry's arguments, are
/// queued (module `deep`) after the lock is released: an argument may hold another instance
/// nested as deep in its own arguments, as in `Tree(Tree(… int …))`, and dropping it here would
/// recurse once per level of nesting.
impl Drop for Env {
    fn drop(&mut self) {
        if !self.members.is_empty() {
            free(Freed::Members(std::mem::take(&mut self.members)));
        }
        let args = std::mem::take(&mut self.args);
        let Some(g) = &self.group else {
            return free_types(args);
        };
        let key = (g.0.number, args);
        let removed = INSTANCES.lock().ok().and_then(|mut t| {
            let thread = t.get_mut(&self.thread)?;
            let mine = thread
                .get(&key)
                .is_some_and(|w| std::ptr::eq(w.as_ptr(), self));
            let removed = mine.then(|| thread.remove_entry(&key)).flatten();
            // The thread's table, empty, holds no type, so it is dropped under the lock.
            if thread.is_empty() {
                t.remove(&self.thread);
            }
            removed
        });
        free_types(key.1);
        if let Some(((_, entry), _)) = removed {
            free_types(entry);
        }
    }
}

/// Queues an instance's types to be dropped (module `deep`); none, when there are none.
fn free_types(types: Vec<Type>) {
    if !types.is_empty() {
        free(Freed::Types(types));
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
            crate::types::Node::Rec(r) => Arc::downgrade(&r.key.env),
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
        t.get(&thread())
            .and_then(|mine| mine.get(&(number, vec![])))
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

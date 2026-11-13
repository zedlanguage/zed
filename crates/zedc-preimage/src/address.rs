//! The key of a written constraint: its content address (DESIGN.md sec:domains, how a
//! constraint reaches the domains; QUESTIONS W6, step KEY-written-addr). Two terms that differ
//! only in the names of their binders have one address, and two terms that differ in anything
//! else have two, however they print.
//!
//! The address holds the canonical term: the term with each binder renamed by its height, one
//! more than the most binders nested in its scope, the binders of one node numbered one after
//! another. Every binder inside the scope has a lower number, so the new name is never
//! captured, and the name depends only on the scope and not on where the term sits: a part
//! held in one [`Shared`] node and reached from many places is renamed once for each binding
//! of its free names, and the canonical term keeps the sharing of the term.
//!
//! Addresses are ordered by a 64-bit digest of the canonical term, and then by the canonical
//! term itself, compared part by part: a digest is never an identity (DESIGN.md sec:theories,
//! the trusted base), so two addresses are one only when their canonical terms are one term.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::Arc;

use imbl::{OrdMap, OrdSet};
use zed_kernel::{Evidence, FixKind, Grade, GuardPos, Pattern, Shared, Term, Value, Witness};

/// The content address of a term, the key of a written constraint.
// Complexity tradeoff: naive version, the key is the term's printed text, which writes a
// shared part once per path to it, 2^d for d levels of shared parts (98 ms at d = 16, 5.5 s
// at d = 22), and keeps two constraints alike up to binder names apart. Used: the term with
// each binder renamed by its height, a shared part renamed once per binding of its free
// names (memo), ordered by a 64-bit digest and then by the canonical terms compared part by
// part, a pair of shared parts once: linear in the distinct parts (0.07 ms at d = 16, 33 ms at
// d = 8,192). Tradeoffs: the canonical term is kept in the key, memory of the term's distinct
// parts; equal digests cost a structural comparison, since a digest is never an identity.
// Tests `l01_39_reduced_product::written_address` and `address::tests`; COMPLEXITY.md row S45.
#[derive(Clone)]
pub struct Address {
    /// The digest of `term`. It is not truncated under the feature `short-addresses`: it orders
    /// the written constraints, and so the conjunctions an `@exact` search reads, which must
    /// not change with the build. Unequal terms with one digest are tested here with a digest
    /// cut to its low 8 bits.
    digest: u64,
    /// The canonical term.
    term: Shared,
}

impl Address {
    /// The address of `t`. It costs the parts of `t`, each part held in a node read once for
    /// each binding of the binder names free in it.
    pub fn of(t: &Term) -> Address {
        let mut c = Canon::default();
        c.read(t);
        let (term, digest) = c.canonical(t);
        Address {
            digest,
            term: Shared::new(term),
        }
    }

    /// The canonical term: `t` with each binder renamed by its height.
    pub fn term(&self) -> &Term {
        &self.term
    }
}

impl PartialEq for Address {
    fn eq(&self, other: &Address) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Address {}

impl PartialOrd for Address {
    fn partial_cmp(&self, other: &Address) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Address {
    /// By digest, then by the canonical terms, compared in a walk that reads each pair of parts
    /// held in nodes once.
    fn cmp(&self, other: &Address) -> Ordering {
        if self.term.id() == other.term.id() {
            return Ordering::Equal;
        }
        self.digest
            .cmp(&other.digest)
            .then_with(|| order(&self.term, &other.term))
    }
}

impl fmt::Debug for Address {
    /// The digest only: a term's text can be exponential in the size of a term with shared
    /// parts.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Address({:016x})", self.digest)
    }
}

/// The name of the binder of height `n`. It starts with U+0000, which no written name holds
/// (the lexer rejects it), followed by `h`, which no canonical name of `zedc::zir::canon`
/// holds, so it is not captured by a name the term already has.
fn height_name(n: u32) -> Arc<str> {
    format!("\0h{n}").into()
}

/// A digest built one word at a time with splitmix64's finalizer, the same in every run.
struct Digest(u64);

impl Digest {
    fn new(tag: u64) -> Digest {
        let mut d = Digest(0);
        d.word(tag);
        d
    }

    fn word(&mut self, x: u64) {
        let mut z = (self.0.rotate_left(29) ^ x).wrapping_add(0x9e37_79b9_7f4a_7c15);
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        self.0 = z ^ (z >> 31);
    }

    fn str(&mut self, s: &str) {
        self.word(s.len() as u64);
        for chunk in s.as_bytes().chunks(8) {
            let mut b = [0u8; 8];
            b[..chunk.len()].copy_from_slice(chunk);
            self.word(u64::from_le_bytes(b));
        }
    }

    /// A value: its variant, and its payload when it is a bool or a 64-bit integer. Equal
    /// values have one variant (`Value`'s equality), so they have one digest; other values
    /// that share a digest are told apart by the order of their terms.
    fn value(&mut self, v: &Value) {
        match v {
            Value::Bool(b) => {
                self.word(1);
                self.word(u64::from(*b));
            }
            Value::Int(n) => {
                self.word(2);
                self.word(*n as u64);
            }
            Value::Big(_) => self.word(3),
            Value::Rat(_) => self.word(4),
            Value::Float(_) => self.word(5),
            Value::Str(_) => self.word(6),
            Value::Atom(_) => self.word(7),
            Value::Tuple(_) => self.word(8),
            Value::Path(_) => self.word(9),
            Value::Family(_) => self.word(10),
            Value::Float32(_) => self.word(11),
        }
    }

    fn evidence(&mut self, ev: &Evidence) {
        self.word(ev.len() as u64);
        for (name, g) in ev {
            self.str(name);
            self.word(grade_rank(*g));
        }
    }
}

/// The height and the free names of a part of a term.
#[derive(Clone, Default)]
struct Info {
    /// The most binders nested in the part, counting each binder at its number.
    height: u32,
    free: OrdSet<Arc<str>>,
}

/// A part of a term below a node: the part, the node that holds it when one does, and the
/// names the node binds in it, left to right.
struct Kid<'t> {
    term: &'t Term,
    node: Option<&'t Shared>,
    binds: Vec<&'t Arc<str>>,
}

impl<'t> Kid<'t> {
    fn held(s: &'t Shared) -> Self {
        Kid {
            term: s,
            node: Some(s),
            binds: Vec::new(),
        }
    }

    fn inline(t: &'t Term) -> Self {
        Kid {
            term: t,
            node: None,
            binds: Vec::new(),
        }
    }

    fn under(mut self, binds: Vec<&'t Arc<str>>) -> Self {
        self.binds = binds;
        self
    }
}

/// The parts of `t`, in the order [`Canon::rebuild`] reads their canonical forms, each with the
/// names it is under. The scopes are those of `zedc::zir::canon::binders`: a lambda binds its
/// parameters in its body, a `let` its name in its body and not in its value, a match arm the
/// names of its pattern, a family its key in its body, and a definedness `fix` the family and
/// the key in its body; a lattice `fix` binds nothing.
fn kids(t: &Term) -> Vec<Kid<'_>> {
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => Vec::new(),
        Term::Lam(ps, b) => vec![Kid::held(b).under(ps.iter().collect())],
        Term::App(g, args) => std::iter::once(Kid::held(g))
            .chain(args.iter().map(Kid::inline))
            .collect(),
        Term::Prim(_, args) => args.iter().map(Kid::inline).collect(),
        Term::Let(x, e, b) => vec![Kid::held(e), Kid::held(b).under(vec![x])],
        Term::If(c, a, b) => vec![Kid::held(c), Kid::held(a), Kid::held(b)],
        Term::Match(s, arms) => std::iter::once(Kid::held(s))
            .chain(
                arms.iter()
                    .map(|(p, a)| Kid::inline(a).under(pattern_names(p))),
            )
            .collect(),
        Term::Fam { domain, var, body } => {
            vec![Kid::held(domain), Kid::held(body).under(vec![var])]
        }
        Term::Reindex { family, kf, vf, .. } => {
            vec![Kid::held(family), Kid::held(kf), Kid::held(vf)]
        }
        Term::Discard { family, sel } => vec![Kid::held(family), Kid::held(sel)],
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => [family, op]
            .into_iter()
            .chain(identity)
            .map(Kid::held)
            .collect(),
        Term::Fix {
            init,
            step,
            this,
            key,
            kind,
            ..
        } => match kind {
            FixKind::Definedness => vec![Kid::held(init), Kid::held(step).under(vec![this, key])],
            FixKind::Lattice { join } => vec![Kid::held(init), Kid::held(step), Kid::held(join)],
        },
        Term::Gen {
            init, step, guard, ..
        } => vec![Kid::held(init), Kid::held(step), Kid::held(guard)],
        Term::Push(_, v) => vec![Kid::held(v)],
    }
}

/// The names `p` binds, left to right.
fn pattern_names(p: &Pattern) -> Vec<&Arc<str>> {
    let mut out = Vec::new();
    let mut todo = vec![p];
    while let Some(p) = todo.pop() {
        match p {
            Pattern::Bind(x) => out.push(x),
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => todo.extend(ps.iter().rev()),
            Pattern::Fields(_, fs) => todo.extend(fs.iter().rev().map(|(_, p)| p)),
            Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
        }
    }
    out
}

/// The binder names in scope, each with the height it is renamed to.
type Env = OrdMap<Arc<str>, u32>;

/// The bindings of an [`Env`] that a part reads, in the order of the names: with the part's
/// node, the key of its canonical form.
type Bindings = Vec<(Arc<str>, u32)>;

/// A canonical part: held in a node when the part it renames is, else inline; with its digest.
enum Out {
    Held(Shared, u64),
    Inline(Term, u64),
}

impl Out {
    fn digest(&self) -> u64 {
        match self {
            Out::Held(_, d) | Out::Inline(_, d) => *d,
        }
    }

    fn shared(self) -> Shared {
        match self {
            Out::Held(s, _) => s,
            Out::Inline(t, _) => Shared::new(t),
        }
    }

    fn term(self) -> Term {
        match self {
            Out::Held(s, _) => (*s).clone(),
            Out::Inline(t, _) => t,
        }
    }
}

/// A step of [`Canon::read`].
enum Read<'t> {
    Enter(Kid<'t>, Option<u64>),
    /// A part whose `count` parts have been read; for a match held inline, the place of its
    /// arms' heights in its owner's list.
    Exit {
        term: &'t Term,
        node: Option<&'t Shared>,
        owner: Option<u64>,
        slot: usize,
        count: usize,
    },
}

/// A step of [`Canon::canonical`].
enum Step<'t> {
    Enter {
        term: &'t Term,
        node: Option<&'t Shared>,
        env: Env,
        /// The walk of a node's part this part belongs to, by its place in `walks`.
        walk: usize,
    },
    Exit {
        term: &'t Term,
        memo: Option<(u64, Bindings)>,
        env: Env,
        /// The heights the binders of each part are renamed to.
        numbers: Vec<Vec<u32>>,
        count: usize,
    },
}

/// The canonical form of one term, built in two walks with stacks of their own, so a deep term
/// does not grow the thread's stack.
#[derive(Default)]
struct Canon {
    /// The height and free names of each part held in a node, by the node's id.
    info: HashMap<u64, Info>,
    /// The heights of the arms of the matches held inline in each node's part (`None` for the
    /// root), in the order a walk of the part enters them.
    arms: HashMap<Option<u64>, Vec<u32>>,
    /// The canonical form of each part held in a node, by the node's id and the bindings it
    /// reads.
    done: HashMap<(u64, Bindings), (Shared, u64)>,
    /// The name of each height, made once.
    names: Vec<Arc<str>>,
}

impl Canon {
    /// The first walk: the height and free names of each part held in a node, and the heights
    /// of the arms of each match, each node read once.
    fn read(&mut self, root: &Term) {
        let mut todo = vec![Read::Enter(Kid::inline(root), None)];
        let mut done: Vec<Info> = Vec::new();
        while let Some(step) = todo.pop() {
            match step {
                Read::Enter(kid, owner) => {
                    if let Some(s) = kid.node
                        && let Some(i) = self.info.get(&s.id())
                    {
                        done.push(i.clone());
                        continue;
                    }
                    let owner = kid.node.map_or(owner, |s| Some(s.id()));
                    let mut slot = 0;
                    if let Term::Match(_, arms) = kid.term {
                        let list = self.arms.entry(owner).or_default();
                        slot = list.len();
                        list.extend(std::iter::repeat_n(0, arms.len()));
                    }
                    let parts = kids(kid.term);
                    todo.push(Read::Exit {
                        term: kid.term,
                        node: kid.node,
                        owner,
                        slot,
                        count: parts.len(),
                    });
                    todo.extend(parts.into_iter().rev().map(|k| Read::Enter(k, owner)));
                }
                Read::Exit {
                    term,
                    node,
                    owner,
                    slot,
                    count,
                } => {
                    let from = done.len() - count;
                    let parts: Vec<Info> = done.drain(from..).collect();
                    let info = self.combine(term, parts, owner, slot);
                    if let Some(s) = node {
                        self.info.insert(s.id(), info.clone());
                    }
                    done.push(info);
                }
            }
        }
    }

    /// The height and free names of `t`, given those of its parts in the order of [`kids`];
    /// records the heights of a match's arms at `slot` of `owner`'s list.
    fn combine(&mut self, t: &Term, parts: Vec<Info>, owner: Option<u64>, slot: usize) -> Info {
        let mut out = Info::default();
        if let Term::Var(x) = t {
            out.free.insert(x.clone());
        }
        for (i, (kid, part)) in kids(t).into_iter().zip(parts).enumerate() {
            if matches!(t, Term::Match(..)) && i > 0 {
                self.arms.get_mut(&owner).expect("the arms reserved")[slot + i - 1] = part.height;
            }
            out.height = out.height.max(part.height + kid.binds.len() as u32);
            let mut free = part.free;
            for x in kid.binds {
                free.remove(x);
            }
            // Complexity tradeoff: the smaller set goes into the larger, which bounds the
            // inserts by n log n on a tree but not on a term with shared parts, and a part
            // read under k bindings of its free names is renamed k times
            // ([`Canon::canonical`]). Nothing is given up: every term gets its address. Why: an
            // address that does not depend on the bindings around a shared part (Maziarz et
            // al., "Hashing modulo alpha-equivalence", PLDI 2021, O(n log² n)) hashes each
            // part with the places of its free names, not a term that can be compared part by
            // part, and the trusted base needs that comparison. Trigger: two shared parts of F
            // free names each, joined at n nodes (n·F inserts), or a part of size m under k
            // nested binders of one of its free names (k·m). Test:
            // `l01_39_reduced_product::written_address::writing_scales_with_the_constraints_and_the_parts`
            // covers the shared case without them. COMPLEXITY.md row C30.
            if free.len() > out.free.len() {
                std::mem::swap(&mut free, &mut out.free);
            }
            out.free.extend(free);
        }
        out
    }

    /// The name of height `n`.
    fn name(&mut self, n: u32) -> Arc<str> {
        let n = n as usize;
        while self.names.len() <= n {
            self.names.push(height_name(self.names.len() as u32));
        }
        self.names[n].clone()
    }

    /// The second walk: the canonical form of `root` and its digest. A part held in a node is
    /// renamed once for each binding of the names free in it.
    fn canonical(&mut self, root: &Term) -> (Term, u64) {
        // Each walk of a node's part, by the node's id (`None` for the root), with the number
        // of its matches' arms entered so far.
        let mut walks: Vec<(Option<u64>, usize)> = vec![(None, 0)];
        let mut todo = vec![Step::Enter {
            term: root,
            node: None,
            env: Env::new(),
            walk: 0,
        }];
        let mut outs: Vec<Out> = Vec::new();
        while let Some(step) = todo.pop() {
            match step {
                Step::Enter {
                    term,
                    node,
                    mut env,
                    mut walk,
                } => {
                    let mut memo = None;
                    if let Some(s) = node {
                        let reads = self.restrict(&env, s.id());
                        let key = (s.id(), reads);
                        if let Some((c, d)) = self.done.get(&key) {
                            outs.push(Out::Held(c.clone(), *d));
                            continue;
                        }
                        env = key.1.iter().cloned().collect();
                        memo = Some(key);
                        walks.push((Some(s.id()), 0));
                        walk = walks.len() - 1;
                    }
                    let parts = kids(term);
                    let mut numbers = Vec::with_capacity(parts.len());
                    for kid in &parts {
                        if kid.binds.is_empty() {
                            numbers.push(Vec::new());
                            continue;
                        }
                        let base = match kid.node {
                            Some(s) => self.info[&s.id()].height,
                            None => {
                                let (owner, next) = &mut walks[walk];
                                let h = self.arms[owner][*next];
                                *next += 1;
                                h
                            }
                        };
                        numbers.push((1..=kid.binds.len() as u32).map(|i| base + i).collect());
                    }
                    let count = parts.len();
                    let enters: Vec<Step<'_>> = parts
                        .into_iter()
                        .zip(&numbers)
                        .map(|(kid, ns)| {
                            let mut env = env.clone();
                            for (x, n) in kid.binds.iter().zip(ns) {
                                env.insert((*x).clone(), *n);
                            }
                            Step::Enter {
                                term: kid.term,
                                node: kid.node,
                                env,
                                walk,
                            }
                        })
                        .collect();
                    todo.push(Step::Exit {
                        term,
                        memo,
                        env,
                        numbers,
                        count,
                    });
                    todo.extend(enters.into_iter().rev());
                }
                Step::Exit {
                    term,
                    memo,
                    env,
                    numbers,
                    count,
                } => {
                    let from = outs.len() - count;
                    let parts: Vec<Out> = outs.drain(from..).collect();
                    let (t, d) = self.rebuild(term, &env, &numbers, parts);
                    outs.push(match memo {
                        Some(key) => {
                            let s = Shared::new(t);
                            self.done.insert(key, (s.clone(), d));
                            Out::Held(s, d)
                        }
                        None => Out::Inline(t, d),
                    });
                }
            }
        }
        match outs.pop().expect("the root, renamed") {
            Out::Inline(t, d) => (t, d),
            Out::Held(s, d) => ((*s).clone(), d),
        }
    }

    /// The bindings of `env` of the names free in the part held in node `id`, walking the
    /// smaller of the two.
    fn restrict(&self, env: &Env, id: u64) -> Bindings {
        let free = &self.info[&id].free;
        if env.len() <= free.len() {
            env.iter()
                .filter(|(x, _)| free.contains(*x))
                .map(|(x, n)| (x.clone(), *n))
                .collect()
        } else {
            free.iter()
                .filter_map(|x| env.get(x).map(|n| (x.clone(), *n)))
                .collect()
        }
    }

    /// The canonical form of `t` and its digest, from those of its parts in the order of
    /// [`kids`]: each name `env` binds renamed, and each binder of the `i`-th part renamed to
    /// `numbers[i]`.
    fn rebuild(
        &mut self,
        t: &Term,
        env: &Env,
        numbers: &[Vec<u32>],
        parts: Vec<Out>,
    ) -> (Term, u64) {
        let mut d = Digest::new(rank(t));
        for p in &parts {
            d.word(p.digest());
        }
        let mut parts = parts.into_iter();
        let mut next = || parts.next().expect("a part of the term");
        let t = match t {
            Term::Lit(v) => {
                d.value(v);
                Term::Lit(v.clone())
            }
            Term::Var(x) => match env.get(x) {
                Some(&n) => {
                    let x = self.name(n);
                    d.str(&x);
                    Term::Var(x)
                }
                None => {
                    d.str(x);
                    Term::Var(x.clone())
                }
            },
            Term::Read(x) => {
                d.str(x);
                Term::Read(x.clone())
            }
            Term::PrimFn(p) => {
                d.word(p.code());
                Term::PrimFn(*p)
            }
            Term::Lam(ps, _) => {
                d.word(ps.len() as u64);
                let ps = numbers[0].iter().map(|&n| self.name(n)).collect();
                Term::Lam(ps, next().shared())
            }
            Term::App(_, args) => {
                d.word(args.len() as u64);
                let g = next().shared();
                Term::App(g, args.iter().map(|_| next().term()).collect())
            }
            Term::Prim(p, args) => {
                d.word(p.code());
                d.word(args.len() as u64);
                Term::Prim(*p, args.iter().map(|_| next().term()).collect())
            }
            Term::Let(..) => {
                let x = self.name(numbers[1][0]);
                let e = next().shared();
                Term::Let(x, e, next().shared())
            }
            Term::If(..) => {
                let (c, a) = (next().shared(), next().shared());
                Term::If(c, a, next().shared())
            }
            Term::Match(_, arms) => {
                d.word(arms.len() as u64);
                let s = next().shared();
                let mut out = Vec::with_capacity(arms.len());
                for (i, (p, _)) in arms.iter().enumerate() {
                    let mut names = numbers[i + 1].iter();
                    let p = self.pattern(p, &mut names, &mut d);
                    out.push((p, next().term()));
                }
                Term::Match(s, out)
            }
            Term::Fam { .. } => {
                let var = self.name(numbers[1][0]);
                let domain = next().shared();
                Term::Fam {
                    domain,
                    var,
                    body: next().shared(),
                }
            }
            Term::Reindex { witness, .. } => {
                d.word(witness_rank(witness));
                if let Witness::Catalog(c) = witness {
                    d.str(c);
                }
                let (family, kf) = (next().shared(), next().shared());
                Term::Reindex {
                    family,
                    kf,
                    vf: next().shared(),
                    witness: witness.clone(),
                }
            }
            Term::Discard { .. } => {
                let family = next().shared();
                Term::Discard {
                    family,
                    sel: next().shared(),
                }
            }
            Term::Fold {
                identity,
                depth,
                ev,
                ..
            } => {
                d.word(u64::from(identity.is_some()));
                d.word(*depth as u64);
                d.evidence(ev);
                let (family, op) = (next().shared(), next().shared());
                Term::Fold {
                    family,
                    op,
                    identity: identity.as_ref().map(|_| next().shared()),
                    depth: *depth,
                    ev: ev.clone(),
                }
            }
            Term::Fix {
                this,
                key,
                kind,
                ev,
                ..
            } => {
                d.evidence(ev);
                let (init, step) = (next().shared(), next().shared());
                let (this, key, kind) = match kind {
                    FixKind::Definedness => (
                        self.name(numbers[1][0]),
                        self.name(numbers[1][1]),
                        FixKind::Definedness,
                    ),
                    FixKind::Lattice { .. } => (
                        this.clone(),
                        key.clone(),
                        FixKind::Lattice {
                            join: next().shared(),
                        },
                    ),
                };
                d.word(u64::from(matches!(kind, FixKind::Definedness)));
                d.str(&this);
                d.str(&key);
                Term::Fix {
                    init,
                    step,
                    this,
                    key,
                    kind,
                    ev: ev.clone(),
                }
            }
            Term::Gen { pos, .. } => {
                d.word(pos_rank(*pos));
                let (init, step) = (next().shared(), next().shared());
                Term::Gen {
                    init,
                    step,
                    guard: next().shared(),
                    pos: *pos,
                }
            }
            Term::Push(port, _) => {
                d.str(port);
                Term::Push(port.clone(), next().shared())
            }
        };
        (t, d.0)
    }

    /// `p` with its binders renamed to `names`, left to right, its digest written to `d`.
    /// A pattern is written source, read by recursion as `Pattern`'s own equality does not:
    /// its depth is that of the source.
    fn pattern(
        &mut self,
        p: &Pattern,
        names: &mut std::slice::Iter<'_, u32>,
        d: &mut Digest,
    ) -> Pattern {
        d.word(pattern_rank(p));
        match p {
            Pattern::Wild => Pattern::Wild,
            Pattern::AnyAtom => Pattern::AnyAtom,
            Pattern::Bind(_) => {
                let n = *names
                    .next()
                    .expect("a height for each binder of the pattern");
                let x = self.name(n);
                d.str(&x);
                Pattern::Bind(x)
            }
            Pattern::Lit(v) => {
                d.value(v);
                Pattern::Lit(v.clone())
            }
            Pattern::Is(ty) => Pattern::Is(ty.clone()),
            Pattern::Atom(a, ps) => {
                d.str(a);
                d.word(ps.len() as u64);
                Pattern::Atom(
                    a.clone(),
                    ps.iter().map(|p| self.pattern(p, names, d)).collect(),
                )
            }
            Pattern::Tuple(ps) => {
                d.word(ps.len() as u64);
                Pattern::Tuple(ps.iter().map(|p| self.pattern(p, names, d)).collect())
            }
            Pattern::Fields(a, fs) => {
                d.str(a);
                d.word(fs.len() as u64);
                Pattern::Fields(
                    a.clone(),
                    fs.iter()
                        .map(|(k, p)| {
                            d.str(k);
                            (k.clone(), self.pattern(p, names, d))
                        })
                        .collect(),
                )
            }
        }
    }
}

/// The rank of a term's variant in the order of terms.
fn rank(t: &Term) -> u64 {
    match t {
        Term::Lit(_) => 0,
        Term::Var(_) => 1,
        Term::Lam(..) => 2,
        Term::App(..) => 3,
        Term::Prim(..) => 4,
        Term::PrimFn(_) => 5,
        Term::Let(..) => 6,
        Term::If(..) => 7,
        Term::Match(..) => 8,
        Term::Fam { .. } => 9,
        Term::Reindex { .. } => 10,
        Term::Discard { .. } => 11,
        Term::Fold { .. } => 12,
        Term::Fix { .. } => 13,
        Term::Gen { .. } => 14,
        Term::Read(_) => 15,
        Term::Push(..) => 16,
    }
}

fn pattern_rank(p: &Pattern) -> u64 {
    match p {
        Pattern::Wild => 0,
        Pattern::Bind(_) => 1,
        Pattern::Lit(_) => 2,
        Pattern::Atom(..) => 3,
        Pattern::Fields(..) => 4,
        Pattern::Tuple(_) => 5,
        Pattern::AnyAtom => 6,
        Pattern::Is(_) => 7,
    }
}

fn grade_rank(g: Grade) -> u64 {
    match g {
        Grade::Axiom => 0,
        Grade::CheckedExhaustive => 1,
        Grade::Proved => 2,
        Grade::Bounded => 3,
        Grade::Obligated => 4,
        Grade::Assumed => 5,
    }
}

fn witness_rank(w: &Witness) -> u64 {
    match w {
        Witness::Residue => 0,
        Witness::Catalog(_) => 1,
    }
}

fn pos_rank(p: GuardPos) -> u64 {
    match p {
        GuardPos::Before => 0,
        GuardPos::After => 1,
    }
}

/// The order of two evidence maps: by size, then entry by entry.
fn evidence_order(a: &Evidence, b: &Evidence) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| {
        a.iter()
            .map(|(x, g)| (x, grade_rank(*g)))
            .cmp(b.iter().map(|(x, g)| (x, grade_rank(*g))))
    })
}

/// A pair of parts still to compare.
enum Pair<'a> {
    Terms(&'a Term, &'a Term),
    Held(&'a Shared, &'a Shared),
    Patterns(&'a Pattern, &'a Pattern),
    /// The pair of nodes whose parts have all been compared equal.
    Done(u64, u64),
}

/// The order of two terms: of the first part where they differ in a walk of each as a tree,
/// each part before its own parts and those in order, by variant and then by the fields that
/// hold no term. A pair of parts held in nodes found equal is not compared again, so the order
/// costs the distinct pairs of parts, and it is the order of the trees: a pair is skipped only
/// once all its parts have been compared, so the walk meets the parts in the order of the
/// trees. The order is total and is `Equal` exactly when the trees are equal.
fn order(a: &Term, b: &Term) -> Ordering {
    let mut equal: HashSet<(u64, u64)> = HashSet::new();
    let mut todo = vec![Pair::Terms(a, b)];
    let mut parts: Vec<Pair<'_>> = Vec::new();
    while let Some(pair) = todo.pop() {
        let o = match pair {
            Pair::Done(x, y) => {
                equal.insert((x, y));
                continue;
            }
            Pair::Held(x, y) => {
                if x.id() == y.id() || equal.contains(&(x.id(), y.id())) {
                    continue;
                }
                todo.push(Pair::Done(x.id(), y.id()));
                head(x, y, &mut parts)
            }
            Pair::Terms(x, y) => head(x, y, &mut parts),
            Pair::Patterns(p, q) => pattern_head(p, q, &mut parts),
        };
        if o != Ordering::Equal {
            return o;
        }
        todo.extend(parts.drain(..).rev());
    }
    Ordering::Equal
}

/// The order of the parts of `a` and `b` that hold no term or pattern; when equal, their
/// parts in order are put in `parts`.
fn head<'a>(a: &'a Term, b: &'a Term, parts: &mut Vec<Pair<'a>>) -> Ordering {
    let o = rank(a).cmp(&rank(b));
    if o != Ordering::Equal {
        return o;
    }
    macro_rules! held {
        ($x:expr, $y:expr) => {
            parts.push(Pair::Held($x, $y))
        };
    }
    match (a, b) {
        (Term::Lit(x), Term::Lit(y)) => x.cmp(y),
        (Term::Var(x), Term::Var(y)) | (Term::Read(x), Term::Read(y)) => x.cmp(y),
        (Term::PrimFn(p), Term::PrimFn(q)) => p.code().cmp(&q.code()),
        (Term::Lam(xs, s), Term::Lam(ys, t)) => xs.cmp(ys).then_with(|| {
            held!(s, t);
            Ordering::Equal
        }),
        (Term::Push(x, s), Term::Push(y, t)) => x.cmp(y).then_with(|| {
            held!(s, t);
            Ordering::Equal
        }),
        (Term::App(f, xs), Term::App(g, ys)) => xs.len().cmp(&ys.len()).then_with(|| {
            held!(f, g);
            parts.extend(xs.iter().zip(ys).map(|(x, y)| Pair::Terms(x, y)));
            Ordering::Equal
        }),
        (Term::Prim(p, xs), Term::Prim(q, ys)) => p
            .code()
            .cmp(&q.code())
            .then(xs.len().cmp(&ys.len()))
            .then_with(|| {
                parts.extend(xs.iter().zip(ys).map(|(x, y)| Pair::Terms(x, y)));
                Ordering::Equal
            }),
        (Term::Let(x, e, s), Term::Let(y, f, t)) => x.cmp(y).then_with(|| {
            held!(e, f);
            held!(s, t);
            Ordering::Equal
        }),
        (Term::If(c, s, t), Term::If(d, u, v)) => {
            held!(c, d);
            held!(s, u);
            held!(t, v);
            Ordering::Equal
        }
        (Term::Match(s, xs), Term::Match(t, ys)) => xs.len().cmp(&ys.len()).then_with(|| {
            held!(s, t);
            for ((p, x), (q, y)) in xs.iter().zip(ys) {
                parts.extend([Pair::Patterns(p, q), Pair::Terms(x, y)]);
            }
            Ordering::Equal
        }),
        (
            Term::Fam { domain, var, body },
            Term::Fam {
                domain: d,
                var: v,
                body: b,
            },
        ) => var.cmp(v).then_with(|| {
            held!(domain, d);
            held!(body, b);
            Ordering::Equal
        }),
        (
            Term::Reindex {
                family,
                kf,
                vf,
                witness,
            },
            Term::Reindex {
                family: g,
                kf: k,
                vf: v,
                witness: w,
            },
        ) => witness_rank(witness)
            .cmp(&witness_rank(w))
            .then_with(|| match (witness, w) {
                (Witness::Catalog(x), Witness::Catalog(y)) => x.cmp(y),
                _ => Ordering::Equal,
            })
            .then_with(|| {
                held!(family, g);
                held!(kf, k);
                held!(vf, v);
                Ordering::Equal
            }),
        (Term::Discard { family, sel }, Term::Discard { family: g, sel: s }) => {
            held!(family, g);
            held!(sel, s);
            Ordering::Equal
        }
        (
            Term::Fold {
                family,
                op,
                identity,
                depth,
                ev,
            },
            Term::Fold {
                family: g,
                op: o,
                identity: i,
                depth: d,
                ev: e,
            },
        ) => identity
            .is_some()
            .cmp(&i.is_some())
            .then(depth.cmp(d))
            .then_with(|| evidence_order(ev, e))
            .then_with(|| {
                held!(family, g);
                held!(op, o);
                if let (Some(x), Some(y)) = (identity, i) {
                    held!(x, y);
                }
                Ordering::Equal
            }),
        (
            Term::Fix {
                init,
                step,
                this,
                key,
                kind,
                ev,
            },
            Term::Fix {
                init: i,
                step: s,
                this: t,
                key: k,
                kind: c,
                ev: e,
            },
        ) => {
            let lattice = |k: &FixKind| matches!(k, FixKind::Lattice { .. });
            lattice(kind)
                .cmp(&lattice(c))
                .then_with(|| this.cmp(t))
                .then_with(|| key.cmp(k))
                .then_with(|| evidence_order(ev, e))
                .then_with(|| {
                    held!(init, i);
                    held!(step, s);
                    if let (FixKind::Lattice { join: x }, FixKind::Lattice { join: y }) = (kind, c)
                    {
                        held!(x, y);
                    }
                    Ordering::Equal
                })
        }
        (
            Term::Gen {
                init,
                step,
                guard,
                pos,
            },
            Term::Gen {
                init: i,
                step: s,
                guard: g,
                pos: p,
            },
        ) => pos_rank(*pos).cmp(&pos_rank(*p)).then_with(|| {
            held!(init, i);
            held!(step, s);
            held!(guard, g);
            Ordering::Equal
        }),
        _ => unreachable!("terms of one rank are of one variant"),
    }
}

/// As [`head`], for two patterns.
fn pattern_head<'a>(a: &'a Pattern, b: &'a Pattern, parts: &mut Vec<Pair<'a>>) -> Ordering {
    let o = pattern_rank(a).cmp(&pattern_rank(b));
    if o != Ordering::Equal {
        return o;
    }
    match (a, b) {
        (Pattern::Wild, Pattern::Wild) | (Pattern::AnyAtom, Pattern::AnyAtom) => Ordering::Equal,
        (Pattern::Bind(x), Pattern::Bind(y)) => x.cmp(y),
        (Pattern::Lit(x), Pattern::Lit(y)) => x.cmp(y),
        (Pattern::Is(s), Pattern::Is(t)) => s.cmp(t),
        (Pattern::Atom(x, ps), Pattern::Atom(y, qs)) => {
            x.cmp(y).then(ps.len().cmp(&qs.len())).then_with(|| {
                parts.extend(ps.iter().zip(qs).map(|(p, q)| Pair::Patterns(p, q)));
                Ordering::Equal
            })
        }
        (Pattern::Tuple(ps), Pattern::Tuple(qs)) => ps.len().cmp(&qs.len()).then_with(|| {
            parts.extend(ps.iter().zip(qs).map(|(p, q)| Pair::Patterns(p, q)));
            Ordering::Equal
        }),
        (Pattern::Fields(x, fs), Pattern::Fields(y, gs)) => x
            .cmp(y)
            .then(fs.len().cmp(&gs.len()))
            .then_with(|| fs.iter().map(|(k, _)| k).cmp(gs.iter().map(|(k, _)| k)))
            .then_with(|| {
                parts.extend(
                    fs.iter()
                        .zip(gs)
                        .map(|((_, p), (_, q))| Pair::Patterns(p, q)),
                );
                Ordering::Equal
            }),
        _ => unreachable!("patterns of one rank are of one variant"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zed_kernel::Prim;
    use zed_kernel::term::build::{lam, lit, var};

    fn prim(p: Prim, args: Vec<Term>) -> Term {
        Term::Prim(p, args)
    }

    /// `t`'s address with its digest cut to its low 8 bits, so unequal terms often share one.
    fn short(t: &Term) -> Address {
        let mut a = Address::of(t);
        a.digest &= 0xff;
        a
    }

    #[test]
    fn binder_names_do_not_change_the_address() {
        let f = |x: &str| {
            prim(
                Prim::Lt,
                vec![Term::App(lam(&[x], var(x)).into(), vec![var("n")]), lit(3)],
            )
        };
        assert_eq!(Address::of(&f("a")), Address::of(&f("b")));
        // A free name is kept: `n` and `m` differ.
        let g = |n: &str| prim(Prim::Lt, vec![var(n), lit(3)]);
        assert_ne!(Address::of(&g("n")), Address::of(&g("m")));
    }

    #[test]
    fn a_binder_is_not_confused_with_a_free_name() {
        // `(x) -> x` and `(x) -> y` differ although both bind one name.
        assert_ne!(
            Address::of(&lam(&["x"], var("x"))),
            Address::of(&lam(&["x"], var("y")))
        );
        // `(x, y) -> x` and `(x, y) -> y` differ.
        assert_ne!(
            Address::of(&lam(&["x", "y"], var("x"))),
            Address::of(&lam(&["x", "y"], var("y")))
        );
        // Shadowing: `(x) -> (x) -> x` is `(a) -> (b) -> b`, not `(a) -> (b) -> a`.
        assert_eq!(
            Address::of(&lam(&["x"], lam(&["x"], var("x")))),
            Address::of(&lam(&["a"], lam(&["b"], var("b"))))
        );
        assert_ne!(
            Address::of(&lam(&["x"], lam(&["x"], var("x")))),
            Address::of(&lam(&["a"], lam(&["b"], var("a"))))
        );
    }

    #[test]
    fn a_let_binds_its_name_in_its_body_only() {
        let t = |x: &str, v: &str, b: &str| {
            Term::Let(x.into(), Shared::new(var(v)), Shared::new(var(b)))
        };
        // `let x = x in x` is `let y = x in y`, and not `let y = y in y`.
        assert_eq!(
            Address::of(&t("x", "x", "x")),
            Address::of(&t("y", "x", "y"))
        );
        assert_ne!(
            Address::of(&t("x", "x", "x")),
            Address::of(&t("y", "y", "y"))
        );
    }

    #[test]
    fn match_arms_rename_their_pattern_names() {
        let t = |x: &str, y: &str, body: &str| {
            Term::Match(
                Shared::new(var("s")),
                vec![(
                    Pattern::Tuple(vec![Pattern::Bind(x.into()), Pattern::Bind(y.into())]),
                    var(body),
                )],
            )
        };
        assert_eq!(
            Address::of(&t("a", "b", "a")),
            Address::of(&t("p", "q", "p"))
        );
        assert_ne!(
            Address::of(&t("a", "b", "a")),
            Address::of(&t("a", "b", "b"))
        );
    }

    #[test]
    fn short_digests_are_confirmed_by_the_terms() {
        let ts: Vec<Term> = (0..2000)
            .map(|i| prim(Prim::Lt, vec![var("n"), lit(i)]))
            .collect();
        let addrs: Vec<Address> = ts.iter().map(short).collect();
        let distinct: std::collections::BTreeSet<&Address> = addrs.iter().collect();
        assert_eq!(distinct.len(), ts.len());
        for (t, a) in ts.iter().zip(&addrs) {
            assert_eq!(short(t), *a);
        }
        // The order is total and agrees with itself across the pairs that share a digest.
        let mut sorted = addrs.clone();
        sorted.sort();
        assert!(sorted.windows(2).all(|w| w[0] < w[1]));
    }

    #[test]
    fn a_shared_part_is_renamed_once_per_binding() {
        // A chain of `d` doublings, each half one node: 2^d paths, d nodes.
        let mut t = var("n");
        for _ in 0..64 {
            let s = Shared::new(t);
            t = Term::App(s.clone(), vec![Term::App(s, vec![])]);
        }
        let t = lam(&["n"], t);
        let a = Address::of(&t);
        assert_eq!(a, Address::of(&t));
    }

    /// `(z) -> s() && s()` where `s` is `match z { p => p + v }`, one node read under the
    /// lambda and, as `t()` with `t` the same node, outside it, where `z` is free.
    fn shared_match(z: &str, p: &str) -> Term {
        let s = Shared::new(Term::Match(
            Shared::new(var(z)),
            vec![(
                Pattern::Bind(p.into()),
                prim(Prim::Add, vec![var(p), var("v")]),
            )],
        ));
        let inside = lam(&[z], Term::App(s.clone(), vec![]));
        prim(
            Prim::And,
            vec![Term::App(inside.into(), vec![]), Term::App(s, vec![])],
        )
    }

    #[test]
    fn a_shared_match_is_renamed_under_each_binding() {
        assert_eq!(
            Address::of(&shared_match("z", "p")),
            Address::of(&shared_match("z", "q"))
        );
        // The node's `z` is bound in one place and free in the other: the canonical term
        // renames the first and keeps the second.
        let a = Address::of(&shared_match("z", "p"));
        let Term::Prim(_, parts) = a.term() else {
            panic!("an and")
        };
        assert_ne!(
            parts[0].to_string().contains("z"),
            parts[1].to_string().contains("z")
        );
        // Another free name is another address.
        assert_ne!(
            Address::of(&shared_match("z", "p")),
            Address::of(&shared_match("y", "p"))
        );
    }

    /// A fix whose step is `g(x)`, binding `this` and `key`.
    fn fix(this: &str, key: &str, g: &str, x: &str, kind: FixKind) -> Term {
        Term::Fix {
            init: Shared::new(var("d")),
            step: Shared::new(Term::App(Shared::new(var(g)), vec![var(x)])),
            this: this.into(),
            key: key.into(),
            kind,
            ev: Evidence::new(),
        }
    }

    #[test]
    fn a_definedness_fix_binds_its_names_and_a_lattice_fix_does_not() {
        let def = |t, k, g, x| Address::of(&fix(t, k, g, x, FixKind::Definedness));
        // `this(key)` with either names is one address; `key(this)` is another.
        assert_eq!(def("f", "k", "f", "k"), def("g", "j", "g", "j"));
        assert_ne!(def("f", "k", "f", "k"), def("f", "k", "k", "f"));
        let join = || FixKind::Lattice {
            join: Shared::new(var("j")),
        };
        assert_ne!(
            Address::of(&fix("f", "k", "f", "k", join())),
            Address::of(&fix("g", "j", "g", "j", join()))
        );
    }
}

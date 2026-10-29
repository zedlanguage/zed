//! Kernel terms: Tier 0, a strict lambda calculus with data, and Tier 1, the seven
//! generators over families (DESIGN.md sec:kernel).
//!
//! Every surface form elaborates to a [`Term`]. Names are plain strings: the front end has
//! resolved scopes before a term is built, so a term never needs renaming.

use std::sync::Arc;

use crate::value::Value;

/// A primitive operation. Applied to a failure atom, every primitive but `Tuple` returns its
/// leftmost atom argument without computing (sec:failure); `Tuple` stores atoms as data, and
/// only `match` inspects one.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Prim {
    /// `a + b` over two ints or two floats; also joins two strings.
    Add,
    /// `a - b`.
    Sub,
    /// `a * b`.
    Mul,
    /// Float division `a / b`.
    Div,
    /// Euclidean `a div b` over ints; `#divByZero` when `b` is 0 (sec:failure).
    IntDiv,
    /// Euclidean `a mod b` over ints, never negative; `#divByZero` when `b` is 0.
    Mod,
    /// `-a`.
    Neg,
    /// `a == b`, bitwise on floats.
    Eq,
    /// `a != b`.
    Ne,
    /// `a < b` in the total order of values.
    Lt,
    /// `a <= b`.
    Le,
    /// `a > b`.
    Gt,
    /// `a >= b`.
    Ge,
    /// `a && b` over bools.
    And,
    /// `a || b` over bools.
    Or,
    /// `!a`.
    Not,
    /// The smaller of two values.
    Min,
    /// The larger of two values.
    Max,
    /// `f[k]`: the entry of family `f` at top-level key `k`, or `#notFound`.
    Get,
    /// The number of top-level entries of a family.
    Count,
    /// The union of two families. A keypath both write must carry equal values, else it is
    /// a collision; on set families this is set union, the join of a reachability `fix`.
    Union,
    /// Builds a keypath value from its key arguments.
    Path,
    /// `p[i]`: key `i` of keypath `p`, counting from 0, or `#notFound`.
    PathKey,
    /// The number of keys of a keypath.
    PathLen,
    /// Builds a tuple from its arguments.
    Tuple,
    /// `t[i]`: component `i` of a tuple, counting from 0.
    TupleGet,
}

impl Prim {
    /// The number of arguments the primitive takes, or `None` when it takes any number.
    pub fn arity(self) -> Option<usize> {
        use Prim::*;
        match self {
            Neg | Not | Count | PathLen => Some(1),
            Path | Tuple => None,
            _ => Some(2),
        }
    }
}

/// A pattern of a `match` arm.
#[derive(Clone, PartialEq, Debug)]
pub enum Pattern {
    /// `_`, matching anything.
    Wild,
    /// A name, matching anything and binding it.
    Bind(Arc<str>),
    /// A literal, matching an equal value.
    Lit(Value),
    /// `#name(p, …)`, matching an atom of that name whose payload matches.
    Atom(Arc<str>, Vec<Pattern>),
    /// `(p, …)`, matching a tuple of that length.
    Tuple(Vec<Pattern>),
}

/// Where a `gen` loop tests its guard (sec:generations).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GuardPos {
    /// `while c { … }`: the guard reads the last committed frame before each step, so a
    /// guard that ends the loop commits nothing.
    Before,
    /// `{ … } while c`: the guard reads the frame just committed, so a guard that ends the
    /// loop does so after its frame is committed.
    After,
}

/// The evidence a `reindex` carries that its key map is injective (T-Reindex). The reference
/// evaluator checks the collision rule on every run whatever the witness, so the witness only
/// records which discharge the checker used.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Witness {
    /// Proved by the Presburger or residue reasoning of (sec:grouping).
    Residue,
    /// Taken from a named entry of the injectivity catalog.
    Catalog(Arc<str>),
}

/// The evidence of a `fix` (T-Fix): which instance of the least-fixed-point rule it is.
#[derive(Clone, PartialEq, Debug)]
pub enum FixKind {
    /// A lattice ascent: `x := join(x, step(x))` from the bottom `init` until nothing
    /// changes. The join is a binary function term, such as `Prim::Union` on sets.
    Lattice {
        /// The join of the lattice.
        join: Arc<Term>,
    },
    /// General recursion, the definedness instance: a partial family over the domain `init`,
    /// which starts undefined everywhere. Each round evaluates the body at every undefined
    /// key, and an entry whose body reads only defined entries becomes defined.
    Definedness,
}

/// A kernel term.
#[derive(Clone, PartialEq, Debug)]
pub enum Term {
    /// A literal value.
    Lit(Value),
    /// A variable.
    Var(Arc<str>),
    /// `(x, …) -> body`.
    Lam(Vec<Arc<str>>, Arc<Term>),
    /// `f(a, …)`, call by value, arguments evaluated left to right.
    App(Arc<Term>, Vec<Term>),
    /// A primitive applied to its arguments.
    Prim(Prim, Vec<Term>),
    /// A primitive as a function value, such as `(+)` passed to `fold`.
    PrimFn(Prim),
    /// `x = e; body`.
    Let(Arc<str>, Arc<Term>, Arc<Term>),
    /// `if c { a } else { b }`. A failure atom as the condition is the result.
    If(Arc<Term>, Arc<Term>, Arc<Term>),
    /// `match e { p -> t, … }`, first matching arm wins.
    Match(Arc<Term>, Vec<(Pattern, Term)>),
    /// `fam(D, i -> e)`: the family over the top-level keys of `D` whose entry at `i` is `e`.
    Fam {
        /// The domain, a family whose top-level keys are used.
        domain: Arc<Term>,
        /// The key variable.
        var: Arc<str>,
        /// The entry at each key.
        body: Arc<Term>,
    },
    /// `reindex(F, kf, vf)`: each leaf `(p, v)` of `F` moves to keypath `kf(p, v)` with value
    /// `vf(p, v)`. Two leaves landing on one keypath is a collision.
    Reindex {
        /// The family to rekey.
        family: Arc<Term>,
        /// `(path, value) -> path`.
        kf: Arc<Term>,
        /// `(path, value) -> value`.
        vf: Arc<Term>,
        /// The injectivity evidence.
        witness: Witness,
    },
    /// `discard(F, sel)`: walks `F` top down calling `sel(path, entry)` at each entry. `true`
    /// keeps the entry and descends into it, `false` drops it with its subtree, and
    /// `#boundary` keeps only the key, as a set leaf.
    Discard {
        /// The family to filter.
        family: Arc<Term>,
        /// `(path, entry) -> bool | #boundary`.
        sel: Arc<Term>,
    },
    /// `fold(F, op, ev)`: collapses the innermost level of `F` with the binary `op`.
    Fold {
        /// The family to fold.
        family: Arc<Term>,
        /// The binary operator.
        op: Arc<Term>,
        /// The identity, which is the result of folding an empty level; without one an
        /// empty level folds to `#empty`.
        identity: Option<Arc<Term>>,
    },
    /// `fix(F0, step, ev)`: the least fixed point of `step` above `F0`.
    Fix {
        /// The bottom for a lattice ascent, the domain for the definedness instance.
        init: Arc<Term>,
        /// For a lattice, a function from one iterate to the next. For definedness, the
        /// body of the entry at key `key`, which reads the partial family as `this`.
        step: Arc<Term>,
        /// The name the definedness body uses for the family being defined.
        this: Arc<str>,
        /// The name of the key variable in the definedness body.
        key: Arc<str>,
        /// Which instance of the rule.
        kind: FixKind,
    },
    /// `gen(init, step, guard)`: a loop over generations. The result is the family from
    /// generation number (0 for `init`) to committed frame; a guard result that is not a bool
    /// ends the loop and is stored as the entry after the last frame.
    Gen {
        /// Generation 0.
        init: Arc<Term>,
        /// `frame -> frame`: reads generation `t - 1`, returns generation `t`.
        step: Arc<Term>,
        /// `frame -> bool | atom`, `true` meaning go on.
        guard: Arc<Term>,
        /// Where the guard is tested.
        pos: GuardPos,
    },
    /// Reads the whole value of an input port.
    Read(Arc<str>),
    /// `p <- v`: pushes a value to an output port, giving its acknowledgment (T-Port).
    Push(Arc<str>, Arc<Term>),
}

/// Shorthands for building terms in tests and in the front end's elaboration.
pub mod build {
    use super::*;

    /// A variable.
    pub fn var(name: &str) -> Term {
        Term::Var(name.into())
    }

    /// A literal.
    pub fn lit(v: impl Into<Value>) -> Term {
        Term::Lit(v.into())
    }

    /// A lambda.
    pub fn lam(params: &[&str], body: Term) -> Term {
        Term::Lam(
            params.iter().map(|p| Arc::from(*p)).collect(),
            Arc::new(body),
        )
    }

    /// An application.
    pub fn app(f: Term, args: Vec<Term>) -> Term {
        Term::App(Arc::new(f), args)
    }

    /// A primitive applied to arguments.
    pub fn prim(p: Prim, args: Vec<Term>) -> Term {
        Term::Prim(p, args)
    }

    /// `x = e; body`.
    pub fn let_(name: &str, e: Term, body: Term) -> Term {
        Term::Let(name.into(), Arc::new(e), Arc::new(body))
    }

    /// `if c { a } else { b }`.
    pub fn if_(c: Term, a: Term, b: Term) -> Term {
        Term::If(Arc::new(c), Arc::new(a), Arc::new(b))
    }
}

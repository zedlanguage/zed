//! Kernel terms: Tier 0, a strict lambda calculus with data, and Tier 1, the seven
//! generators over families (DESIGN.md sec:kernel).
//!
//! Every surface form elaborates to a [`Term`]. Names are plain strings: the front end has
//! resolved scopes before a term is built, so a term never needs renaming.

use std::collections::BTreeMap;
use std::fmt;
use std::ops::Deref;
use std::sync::Arc;

use crate::deep;

mod walk;
use crate::types::Type;
use crate::value::Value;
use crate::value::{Id, fresh_id};
pub(crate) use walk::{Binds, Kid, kids, small};

/// A primitive operation. Applied to a failure atom, every primitive but `Tuple`, `Atom`,
/// `Eq` and `Ne` returns its leftmost atom argument without computing (sec:failure): a loose
/// atom selects no arrow. `Tuple` and `Atom` store atoms as data, and `==` and `!=` compare
/// them, having an arrow at every type (step L1.17).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Prim {
    /// `a + b` over two ints or two floats.
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
    /// `a == b`: structural, but two floats compare as IEEE 754 does ([`Value::surface_eq`]).
    Eq,
    /// `a != b`.
    Ne,
    /// `a < b` in the total order of values, two floats compared as IEEE 754 does.
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
    /// `a ++ b`, two strings joined. It is not `Add`, so no law of `+` (commutativity) is
    /// ever read as one of `++`.
    Concat,
    /// `a ^ b`: an int to a non-negative int power, or a float to a float power.
    Pow,
    /// Builds an atom: `atom("err", (), 1)` is `#err(1)` and `atom("err", ("code",), 3)` is
    /// `#err(code: 3)`. The first argument is the name, the second the field names of a
    /// struct payload, empty for a tuple payload, and the rest the payload's values.
    Atom,
    /// `String(x)`: a string as itself, any other value as it prints (step L1.18).
    Show,
    /// `int(x)`, the checked cast: exact, `#inexact`, or `#invalid` (DESIGN.md, "Casts are
    /// domain proofs").
    CastInt,
    /// `rat(x)`, the checked cast.
    CastRat,
    /// `f64(x)`, the checked cast; from a string it reads what `String` prints.
    CastF64,
    /// `abs(x)` of a number.
    Abs,
    /// `len(s)`, the number of Unicode scalars of a string.
    Len,
    /// `lower(s)`, Unicode lowercase.
    Lower,
    /// `upper(s)`, Unicode uppercase.
    Upper,
    /// `trim(s)`, without leading and trailing Unicode white space.
    Trim,
    /// `sum(t)`, the `+` of a tuple's components, `0` for the empty tuple.
    Sum,
    /// `bitAnd(a, b)`: the binary digits of two non-negative ints, and-ed (step L1.39a).
    BitAnd,
    /// `bitOr(a, b)`, or-ed.
    BitOr,
    /// `bitXor(a, b)`, exclusive-or-ed.
    BitXor,
    /// `bitNot(x, width: w)`: `2^w - 1 - x`, for `x` in `0 ..< 2^w`.
    BitNot,
    /// `shl(x, k)`: `x * 2^k`, for any int `x` and `k >= 0`.
    Shl,
    /// `shr(x, k)`: `x div 2^k`, Euclidean, for any int `x` and `k >= 0`.
    Shr,
    /// `popCount(x)`: the number of one digits of `x >= 0`.
    PopCount,
    /// `leadingZeros(x, width: w)`: `w` minus the number of binary digits of `x`.
    LeadingZeros,
    /// `trailingZeros(x, width: w)`: the zero digits below the lowest one digit; `w` for 0.
    TrailingZeros,
    /// `rotl(x, k, width: w)`: the `w` low digits of `x` rotated `k` places toward the high.
    Rotl,
    /// `rotr(x, k, width: w)`: rotated toward the low digits.
    Rotr,
    /// `f64Bits(x)`: the IEEE 754 binary64 encoding of a float, an int in `0 ..< 2^64`.
    F64Bits,
    /// `codePoint(s)`: the Unicode scalar value of a string of one scalar, an int in
    /// `0 ..= 1114111`; `#notScalar` for any other string (step L1.39c).
    CodePoint,
    /// `scalar(n)`: the string of the one scalar `n`; `#notScalar` for a surrogate or an `n`
    /// outside `0 ..= 1114111`.
    Scalar,
    /// `utf8(s)`: the family of the UTF-8 bytes of `s`, keyed by byte offset from 0.
    Utf8,
    /// `fromUtf8(b)`: the string the bytes of `b`, in key order, encode; `#badUtf8` when they
    /// are not well-formed UTF-8.
    FromUtf8,
    /// `mulHi(a, b, width: w)`: `shr(a * b, w)`, for `a` and `b` in `0 ..< 2^w`, the high half of
    /// the product (step L1.39f, DESIGN.md sec:linalg, machine operations).
    MulHi,
    /// `bitReverse(x, width: w)`: the `w` low digits of `x` in reverse order.
    BitReverse,
    /// `byteSwap(x, width: w)`, `w` a multiple of 8: the `w / 8` low bytes of `x` in reverse order.
    ByteSwap,
    /// `pdep(x, mask)`: the low digits of `x` deposited at the one digits of `mask`, lowest first.
    Pdep,
    /// `pext(x, mask)`: the digits of `x` at the one digits of `mask`, gathered into the low
    /// digits.
    Pext,
    /// `funnelShl(hi, lo, k, width: w)`: the high `w` digits of the `2w` digits `hi * 2^w + lo`
    /// shifted `k` places toward the high, for `k` in `0 ..< w`.
    FunnelShl,
    /// `funnelShr(hi, lo, k, width: w)`: the low `w` digits of `hi * 2^w + lo` shifted `k` places
    /// toward the low.
    FunnelShr,
    /// `v[k]` at a read the checker proved is of a family whose keys are one integer interval,
    /// every key present: the entry at `k`, or `#outOfBounds` (DESIGN.md sec:type_language, the
    /// `m[k]` row); on a tuple, `TupleGet`.
    At,
}

impl Prim {
    /// The number of arguments the primitive takes, or `None` when it takes any number.
    pub fn arity(self) -> Option<usize> {
        use Prim::*;
        match self {
            Neg | Not | Count | PathLen | Show | CastInt | CastRat | CastF64 | Abs | Len
            | Lower | Upper | Trim | Sum | PopCount | F64Bits | CodePoint | Scalar | Utf8
            | FromUtf8 => Some(1),
            Rotl | Rotr | MulHi => Some(3),
            FunnelShl | FunnelShr => Some(4),
            Path | Tuple | Atom => None,
            _ => Some(2),
        }
    }

    /// The fixed number of the primitive, by which the canonical serialization writes it.
    /// Each number is assigned here and never changes, so that renaming a variant, reordering
    /// the enum, or adding a primitive leaves every other primitive's number, and with it every
    /// canonical address, as it was; a new primitive takes the next unused number. The numbers
    /// are the positions of the ZIR binary form's list, `zedc::zir::text::PRIMS`.
    pub fn code(self) -> u64 {
        use Prim::*;
        match self {
            Add => 0,
            Sub => 1,
            Mul => 2,
            Div => 3,
            IntDiv => 4,
            Mod => 5,
            Neg => 6,
            Eq => 7,
            Ne => 8,
            Lt => 9,
            Le => 10,
            Gt => 11,
            Ge => 12,
            And => 13,
            Or => 14,
            Not => 15,
            Min => 16,
            Max => 17,
            Get => 18,
            Count => 19,
            Union => 20,
            Path => 21,
            PathKey => 22,
            PathLen => 23,
            Tuple => 24,
            TupleGet => 25,
            Concat => 26,
            Pow => 27,
            Atom => 28,
            Show => 29,
            CastInt => 30,
            CastRat => 31,
            CastF64 => 32,
            Abs => 33,
            Len => 34,
            Lower => 35,
            Upper => 36,
            Trim => 37,
            Sum => 38,
            BitAnd => 39,
            BitOr => 40,
            BitXor => 41,
            BitNot => 42,
            Shl => 43,
            Shr => 44,
            PopCount => 45,
            LeadingZeros => 46,
            TrailingZeros => 47,
            Rotl => 48,
            Rotr => 49,
            F64Bits => 50,
            CodePoint => 51,
            Scalar => 52,
            Utf8 => 53,
            FromUtf8 => 54,
            MulHi => 55,
            BitReverse => 56,
            ByteSwap => 57,
            Pdep => 58,
            Pext => 59,
            FunnelShl => 60,
            FunnelShr => 61,
            At => 62,
        }
    }
}

/// A pattern of a `match` arm.
pub enum Pattern {
    /// `_`, matching anything.
    Wild,
    /// A name, matching anything and binding it.
    Bind(Arc<str>),
    /// A literal, matching an equal value.
    Lit(Value),
    /// `#name(p, …)`, matching an atom of that name whose tuple payload matches.
    Atom(Arc<str>, Vec<Pattern>),
    /// `#name(f: p, …)`, matching an atom of that name with a struct payload that has each
    /// field named, its value matching; the payload may have other fields.
    Fields(Arc<str>, Vec<(Arc<str>, Pattern)>),
    /// `(p, …)`, matching a tuple of that length.
    Tuple(Vec<Pattern>),
    /// `#_`, any atom, its payload included: the arm `else` and `?.` write for the atom
    /// members of a value until its type enumerates them (DESIGN.md, step L1.16).
    AnyAtom,
    /// `x is T` as a pattern: a value of the type `T`, which is decidable (step L1.22).
    Is(Type),
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

/// How strongly a tracked property is established (DESIGN.md sec:property_tracking), in the
/// order of that section: `Axiom > CheckedExhaustive | Proved > Bounded > Obligated > Assumed`,
/// the two in the middle incomparable. A property derived by the derivation rules has the meet
/// of its premises' grades, and that meet is what a record holds; the rule and the premises are
/// the property tracker's to keep.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Grade {
    /// A built-in's law, such as `+` on exact numerics being associative.
    Axiom,
    /// Checked over the whole of a small finite domain at compile time.
    CheckedExhaustive,
    /// A certificate the independent checker accepted.
    Proved,
    /// Checked up to a bound (rung 6 of the discharge ladder).
    Bounded,
    /// Emitted as a generated property test bound to the definition.
    Obligated,
    /// Waived by `@assume`.
    Assumed,
}

impl Grade {
    /// Whether the grade is proof grade, the grades that may change a type.
    pub fn is_proof_grade(self) -> bool {
        matches!(
            self,
            Grade::Axiom | Grade::CheckedExhaustive | Grade::Proved
        )
    }
}

/// The evidence record `ev` of a `fold` or a `fix`: each tracked property established, with
/// its grade. A property absent is unknown. `fold` reads the Boom row (`associative`,
/// `commutative`, `idempotent`), `fix` reads `monotone`, `inflationary` and the ACC fact.
pub type Evidence = BTreeMap<Arc<str>, Grade>;

/// The evidence of a `fix` (T-Fix): which instance of the least-fixed-point rule it is.
#[derive(Clone, PartialEq, Debug)]
pub enum FixKind {
    /// A lattice ascent: `x := join(x, step(x))` from the bottom `init` until nothing
    /// changes. The join is a binary function term, such as `Prim::Union` on sets.
    Lattice {
        /// The join of the lattice.
        join: Shared,
    },
    /// General recursion, the definedness instance: a partial family over the domain `init`,
    /// which starts undefined everywhere. Each round evaluates the body at every undefined
    /// key, and an entry whose body reads only defined entries becomes defined.
    Definedness,
}

/// A subterm, shared: a copy is a reference count. It carries the id it was given when it was
/// built: copies share it, no other subterm has it, and a subterm changed in place
/// ([`Shared::make_mut`]) takes a new one. So a walk that meets a shared subterm again knows it
/// by its id (memo keys are ids or structure, never addresses), the way [`crate::Items`] and
/// [`crate::Family`] are known by theirs. The id does not change what the term means: equality,
/// `Debug` and every evaluation read the term alone.
#[derive(Clone)]
pub struct Shared(Arc<Held>);

#[derive(Clone)]
struct Held {
    id: Id,
    term: Term,
}

impl Shared {
    /// `t`, shared, with a new id.
    pub fn new(t: Term) -> Shared {
        Shared(Arc::new(Held {
            id: fresh_id(),
            term: t,
        }))
    }

    /// The id of the subterm: copies share it, and no other subterm has it. Ids are only
    /// compared; no result may depend on their values.
    pub fn id(&self) -> u64 {
        self.0.id
    }

    /// The term, to change in place: copied first when another holder shares it. Either way it
    /// takes a new id, since what the old id named is no longer this term.
    pub fn make_mut(this: &mut Shared) -> &mut Term {
        let held = Arc::make_mut(&mut this.0);
        held.id = fresh_id();
        &mut held.term
    }

    /// The term, moved out when `this` is its only holder, else copied.
    pub fn unwrap_or_clone(this: Shared) -> Term {
        Arc::unwrap_or_clone(this.0).term
    }

    /// The number of holders of the subterm.
    pub fn strong_count(this: &Shared) -> usize {
        Arc::strong_count(&this.0)
    }

    /// The term, when `this` is its only holder (only to free it).
    fn get_mut(this: &mut Shared) -> Option<&mut Term> {
        Arc::get_mut(&mut this.0).map(|h| &mut h.term)
    }
}

impl Deref for Shared {
    type Target = Term;

    fn deref(&self) -> &Term {
        &self.0.term
    }
}

impl AsRef<Term> for Shared {
    fn as_ref(&self) -> &Term {
        &self.0.term
    }
}

impl From<Term> for Shared {
    fn from(t: Term) -> Shared {
        Shared::new(t)
    }
}

impl PartialEq for Shared {
    fn eq(&self, other: &Shared) -> bool {
        self.0.id == other.0.id || self.0.term == other.0.term
    }
}

impl fmt::Debug for Shared {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0.term, f)
    }
}

impl fmt::Display for Shared {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0.term, f)
    }
}

/// A kernel term.
pub enum Term {
    /// A literal value.
    Lit(Value),
    /// A variable.
    Var(Arc<str>),
    /// `(x, …) -> body`.
    Lam(Vec<Arc<str>>, Shared),
    /// `f(a, …)`, call by value, arguments evaluated left to right.
    App(Shared, Vec<Term>),
    /// A primitive applied to its arguments.
    Prim(Prim, Vec<Term>),
    /// A primitive as a function value, such as `(+)` passed to `fold`.
    PrimFn(Prim),
    /// `x = e; body`.
    Let(Arc<str>, Shared, Shared),
    /// `if c { a } else { b }`. A failure atom as the condition is the result.
    If(Shared, Shared, Shared),
    /// `match e { p -> t, … }`, first matching arm wins.
    Match(Shared, Vec<(Pattern, Term)>),
    /// `fam(D, i -> e)`: the family over the top-level keys of `D` whose entry at `i` is `e`.
    Fam {
        /// The domain, a family whose top-level keys are used.
        domain: Shared,
        /// The key variable.
        var: Arc<str>,
        /// The entry at each key.
        body: Shared,
    },
    /// `reindex(F, kf, vf)`: each leaf `(p, v)` of `F` moves to keypath `kf(p, v)` with value
    /// `vf(p, v)`. Two leaves landing on one keypath is a collision.
    Reindex {
        /// The family to rekey.
        family: Shared,
        /// `(path, value) -> path`.
        kf: Shared,
        /// `(path, value) -> value`.
        vf: Shared,
        /// The injectivity evidence.
        witness: Witness,
    },
    /// `discard(F, sel)`: walks `F` top down calling `sel(path, entry)` at each entry. `true`
    /// keeps the entry and descends into it, `false` drops it with its subtree, and
    /// `#boundary` keeps only the key, as a set leaf.
    Discard {
        /// The family to filter.
        family: Shared,
        /// `(path, entry) -> bool | #boundary`.
        sel: Shared,
    },
    /// `fold(F, op, ev)`: collapses the innermost level of `F` with the binary `op`.
    Fold {
        /// The family to fold.
        family: Shared,
        /// The binary operator.
        op: Shared,
        /// The identity, which is the result of folding an empty level; without one an
        /// empty level folds to `#empty`.
        identity: Option<Shared>,
        /// The number of key levels of `family`, at least 1, which its type gives. A family
        /// with no leaves does not show its depth, and folds to the empty family when the
        /// depth is above 1.
        depth: usize,
        /// The evidence for `op`, which the reduction checker reads (T-Fold).
        ev: Evidence,
    },
    /// `fix(F0, step, ev)`: the least fixed point of `step` above `F0`.
    Fix {
        /// The bottom for a lattice ascent, the domain for the definedness instance.
        init: Shared,
        /// For a lattice, a function from one iterate to the next. For definedness, the
        /// body of the entry at key `key`, which reads the partial family as `this`.
        step: Shared,
        /// The name the definedness body uses for the family being defined.
        this: Arc<str>,
        /// The name of the key variable in the definedness body.
        key: Arc<str>,
        /// Which instance of the rule.
        kind: FixKind,
        /// The evidence for `step`, which T-Fix reads.
        ev: Evidence,
    },
    /// `gen(init, step, guard)`: a loop over generations. The result is the family from
    /// generation number (0 for `init`) to committed frame; a guard result that is not a bool
    /// ends the loop and is stored as the entry after the last frame.
    Gen {
        /// Generation 0.
        init: Shared,
        /// `frame -> frame`: reads generation `t - 1`, returns generation `t`.
        step: Shared,
        /// `frame -> bool | atom`, `true` meaning go on.
        guard: Shared,
        /// Where the guard is tested.
        pos: GuardPos,
    },
    /// Reads the whole value of an input port.
    Read(Arc<str>),
    /// `p <- v`: pushes a value to an output port, giving its acknowledgment (T-Port).
    Push(Arc<str>, Shared),
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
            Shared::new(body),
        )
    }

    /// An application.
    pub fn app(f: Term, args: Vec<Term>) -> Term {
        Term::App(Shared::new(f), args)
    }

    /// A primitive applied to arguments.
    pub fn prim(p: Prim, args: Vec<Term>) -> Term {
        Term::Prim(p, args)
    }

    /// `x = e; body`.
    pub fn let_(name: &str, e: Term, body: Term) -> Term {
        Term::Let(name.into(), Shared::new(e), Shared::new(body))
    }

    /// `if c { a } else { b }`.
    pub fn if_(c: Term, a: Term, b: Term) -> Term {
        Term::If(Shared::new(c), Shared::new(a), Shared::new(b))
    }
}

/// A part of a term or pattern whose owner is being dropped (module `deep`): a term nested deep
/// is freed in a loop, on any stack.
#[expect(dead_code, reason = "a part is held only to be dropped")]
enum Freed {
    Term(Term),
    Shared(Shared),
    Terms(Vec<Term>),
    Arms(Vec<(Pattern, Term)>),
    Patterns(Vec<Pattern>),
    Fields(Vec<(Arc<str>, Pattern)>),
}

thread_local! {
    /// The parts of terms and patterns waiting to be dropped.
    static FREED: deep::Queue<Freed> = const { deep::Queue::new() };
    /// What a shared subterm still held elsewhere leaves in its place when it is queued.
    static HOLE: Shared = Shared::new(Term::PrimFn(Prim::Tuple));
}

fn free(part: Freed) {
    deep::free_in(&FREED, part);
}

/// Queues the term `t` holds, when `t` is its last owner, and otherwise `t` itself: a subterm
/// that one term holds in several places, as a DAG does, or that another thread lets go of at
/// the same moment, is freed by the queue when its last holder there lets go, not by this
/// term's own drop recursing into it.
fn free_shared(t: &mut Shared) {
    if let Some(t) = Shared::get_mut(t) {
        free(Freed::Term(std::mem::replace(t, Term::PrimFn(Prim::Tuple))));
    } else if let Ok(hole) = HOLE.try_with(Shared::clone) {
        free(Freed::Shared(std::mem::replace(t, hole)));
    }
}

fn free_terms(ts: &mut Vec<Term>) {
    if !ts.is_empty() {
        free(Freed::Terms(std::mem::take(ts)));
    }
}

/// A term's parts are freed in a loop, not by recursion.
impl Drop for Term {
    fn drop(&mut self) {
        match self {
            Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => {}
            Term::Lam(_, b) | Term::Push(_, b) => free_shared(b),
            Term::App(f, args) => {
                free_shared(f);
                free_terms(args);
            }
            Term::Prim(_, args) => free_terms(args),
            Term::Let(_, a, b) | Term::Discard { family: a, sel: b } => {
                free_shared(a);
                free_shared(b);
            }
            Term::Fam { domain, body, .. } => {
                free_shared(domain);
                free_shared(body);
            }
            Term::If(a, b, c)
            | Term::Reindex {
                family: a,
                kf: b,
                vf: c,
                ..
            }
            | Term::Gen {
                init: a,
                step: b,
                guard: c,
                ..
            } => {
                free_shared(a);
                free_shared(b);
                free_shared(c);
            }
            Term::Match(e, arms) => {
                free_shared(e);
                if !arms.is_empty() {
                    free(Freed::Arms(std::mem::take(arms)));
                }
            }
            Term::Fold {
                family,
                op,
                identity,
                ..
            } => {
                free_shared(family);
                free_shared(op);
                if let Some(i) = identity {
                    free_shared(i);
                }
            }
            Term::Fix {
                init, step, kind, ..
            } => {
                free_shared(init);
                free_shared(step);
                match kind {
                    FixKind::Lattice { join } => free_shared(join),
                    FixKind::Definedness => {}
                }
            }
        }
    }
}

/// A pattern's parts are freed in a loop, as a term's are.
impl Drop for Pattern {
    fn drop(&mut self) {
        match self {
            Pattern::Wild
            | Pattern::Bind(_)
            | Pattern::Lit(_)
            | Pattern::AnyAtom
            | Pattern::Is(_) => {}
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => {
                if !ps.is_empty() {
                    free(Freed::Patterns(std::mem::take(ps)));
                }
            }
            Pattern::Fields(_, fs) => {
                if !fs.is_empty() {
                    free(Freed::Fields(std::mem::take(fs)));
                }
            }
        }
    }
}

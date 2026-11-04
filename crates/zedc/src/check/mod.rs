//! The checker (step L1.26): resolution rules 1, 3 and 4 of DESIGN.md "Resolution". Each
//! node is typed bottom up; an `is` test narrows the name it tests in each branch it guards;
//! each declared function gets a signature from its body. A numeric literal adopts the
//! carrier an operator or a parameter expects, exactly or not at all (sec:domains). A lambda
//! in a slot of function type takes its parameter types and kinds from that type, and a
//! declared function passed there must have its parameter kinds.
//!
//! A function's parameter with neither a type nor a closed default is inferred, with the body
//! checked once (docs/thresholds.md, replacement 1). The parameter's values form a class, a
//! node of a union-find forest, holding the carriers it may still take. A use that needs two
//! values to share a carrier, as the operands of `+` do, merges their classes; a use that
//! accepts some carriers removes the rest; a literal joins the class it meets. Each step only
//! merges classes or removes carriers, so the solution is reached by propagation with no
//! search. When the function ends, each class of its parameters takes its type: the first of
//! int, f64 and rat if it holds a literal, which then adopts it; a type variable if it may
//! take any value; its one carrier; a type variable bounded by its carriers if several; and an
//! error if none, listing every use that removed one.
//!
//! A use of a value whose type is a type variable is a need of the signature, checked again at
//! each call on the type the call binds the variable to, so `first(p) = p[0]` is generic and a
//! non-tuple argument is rejected at the call. `_` is the type of every value: it passes only
//! where any value is accepted (DESIGN.md "Soundness").
//!
//! An atom passes through the operators and the prelude words, as the kernel's primitives
//! pass it, and through a declared function whose parameter's type omits it (rule 6 of
//! sec:type_resolution). An undeclared parameter's type holds the atoms its uses handle, so
//! `r(positional line) = trim(line else "")` is `(String | #_) -> String`: a call passing
//! `#notFound` runs the body, whose `else` replaces it. Where DESIGN.md does not say: a call
//! matching several arrows takes the first one's result.
//!
//! Step L1.27: an atom of a named family is data (sec:failure). `else` strips only the loose
//! atoms, and a family atom that selects no arrow is an error, where a loose one flows on.

pub mod read;
pub mod ty;
pub mod widen;

mod walk;

use std::borrow::Cow;
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;

use zed_kernel::types::{Type as KType, Verdict};
use zed_kernel::{Prim, Rat, Term, Universe, Value, eval};

use crate::ast::{
    Error, Every, Expr, ExprKind, Function, Note, Param, Pattern, Stmt, StmtKind, StrPart, Target,
    Type, TypeKind,
};
use crate::elab::Tables;
use crate::lex::Span;
use crate::rejection::Row;
use crate::resolve::{Handle, Ref, Resolution};
use crate::store::int::Int;
use crate::store::interval::{
    End::{self, Fin, NegInf, PosInf},
    IntervalSet, Num, bit_word,
};
use crate::store::revision::{Op, forward};

use ty::{
    Arrow, Binds, Carrier, EVERY, Need, NeedKind, OTHER, Piece, SParam, Shape, Sig, Slot, Ty,
    VarFacts, Vars, atoms, errs, mask_text,
};

/// How a function argument fits the function type its slot expects.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fit {
    /// A lambda: for each parameter of the expected type, the lambda's parameter that takes
    /// it, if any; and the lambda's parameters the type does not pass, each filled by its
    /// default.
    Lambda {
        /// The lambda parameter for each parameter of the type.
        order: Vec<Option<usize>>,
        /// The lambda parameters filled by their defaults.
        extra: Vec<usize>,
    },
    /// A declared function whose named parameters are in another order: for each of its
    /// parameters, the index of the type's parameter that fills it.
    Adapter {
        /// The type's parameter for each of the function's.
        from: Vec<usize>,
    },
}

/// Why a call's arguments do not fill its function's parameters. The checker and
/// elaboration both report these, each from its own pass over the arguments, with the
/// message and row given here, so that the two agree on every call.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Misfit<'s> {
    /// A receiver for a function of no parameters.
    NoReceiver,
    /// A positional argument after the parameters run out; the function takes this many.
    TooMany(usize),
    /// A positional argument for this named parameter.
    Named(&'s str),
    /// A named argument for this positional parameter.
    Positional(&'s str),
    /// A named argument of a name no parameter has.
    NoParam(&'s str),
    /// A named argument for a parameter already filled.
    Supplied(&'s str),
    /// A `...` call that leaves out this positional parameter.
    CurriedPositional(&'s str),
    /// A `...` call that leaves out no parameter.
    NothingLeftOut,
    /// A saturated call that leaves out this parameter, which has no default.
    Missing(&'s str),
    /// A call through a value that leaves out this parameter, whose default reads the other
    /// parameters.
    OpenDefault(&'s str),
}

impl Misfit<'_> {
    /// The row of the rejection table the misfit is a case of, if any.
    pub(crate) fn row(self) -> Option<Row> {
        match self {
            Misfit::NoReceiver | Misfit::TooMany(_) | Misfit::NoParam(_) | Misfit::Supplied(_) => {
                None
            }
            Misfit::Named(_) | Misfit::Positional(_) => Some(Row::WrongForm),
            Misfit::CurriedPositional(_) | Misfit::NothingLeftOut => Some(Row::NothingLeftOut),
            Misfit::Missing(_) | Misfit::OpenDefault(_) => Some(Row::MissingArgument),
        }
    }

    /// The message, for the function called `who`.
    pub(crate) fn message(self, who: &str) -> String {
        match self {
            Misfit::NoReceiver => format!("`{who}` has no parameter for a receiver"),
            Misfit::TooMany(n) => format!("too many arguments: `{who}` takes {n}"),
            Misfit::Named(name) => format!("`{name}` of `{who}` is named: pass it as `{name}: …`"),
            Misfit::Positional(name) => {
                format!("`{name}` of `{who}` is positional: pass it by position")
            }
            Misfit::NoParam(name) => format!("`{who}` has no parameter `{name}`"),
            Misfit::Supplied(name) => format!("`{name}` is already supplied"),
            Misfit::CurriedPositional(name) => {
                format!("`...` curries named parameters only; the positional `{name}` is left out")
            }
            Misfit::NothingLeftOut => "`...` leaves no named parameter out".into(),
            Misfit::Missing(name) => format!("missing argument `{name}` of `{who}`"),
            Misfit::OpenDefault(name) => format!(
                "the default of `{name}` reads the function's other parameters, so only a call \
                 of the declared function fills it: pass `{name}`"
            ),
        }
    }
}

/// What the checker finds.
#[derive(Clone, Debug, Default)]
pub struct Info {
    /// The value each adopted literal takes, by its span, before any `-`.
    pub adopt: HashMap<Span, Value>,
    /// The signature of the function called through a value, by the call's span.
    pub calls: HashMap<Span, Arc<Sig>>,
    /// The fit of each function argument that needs one, by its span.
    pub fits: HashMap<Span, Fit>,
    /// Each declared function's signature, by its binder.
    pub sigs: BTreeMap<usize, Arc<Sig>>,
    /// The type of each top-level name bound by `=` (step L1.37).
    pub tops: HashMap<String, Ty>,
    /// For each call of a function, the arguments whose loose atoms its parameter does not
    /// take: an atom there selects no arrow and is the call's value (rule 6 of
    /// sec:type_resolution), by the call's span and the arguments' spans.
    pub passes: HashMap<Span, Vec<(Span, KType)>>,
    /// For each `*`, whether `/` is defined wherever the checker typed it: each type it gave
    /// the product holds no `int` (step L25.8, the `*` to `/` mutant).
    pub quotients: HashMap<Span, bool>,
    /// Each literal compared by `==` or `!=` with a class that became a type variable, and each
    /// generic literal `kn` operand of an operator in such a class (L1.26a), by its span: the
    /// value it takes at each other numeric carrier of the variable's bound that it adopts
    /// exactly, after any `-`. The comparison adopts at run time the carrier of the
    /// other operand (DESIGN.md L1.26, "a literal compared by `==` with a class takes the
    /// class's carrier"), as does the operator of a generic literal; at any other value the
    /// literal keeps its own.
    pub follows: HashMap<Span, Vec<(Carrier, Value)>>,
    /// Each generic literal of [`Self::follows`] that has no other operand to take its carrier
    /// from, by its span: a call's argument, an `if` branch, an operand of an operator whose
    /// other operand is generic too (L1.26a). Its value is the binder of a parameter of the
    /// literal's class in scope at it, whose value has the class's carrier at run time.
    pub witness: HashMap<Span, usize>,
    /// The type errors.
    pub errors: Vec<Error>,
}

/// Checks a resolved unit.
pub fn check(unit: &[Stmt], res: &Resolution) -> Info {
    check_with(&Tables::new(unit, res), unit)
}

pub(crate) fn check_with<'a>(t: &Tables<'a>, unit: &'a [Stmt]) -> Info {
    KType::forget_emptiness();
    let mut ck = Ck::new(t);
    ck.bounds();
    ck.walk(unit);
    ck.finish();
    ck.info
        .errors
        .sort_by(|a, b| (a.span, &a.message).cmp(&(b.span, &b.message)));
    ck.info.errors.dedup();
    ck.info
}

/// The type of the binary operator `op` applied to arguments of the types `args`, with the
/// errors the application reports: how an operator treats loose and family atoms.
pub fn operator(op: &str, args: &[Ty]) -> (Ty, Vec<String>) {
    let res = crate::resolve::resolve(&[]).expect("the empty unit resolves");
    let t = Tables::new(&[], &res);
    let mut ck = Ck::new(&t);
    let args = args.iter().map(|a| Some(Arg::of(a.clone()))).collect();
    let (out, _) = ck.apply(
        &format!("`{op}`"),
        &op_sig(op),
        args,
        true,
        Span { start: 0, end: 0 },
    );
    (out, ck.info.errors.into_iter().map(|e| e.message).collect())
}

/// The two operands of `==` that [`Ck::equal`] pairs, built before a scaling test, so that
/// the test times the pairing alone and not the check of the program around it: a value of
/// the type `x`, and the expression `e`, of the type `et`, with the literals written in it.
#[doc(hidden)]
pub struct Operands {
    x: Ty,
    e: Expr,
    et: Ty,
}

impl Operands {
    #[doc(hidden)]
    pub fn new(x: Ty, e: Expr, et: Ty) -> Self {
        Operands { x, e, et }
    }

    /// Pairs the operands as `x == e` does, in a checker of the empty unit, and gives the
    /// number of literals that adopt a carrier.
    #[doc(hidden)]
    pub fn adoptions(&self) -> usize {
        let res = crate::resolve::resolve(&[]).expect("the empty unit resolves");
        let t = Tables::new(&[], &res);
        let mut ck = Ck::new(&t);
        let (lit, parts) = (literal(&self.e), parts(&self.e));
        let y = (vec![&self.et], lit.as_ref(), parts.as_deref());
        ck.pair((vec![&self.x], None, None), y);
        ck.info.adopt.len()
    }
}

/// A numeric literal: its span, its value, whether a `-` is applied to it, its text, whether
/// it is written with the suffix `n`, whether it is generic (step L1.26a): written `kn` where
/// it joins a class other than under `==` and `!=`, and whether, generic, it has no other
/// operand to take its carrier from at run time and takes it from a parameter of its class
/// ([`Info::witness`]). Where it joins no class, a `kn` is read as `k`.
#[derive(Clone)]
struct Lit {
    span: Span,
    value: Value,
    neg: bool,
    text: String,
    n: bool,
    generic: bool,
    witness: bool,
}

impl Lit {
    /// The literal as it joins a class with no other operand: generic, taking its carrier
    /// from a parameter of the class, if it is written `kn`.
    fn joining(&self) -> Lit {
        Lit {
            generic: self.n,
            witness: self.n,
            ..self.clone()
        }
    }
}

/// An argument: its type, the literal it is, if it is one, the expression it is, if any, and
/// the literals written in it, by component, if it is a tuple that holds one at any depth.
#[derive(Clone)]
struct Arg {
    ty: Ty,
    lit: Option<Lit>,
    at: Option<Span>,
    parts: Option<Rc<[Part]>>,
}

impl Arg {
    fn of(ty: Ty) -> Arg {
        Arg {
            ty,
            lit: None,
            at: None,
            parts: None,
        }
    }
}

/// A component of a tuple argument as written: a numeric literal, a tuple holding one at
/// some depth, or anything else. A literal in a tuple adopts the carrier the type its tuple
/// meets gives its component, as a literal argument adopts its parameter's.
#[derive(Clone)]
enum Part {
    Lit(Lit),
    Tuple(Rc<[Part]>),
    Other,
}

/// An argument of a call: an expression, or an argument already found, as when a use the
/// body of a generic function makes is checked again at a call of the function.
#[derive(Clone)]
enum ArgSrc<'a> {
    Expr(&'a Expr),
    Got(Box<Arg>),
}

/// Facts an `is` test makes: binders narrowed to a type, and the test.
type Facts = Vec<(usize, Ty, Span)>;

/// Where an expression's type comes from, for a derivation (DESIGN.md "Diagnostics").
#[derive(Clone)]
enum Src<'a> {
    /// A name, by its binder.
    Name(usize),
    /// A call of a declared function, by its binder, and the call.
    Call(usize, &'a Expr),
    /// Anything else: its parts' derivations continue it.
    Other(&'a Expr),
}

/// An expression's type as the checker last found it, and where it comes from. A tuple written
/// out keeps no type of its own: its type is its components' as last found ([`Ck::tuple_seen`]),
/// so a tuple nested d deep keeps O(d) and not a copy of each level's type.
type Seen<'a> = (Option<Ty>, Src<'a>);

/// A call's callee as [`Ck::called`] finds it: the function, and a method call's receiver with
/// whether it is `?.`.
type Called<'e> = (Arc<Sig>, Option<(&'e Expr, bool)>);

/// Where a binder's type comes from: what it says, the expression whose derivation continues
/// it, and the origin it narrows. A narrowing shares the origin it narrows, so narrowing a
/// binder costs one origin however many tests already narrow it. What it says is kept as data
/// and put into words only by a derivation that reaches it (step L1.39b), since a derivation
/// is built only for a rejection that is reported.
struct Origin<'a> {
    span: Span,
    why: Why<'a>,
    from: Option<Span>,
    then: Option<Rc<Origin<'a>>>,
}

/// What an origin says of its binder, `b` below.
enum Why<'a> {
    /// `b` is a function declared with this signature.
    Declared(Arc<Sig>),
    /// `b` is defined as an expression of this type.
    Defined(Ty),
    /// `b` is this component of a tuple, of this type.
    Component(usize, Ty),
    /// `b` is an output port.
    Port,
    /// `b` is a parameter declared with this type, whose values the checker does not track.
    Untracked(&'a Type),
    /// `b` is a parameter declared with this type, which the checker takes as the given one.
    Typed(&'a Type, Ty, Masks),
    /// `b` is a parameter of this type, the carrier of its default.
    Default(Ty),
    /// `b` is a parameter with no declared type, given this class.
    Untyped(usize),
    /// `b` is narrowed to this type by a test.
    Narrowed(Ty),
}

/// The carriers each class in a type was narrowed to when an origin was recorded: what
/// [`Ck::show`] reads of the classes, kept so that a derivation printed later shows the type
/// as it was then.
type Masks = Vec<(Arc<str>, u8)>;

/// `t` shown with each class of `masks`, a variable of `t` with its carriers, shown as the
/// union of those carriers.
fn show_with(t: &Ty, masks: &Masks) -> String {
    if masks.is_empty() {
        return t.to_string();
    }
    let mut rest = t.clone();
    let mut parts = Vec::new();
    let mut narrowed = 0;
    for (v, m) in masks {
        parts.push(mask_text(*m));
        narrowed |= m;
        rest.vars.remove(v);
    }
    if !rest.is_empty() {
        parts.push(rest.to_string());
    }
    let text = parts.join(" | ");
    #[cfg(feature = "printed-types")]
    {
        let carriers: Vec<Ty> = Carrier::of_mask(narrowed).map(Ty::carrier).collect();
        ty::printed::record(&rest.union(&Ty::union_all(&carriers)), &text);
    }
    #[cfg(not(feature = "printed-types"))]
    let _ = narrowed;
    text
}

/// A use that removed carriers from a class, kept as data until a reported rejection lists
/// it: where, what it is, and the carriers it takes, `None` for a merge.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Reason {
    span: Span,
    what: Box<str>,
    takes: Option<u8>,
}

impl Reason {
    fn note(&self) -> Note {
        built(1);
        let text = match self.takes {
            Some(m) => format!("{} takes {}", self.what, mask_text(m)),
            None => format!("{} gives these values one carrier", self.what),
        };
        Note {
            span: self.span,
            text,
        }
    }
}

thread_local! {
    /// The parts of derivations built on this thread since [`derivation_steps`] last read
    /// it: each expression a derivation walks and each premise put into words.
    static DERIVED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

fn built(k: u64) {
    DERIVED.with(|c| c.set(c.get() + k));
}

/// The parts of derivations built on this thread since the last call, which resets the
/// count: each expression a derivation walked and each premise put into words. A check whose
/// rejections are not reported builds none (step L1.39b).
pub fn derivation_steps() -> u64 {
    DERIVED.replace(0)
}

/// A chain of narrowings is as long as the tests nest, so its origins are dropped in a loop,
/// each one whose last holder this is.
impl Drop for Origin<'_> {
    fn drop(&mut self) {
        let mut next = self.then.take();
        while let Some(o) = next {
            next = match Rc::try_unwrap(o) {
                Ok(mut o) => o.then.take(),
                Err(_) => None,
            };
        }
    }
}

/// A class of values that must share one carrier: a node of the union-find forest of
/// docs/thresholds.md, replacement 1. Only a root's fields other than `parent` and `rank`
/// are read.
#[derive(Clone)]
struct Class {
    parent: usize,
    rank: u8,
    /// The carriers it may still take, and [`OTHER`] if it may take other values.
    mask: u8,
    /// The depth of the function whose parameter made it; of a merged class, the least.
    level: usize,
    /// The literals that joined it, each with whether it follows: a follower adopts the
    /// class's carrier but does not restrict it.
    lits: Vec<(Lit, bool)>,
    /// The uses that removed carriers from it.
    reasons: Vec<Reason>,
    /// Its type, once the function of its level ends.
    resolved: Option<Ty>,
    /// The name it is shown by, if it is a type variable of the function of its level, which
    /// ended: `resolved` is then its own variable `$k`, and it is a class no more.
    name: Option<Arc<str>>,
    /// What uses of its values need of them, each numbered in the order of all needs.
    uses: Vec<(usize, Need)>,
    /// The tuples and functions that flowed into it, each with where: every use is checked
    /// on each.
    flowed: Vec<(Ty, Span)>,
    /// A parameter of the class whose value has the class's carrier at run time, if any:
    /// its binder and the body it is in scope in; of a merged class, the outer one where one
    /// body holds the other.
    binder: Option<(usize, Span)>,
    /// Whether its values are those of generic literals only, as of `1n + 1n`: of a merged
    /// class, whether both were. An `if` merges it with the class of its other branch.
    generic: bool,
}

struct Ck<'t, 'a> {
    t: &'t Tables<'a>,
    env: HashMap<usize, Ty>,
    info: Info,
    /// Each write to `info`'s maps, and to a class while a repair is tried, with the value
    /// it replaced, so that a repair is undone by what it wrote.
    log: Vec<Undo>,
    /// Each expression's type, by its span, as last found.
    seen: HashMap<Span, Seen<'a>>,
    /// Each expression's loose atoms that reach its value unnamed, by its span, as last
    /// found: a superset of those no `else` default on their path writes. No entry is none.
    unnamed: HashMap<Span, KType>,
    /// The loose atoms each expression makes itself, of those it may give unnamed: where a
    /// dropped failure enters. No entry is none.
    made: HashMap<Span, KType>,
    /// The binders of `name = e`, each with the span of `e`, whose unnamed atoms it keeps.
    alias: HashMap<usize, Span>,
    /// What the text of each expression shows of its `int` value, by its span.
    known: HashMap<Span, Known>,
    /// The value of each binder `name = e`, read for what it shows of its `int` value only when
    /// a bit word or an exponent reads the name.
    facts: HashMap<usize, &'a Expr>,
    /// Where each binder's type comes from.
    whence: HashMap<usize, Rc<Origin<'a>>>,
    /// Whether a repair is being tried, so its errors offer none.
    trying: bool,
    /// The output ports declared `Lines`.
    lines_out: HashSet<String>,
    /// The classes; class `k` is the type variable `$k`.
    classes: Vec<Class>,
    /// How many declared functions are being checked, one inside another.
    level: usize,
    /// The classes each of those functions resolves when it ends, by its level.
    pending: Vec<Vec<usize>>,
    /// The needs recorded so far.
    needs: usize,
    /// How many checks of a generic function's needs are under way; they write nothing for
    /// elaboration.
    replaying: usize,
    /// The atoms an application inside a check of a need passed by at parameter `i` of the
    /// function value `what` it applied, for the check to give to the call of the function
    /// whose need it is: `(what, i, atoms)`.
    refused: Vec<(Arc<str>, usize, KType)>,
    /// Those atoms, each with the variables of the need's argument at `i`, for the call whose
    /// needs are checked to pass by at its own arguments of those variables.
    need_passed: Vec<NeedPass>,
    /// Which arguments of the application a check of a need is about to make hold a
    /// variable of the need: only their atoms may pass by to the call around, the first
    /// application taking it.
    need_args: Option<Vec<bool>>,
    /// The needs being checked at calls, one inside another.
    open: Vec<Open>,
    /// The variables of the parameters a partial call leaves out: the next application
    /// leaves the needs on them to the function the call gives.
    defer: BTreeSet<Arc<str>>,
    /// What the last application of one arrow bound, and the needs it left.
    applied: Option<(Binds, Vec<Need>)>,
    /// The atoms the uses of each binder handle, `else` and `is` on its name or on a name
    /// bound to it: an undeclared parameter's type holds them.
    handled: Handled,
    /// The undeclared parameters whose type in the body holds the atoms its uses handle.
    widened: HashSet<usize>,
    /// Each expression's loose atoms that may reach its value from elsewhere than a parameter
    /// of [`Self::widened`], by its span, as last found: those a call passing that parameter
    /// no atom may still give. No entry is none.
    outside: HashMap<Span, KType>,
    /// The loose atoms each call gives from outside, by its span, as [`Self::try_outside`]
    /// found them since the call was last seen; `None` for unknown. [`Self::outside_of`]
    /// takes the entry.
    tried: HashMap<Span, Option<KType>>,
}

/// Atoms that a function value applied in a check of a need passed by (rule 6 of
/// sec:type_resolution): the value's name, the variables of the need's argument, the atoms.
type NeedPass = (Arc<str>, Vec<Arc<str>>, KType);

/// A need being checked at a call.
struct Open {
    /// The need's use in the body.
    span: Span,
    /// The type of the value it is checked on, its variables read as the unknown.
    shape: Ty,
    /// What a use met again inside the check gives: nothing at first, then what the check
    /// gave.
    result: Ty,
    /// Whether the check met the use again and took `result`.
    used: bool,
}

impl<'t, 'a> Ck<'t, 'a> {
    fn new(t: &'t Tables<'a>) -> Self {
        Ck {
            t,
            env: HashMap::new(),
            info: Info::default(),
            log: Vec::new(),
            seen: HashMap::new(),
            unnamed: HashMap::new(),
            made: HashMap::new(),
            alias: HashMap::new(),
            known: HashMap::new(),
            facts: HashMap::new(),
            whence: HashMap::new(),
            trying: false,
            lines_out: HashSet::new(),
            classes: Vec::new(),
            level: 0,
            pending: vec![Vec::new()],
            needs: 0,
            replaying: 0,
            refused: Vec::new(),
            need_passed: Vec::new(),
            need_args: None,
            open: Vec::new(),
            defer: BTreeSet::new(),
            applied: None,
            handled: handled(t.res),
            widened: HashSet::new(),
            outside: HashMap::new(),
            tried: HashMap::new(),
        }
    }

    /// The type an undeclared parameter `id` of the class variable `v` is bound to in its
    /// body: `v` and the atoms its uses handle.
    fn param_ty(&mut self, id: usize, v: Ty) -> Ty {
        match self.handled.get(id) {
            Some(a) => {
                self.widened.insert(id);
                v.union(&Ty::set(a.clone()))
            }
            None => v,
        }
    }

    /// Records the parameter `id` of type `t`, bound to `bound` in the body `body`, as the
    /// binder of its class when `t` is a class and the body sees the class's values only: a
    /// generic literal of the class with no other operand takes its carrier from the
    /// parameter's value at run time (L1.26a). A parameter that also holds the atoms its uses
    /// handle may hold an atom there, and is not recorded.
    fn bind_param(&mut self, id: usize, t: &Ty, bound: &Ty, body: Span) {
        if bound != t {
            return;
        }
        if let Some(k) = self.class_of_ty(t) {
            self.touch(k);
            self.classes[k].binder.get_or_insert((id, body));
        }
    }

    /// A class of its own, of generic literals only, that the literal `l`, written `kn`, joins
    /// generic with no other operand (L1.26a); it takes int where it meets no carrier.
    fn generic_class(&mut self, l: &Lit) -> usize {
        let k = self.class();
        self.classes[k].generic = true;
        self.join(k, &l.joining(), false);
        k
    }

    /// The signature of a function of parameters `params`, whose binders are `ids`, of types
    /// `tys`, whose body `body` gives `result`. An undeclared parameter whose class holds
    /// only carriers also holds the atoms its uses handle, so a call passing one runs the
    /// body; a class that may hold other values already holds every atom. When the result
    /// then holds loose atoms that reach it only from those parameters, the signature has
    /// two arrows: first the parameters without the atoms, whose result lacks them, then the
    /// parameters with them. So `if (line else "") == "" { "empty" } else { trim(line) }` is
    /// `((String) -> String) & ((String | #_) -> String | #_)`, and a call passing a `String`
    /// gives a `String` ([`Self::apply`] takes the first arrow that takes the arguments'
    /// atoms). When a parameter of [`Self::widened`] may hold other values, its atoms reach
    /// the result on both arrows, and the signature has the one arrow.
    fn handled_sig(
        &self,
        params: Vec<SParam>,
        ids: &[Option<usize>],
        tys: Vec<Ty>,
        result: Ty,
        body: &Expr,
    ) -> Sig {
        let mut wide = Vec::with_capacity(tys.len());
        let (mut added, mut other) = (false, false);
        for (t, id) in tys.iter().zip(ids) {
            let a = id.and_then(|id| self.handled.get(id));
            let k = t.as_var().and_then(|v| class_id(v));
            match (a, k) {
                (Some(a), Some(k)) if self.classes[self.find(k)].mask & OTHER == 0 => {
                    added = true;
                    wide.push(t.union(&Ty::set(a.clone())));
                }
                (Some(_), Some(_)) => {
                    other = true;
                    wide.push(t.clone());
                }
                _ => wide.push(t.clone()),
            }
        }
        if !added {
            return Sig::one(params, tys, result);
        }
        let loose = result.loose();
        let kept = &loose & &self.outside_body(body);
        // One difference per function, at its end.
        if other || (&loose - &kept).is_empty() {
            return Sig::one(params, wide, result);
        }
        let plain = result
            .without_loose()
            .union(&result.of_piece(&Piece::Set(kept)));
        Sig {
            arrows: vec![
                Arrow {
                    params: tys,
                    result: plain,
                },
                Arrow {
                    params: wide,
                    result,
                },
            ],
            ..Sig::one(params, Vec::new(), Ty::empty())
        }
    }

    /// The loose atoms that may reach the value of `body`, a function's body, from elsewhere
    /// than a parameter of [`Self::widened`]: a block's are its export's.
    fn outside_body(&self, body: &Expr) -> KType {
        let o = |s: Span| self.outside.get(&s).cloned().unwrap_or_else(KType::empty);
        match &body.kind {
            ExprKind::Block(_) => flows(body)
                .into_iter()
                .fold(KType::empty(), |a, s| &a | &o(s)),
            _ => o(body.span),
        }
    }

    /// Checks that the guarantee of every `L .. U -> V` in the unit's written types is within
    /// its permission ([`crate::elab::kernel_type`]). Every way of checking a program comes
    /// here once, so the check runs on each bound once. The walk keeps its own stack, as a
    /// written type nests as deep as its text; each outermost bound is read whole, with the
    /// bounds inside it, so each node of a written type is read once.
    fn bounds(&mut self) {
        let t = self.t;
        let (mut ports, mut bad) = (Vec::new(), Vec::new());
        let mut stack: Vec<&Type> = Vec::new();
        for &root in &t.written {
            stack.push(root);
            while let Some(ty) = stack.pop() {
                match &ty.kind {
                    TypeKind::Bounded { .. } => {
                        crate::elab::kernel_type(ty, &mut ports, Some(&mut bad));
                        ports.clear();
                    }
                    TypeKind::Tuple(ts) | TypeKind::Union(ts) | TypeKind::And(ts) => {
                        stack.extend(ts);
                    }
                    TypeKind::Diff(a, b) => stack.extend([&**a, &**b]),
                    TypeKind::Arrow { params, result, .. } => {
                        stack.extend(params.iter().map(|p| &p.ty));
                        stack.push(result);
                    }
                    // A bound is a union of carrier names, which holds no morphism type.
                    TypeKind::For { ty, .. } => stack.push(ty),
                    TypeKind::Name(_)
                    | TypeKind::Atom(_)
                    | TypeKind::Every(_)
                    | TypeKind::AtomAny(_) => {}
                    TypeKind::Apply(..) | TypeKind::AtomApply(..) | TypeKind::Record(_) => {
                        unreachable!("resolve rejects the forms of layer L2")
                    }
                    TypeKind::Array(_) => unreachable!("resolve rejects the forms of layer L3"),
                }
            }
        }
        for (span, message) in bad {
            self.error(span, message);
        }
    }

    /// An error at `span`, with the derivation of the expression there.
    fn error(&mut self, span: Span, message: impl Into<String>) {
        let notes = self.derive(&[span]);
        self.error_with(span, message, notes);
    }

    /// An error at `span` that is a case of the row `row` of the rejection table, with the
    /// derivation of the expression there.
    fn rejects(&mut self, row: Row, span: Span, message: impl Into<String>) {
        let notes = self.derive(&[span]);
        self.rejects_with(row, span, message, notes);
    }

    /// An error at `span` that is a case of the row `row` of the rejection table, with the
    /// notes `notes`.
    fn rejects_with(&mut self, row: Row, span: Span, message: impl Into<String>, notes: Vec<Note>) {
        self.info.errors.push(Error {
            row: Some(row),
            span,
            message: message.into(),
            notes,
        });
    }

    fn error_with(&mut self, span: Span, message: impl Into<String>, notes: Vec<Note>) {
        self.info.errors.push(Error {
            row: None,
            span,
            message: message.into(),
            notes,
        });
    }

    /// The derivation of the expressions at `spans`: for each, its type, and for a name or a
    /// call, where the binder's type comes from, followed through each definition.
    fn derive(&self, spans: &[Span]) -> Vec<Note> {
        let mut out = Vec::new();
        self.derive_into(spans, &mut out);
        out
    }

    /// Each expression is derived once, however many others it continues, so a derivation
    /// is at most the size of the graph of origins it walks. The walk keeps its own stack,
    /// since a chain of definitions can be as long as the program.
    fn derive_into(&self, spans: &[Span], out: &mut Vec<Note>) {
        if self.trying {
            return;
        }
        enum Work {
            Derive(Span),
            Show(Note),
        }
        let mut shown: HashSet<Note> = out.iter().cloned().collect();
        let mut visited = HashSet::new();
        let mut stack: Vec<Work> = spans.iter().rev().map(|&s| Work::Derive(s)).collect();
        let note = |span: Span, text: String| Work::Show(Note { span, text });
        while let Some(w) = stack.pop() {
            let span = match w {
                Work::Show(n) => {
                    if shown.insert(n.clone()) {
                        out.push(n);
                    }
                    continue;
                }
                Work::Derive(span) => span,
            };
            if !visited.insert(span) {
                continue;
            }
            let Some((kept, src)) = self.seen.get(&span) else {
                continue;
            };
            built(1);
            let ty = match (kept, src) {
                (Some(t), _) => self.show(t),
                (None, Src::Other(e)) => match self.tuple_seen(e) {
                    Some(t) => self.show(&t),
                    None => continue,
                },
                (None, _) => continue,
            };
            // What this expression shows, in order; pushed reversed so it pops in order.
            let mut next = Vec::new();
            let id = match src {
                Src::Name(id) => {
                    let name = &self.t.res.binders[*id].name;
                    next.push(note(span, format!("`{name}` is {ty} here")));
                    *id
                }
                Src::Call(id, _) => {
                    let name = &self.t.res.binders[*id].name;
                    next.push(note(span, format!("this call of `{name}` gives {ty}")));
                    *id
                }
                Src::Other(e) => {
                    let parts: Vec<&Expr> = match &e.kind {
                        ExprKind::Unary(_, a) => vec![a],
                        ExprKind::Binary(_, a, b) => vec![a, b],
                        ExprKind::Else { of, default, .. } => vec![of, default],
                        ExprKind::If {
                            cond,
                            then,
                            otherwise,
                        } => vec![cond, then, otherwise],
                        ExprKind::Call {
                            positional, named, ..
                        } => positional
                            .iter()
                            .chain(named.iter().map(|(_, a)| a))
                            .collect(),
                        ExprKind::Tuple(items) => items.iter().collect(),
                        ExprKind::Index(of, _) => vec![of],
                        ExprKind::Block(stmts) => stmts
                            .iter()
                            .filter_map(|s| match &s.kind {
                                StmtKind::Return(es) if es.len() == 1 => Some(&es[0]),
                                _ => None,
                            })
                            .collect(),
                        _ => Vec::new(),
                    };
                    let what = match &e.kind {
                        ExprKind::Unary(op, _) | ExprKind::Binary(op, _, _) => {
                            format!("this `{op}`")
                        }
                        ExprKind::Else { .. } => "this `else`".into(),
                        ExprKind::If { .. } => "this `if`".into(),
                        ExprKind::Block(_) => "this block".into(),
                        ExprKind::Call { callee, .. } => match &callee.kind {
                            ExprKind::Name(n) => format!("this call of `{n}`"),
                            _ => "this call".into(),
                        },
                        _ => "this expression".into(),
                    };
                    let verb = if parts.is_empty() { "is" } else { "gives" };
                    next.push(note(span, format!("{what} {verb} {ty}")));
                    for p in parts {
                        next.push(match literal(p) {
                            Some(l) => note(
                                p.span,
                                format!("this literal, {}, is {}", l.text, {
                                    lit_ty(&l.value, l.neg)
                                }),
                            ),
                            None => Work::Derive(p.span),
                        });
                    }
                    stack.extend(next.into_iter().rev());
                    continue;
                }
            };
            let mut o = self.whence.get(&id).map(|o| &**o);
            if o.is_none() {
                let b = &self.t.res.binders[id];
                next.push(note(b.span, format!("`{}` is bound here", b.name)));
            }
            while let Some(origin) = o {
                next.push(note(origin.span, self.said(id, &origin.why)));
                if let Some(f) = origin.from {
                    next.push(Work::Derive(f));
                }
                o = origin.then.as_deref();
            }
            stack.extend(next.into_iter().rev());
        }
    }

    /// The type of the tuple `e` as last found: its components' types, a tuple written as a
    /// component found the same way; `None` when `e` is no tuple or a component was not
    /// checked. The tuples nest as deep as the text, so the walk keeps its own stack: each
    /// open tuple's items and its component types so far.
    fn tuple_seen(&self, e: &Expr) -> Option<Ty> {
        let ExprKind::Tuple(items) = &e.kind else {
            return None;
        };
        let mut stack: Vec<(&[Expr], Vec<Ty>)> = vec![(items, Vec::new())];
        while let Some((items, out)) = stack.last_mut() {
            let Some(item) = items.get(out.len()) else {
                let (_, out) = stack.pop()?;
                let t = Ty::tuple(out);
                match stack.last_mut() {
                    None => return Some(t),
                    Some(up) => up.1.push(t),
                }
                continue;
            };
            match (&item.kind, &self.seen.get(&item.span)?.0) {
                (_, Some(t)) => out.push(t.clone()),
                (ExprKind::Tuple(inner), None) => stack.push((inner, Vec::new())),
                (_, None) => return None,
            }
        }
        None
    }

    /// Records where binder `id` gets its type.
    fn origin(&mut self, id: usize, span: Span, why: Why<'a>, from: Option<Span>) {
        self.whence.insert(
            id,
            Rc::new(Origin {
                span,
                why,
                from,
                then: None,
            }),
        );
    }

    /// What the origin `why` of binder `id` says, in words: the one place an origin is put
    /// into words, by a derivation that reaches it.
    fn said(&self, id: usize, why: &Why<'a>) -> String {
        built(1);
        let b = &self.t.res.binders[id].name;
        match why {
            Why::Declared(sig) => format!("`{b}` is declared here, `{}`", self.sig_text(sig)),
            Why::Defined(v) => format!("`{b}` is defined as this expression, {}", self.text(v)),
            Why::Component(i, c) => format!("`{b}` is component {i} of this, {}", self.text(c)),
            Why::Port => format!("`{b}` is an output port"),
            Why::Untracked(a) => {
                let shown = declared_text(a).unwrap_or_else(|| Ty::dynamic().to_string());
                format!(
                    "`{b}` is declared `{shown}`, whose values the checker does not track: \
                     it takes `{b}` as unknown, _"
                )
            }
            // A name is shown as written; any other type as the checker printed it then.
            Why::Typed(a, t, masks) => match &a.kind {
                TypeKind::Name(n) => format!("`{b}` is declared `{n}`"),
                _ => {
                    // A class solved since is shown as its type, not by its carriers then.
                    let t = self.settled(t);
                    let masks: Masks = (masks.iter())
                        .filter(|(v, _)| t.vars.contains(v))
                        .cloned()
                        .collect();
                    format!("`{b}` is declared `{}`", show_with(&t, &masks))
                }
            },
            Why::Default(t) => format!("`{b}` is {}, the carrier of its default", self.text(t)),
            Why::Untyped(k) => format!("`{b}` has no declared type; its uses give it $${k}"),
            Why::Narrowed(t) => format!(
                "`{b}` is narrowed to {} where this test decides",
                self.text(t)
            ),
        }
    }

    fn id(&self, span: Span, name: &str) -> usize {
        self.t.id(span, name)
    }

    /// Component `i` of `v`, destructured into `n` names: of each tuple shape, with `v`'s
    /// atoms, which `TupleGet` passes.
    fn component(&mut self, v: &Ty, i: usize, n: usize, span: Span) -> Ty {
        let mut out = self.passing(v, "a tuple", span);
        for p in v.pieces() {
            match p {
                Piece::Tuple(cs) if cs.len() == n => out = out.union(&cs[i]),
                Piece::Dyn => {
                    if i == 0 {
                        self.any("destructuring", span);
                    }
                }
                Piece::Var(_) => out = out.union(&Ty::dynamic()),
                p if p.is_atoms() => {}
                p => {
                    if i == 0 {
                        self.error(
                            span,
                            format!("this value is {}, not a tuple of {n}", self.text(&p.ty())),
                        );
                    }
                }
            }
        }
        out
    }

    /// The loose atoms of `v`, a value of the expression at `span`, that reach it unnamed.
    /// One intersection, in `O(s log l)` for the smaller set's `s` atoms.
    fn unnamed_in(&self, v: &Ty, span: Span) -> KType {
        match self.unnamed.get(&span) {
            Some(u) => &v.loose() & u,
            None => KType::empty(),
        }
    }

    /// The loose atoms that may reach the value of `e`, of type `t`, unnamed, and those of
    /// them that `e` itself makes (DESIGN.md sec:tour_methods): a failure is named only by
    /// the `else` whose default writes it on the path it flows on, never by an atom of the
    /// same name elsewhere. An `if` passes on each branch's, a block its export's, a name
    /// bound by `name = e` that of `e`. An operator or a call of a declared function passes
    /// on its parts' and makes the atoms its signature's results hold, and `#errs`, unless a
    /// type variable of a result is no parameter's own: then it makes all its loose atoms,
    /// as any other expression does. The set may hold more atoms than the
    /// value's type, where a part's failure stops there (`==` gives a `bool`); `_` keeps
    /// only those of the type it binds, so the extra atoms can only reject, never accept.
    ///
    /// Each part was recorded before `e`, and only unions and intersections with a set of
    /// the signature's size are taken, each in `O(s log l)` for the smaller set's `s` atoms,
    /// so a chain of `n` failures costs `O(n log² n)`; a difference would complement the
    /// larger set (COMPLEXITY.md F21).
    fn unnamed_of(&self, e: &Expr, t: &Ty, src: &Src<'_>) -> Option<(KType, Option<KType>)> {
        let loose = t.loose();
        // Complexity tradeoff: `loose` is compared with the empty type as written, which
        // orders by digest in `O(1)`, not tested with `is_empty`. What is given up: a set of
        // loose atoms that is empty but not written as the empty type (an atom whose payload
        // type is empty but not reduced) counts as holding atoms, so `e` keeps its parts'
        // unnamed atoms; where the value bound to `_` has such an atom loose from elsewhere,
        // `_` is rejected with the error of `discard`, never accepted wrongly. Why: the memo of
        // `is_empty` is a map ordered by contents, and `passed` tests the operand's atoms, an
        // equal set built apart, so each lookup compares the two sets in full, `O(n)`, and a
        // chain of `n` failures costs `O(n²)` (COMPLEXITY.md F32 and F59). Trigger: a value
        // whose type writes an empty payload type that was not reduced to the empty type. Test
        // of the cost: `l01_27_absences::scaling::a_chain_of_many_failure_atoms_scales` (with
        // `is_empty` here it fails at 40.2 times per 8 times the size); no test writes such a
        // payload. A complete solution would key the emptiness memo by the type's digest,
        // comparing contents only when two digests are equal, or reduce each atom's payload
        // type to the empty type when it is built, so that comparison with the empty type as
        // written is exact.
        if loose == KType::empty() {
            return None;
        }
        let u = |s: Span| self.unnamed.get(&s).cloned().unwrap_or_else(KType::empty);
        let union = |spans: Vec<Span>| spans.into_iter().fold(KType::empty(), |a, s| &a | &u(s));
        let made = |sigs: &[Arrow]| {
            // A type variable of the result that is no parameter's own takes its atoms at the
            // call from elsewhere (the result of a function value, a tuple's component), not
            // from an argument's value, whose unnamed set `flows` passes on: then the call
            // makes every loose atom of its value.
            let own = if sigs.iter().all(passes_vars_on) {
                let atoms = sigs
                    .iter()
                    .fold(errs(), |a, arrow| &a | &arrow.result.loose());
                &loose & &atoms
            } else {
                loose.clone()
            };
            (&union(flows(e)) | &own, Some(own))
        };
        Some(match (&e.kind, src) {
            (
                ExprKind::Else {
                    of,
                    pattern,
                    default,
                },
                _,
            ) => {
                let d = if named_default(default) {
                    KType::empty()
                } else {
                    u(default.span)
                };
                let kept = match pattern {
                    // The plain form strips every loose atom of its value.
                    None => KType::empty(),
                    Some(Pattern::Atom {
                        name,
                        fields,
                        items,
                        ..
                    }) if fields.is_empty() && items.is_empty() => &u(of.span) - &any_payload(name),
                    Some(_) => u(of.span),
                };
                (&kept | &d, None)
            }
            (ExprKind::If { .. } | ExprKind::Block(_), _) => (union(flows(e)), None),
            (ExprKind::Unary(op, _) | ExprKind::Binary(op, _, _), _) => made(&op_sig(op).arrows),
            (_, Src::Call(id, _)) => match self.env.get(id).and_then(only_fn) {
                Some(sig) => made(&sig.arrows),
                None => (loose.clone(), Some(loose)),
            },
            (_, Src::Name(id)) => match self.alias.get(id) {
                Some(&value) if self.seen.contains_key(&value) => (u(value), None),
                _ => (loose.clone(), Some(loose)),
            },
            _ => (loose.clone(), Some(loose)),
        })
    }

    /// The loose atoms that may reach the value of `e`, of type `t`, from elsewhere than a
    /// parameter of [`Self::widened`]: what `e` gives when each such parameter holds no atom,
    /// as on the first arrow of [`Self::handled_sig`]. It follows [`Self::unnamed_of`]: a
    /// name of such a parameter gives none; an `else` gives its default's only when its
    /// value may give an atom; a call that [`Self::try_outside`] applied again, `tried`, gives
    /// what that application gave (unknown, `None`, is all its loose atoms), so a call of a
    /// function of two arrows from [`Self::handled_sig`] gives only those of the arrow it
    /// takes from outside; an operator, another call of a function [`Self::called`] names (a
    /// method call's receiver one of its parts, `x.r` as `x.r()`) or a prelude word passes on
    /// its parts' and gives the atoms its arrows' results hold, and `#errs` only when two of
    /// its parts give atoms; any other expression gives all its loose atoms.
    /// Each set is compared with the empty type as written, in `O(1)`, as in
    /// [`Self::unnamed_of`], so a chain of `n` expressions costs `O(n log² n)`.
    fn outside_of(
        &self,
        e: &Expr,
        t: &Ty,
        src: &Src<'_>,
        tried: Option<Option<KType>>,
    ) -> Option<KType> {
        let loose = t.loose();
        if loose == KType::empty() {
            return None;
        }
        let o = |s: Span| self.outside.get(&s).cloned().unwrap_or_else(KType::empty);
        let union = |spans: Vec<Span>| spans.into_iter().fold(KType::empty(), |a, s| &a | &o(s));
        let made = |sigs: &[Arrow], parts: Vec<Span>| {
            if !sigs.iter().all(passes_vars_on) {
                return loose.clone();
            }
            let parts: Vec<KType> = parts.into_iter().map(o).collect();
            let mut atoms = sigs
                .iter()
                .fold(KType::empty(), |a, arrow| &a | &arrow.result.loose());
            if parts.iter().filter(|p| **p != KType::empty()).count() > 1 {
                atoms = &atoms | &errs();
            }
            parts.iter().fold(&loose & &atoms, |a, p| &a | p)
        };
        Some(match (&e.kind, src) {
            (
                ExprKind::Else {
                    of,
                    pattern,
                    default,
                },
                _,
            ) => {
                let of = o(of.span);
                if of == KType::empty() {
                    return Some(of);
                }
                let kept = match pattern {
                    None => KType::empty(),
                    Some(Pattern::Atom {
                        name,
                        fields,
                        items,
                        ..
                    }) if fields.is_empty() && items.is_empty() => &of - &any_payload(name),
                    Some(_) => of,
                };
                &kept | &o(default.span)
            }
            (ExprKind::If { .. } | ExprKind::Block(_), _) => union(flows(e)),
            (ExprKind::Unary(op, _) | ExprKind::Binary(op, _, _), _) => {
                made(&op_sig(op).arrows, flows(e))
            }
            // A call [`Self::try_outside`] applied again from outside gives what that gave, and
            // what reaches its value around the application: the callee's own atoms, and a
            // receiver's through `?.`.
            (ExprKind::Call { callee: f, .. }, _) | (ExprKind::Member { of: f, .. }, _)
                if let Some(k) = &tried =>
            {
                // `f` is a call's callee, or a member's receiver.
                let around = match (&e.kind, &f.kind) {
                    (ExprKind::Member { safe, .. }, _) if *safe => o(f.span),
                    (ExprKind::Member { .. }, _) => KType::empty(),
                    (_, ExprKind::Member { of, safe, .. }) if *safe => o(of.span),
                    (_, ExprKind::Member { .. }) => KType::empty(),
                    _ => o(f.span),
                };
                match k {
                    Some(k) => &loose & &(k | &around),
                    None => loose,
                }
            }
            (ExprKind::Call { callee, .. }, _)
                if let Some((sig, receiver)) = self.called(callee) =>
            {
                // The receiver's atoms reach the value as an argument's do; through `?.` they
                // pass the call by.
                let mut parts = flows(e);
                if let Some((r, _)) = receiver {
                    parts.insert(0, r.span);
                }
                made(&sig.arrows, parts)
            }
            // `x.r` is `x.r()`; its one part is the receiver.
            (ExprKind::Member { .. }, _) if let Some((sig, _)) = self.called(e) => {
                made(&sig.arrows, flows(e))
            }
            (_, Src::Name(id)) => match self.alias.get(id) {
                Some(&value) if self.seen.contains_key(&value) => o(value),
                _ if self.widened.contains(id) => KType::empty(),
                _ => loose,
            },
            _ => match self.word_call(e) {
                Some((w, x)) => made(&word_sig(w).arrows, vec![x]),
                None => loose,
            },
        })
    }

    /// The arguments of a call as they are when each parameter of [`Self::widened`] holds no
    /// atom: each argument's loose atoms cut to those [`Self::outside`] keeps for its
    /// expression. `None` when no argument holds a loose atom, so that the call gives the same
    /// from outside.
    fn outside_args(&self, args: &[Option<Arg>]) -> Option<Vec<Option<Arg>>> {
        let holds = |a: &Arg| a.at.is_some() && a.ty.loose() != KType::empty();
        if !args.iter().flatten().any(holds) {
            return None;
        }
        let cut = |a: &Arg| match a.at {
            Some(at) if holds(a) => {
                let o = self.outside.get(&at).cloned().unwrap_or_else(KType::empty);
                let kept = &a.ty.loose() & &o;
                Arg {
                    ty: a
                        .ty
                        .without_loose()
                        .union(&a.ty.of_piece(&Piece::Set(kept))),
                    ..a.clone()
                }
            }
            _ => a.clone(),
        };
        Some(args.iter().map(|a| a.as_ref().map(cut)).collect())
    }

    /// The call of `sig` at `span` applied again to `with`, from [`Self::outside_args`], with
    /// the checker's state restored after, as [`Self::repairs`] tries a call: the loose atoms
    /// it then gives are those that reach the call's value from outside, which
    /// [`Self::outside_of`] reads. It selects the arrow the call takes from outside for any
    /// callee, a declared function, a method, a function value passed to another function or
    /// computed: `r(x)`, `x.r()`, `x.r`, `ap(r, x)` and `(if c { r } else { r })(x)` alike. A
    /// trial the arguments do not pass leaves the call's atoms from outside unknown, so all
    /// its loose atoms. One more application per call that passes a loose atom inside a
    /// function with a widened parameter.
    fn try_outside(&mut self, what: &str, sig: &Sig, with: Vec<Option<Arg>>, span: Span) {
        let applied = self.applied.take();
        let saved = self.mark();
        self.trying = true;
        let (t, _) = self.apply(what, sig, with, false, span);
        let ok = self.info.errors.len() == saved.errors;
        self.trying = false;
        self.undo(&saved);
        self.applied = applied;
        self.tried_at(span, ok.then(|| t.loose()));
    }

    /// Joins `k` to the loose atoms from outside recorded for the call at `span`: a call of a
    /// value of several functions is applied once per function. `None`, unknown, absorbs.
    /// A trial, or the check of a need at a call, applies calls that are not in the text, so
    /// it records nothing.
    fn tried_at(&mut self, span: Span, k: Option<KType>) {
        if self.trying || self.replaying > 0 {
            return;
        }
        match self.tried.entry(span) {
            Entry::Vacant(v) => {
                v.insert(k);
            }
            Entry::Occupied(mut o) => {
                let v = o.get_mut();
                *v = v.take().zip(k).map(|(a, b)| &a | &b);
            }
        }
    }

    /// The prelude word `e` applies to one argument, and the argument's span, when `e` is
    /// `w(x)`, `x.w()` or `x.w` for a word of layer L1 other than `sum` and the bit words,
    /// which [`word_sig`] types.
    fn word_call<'e>(&self, e: &'e Expr) -> Option<(&'e str, Span)> {
        if let ExprKind::Member {
            of,
            name,
            safe: false,
        } = &e.kind
        {
            return match self.t.res.uses.get(&e.span) {
                Some(Ref::Bound(_)) => None,
                _ if crate::resolve::prelude_layer(name) == Some(1)
                    && name != "sum"
                    && bit_prim(name).is_none()
                    && word_arity(name) == 1 =>
                {
                    Some((name.as_str(), of.span))
                }
                _ => None,
            };
        }
        let ExprKind::Call {
            callee,
            positional,
            named,
            curry: false,
        } = &e.kind
        else {
            return None;
        };
        let (w, x) = match (&callee.kind, &positional[..]) {
            (ExprKind::Name(w), [x]) => match self.t.res.uses.get(&callee.span) {
                Some(Ref::Prelude(_)) => (w, x.span),
                _ => return None,
            },
            (
                ExprKind::Member {
                    of,
                    name,
                    safe: false,
                },
                [],
            ) => match self.t.res.uses.get(&callee.span) {
                Some(Ref::Bound(_)) => return None,
                _ if crate::resolve::prelude_layer(name) == Some(1) => (name, of.span),
                _ => return None,
            },
            _ => return None,
        };
        (named.is_empty() && w != "sum" && bit_prim(w).is_none() && word_arity(w) == 1)
            .then_some((w.as_str(), x))
    }

    /// `_` bound to a value of `e`, or its component `i`, in the binding at `span`, where
    /// `dropped` is the loose atoms that reach it unnamed (DESIGN.md sec:tour_methods): `_`
    /// drops a loose failure only where the text names it, as the default an `else` on its
    /// path writes, so any of `dropped` is an error. The error names the atoms, where each
    /// enters the value, the derivation, and the repairs.
    fn discard(&mut self, dropped: KType, e: &'a Expr, i: Option<usize>, span: Span) {
        if dropped.is_empty() {
            return;
        }
        let what = match i {
            None => "this value".to_string(),
            Some(i) => format!("component {i} of this value"),
        };
        let mut notes = self.entries(e.span, &dropped);
        let atoms = Ty::set(dropped);
        self.derive_into(&[e.span], &mut notes);
        let menu = [
            "repair: write a default for the value, as `_ = … else #ok;`, so the text names what it drops".to_string(),
            "repair: handle each failure with a `match` on the value".to_string(),
            "repair: bind the value to a name, and use the name".to_string(),
        ];
        notes.extend(menu.into_iter().map(|text| Note { span, text }));
        self.rejects_with(
            Row::WritesNothing,
            span,
            format!("`_` drops a loose failure {what} may be, {atoms}"),
            notes,
        );
    }

    /// Where the atoms of `wanted` enter the value at `root`: a note at each expression, or
    /// at the origin of each name, that makes some of them (`unnamed_of`), reached from
    /// `root` along parts that pass some atom on unnamed. A pattern `else` passes on what it
    /// does not handle. The walk visits each expression once and keeps its own stack, since
    /// a chain of definitions can be as long as the program; atoms it places nowhere enter
    /// at `root`. Each step intersects with the atoms the expression makes, a set of its
    /// signature's size, so the walk costs `O(m log n)` for the `m` expressions it visits.
    fn entries(&self, root: Span, wanted: &KType) -> Vec<Note> {
        let mut out = Vec::new();
        let mut left = wanted.clone();
        let mut visited = HashSet::new();
        let mut stack = vec![(root, wanted.clone())];
        while let Some((span, want)) = stack.pop() {
            if !visited.insert(span) || !self.unnamed.contains_key(&span) {
                continue;
            }
            let Some((_, src)) = self.seen.get(&span) else {
                continue;
            };
            let site = match src {
                Src::Name(id) => self
                    .whence
                    .get(id)
                    .map_or(self.t.res.binders[*id].span, |o| o.span),
                _ => span,
            };
            if let Some(own) = self.made.get(&span) {
                let new = &(own & &want) & &left;
                if !new.is_empty() {
                    left = &left - &new;
                    let text = format!("the loose failure {} enters here", Ty::set(new));
                    out.push(Note { span: site, text });
                }
            }
            let parts: Vec<(Span, KType)> = match src {
                Src::Name(id) => self
                    .alias
                    .get(id)
                    .map(|&v| (v, want.clone()))
                    .into_iter()
                    .collect(),
                Src::Call(_, e) | Src::Other(e) => match &e.kind {
                    ExprKind::Else {
                        of,
                        pattern:
                            Some(Pattern::Atom {
                                name,
                                fields,
                                items,
                                ..
                            }),
                        default,
                    } if fields.is_empty() && items.is_empty() => {
                        let mut parts = vec![(of.span, &want - &any_payload(name))];
                        if !named_default(default) {
                            parts.push((default.span, want.clone()));
                        }
                        parts
                    }
                    _ => flows(e).into_iter().map(|p| (p, want.clone())).collect(),
                },
            };
            // Pushed reversed, so the parts are visited in written order.
            stack.extend(parts.into_iter().rev());
        }
        if !left.is_empty() {
            let text = format!("the loose failure {} enters here", Ty::set(left));
            out.push(Note { span: root, text });
        }
        out
    }

    /// The signature `sig` of the function of `level`, which ends: each class of the level
    /// takes its type, a type variable of the signature named in order of appearance. The
    /// uses of a class that is a type variable join the signature as its needs; those of a
    /// class of one type are checked on it now.
    fn generalize(&mut self, level: usize, mut sig: Sig) -> Arc<Sig> {
        // The roots of this level, and the classes whose roots have a type by now: each of
        // the latter takes its root's type in `sig`. A class of a function around goes to
        // that function's list.
        let mut own = Vec::new();
        let mut done = Vec::new();
        for k in std::mem::take(&mut self.pending[level]) {
            let r = self.find(k);
            let at = self.classes[r].level;
            if self.classes[r].resolved.is_none() {
                if at < level {
                    self.pending[at].push(k);
                    continue;
                }
                self.resolve(r);
                own.push(r);
            }
            done.push(k);
        }
        let mut needs: Vec<(usize, Need)> = Vec::new();
        let mut now = Vec::new();
        for &r in &own {
            let uses = std::mem::take(&mut self.classes[r].uses);
            match self.classes[r].resolved.clone() {
                Some(t) if t == Ty::var(format!("${r}").into()) => needs.extend(uses),
                Some(t) => now.extend(uses.into_iter().map(|(_, n)| (n, t.clone()))),
                None => unreachable!("resolved above"),
            }
        }
        for (n, t) in &now {
            self.check_on(n, t, n.span);
        }
        needs.sort_by_key(|(n, _)| *n);
        sig.needs = needs.into_iter().map(|(_, n)| n).collect();
        // Only the classes listed for this level are replaced here, not every class `sig`
        // holds. A type variable keeps its class's name `$k` until `finish`, so a function
        // around does not rewrite the signatures inside it at each depth (CHK-curried);
        // `finish` renames each signature it shows once. A class that takes another class's
        // variable is replaced at every depth of `sig`, so that its variable is found where
        // the signature's own are. A class that takes a type with no variable is replaced
        // only outside the functions `sig` holds: inside them its variable stays, and is read
        // as its type wherever a function's arrows are read ([`Self::open`], [`Self::stale`]),
        // and replaced once in what `finish` shows. Replacing it at every depth cost the
        // size of `sig` at each level, n^2 for n nested lambdas whose parameters each take a
        // carrier (ledger CHK-carrier, COMPLEXITY.md F77).
        // Complexity tradeoff: a class bound to another class's variable or to the unknown is
        // still replaced at every depth, O(size of `sig`) at each level that binds one, so n
        // nested lambdas that each bind such a class would cost n^2 (no such family measured);
        // reading it lazily needs each reading site to follow class-to-class links too.
        let mut deep = Binds::new();
        let mut outside = Binds::new();
        for k in done {
            let v: Arc<str> = format!("${k}").into();
            let t = self.classes[self.find(k)]
                .resolved
                .clone()
                .expect("resolved");
            if t.as_var() == Some(&v) {
                continue;
            }
            match is_solved(&t) {
                true => outside.insert(v, t),
                false => deep.insert(v, t),
            };
        }
        let mut sig = sig.replace(&deep).replace_outside(&outside);
        // The classes of this level that are type variables, named in order of appearance.
        // The names it holds, inside the functions it holds too, are taken; the facts of
        // those functions are shared, not walked again. A class `outside` replaced is still
        // inside those functions, and is no type variable.
        let facts = VarFacts::of(&sig);
        let mine: HashSet<Arc<str>> = own
            .iter()
            .map(|r| Arc::from(format!("${r}")))
            .filter(|v| facts.classes.contains(v) && !outside.contains_key(v))
            .collect();
        // The names before `free` are all taken.
        let mut n = facts.free;
        let mut mine_seen = BTreeSet::new();
        for v in sig.first_seen(&mine) {
            let r = class_id(&v).expect("a class variable");
            let name = loop {
                let name = var_name(n);
                n += 1;
                if !facts.names.contains(&name) {
                    break name;
                }
            };
            if self.classes[r].mask != EVERY {
                sig.bounds.insert(v.clone(), self.classes[r].mask);
            }
            self.classes[r].name = Some(name);
            mine_seen.insert(v);
        }
        // A type variable that does not reach the signature means nothing outside it.
        for &r in &own {
            if self.classes[r].name.is_none()
                && let Some(t) = &self.classes[r].resolved
                && t.vars.iter().any(|v| class_id(v).is_some())
            {
                self.classes[r].resolved = Some(Ty::dynamic());
            }
        }
        sig.own = mine_seen;
        sig.named = n;
        sig.facts = Default::default();
        sig.note_held();
        self.level -= 1;
        Arc::new(sig)
    }

    /// A new class, of every value, at the current level.
    fn class(&mut self) -> usize {
        let id = self.classes.len();
        self.classes.push(Class {
            parent: id,
            rank: 0,
            mask: EVERY,
            level: self.level,
            lits: Vec::new(),
            reasons: Vec::new(),
            resolved: None,
            name: None,
            uses: Vec::new(),
            flowed: Vec::new(),
            binder: None,
            generic: false,
        });
        self.pending[self.level].push(id);
        id
    }

    /// The root of class `k`'s tree.
    fn find(&self, mut k: usize) -> usize {
        while self.classes[k].parent != k {
            k = self.classes[k].parent;
        }
        k
    }

    /// Logs class `r` before a change, while a repair is tried.
    fn touch(&mut self, r: usize) {
        if self.trying {
            self.log
                .push(Undo::Class(r, Box::new(self.classes[r].clone())));
        }
    }

    /// Removes from class `k` the carriers `mask` lacks, as `what` at `span` requires;
    /// false, changing nothing, if none would be left.
    fn restrict(&mut self, k: usize, mask: u8, what: &str, span: Span) -> bool {
        let r = self.find(k);
        let m = self.classes[r].mask & mask;
        if m == self.classes[r].mask {
            return true;
        }
        if m == 0 {
            return false;
        }
        self.touch(r);
        let c = &mut self.classes[r];
        c.mask = m;
        c.reasons.push(Reason {
            span,
            what: what.into(),
            takes: Some(mask),
        });
        true
    }

    /// Merges classes `a` and `b`, as `what` at `span` requires; false, changing nothing, if
    /// they share no carrier. The shorter lists move into the longer, so that each item
    /// moves `O(log n)` times.
    fn merge(&mut self, a: usize, b: usize, what: &str, span: Span) -> bool {
        let (a, b) = (self.find(a), self.find(b));
        if a == b {
            return true;
        }
        let m = self.classes[a].mask & self.classes[b].mask;
        if m == 0 {
            return false;
        }
        self.touch(a);
        self.touch(b);
        let (root, child) = match self.classes[a].rank < self.classes[b].rank {
            true => (b, a),
            false => (a, b),
        };
        if self.classes[a].rank == self.classes[b].rank {
            self.classes[root].rank += 1;
        }
        // Each use of one class is checked on what flowed into the other.
        let mut cross: Vec<(Need, Ty, Span)> = Vec::new();
        for (x, y) in [(a, b), (b, a)] {
            for (_, n) in &self.classes[x].uses {
                for (t, at) in &self.classes[y].flowed {
                    cross.push((n.clone(), t.clone(), *at));
                }
            }
        }
        let lowered = self.classes[a].level != self.classes[b].level;
        let mut lits = std::mem::take(&mut self.classes[child].lits);
        let mut reasons = std::mem::take(&mut self.classes[child].reasons);
        let mut uses = std::mem::take(&mut self.classes[child].uses);
        let mut flowed = std::mem::take(&mut self.classes[child].flowed);
        let level = self.classes[child].level;
        let binder = self.classes[child].binder;
        let generic = self.classes[child].generic;
        self.classes[child].parent = root;
        let c = &mut self.classes[root];
        c.generic &= generic;
        c.binder = match (c.binder, binder) {
            (Some(a), Some(b)) if b.1.start <= a.1.start && a.1.end <= b.1.end => Some(b),
            (a, b) => a.or(b),
        };
        if c.uses.len() < uses.len() {
            std::mem::swap(&mut c.uses, &mut uses);
        }
        c.uses.extend(uses);
        if c.flowed.len() < flowed.len() {
            std::mem::swap(&mut c.flowed, &mut flowed);
        }
        c.flowed.extend(flowed);
        if c.lits.len() < lits.len() {
            std::mem::swap(&mut c.lits, &mut lits);
        }
        c.lits.extend(lits);
        if c.reasons.len() < reasons.len() {
            std::mem::swap(&mut c.reasons, &mut reasons);
        }
        c.reasons.extend(reasons);
        c.reasons.push(Reason {
            span,
            what: what.into(),
            takes: None,
        });
        c.mask = m;
        c.level = c.level.min(level);
        if lowered {
            let mut vars = Vars::default();
            for (_, n) in &self.classes[root].uses {
                n.vars_in(&mut vars);
            }
            let level = self.classes[root].level;
            self.lower(vars.order, level);
        }
        for (n, t, at) in &cross {
            self.check_on(n, t, *at);
        }
        true
    }

    /// Lowers the classes the variables `vars` name, and those their uses mention, to
    /// `level` at most, so that none becomes a type variable of a function that ends before
    /// the one of `level`. A class is lowered at most once per level.
    fn lower(&mut self, mut vars: Vec<Arc<str>>, level: usize) {
        while let Some(v) = vars.pop() {
            let Some(k) = class_id(&v).filter(|&k| k < self.classes.len()) else {
                continue;
            };
            let r = self.find(k);
            if self.classes[r].level <= level || self.classes[r].resolved.is_some() {
                continue;
            }
            self.touch(r);
            self.classes[r].level = level;
            let mut more = Vars::default();
            for (_, n) in &self.classes[r].uses {
                n.vars_in(&mut more);
            }
            vars.extend(more.order);
        }
    }

    /// Records that the use at `span` needs `kind` of each value of class `k`, and gives what
    /// the use gives: a new class at `k`'s level if `gives`, else nothing. The use is checked
    /// now on each tuple and function that flowed into the class; on the type the class
    /// takes, if that is not a type variable, when its function ends; else at each call of
    /// that function, on the type the call binds the variable to. A use the class has met
    /// already gives what it gave then, since what a use gives depends only on the type it is
    /// made of; so a call met twice checks its needs once.
    fn need(&mut self, k: usize, kind: NeedKind, gives: bool, span: Span) -> Ty {
        let r = self.find(k);
        let data = |n: &NeedKind| matches!(n, NeedKind::Data(_));
        if data(&kind) && self.classes[r].uses.iter().any(|(_, n)| data(&n.kind)) {
            return Ty::empty();
        }
        if let Some((_, n)) = self.classes[r]
            .uses
            .iter()
            .find(|(_, n)| n.kind == kind && n.result.is_some() == gives)
        {
            return n.result.clone().unwrap_or_else(Ty::empty);
        }
        let level = self.classes[r].level;
        let result = gives.then(|| {
            let j = self.class();
            self.classes[j].level = level;
            Ty::var(format!("${j}").into())
        });
        let need = Need {
            on: Ty::var(format!("${r}").into()),
            kind,
            result: result.clone(),
            span,
        };
        let mut vars = Vars::default();
        need.vars_in(&mut vars);
        self.lower(vars.order, level);
        let flowed = self.classes[r].flowed.clone();
        self.touch(r);
        self.needs += 1;
        let seq = self.needs;
        self.classes[r].uses.push((seq, need.clone()));
        for (t, at) in &flowed {
            self.check_on(&need, t, *at);
        }
        result.unwrap_or_else(Ty::empty)
    }

    /// Checks the use `n` of a class on `t`, which flowed into the class at `span` or which
    /// the class takes: what the use gives flows into the class of its result.
    fn check_on(&mut self, n: &Need, t: &Ty, span: Span) {
        let from = self.info.errors.len();
        let start = self.need_passed.len();
        let got = self.meet(n, t, &Binds::new(), span);
        // A use checked on a value that flowed in has no call whose argument gave the atoms.
        let passed: Vec<NeedPass> = self.need_passed.drain(start..).collect();
        for (inner, _, k) in passed {
            let message = format!(
                "{inner} does not take {}: an atom passes by only at a call given it",
                Ty::set(k)
            );
            self.error(n.span, message);
        }
        if let Some(r) = &n.result
            && let Some(k) = self.class_of_ty(r)
            && !self.flow(k, &got, "this use", n.span)
        {
            let shown = self.show(r);
            let got = self.text(&got);
            self.error(n.span, format!("this use gives {got}, not {shown}"));
        }
        self.also(from, n.span, |_| "this use needs it here".to_string());
    }

    /// The use `n`, of a value of `on`, checked at `span` where the variables of the
    /// signature that holds it are bound as `binds`; a variable left unbound is unknown.
    /// Gives what the use gives.
    fn meet(&mut self, n: &Need, on: &Ty, binds: &Binds, span: Span) -> Ty {
        let b = |ck: &Self, t: &Ty| bound(t, binds, |v| ck.is_class(v));
        let on = b(self, on);
        self.replaying += 1;
        let has_vars = |t: &Ty| {
            let mut vars = Vars::default();
            t.vars_in(&mut vars);
            !vars.order.is_empty()
        };
        self.need_args = match &n.kind {
            NeedKind::Call { positional, .. } => Some(positional.iter().map(has_vars).collect()),
            NeedKind::Index(t) => Some(vec![has_vars(t)]),
            _ => None,
        };
        let start = self.refused.len();
        let out = match &n.kind {
            NeedKind::Component { i, key } => self.at_index(&on, *i, Arg::of(key.clone()), span),
            NeedKind::Index(k) => self.at_key(&on, Arg::of(b(self, k)), span),
            NeedKind::Call {
                what,
                positional,
                named,
                curry,
            } => {
                let args = walk::Args {
                    positional: positional
                        .iter()
                        .map(|t| ArgSrc::Got(Box::new(Arg::of(b(self, t)))))
                        .collect(),
                    named: named
                        .iter()
                        .map(|(m, t)| (m.to_string(), ArgSrc::Got(Box::new(Arg::of(b(self, t))))))
                        .collect(),
                };
                self.call_found(&on, what, args, *curry, span)
            }
            NeedKind::Data(what) => {
                self.data(&on, what, span);
                Ty::empty()
            }
            NeedKind::Into { what, ty } => {
                self.into(&on, ty, what, span);
                Ty::empty()
            }
            NeedKind::Payload { atom, slot } => self.payload(&on, atom, slot, span),
        };
        self.replaying -= 1;
        self.need_args = None;
        // Each argument the use's applications passed atoms of by is named by the variables
        // of its type in the need: an argument of no variable gives them to no call.
        for (what, i, k) in self.refused.drain(start..).collect::<Vec<_>>() {
            let t = match &n.kind {
                NeedKind::Call { positional, .. } => positional.get(i),
                NeedKind::Index(t) if i == 0 => Some(t),
                _ => None,
            };
            let mut vars = Vars::default();
            if let Some(t) = t {
                t.vars_in(&mut vars);
            }
            self.need_passed.push((what, vars.order, k));
        }
        out
    }

    /// Passes by, at the call at `span` of `sig`'s arrow `arrow` on `args`, the atoms that
    /// the checks of its needs since the `start`th found a function value omits (rule 6 of
    /// sec:type_resolution): at each argument whose parameter holds a variable of the need's
    /// argument, the atoms of it the argument holds. Inside another check they go on to the
    /// call around it. Gives the atoms passed by, or an error for atoms no argument gives.
    fn pass_needs(
        &mut self,
        what: &str,
        params: &[Ty],
        args: &[Option<Arg>],
        start: usize,
        span: Span,
    ) -> Result<Ty, String> {
        let mut out = Ty::empty();
        let passed: Vec<NeedPass> = self.need_passed.drain(start..).collect();
        for (inner, vars, k) in passed {
            let mut covered = KType::empty();
            for (i, (p, a)) in params.iter().zip(args).enumerate() {
                let Some(a) = a else {
                    continue;
                };
                if !p.vars.iter().any(|v| vars.contains(v)) {
                    continue;
                }
                let c = &a.ty.loose() & &k;
                if c.is_empty() {
                    continue;
                }
                out = out.union(&a.ty.of_piece(&Piece::Set(c.clone())));
                match a.at {
                    Some(at) => self.pass_at(span, at, &c),
                    None => self.refused.push((what.into(), i, c.clone())),
                }
                covered = &covered | &c;
            }
            let left = &k - &covered;
            if !left.is_empty() {
                return Err(format!(
                    "{inner}, which {what} applies, does not take {}, and no argument of \
                     this call gives it",
                    Ty::set(left)
                ));
            }
        }
        Ok(out)
    }

    /// Records that the call at `span` passes by the atoms `k` of its argument at `at`.
    fn pass_at(&mut self, span: Span, at: Span, k: &KType) {
        let mut v = self.info.passes.get(&span).cloned().unwrap_or_default();
        match v.iter_mut().find(|(s, _)| *s == at) {
            Some((_, old)) if (k - &*old).is_empty() => return,
            Some((_, old)) => *old = &*old | k,
            None => v.push((at, k.clone())),
        }
        self.put(Undo::Passes(span, Some(v)));
    }

    /// Checks the needs of `sig`, named `what`, at a call at `span` that binds its variables
    /// as `binds`, in the order its body met them; binds what each use gives. A need on a
    /// value of type `_` fails, since the value may be any.
    ///
    /// A need met again inside its own check, as by `w(w)` for `w(f) = f(f)`, on the same type
    /// up to its variables, gives the least result: the inner use first gives nothing, and if
    /// the check took that, it runs once more with the inner use giving what the first run
    /// gave. The second result must lie within the first, which then holds every value the
    /// use may give; otherwise the result is not settled and it is an error. Met again on
    /// another type, it is an error, since the types could grow without end. So the checks
    /// nest at most as deep as the program has needs.
    ///
    /// A need on a variable of `defer`, or on what such a need gives, is left: the needs left
    /// are given back.
    fn replay(
        &mut self,
        what: &str,
        needs: &[Need],
        binds: &mut Binds,
        mut defer: BTreeSet<Arc<str>>,
        span: Span,
    ) -> Vec<Need> {
        let mut left = Vec::new();
        for n in needs {
            if !defer.is_empty() {
                let mut vars = Vars::default();
                n.vars_in(&mut vars);
                if vars.order.iter().any(|v| defer.contains(v)) {
                    defer.extend(vars.order);
                    left.push(n.clone());
                    continue;
                }
            }
            let from = self.info.errors.len();
            let on = bound(&n.on, binds, |v| self.is_class(v));
            let shape = bound(&on, &Binds::new(), |v| self.is_class(v));
            let got = match self.open.iter_mut().find(|o| o.span == n.span) {
                _ if on.dynamic => {
                    self.any(&format!("{what}, which needs this of its argument,"), span);
                    Ty::empty()
                }
                Some(o) if o.shape == shape => {
                    o.used = true;
                    o.result.clone()
                }
                Some(o) => {
                    let t = o.shape.clone();
                    let (on, t) = (self.text(&on), self.text(&t));
                    self.error(
                        span,
                        format!(
                            "{what} needs this of its argument again inside its own check, on \
                             {on} where it was {t}: the checker does not follow a call at a \
                             type that may grow without end"
                        ),
                    );
                    Ty::empty()
                }
                None => {
                    let before = binds.clone();
                    let errors = self.info.errors.len();
                    self.open.push(Open {
                        span: n.span,
                        shape,
                        result: Ty::empty(),
                        used: false,
                    });
                    let passing = self.need_passed.len();
                    let mut got = self.meet(n, &on, binds, span);
                    let used = self.open.last().is_some_and(|o| o.used);
                    if used && !got.is_empty() {
                        *binds = before;
                        self.info.errors.truncate(errors);
                        self.need_passed.truncate(passing);
                        let o = self.open.last_mut().expect("the need just pushed");
                        o.result = got.clone();
                        let first = got;
                        got = self.meet(n, &on, binds, span);
                        if !self.subtype(&got, &first) {
                            let why = got.refused(&first);
                            let (got, first) = (self.text(&got), self.text(&first));
                            self.error(
                                span,
                                format!(
                                    "{what} needs this of its argument again inside its own \
                                     check, and the result is not settled: it gives {got} \
                                     where the use inside gave {first}{why}"
                                ),
                            );
                        }
                    }
                    self.open.pop();
                    got
                }
            };
            // What the use gives is within its result: a variable there joins it, as for an
            // argument, and one it leaves unbound gives nothing.
            if let Some(r) = &n.result {
                if !self.sub(&got, r, binds) {
                    let why = got.refused(r);
                    self.error(
                        span,
                        format!(
                            "{what} gives {} here, which is not {}{why}",
                            self.text(&got),
                            self.text(r)
                        ),
                    );
                }
                for v in &r.vars {
                    binds.entry(v.clone()).or_insert_with(Ty::empty);
                }
            }
            self.also(from, n.span, |_| {
                format!("{what} needs this of its argument here")
            });
        }
        left
    }

    /// Checks that a value of `on` may be passed, by `what` at `span`, at a parameter of the
    /// closed type `ty`.
    fn into(&mut self, on: &Ty, ty: &Ty, what: &str, span: Span) {
        for piece in on.pieces() {
            let ok = match self.class_of(&piece) {
                _ if piece == Piece::Dyn => ty.dynamic,
                _ if matches!(piece, Piece::Var(_)) && self.class_of(&piece).is_none() => true,
                Some(k) => {
                    let ok = self.restrict(k, mask_of(ty), what, span);
                    let kind = NeedKind::Into {
                        what: what.into(),
                        ty: ty.clone(),
                    };
                    self.need(k, kind, false, span);
                    ok
                }
                None => match &piece {
                    Piece::Fn(s) if !s.needs.is_empty() => {
                        self.fit_needs(s, ty, &mut Binds::new(), what, span)
                    }
                    _ => self.sub(&piece.ty(), ty, &mut Binds::new()),
                },
            };
            if !ok {
                let p = self.show(&piece.ty());
                let why = on.of_piece(&piece).refused(ty);
                self.error(
                    span,
                    format!(
                        "{what} does not take {p}, which is not {}{why}",
                        self.text(ty)
                    ),
                );
            }
        }
    }

    /// Whether a function of `s`, whose body has needs, may be passed, by `what` at `span`,
    /// at a parameter of type `p`: `s` applied to the parameters of `p`'s one function type
    /// gives its result. The application reports its own errors.
    fn fit_needs(
        &mut self,
        s: &Arc<Sig>,
        p: &Ty,
        binds: &mut Binds,
        what: &str,
        span: Span,
    ) -> bool {
        let bare = Sig {
            needs: Vec::new(),
            ..(**s).clone()
        };
        let [q] = p.fns.iter().collect::<Vec<_>>()[..] else {
            return false;
        };
        if !self.sub(&Ty::func(Arc::new(bare)), p, binds) {
            return false;
        }
        let q = q.replace(binds);
        let from = self.info.errors.len();
        let mut ok = true;
        for a in &q.arrows {
            let args = a.params.iter().map(|t| Some(Arg::of(t.clone()))).collect();
            let (r, _) = self.apply(what, s, args, false, span);
            ok &= self.subtype(&r, &a.result);
        }
        ok || self.info.errors.len() > from
    }

    /// The literal `l` joins class `k`; unless it follows, the class keeps only the carriers
    /// it may adopt, and false if none would be left. A generic literal keeps only those that
    /// hold it exactly: `9007199254740993n` removes `f64`.
    fn join(&mut self, k: usize, l: &Lit, follower: bool) -> bool {
        if !follower {
            let m = Carrier::ALL
                .into_iter()
                .filter(|&c| adoptable(l, c) && (!l.generic || adopt(l, c).is_ok()))
                .fold(0, |m, c| m | c.bit());
            if !self.restrict(k, m, &format!("the literal {}", l.text), l.span) {
                return false;
            }
        }
        let r = self.find(k);
        self.touch(r);
        self.classes[r].lits.push((l.clone(), follower));
        true
    }

    /// The values of `t` flow into class `k`: a class merges with it, a carrier restricts it
    /// to that carrier, and a tuple or a function to other values; atoms change nothing, and
    /// a value of type `_`, which may be any, does not flow.
    fn flow(&mut self, k: usize, t: &Ty, what: &str, span: Span) -> bool {
        for p in t.pieces() {
            let ok = match (self.class_of(&p), p.carrier()) {
                (Some(j), _) => self.merge(k, j, what, span),
                _ if p == Piece::Dyn => false,
                _ if matches!(p, Piece::Var(_)) || p.is_atoms() => true,
                (None, Some(c)) => self.restrict(k, c.bit(), what, span),
                (None, None) => self.restrict(k, OTHER, what, span),
            };
            if !ok {
                return false;
            }
            if matches!(p, Piece::Tuple(_) | Piece::Fn(_)) {
                let r = self.find(k);
                let t = p.ty();
                let uses: Vec<Need> = self.classes[r]
                    .uses
                    .iter()
                    .map(|(_, n)| n.clone())
                    .collect();
                self.touch(r);
                self.classes[r].flowed.push((t.clone(), span));
                for n in &uses {
                    self.check_on(n, &t, span);
                }
            }
        }
        true
    }

    /// Gives class `r` its type: the first of int, f64 and rat it may take if a literal that
    /// neither follows nor is generic joined it, or a generic one with no other operand and no
    /// parameter of the class in scope at it ([`Info::witness`]), every literal adopting it;
    /// a type variable if it may take any value; its carrier if one; a type variable bounded
    /// by its carriers if several; else the unknown.
    ///
    /// Complexity tradeoff: a class that a literal joined takes one carrier, the first of int,
    /// f64 and rat, so a function such as `f(x) = x * 2` takes int only, and a call at f64 is
    /// rejected ("`f` does not take (1.5)") though the body would check there. Why: the body
    /// elaborates once; keeping each carrier a literal may adopt would elaborate the body once
    /// per combination of carriers over its classes, 3^k for k such classes. Trigger: a
    /// parameter's class joined by a literal that does not follow another operand's carrier.
    /// Test: `l01_26_type_resolution::adoption::a_body_keeps_the_arrows_with_the_fewest_adoptions`.
    /// COMPLEXITY.md Kept row "undeclared parameters (check), `apply`"; docs/thresholds.md
    /// replacement 1. A complete solution would give the class a type variable bounded by its
    /// numeric carriers and elaborate the literal at each carrier the calls use (one
    /// elaboration per carrier used, not per combination). The written way out is a generic
    /// literal (step L1.26a): `f(x) = x * 2n` takes int, f64 and rat, its `2n` taking the
    /// carrier of `x` by one `match` at run time.
    fn resolve(&mut self, r: usize) {
        let (mask, lits) = (self.classes[r].mask, self.classes[r].lits.clone());
        // A generic literal with no other operand takes the carrier from a parameter of the
        // class in scope at it; with none, it is read as a plain literal, which fixes the
        // class's carrier.
        let binder = self.classes[r].binder;
        let witness = |l: &Lit| {
            binder
                .filter(|(_, s)| s.start <= l.span.start && l.span.end <= s.end)
                .map(|(id, _)| id)
        };
        let numeric = [Carrier::Int, Carrier::F64, Carrier::Rat]
            .into_iter()
            .find(|c| mask & c.bit() != 0)
            .filter(|_| {
                lits.iter().any(|(l, follows)| {
                    !follows && (!l.generic || (l.witness && witness(l).is_none()))
                })
            });
        let ty = match numeric {
            Some(c) => Ty::carrier(c),
            None if mask == EVERY => Ty::var(format!("${r}").into()),
            None if mask & OTHER == 0 && mask.count_ones() == 1 => {
                Ty::carrier(Carrier::of_mask(mask).next().expect("one carrier"))
            }
            None => Ty::var(format!("${r}").into()),
        };
        match ty.numeric_carrier() {
            Some(c) => {
                for (l, _) in &lits {
                    self.adopt_to(l, c);
                }
            }
            // A type variable: each literal compared with the class, and each generic one,
            // takes, at run time, the carrier its other operand has, of those in the bound it
            // is exactly.
            None => {
                for (l, _) in lits.iter().filter(|(l, follows)| *follows || l.generic) {
                    let values: Vec<(Carrier, Value)> = [Carrier::Int, Carrier::F64, Carrier::Rat]
                        .into_iter()
                        .filter(|&c| mask & c.bit() != 0 && c != lit_carrier(&l.value))
                        .filter_map(|c| match adopt(l, c) {
                            Ok(Some(v)) => Some((c, neg_value(&v, l.neg))),
                            // A literal that is not exactly a value of `c`, as `9007199254740993`
                            // at `f64`, equals no value of `c`: it keeps its own carrier, and
                            // the comparison is false there, as it is in exact arithmetic.
                            _ => None,
                        })
                        .collect();
                    if !values.is_empty() {
                        self.put(Undo::Follows(l.span, Some(values)));
                        if l.witness {
                            let id = witness(l).expect("a witnessed literal's binder");
                            self.put(Undo::Witness(l.span, Some(id)));
                        }
                    }
                }
            }
        }
        self.classes[r].resolved = Some(ty);
    }

    /// The class `p` is, if it is a class not yet resolved: its root.
    fn class_of(&self, p: &Piece) -> Option<usize> {
        let Piece::Var(v) = p else {
            return None;
        };
        let r = self.find(class_id(v)?);
        self.classes[r].resolved.is_none().then_some(r)
    }

    /// The class `t` is, if it is one and nothing else.
    fn class_of_ty(&self, t: &Ty) -> Option<usize> {
        match t.pieces().as_slice() {
            [p] => self.class_of(p),
            _ => None,
        }
    }

    /// `t` shown with each class narrowed to some carriers shown as their union.
    fn show(&self, t: &Ty) -> String {
        let t = &self.settled(t);
        show_with(t, &self.masks(t))
    }

    /// The classes of `t` narrowed to some carriers, each with its carriers: what
    /// [`Self::show`] reads of the classes, in the order of `t`'s variables.
    fn masks(&self, t: &Ty) -> Masks {
        let mut out = Masks::new();
        for v in &t.vars {
            if let Some(r) = self.class_of(&Piece::Var(v.clone())) {
                let m = self.classes[r].mask;
                if m != EVERY && m & OTHER == 0 {
                    out.push((v.clone(), m));
                }
            }
        }
        out
    }

    /// The uses that narrowed the classes in `t`; none while a repair is tried, since its
    /// errors are only counted.
    fn reasons(&self, t: &Ty) -> Vec<Note> {
        let mut out: Vec<Note> = Vec::new();
        if self.trying {
            return out;
        }
        let mut seen: HashSet<Note> = HashSet::new();
        for p in t.pieces() {
            if let Some(k) = self.class_of(&p) {
                for r in &self.classes[k].reasons {
                    let n = r.note();
                    if seen.insert(n.clone()) {
                        out.push(n);
                    }
                }
            }
        }
        out
    }

    /// For each class variable in `vars`, its root's type: the one it was given, else the
    /// root's variable.
    fn solving<'v>(&self, vars: impl IntoIterator<Item = &'v Arc<str>>) -> Binds {
        let mut b = Binds::new();
        for v in vars {
            let Some(k) = class_id(v).filter(|&k| k < self.classes.len()) else {
                continue;
            };
            // Every class variable is written `$k` for its class `k`, so a class that is its
            // own root and has no type yet stands for itself, and needs no binding.
            let r = self.find(k);
            match &self.classes[r].resolved {
                Some(t) if t.as_var() != Some(v) => b.insert(v.clone(), t.clone()),
                Some(_) => None,
                None if r != k => b.insert(v.clone(), Ty::var(format!("${r}").into())),
                None => None,
            };
        }
        b
    }

    /// `t` with each class variable replaced by its root's type.
    fn solved(&self, t: &Ty) -> Ty {
        let mut vars = Vars::default();
        t.vars_in(&mut vars);
        t.replace(&self.solving(&vars.order))
    }

    /// The type the class of the variable `v` was solved to, if that holds no variable: a
    /// signature solved before it keeps `v` inside the functions it holds
    /// ([`Self::generalize`]), and each reading of those functions reads it as this type.
    fn stale(&self, v: &str) -> Option<Ty> {
        let k = class_id(v).filter(|&k| k < self.classes.len())?;
        let t = self.classes[self.find(k)].resolved.as_ref()?;
        is_solved(t).then(|| t.clone())
    }

    /// `s` with each solved class variable [`Self::stale`] gives a type replaced by it outside
    /// the functions `s` holds: as a function's arrows and needs are read. The cost is that of
    /// the arrows and needs outside those functions, which reading them costs too.
    fn open(&self, s: &Arc<Sig>) -> Arc<Sig> {
        let mut vs = Vars::default();
        for a in &s.arrows {
            a.params.iter().for_each(|p| p.vars_outside(&mut vs));
            a.result.vars_outside(&mut vs);
        }
        s.needs
            .iter()
            .for_each(|n| n.tys().for_each(|t| t.vars_outside(&mut vs)));
        let binds: Binds = (vs.order.into_iter())
            .filter_map(|v| self.stale(&v).map(|t| (v, t)))
            .collect();
        match binds.is_empty() {
            true => s.clone(),
            false => Arc::new(s.replace_outside(&binds)),
        }
    }

    /// `t` with each solved class variable replaced by its type at every depth, as a message
    /// shows it: at the cost of printing it.
    // Complexity tradeoff: each message settles the type it prints, O(size of the type) per
    // message with no memo across messages; a message prints the whole type anyway, so the
    // order is that of printing it.
    fn settled(&self, t: &Ty) -> Ty {
        let mut vs = Vars::default();
        t.vars_in(&mut vs);
        let binds: Binds = (vs.order.into_iter())
            .filter_map(|v| self.stale(&v).map(|t| (v, t)))
            .collect();
        t.replace(&binds)
    }

    /// The text of `t` in a message.
    fn text(&self, t: &Ty) -> String {
        self.settled(t).to_string()
    }

    /// The text of `s` in a message.
    fn sig_text(&self, s: &Sig) -> String {
        s.solved_with(&|v| self.stale(v)).to_string()
    }

    /// [`Ty::sub`], each solved class variable read as its type ([`Self::stale`]).
    fn sub(&self, a: &Ty, b: &Ty, binds: &mut Binds) -> bool {
        a.sub_with(b, binds, &|v| self.stale(v))
    }

    /// [`Ty::subtype`], each solved class variable read as its type ([`Self::stale`]).
    fn subtype(&self, a: &Ty, b: &Ty) -> bool {
        a.subtype_with(b, &|v| self.stale(v))
    }

    /// Whether `v` is the variable of a class, not of a type variable of a function that
    /// ended, which [`Self::generalize`] named.
    fn is_class(&self, v: &str) -> bool {
        class_id(v)
            .filter(|&k| k < self.classes.len())
            .is_some_and(|k| self.classes[self.find(k)].name.is_none())
    }

    /// The names of the type variables `vars` holds that functions which ended named.
    fn names(&self, vars: impl IntoIterator<Item = Arc<str>>) -> Binds {
        vars.into_iter()
            .filter_map(|v| {
                let k = class_id(&v).filter(|&k| k < self.classes.len())?;
                let name = self.classes[self.find(k)].name.clone()?;
                Some((v, Ty::var(name)))
            })
            .collect()
    }

    /// `t` with each type variable of a function that ended given its name.
    fn shown(&self, t: &Ty) -> Ty {
        let mut vars = Vars::default();
        t.vars_in(&mut vars);
        t.renamed(&self.names(vars.order))
    }

    /// `s` with each class variable replaced by its type, as [`Self::finish`] puts it: a
    /// type variable of the function around named as one of `s`'s own takes the next name
    /// `s` does not use.
    fn finished(&self, s: &Sig) -> Sig {
        // One that holds no class variable, as most do once settled, is as it is.
        if s.facts().classes.is_empty() {
            return s.clone();
        }
        let mut b = self.solving(&sig_vars(s));
        for t in b.values_mut() {
            *t = self.shown(t);
        }
        let s = &s.renamed(&self.names(sig_vars(s)));
        let vars = sig_vars(s);
        let own: HashSet<Arc<str>> = vars
            .iter()
            .filter(|v| class_id(v).is_none())
            .cloned()
            .collect();
        let mut used = own.clone();
        for t in b.values() {
            used.extend(t.vars.iter().cloned());
        }
        let mut renamed: BTreeMap<Arc<str>, Arc<str>> = BTreeMap::new();
        let mut n = 0;
        for t in b.values_mut() {
            let Some(v) = t.vars.iter().find(|v| own.contains(*v)).cloned() else {
                continue;
            };
            let to = renamed
                .entry(v.clone())
                .or_insert_with(|| {
                    loop {
                        let name = var_name(n);
                        n += 1;
                        if used.insert(name.clone()) {
                            break name;
                        }
                    }
                })
                .clone();
            *t = t.subst(&[(v, Ty::var(to))].into());
        }
        s.replace(&b)
    }

    /// Puts each class's type in place of its variable in what the checker found. Each
    /// signature is settled first ([`Sig::settle`]): the signatures of calls through values
    /// share the functions they hold, as `g(0)(1)…(n)` does, and are settled once each, not
    /// once for each signature that holds them.
    fn finish(&mut self) {
        let sigs = std::mem::take(&mut self.info.sigs);
        self.info.sigs = sigs
            .into_iter()
            .map(|(k, s)| (k, self.finished_arc(&s)))
            .collect();
        let calls = std::mem::take(&mut self.info.calls);
        self.info.calls = calls
            .into_iter()
            .map(|(k, s)| (k, self.finished_arc(&s)))
            .collect();
        let tops = std::mem::take(&mut self.info.tops);
        self.info.tops = tops
            .into_iter()
            .map(|(k, t)| (k, self.shown(&self.solved(&t))))
            .collect();
        let mut errors = std::mem::take(&mut self.info.errors);
        for e in &mut errors {
            e.message = self.named(&e.message);
            for n in &mut e.notes {
                n.text = self.named(&n.text);
            }
        }
        self.info.errors = errors;
    }

    /// [`Self::finished`] on `s` settled, which is `s` itself when it holds no class variable.
    fn finished_arc(&self, s: &Arc<Sig>) -> Arc<Sig> {
        let s = s.settle(&|v| self.stale(v));
        match s.facts().classes.is_empty() {
            true => s,
            false => Arc::new(self.finished(&s)),
        }
    }

    /// `text` with each class variable replaced by its type. A `$k` is left in a text by the
    /// printer only where it is printed by name, inside a signature that bounds it by carriers
    /// (printed alone it is `_`), so a class that is a named type variable is written by its
    /// name there. A `$$k`, which a note writes for the type its class takes in the end, is
    /// that type printed alone.
    fn named(&self, text: &str) -> String {
        let mut out = String::new();
        let mut rest = text;
        while let Some(i) = rest.find('$') {
            out.push_str(&rest[..i]);
            let mut tail = &rest[i + 1..];
            let alone = tail.starts_with('$');
            if alone {
                tail = &tail[1..];
            }
            let n = tail.bytes().take_while(u8::is_ascii_digit).count();
            match tail[..n]
                .parse::<usize>()
                .ok()
                .filter(|&k| k < self.classes.len())
            {
                Some(k) => {
                    let t = self.shown(&self.solved(&Ty::var(format!("${k}").into())));
                    match t.as_var() {
                        Some(v) if !alone && class_id(v).is_none() => out.push_str(v),
                        _ => out.push_str(&t.to_string()),
                    }
                }
                None => {
                    out.push_str(if alone { "$$" } else { "$" });
                    out.push_str(&tail[..n]);
                }
            }
            rest = &tail[n..];
        }
        out.push_str(rest);
        out
    }

    /// The literal `l` adopting `c`, recorded; an error when it is not exactly a `c`.
    fn adopt_to(&mut self, l: &Lit, c: Carrier) -> Ty {
        match adopt(l, c) {
            Ok(None) => lit_ty(&l.value, l.neg),
            Ok(Some(v)) => {
                let t = lit_ty(&v, l.neg);
                self.put(Undo::Adopt(l.span, Some(v)));
                t
            }
            Err(m) => {
                self.error(l.span, m);
                lit_ty(&l.value, l.neg)
            }
        }
    }

    /// Binds the names of the pattern `p`, matched on a value of `v`, from the binder `next`
    /// on, in the order the resolver gave them: each to what the payloads of `v`'s atoms of
    /// the pattern's name hold there.
    ///
    /// The patterns nest as deep as the text, so the walk keeps its own stack: each pattern
    /// being matched, its atom, the type it is matched on (`None` for `v`), and its next slot.
    fn bind_pattern(&mut self, p: &Pattern, v: &Ty, mut next: usize) {
        let atom_of = |p: &Pattern| -> Arc<str> {
            let Pattern::Atom { name, .. } = p else {
                unreachable!("resolve rejects the forms of layer L2")
            };
            name.as_str().into()
        };
        let mut stack: Vec<(&Pattern, Arc<str>, Option<Ty>, usize)> =
            vec![(p, atom_of(p), None, 0)];
        while let Some((p, atom, on, i)) = stack.last_mut() {
            let Pattern::Atom {
                fields,
                items,
                span,
                ..
            } = *p
            else {
                unreachable!("resolve rejects the forms of layer L2")
            };
            let (slot, sub) = match fields.get(*i) {
                Some((f, sub)) => (Slot::Field(f.as_str().into()), sub.as_ref()),
                None => match items.get(*i - fields.len()) {
                    Some(sub) => (Slot::Item(*i - fields.len()), Some(sub)),
                    None => {
                        stack.pop();
                        continue;
                    }
                },
            };
            *i += 1;
            let t = self.payload(on.as_ref().unwrap_or(v), atom, &slot, *span);
            match sub {
                Some(sub) => stack.push((sub, atom_of(sub), Some(t), 0)),
                None => {
                    self.env.insert(next, t);
                    next += 1;
                }
            }
        }
    }

    /// What the payloads of the atoms named `atom` among the values of `v` hold at `slot`,
    /// for a pattern at `span`: what the shapes they were built with hold there, what a need
    /// gives on a type variable's class, and the unknown where it is not known.
    fn payload(&mut self, v: &Ty, atom: &Arc<str>, slot: &Slot, span: Span) -> Ty {
        let mut known = v.clone();
        known.vars.clear();
        known.dynamic = false;
        let mut out = match known.shapes(atom) {
            Some(ss) => Ty::union_all(ss.iter().filter_map(|s| s.at(slot))),
            None => Ty::dynamic(),
        };
        if v.dynamic {
            out = out.union(&Ty::dynamic());
        }
        for x in &v.vars {
            let t = match self.class_of(&Piece::Var(x.clone())) {
                Some(k) => {
                    let kind = NeedKind::Payload {
                        atom: atom.clone(),
                        slot: slot.clone(),
                    };
                    self.need(k, kind, true, span)
                }
                None => Ty::dynamic(),
            };
            out = out.union(&t);
        }
        out
    }

    /// The loose atoms of `t`, which flow through `what` unchanged: an atom of a named family
    /// is data, and data that selects no arrow is an error (sec:failure).
    fn passing(&mut self, t: &Ty, what: &str, span: Span) -> Ty {
        if !t.family.is_empty() {
            self.error(
                span,
                format!("{what} does not take {}", Ty::set(t.family.clone())),
            );
        }
        t.loose_ty()
    }

    /// Narrows the binders of `facts`, each origin now the test; gives what to restore.
    fn narrow(&mut self, facts: &Facts) -> walk::Saved<'a> {
        facts
            .iter()
            .map(|(b, t, test)| {
                let old = self.whence.get(b).cloned();
                let o = Origin {
                    span: *test,
                    why: Why::Narrowed(t.clone()),
                    from: None,
                    then: old.clone(),
                };
                self.whence.insert(*b, Rc::new(o));
                (*b, self.env.insert(*b, t.clone()), old)
            })
            .collect()
    }

    /// Restores what [`Self::narrow`] changed.
    fn widen(&mut self, saved: walk::Saved<'a>) {
        for (b, old, o) in saved.into_iter().rev() {
            match old {
                Some(t) => self.env.insert(b, t),
                None => self.env.remove(&b),
            };
            match o {
                Some(o) => self.whence.insert(b, o),
                None => self.whence.remove(&b),
            };
        }
    }

    /// `x ** n` on an `int` `x` needs `n : int[0..]`, decided from the interval of `n`'s
    /// expression or the listed `int` values of its type. A class's values are not known here.
    fn exponent(&mut self, x: &Arg, n: &Arg, e: &'a Expr, span: Span) {
        let int = KType::int();
        let ns = &n.ty.set & &int;
        if (&x.ty.set & &int).is_empty() || ns.is_empty() {
            return;
        }
        let zero = Value::Int(0);
        let listed = ns.ints_listed();
        let at_least_zero = self
            .known(e)
            .ints
            .is_subset(&IntervalSet::range(End::of(0), PosInf))
            || listed.is_some_and(|vs| {
                vs.iter().all(|v| {
                    v.surface_cmp(&zero)
                        .is_some_and(|o| o != std::cmp::Ordering::Less)
                })
            });
        if !at_least_zero {
            let shown = self.show(&Ty::set(ns));
            let notes = self.derive(&[n.at.unwrap_or(span)]);
            self.error_with(
                span,
                format!("`**` on an int needs an exponent of at least 0, and this one is {shown}"),
                notes,
            );
        }
    }

    /// Checks that a value of `t` is data, as `what` at `span` needs (L1.17): it holds no
    /// function at any depth.
    fn data(&mut self, t: &Ty, what: &str, span: Span) {
        if let Some(s) = t.held_function() {
            let s = self.sig_text(s);
            self.error(
                span,
                format!("{what} takes data, and this value may hold a function, `{s}`"),
            );
        }
        // A class, at any depth, needs data of each of its values. A row that holds no class
        // or unknown is not entered; nor is one whose classes were checked as data when it
        // was made, since a class keeps a data need once it has one and a second is nothing.
        // Of such a row only its unknown is reported, once, as each would be at this span.
        let mut stack = vec![t];
        while let Some(t) = stack.pop() {
            for r in t.tuples.iter().filter(|r| r.open()) {
                match r.data() {
                    true if r.dynamic() => self.any(what, span),
                    true => {}
                    false => stack.extend(r.iter()),
                }
            }
            for v in &t.vars {
                if let Some(k) = self.class_of(&Piece::Var(v.clone())) {
                    self.need(k, NeedKind::Data(what.into()), false, span);
                }
            }
            if t.dynamic {
                self.any(what, span);
            }
        }
    }

    /// Reports `what`, a use that does not take every value, of a value of type `_`, which may
    /// be any: an `is` test narrows it first (DESIGN.md, Soundness).
    fn any(&mut self, what: &str, span: Span) {
        self.error(
            span,
            format!("{what} does not take every value, and this value is `_`, which may be any: test it with `is` first"),
        );
    }

    /// Checks that a value of `t` may be pushed to a `Lines` port (L1.19): a `String` or a
    /// family of strings. A failure is disposed of before it reaches a port (sec:failure). A
    /// family writes its stored entries, so the `#notFound` of a key it lacks is not pushed;
    /// at L1 the families are the `Lines` and `CommandLine` ports, which store no `#notFound`.
    fn pushed(&mut self, t: &Ty, span: Span) {
        let strings = |t: &KType| t.subtype(&KType::string());
        let plain = |t: &Ty| t.tuples.is_empty() && t.vars.is_empty();
        let not_found = KType::atom("notFound");
        let ok = strings(&t.set)
            && plain(t)
            && t.fns.iter().all(|s| {
                s.data
                    && s.arrows
                        .iter()
                        .all(|a| plain(&a.result) && strings(&(&a.result.set - &not_found)))
            });
        if !ok && !t.dynamic && t.vars.is_empty() {
            self.error(
                span,
                format!(
                    "a `Lines` port takes a `String` or a family of strings, not {}",
                    self.show(t)
                ),
            );
        }
    }

    /// `==` and `!=`: any two values; a literal adopts the carrier the other side's type gives
    /// it by the rule of a parameter ([`carriers_in`]), and of two literals the integer adopts
    /// the other's. Two tuples of one length are paired component by component, at any depth,
    /// across every tuple shape of that length a side's type holds, as [`adopted`] pairs them:
    /// `p == (1, 2)` with `p: (f64, f64) | (String, f64)` reads both literals at `f64`.
    ///
    /// The tuples nest as deep as the text, so the pairs wait on a stack, each with whether it
    /// is inside a tuple. Each side borrows its component types, one per shape, so a tuple
    /// nested d deep at s shapes costs O(d·s) and not a copy of each level's type.
    fn equal(&mut self, x: &Arg, y: &Arg) {
        self.pair(side(x), side(y));
    }

    /// [`Ck::equal`] of the two sides `x` and `y`.
    fn pair(&mut self, x: Side<'_>, y: Side<'_>) {
        let mut stack = vec![(x, y, false)];
        while let Some(((xt, xl, xp), (yt, yl, yp), inner)) = stack.pop() {
            match (xl, yl) {
                (Some(l), Some(m)) => {
                    let (lc, mc) = (lit_carrier(&l.value), lit_carrier(&m.value));
                    if rank(lc) < rank(mc) {
                        self.adopt_to(l, mc);
                    } else if rank(mc) < rank(lc) {
                        self.adopt_to(m, lc);
                    }
                }
                (Some(l), None) => self.follow(l, &yt, inner),
                (None, Some(m)) => self.follow(m, &xt, inner),
                (None, None) if xp.is_none() && yp.is_none() => {}
                (None, None) => {
                    let n = xp.or(yp).map_or(0, <[Part]>::len);
                    let (Some(xs), Some(ys)) = (sides(&xt, xp, n), sides(&yt, yp, n)) else {
                        continue;
                    };
                    stack.extend(xs.zip(ys).map(|(a, b)| (a, b, true)));
                }
            }
        }
    }

    /// The literal `l` compared with a value of one of the types `ts`: it follows the class
    /// of a lone `ts`, outside a tuple, and otherwise adopts the one carrier [`carriers_in`]
    /// finds; at two or more it keeps its own carrier when one of them is that, and is an
    /// error otherwise, as at a parameter.
    // A literal in a tuple compared with a class's component keeps its own carrier, because
    // the elaborator's rewrite that follows the class's carrier at run time (`Info::follows`)
    // is built for an operand of `==` only; follow-up LIT-follow-tuple.
    fn follow(&mut self, l: &Lit, ts: &[&Ty], inner: bool) {
        if let [t] = ts
            && let Some(k) = self.class_of_ty(t)
        {
            if !inner {
                self.join(k, l, true);
            }
            return;
        }
        let cs = carriers_in(l, ts);
        match cs[..] {
            [c] => {
                self.adopt_to(l, c);
            }
            [_, _, ..] if !cs.contains(&lit_carrier(&l.value)) => {
                let want = Ty::union_all(ts.iter().copied());
                self.error(l.span, no_one_carrier(l, &want, &cs));
            }
            _ => {}
        }
    }

    /// An ordering: two values of one carrier, or two tuples of one length; atoms pass.
    fn compare(&mut self, op: &str, x: Arg, y: Arg, span: Span) -> Ty {
        let what = format!("`{op}`");
        if x.ty.tuples.is_empty() && y.ty.tuples.is_empty() {
            return self
                .apply(&what, &op_sig("<"), vec![Some(x), Some(y)], true, span)
                .0;
        }
        let out = self.passing(&x.ty, &what, span);
        let out = out.union(&self.passing(&y.ty, &what, span));
        self.components(&what, &x.ty.without_loose(), &y.ty.without_loose(), span);
        out.union(&Ty::carrier(Carrier::Bool))
    }

    /// Checks that each value of `a` compares with each of `b` (sec:keys): two numbers of one
    /// carrier or two values of one other kind, the atoms as data, and two tuples component by
    /// component as far as the shorter goes, since a proper prefix comes first.
    fn components(&mut self, what: &str, a: &Ty, b: &Ty, span: Span) {
        let refuse = |ck: &mut Self, p: &Piece, q: &str| {
            let p = ck.text(&p.ty());
            ck.error(span, format!("{what} does not compare {p} with {q}"));
        };
        for (s, t) in [(a, b), (b, a)] {
            let atoms = !s.atoms().is_empty();
            for p in t.pieces() {
                let ok = match self.class_of(&p) {
                    Some(k) if !s.tuples.is_empty() => self.restrict(k, OTHER, what, span),
                    Some(_) => true,
                    None => match &p {
                        Piece::Dyn => false,
                        Piece::Var(_) | Piece::Tuple(_) => true,
                        _ if !s.tuples.is_empty() => false,
                        _ => !atoms || p.is_atoms() || p.carrier().is_none(),
                    },
                };
                if !ok {
                    let q = if s.tuples.is_empty() {
                        "an atom"
                    } else {
                        "a tuple"
                    };
                    return refuse(self, &p, q);
                }
            }
        }
        for s in &a.tuples {
            for t in &b.tuples {
                for (c, d) in s.iter().zip(t) {
                    self.components(what, c, d, span);
                }
            }
        }
        let rest = |t: &Ty| Ty {
            tuples: Vec::new(),
            ..t.without_atoms()
        };
        let (x, y) = (rest(a), rest(b));
        if !x.is_empty() && !y.is_empty() {
            self.apply(
                what,
                &op_sig("<"),
                vec![Some(Arg::of(x)), Some(Arg::of(y))],
                true,
                span,
            );
        }
    }

    fn name(&mut self, span: Span) -> Ty {
        match self.t.res.uses.get(&span) {
            Some(Ref::Bound(ids)) if ids.len() == 1 => {
                self.env.get(&ids[0]).cloned().unwrap_or_else(Ty::dynamic)
            }
            Some(Ref::Prelude(w)) if w != "sum" => Ty::func(word_sig(w)),
            // Elaboration rejects a use of an overloaded name.
            Some(Ref::Bound(_)) => Ty::empty(),
            _ => Ty::dynamic(),
        }
    }

    /// The declared function that `e` names, if it names exactly one.
    fn declared(&self, e: &Expr) -> Option<usize> {
        match (&e.kind, self.t.res.uses.get(&e.span)) {
            (ExprKind::Name(_), Some(Ref::Bound(ids))) if ids.len() == 1 => {
                self.t.funcs.contains_key(&ids[0]).then_some(ids[0])
            }
            _ => None,
        }
    }

    /// The one function a call's callee names, and for a method call `x.r()` or `x?.r()` its
    /// receiver `x` and whether it is `?.`: the callee `r` or `x.r` resolved to one binder whose
    /// type is a function, a declared one or a value, as `call` and `member_end` resolve it.
    /// `x.r()` is `r(x)`: the receiver fills the first parameter.
    fn called<'e>(&self, callee: &'e Expr) -> Option<Called<'e>> {
        let receiver = match &callee.kind {
            ExprKind::Name(_) => None,
            ExprKind::Member { of, safe, .. } => Some((&**of, *safe)),
            _ => return None,
        };
        let Some(Ref::Bound(ids)) = self.t.res.uses.get(&callee.span) else {
            return None;
        };
        if ids.len() != 1 {
            return None;
        }
        Some((self.env.get(&ids[0]).and_then(only_fn)?, receiver))
    }

    /// Checks each operand of the bit word `w` against its domain (DESIGN.md sec:domains):
    /// `int[0..]` for every one but the `x` of `shl` and `shr`, and `int[0..<2 ** width]` for the
    /// `x` of a word with a width. An operand is rejected when its int part is not shown to lie
    /// in the domain, from its listed values or the interval of its expression, as `**`'s
    /// exponent is.
    fn bit_domains(&mut self, w: &str, p: Prim, slots: &[(Arg, &'a Expr)], span: Span) {
        let names = zed_kernel::bits::params(p);
        let shift = matches!(p, Prim::Shl | Prim::Shr);
        let nonneg = IntervalSet::range(End::of(0), PosInf);
        let ranges: Vec<Option<IntRange>> =
            slots.iter().map(|(a, e)| self.int_range(a, e)).collect();
        let mut fine = true;
        for (i, (((a, e), r), name)) in slots.iter().zip(&ranges).zip(names).enumerate() {
            let Some(r) = r else { continue };
            if shift && i == 0 || r.ints.is_subset(&nonneg) {
                continue;
            }
            fine = false;
            let at = a.at.unwrap_or(e.span);
            let shown = &r.shown;
            let mut notes = vec![Note {
                span: at,
                text: format!("`{name}` is this operand, {shown}"),
            }];
            self.derive_into(&[at], &mut notes);
            self.error_with(
                span,
                format!("`{w}` takes `{name}` in int[0..], and this `{name}` is {shown}"),
                notes,
            );
        }
        if !fine || !zed_kernel::bits::has_width(p) {
            return;
        }
        let ((x, xe), (wa, we)) = (&slots[0], &slots[slots.len() - 1]);
        let (Some(rx), Some(rw)) = (&ranges[0], &ranges[slots.len() - 1]) else {
            return;
        };
        // `x` lies below `2 ** width` when its largest value does below the smallest width.
        let (hi, lo) = (
            rx.extreme(std::cmp::Ordering::Greater),
            rw.extreme(std::cmp::Ordering::Less),
        );
        let below = hi
            .zip(lo)
            .is_some_and(|(h, l)| zed_kernel::bits::below_two_pow(&h, &l));
        if !below {
            let (sx, sw) = (&rx.shown, &rw.shown);
            let (ax, aw) = (x.at.unwrap_or(xe.span), wa.at.unwrap_or(we.span));
            let mut notes = vec![
                Note {
                    span: ax,
                    text: format!("`x` is this operand, {sx}"),
                },
                Note {
                    span: aw,
                    text: format!("`width` is this operand, {sw}"),
                },
            ];
            self.derive_into(&[ax, aw], &mut notes);
            self.error_with(
                span,
                format!(
                    "`{w}` takes `x` in int[0..<2 ** width], and this `x` is {sx} with `width` {sw}"
                ),
                notes,
            );
        }
    }

    /// The integers an argument may be, when its type has an int part: an interval holding them,
    /// the values themselves when its type lists them or its text shows its value, and how to
    /// show them. The interval is what the text shows (see [`Known`]), met with the listed
    /// values, a value past `i64` read as the end of the interval on its side.
    fn int_range(&mut self, a: &Arg, e: &'a Expr) -> Option<IntRange> {
        let ns = &a.ty.set & &KType::int();
        if ns.is_empty() {
            return None;
        }
        let k = self.known(e);
        let mut ints = k.ints;
        let listed = ns.ints_listed();
        let shown_as_type = listed.is_some();
        let values = match listed {
            Some(vs) => {
                let piece = |v: &Value| match v {
                    Value::Int(n) => (End::of(*n), End::of(*n)),
                    Value::Big(n) => (Fin(Num::from(&**n)), Fin(Num::from(&**n))),
                    _ => (NegInf, PosInf),
                };
                ints = ints.meet(&IntervalSet::from_pieces(vs.iter().map(piece).collect()));
                Some(vs)
            }
            None => k.value.map(|v| vec![v]),
        };
        let shown = match &values {
            _ if shown_as_type || ints == IntervalSet::top() => self.show(&Ty::set(ns)),
            Some(vs) => vs[0].to_string(),
            None => format!("int{ints}"),
        };
        Some(IntRange {
            ints,
            values,
            shown,
        })
    }
    /// `sum` of a tuple: its components added in turn, `0` for the empty tuple; atoms pass.
    fn sum(&mut self, x: Arg, span: Span) -> Ty {
        let t = &x.ty;
        let mut out = self.passing(t, "`sum`", span);
        let add = op_sig("+");
        for p in t.pieces() {
            match p {
                Piece::Tuple(cs) => {
                    // The components as `+` takes them: a literal written in the tuple stays
                    // one, and adopts the carrier of the others, which are added first. Each
                    // `+` takes its two operands in the order they are written, as a message
                    // shows them.
                    let args = components(&x, cs.len())
                        .unwrap_or_else(|| cs.iter().cloned().map(Arg::of).collect());
                    let mut args: Vec<(usize, Arg)> = args.into_iter().enumerate().collect();
                    args.sort_by_key(|(_, a)| a.lit.is_some());
                    let mut args = args.into_iter();
                    let Some((mut at, mut acc)) = args.next() else {
                        out = out.union(&Ty::lit(&Value::Int(0)));
                        continue;
                    };
                    for (i, c) in args {
                        let pair = if i < at { [c, acc] } else { [acc, c] };
                        let ty = self
                            .apply("`sum`", &add, pair.map(Some).to_vec(), true, span)
                            .0;
                        (at, acc) = (at.min(i), Arg::of(ty));
                    }
                    let acc = acc.ty;
                    if let Some(c) = acc.pieces().iter().find(|p| {
                        !matches!(p, Piece::Var(_))
                            && !p.is_atoms()
                            && !p.carrier().is_some_and(Carrier::numeric)
                    }) {
                        let shown = self.text(&c.ty());
                        self.error(span, format!("`sum` does not take ({shown})"));
                    }
                    out = out.union(&acc);
                }
                Piece::Dyn => self.any("`sum`", span),
                Piece::Var(_) => out = out.union(&Ty::dynamic()),
                p if p.is_atoms() => {}
                p => {
                    let shown = self.text(&p.ty());
                    self.error(span, format!("`sum` does not take ({shown})"))
                }
            }
        }
        out
    }

    /// `sig`, named `what`, applied at `span` to `args`, which leave out the parameters
    /// `missing`: the function of those parameters, each a positional one with no default
    /// when `section`, whose types and needs are `sig`'s with the variables the arguments
    /// bind replaced. The needs on the variables of the parameters left out are checked at
    /// its calls.
    fn partial(
        &mut self,
        sig: &Sig,
        args: Vec<Option<Arg>>,
        missing: &[usize],
        section: bool,
        what: &str,
        span: Span,
    ) -> Ty {
        let mut out = vec![false; sig.params.len()];
        missing.iter().for_each(|&j| out[j] = true);
        let (mut given, mut left) = (Vars::default(), Vars::default());
        for a in &sig.arrows {
            for (j, p) in a.params.iter().enumerate() {
                p.vars_in(if out[j] { &mut left } else { &mut given });
            }
        }
        let given: BTreeSet<Arc<str>> = given.order.into_iter().collect();
        self.defer = left
            .order
            .into_iter()
            .filter(|v| !given.contains(v))
            .collect();
        let (result, kept) = self.apply(&format!("`{what}`"), sig, args, false, span);
        let Some((binds, needs)) = self.applied.take() else {
            return result;
        };
        if missing.is_empty() {
            return result;
        }
        let params = missing
            .iter()
            .map(|&j| match section {
                true => SParam {
                    positional: true,
                    default: None,
                    ..sig.params[j].clone()
                },
                false => sig.params[j].clone(),
            })
            .collect();
        let arrows = kept
            .iter()
            .map(|&k| Arrow {
                params: missing
                    .iter()
                    .map(|&j| sig.arrows[k].params[j].clone())
                    .collect(),
                result: sig.arrows[k].result.clone(),
            })
            .collect();
        let mut rest = Sig {
            params,
            arrows,
            bounds: sig.bounds.clone(),
            data: false,
            needs,
            own: sig.own.clone(),
            held: BTreeSet::new(),
            named: sig.named,
            facts: Default::default(),
        };
        // A variable only the arguments given held is held by no parameter of the rest.
        rest.note_held();
        Ty::func(Arc::new(rest.replace(&binds)))
    }

    /// `v[x]` with `x` no literal: an application of each function `v` may be.
    fn at_key(&mut self, v: &Ty, x: Arg, span: Span) -> Ty {
        let mut out = self.passing(v, "a call", span);
        for p in v.pieces() {
            match p {
                Piece::Fn(sig) => {
                    let r = self
                        .apply("this function", &sig, vec![Some(x.clone())], false, span)
                        .0;
                    out = out.union(&r);
                }
                Piece::Var(_) if let Some(k) = self.class_of(&p) => {
                    let r = self.need(k, NeedKind::Index(x.ty.clone()), true, span);
                    out = out.union(&r);
                }
                Piece::Dyn => self.any("an application", span),
                Piece::Var(_) => out = out.union(&Ty::dynamic()),
                p if p.is_atoms() => {}
                p => {
                    let shown = self.text(&p.ty());
                    self.error(span, format!("this value is {shown}, not a function"));
                }
            }
        }
        out
    }

    /// `v[i]` with the literal `x`, `i` if it is a component number: a tuple's component, or
    /// a family's entry.
    fn at_index(&mut self, v: &Ty, i: Option<usize>, x: Arg, span: Span) -> Ty {
        let mut out = self.passing(v, "an index", span);
        let shown = x.ty.to_string();
        for p in v.pieces() {
            match p {
                Piece::Fn(sig) if sig.data => {
                    let r = self
                        .apply("this family", &sig, vec![Some(x.clone())], true, span)
                        .0;
                    out = out.union(&r);
                }
                Piece::Tuple(cs) => match i.and_then(|i| cs.get(i)) {
                    Some(c) => out = out.union(c),
                    None => self.error(
                        span,
                        format!(
                            "{} has no component {shown}",
                            self.text(&Ty::of_row(cs.clone()))
                        ),
                    ),
                },
                Piece::Var(_) if let Some(k) = self.class_of(&p) => {
                    let kind = NeedKind::Component {
                        i,
                        key: x.ty.clone(),
                    };
                    out = out.union(&self.need(k, kind, true, span));
                }
                Piece::Dyn => self.any(&format!("`[{shown}]`"), span),
                Piece::Var(_) => out = out.union(&Ty::dynamic()),
                p if p.is_atoms() => {}
                p => {
                    let t = self.text(&p.ty());
                    self.error(span, format!("`[{shown}]` takes a tuple, not {t}"))
                }
            }
        }
        out
    }

    /// A declared function in a slot of the function type `e`: the same number of positional
    /// parameters and the same named ones, in any order, and types that fit.
    fn fit_declared(&mut self, id: usize, e: &Arc<Sig>, span: Span) -> Ty {
        let f = self.t.funcs[&id];
        let own = self.env.get(&id).cloned().unwrap_or_else(Ty::dynamic);
        let Some(s) = only_fn(&own) else {
            return own;
        };
        let pos = |s: &Sig| s.params.iter().filter(|p| p.positional).count();
        let mut from = Vec::new();
        let mut k = 0;
        let mut ok = pos(&s) == pos(e) && s.params.len() == e.params.len();
        let epos: Vec<usize> = (0..e.params.len())
            .filter(|&j| e.params[j].positional)
            .collect();
        for p in &s.params {
            if !ok {
                break;
            }
            if p.positional {
                from.push(epos[k]);
                k += 1;
            } else {
                match e
                    .params
                    .iter()
                    .position(|q| !q.positional && q.name == p.name)
                {
                    Some(j) => from.push(j),
                    None => ok = false,
                }
            }
        }
        if !ok {
            let names: Vec<&str> = f.params.iter().map(|p| p.name.as_str()).collect();
            let call: Vec<String> = names.iter().map(|n| format!("{n}: {n}")).collect();
            let shown = self.sig_text(e);
            self.rejects(
                Row::ParameterKinds,
                span,
                format!(
                    "the parameters of `{}` ({}) do not fit `{shown}`: declare them as it passes them, \
                     with `positional` where it passes by position, or pass a lambda, ({}) -> {}({})",
                    f.name,
                    s.params
                        .iter()
                        .map(|p| match p.positional {
                            true => format!("positional {}", p.name),
                            false => p.name.to_string(),
                        })
                        .collect::<Vec<_>>()
                        .join(", "),
                    names.join(", "),
                    f.name,
                    call.join(", ")
                ),
            );
            return Ty::func(e.clone());
        }
        // `s` with its parameters in `e`'s order.
        let mut inv = vec![0; from.len()];
        for (i, &j) in from.iter().enumerate() {
            inv[j] = i;
        }
        let permuted = Sig {
            bounds: s.bounds.clone(),
            data: s.data,
            needs: s.needs.clone(),
            own: s.own.clone(),
            held: s.held.clone(),
            named: s.named,
            facts: Default::default(),
            params: e.params.clone(),
            arrows: s
                .arrows
                .iter()
                .map(|a| Arrow {
                    params: inv.iter().map(|&i| a.params[i].clone()).collect(),
                    result: a.result.clone(),
                })
                .collect(),
        };
        let what = format!("`{}`", f.name);
        let permuted = Arc::new(permuted);
        if !self.fits_slot(&permuted, e, &what, span) {
            // The cover of rule 6 the checker refuses, if that is why ([`ty::why_unfit`]).
            let why = match permuted.needs.is_empty() {
                true => ty::why_unfit_with(&permuted, e, &|v| self.stale(v))
                    .map_or_else(String::new, |w| format!(": {w}")),
                false => String::new(),
            };
            let (s, e) = (self.sig_text(&s), self.sig_text(e));
            self.error(span, format!("`{}` is `{s}`, not `{e}`{why}", f.name));
        }
        if from.iter().enumerate().any(|(i, &j)| i != j) {
            self.put(Undo::Fit(span, Some(Fit::Adapter { from })));
        }
        Ty::func(e.clone())
    }

    /// Whether the function `s`, named `what` in messages, with its parameters in the order of
    /// the function type `e`'s, fits a slot of `e`: as a type, or, when its body makes uses of
    /// its type variables, by those uses checked on the types `e` passes. False only when no
    /// error says why.
    fn fits_slot(&mut self, s: &Arc<Sig>, e: &Arc<Sig>, what: &str, span: Span) -> bool {
        match s.needs.is_empty() {
            true => ty::fits_sig_with(s, e, &|v| self.stale(v)),
            false => {
                let p = Ty::func(e.clone());
                self.fit_needs(s, &p, &mut Binds::new(), what, span)
            }
        }
    }

    /// The derivation of an application `apply` rejects: each argument's, in order, then each
    /// arrow of `sig`, the constraints it failed.
    fn applied(&self, what: &str, sig: &Sig, args: &[Option<Arg>], span: Span) -> Vec<Note> {
        let mut out = Vec::new();
        for a in args.iter().flatten() {
            match (&a.lit, a.at) {
                (Some(l), Some(at)) => out.push(Note {
                    span: at,
                    text: format!("this literal, {}, is {}", l.text, self.text(&a.ty)),
                }),
                (None, Some(at)) => self.derive_into(&[at], &mut out),
                _ => {}
            }
        }
        for arrow in &sig.arrows {
            let one = Sig {
                params: sig.params.clone(),
                arrows: vec![arrow.clone()],
                bounds: sig.bounds.clone(),
                data: sig.data,
                needs: Vec::new(),
                own: sig.own.clone(),
                held: sig.held.clone(),
                named: sig.named,
                facts: Default::default(),
            };
            out.push(Note {
                span,
                text: format!("{what} takes {}", self.sig_text(&one)),
            });
        }
        out
    }

    /// The repairs of a rejected application the checker discharges: each argument wrapped
    /// in a prelude word, when the application then checks, tried with the checker's state
    /// restored after.
    fn repairs(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &[Option<Arg>],
        pass: bool,
        span: Span,
    ) -> Vec<Note> {
        let mut out = Vec::new();
        if self.trying {
            return out;
        }
        for (i, a) in args.iter().enumerate() {
            let Some(Arg {
                lit: None,
                at: Some(at),
                ty,
                ..
            }) = a
            else {
                continue;
            };
            for w in ["String", "int", "rat", "f64"] {
                let Some(r) = converted(&word_sig(w), ty) else {
                    continue;
                };
                let mut with = args.to_vec();
                with[i] = Some(Arg::of(r));
                let saved = self.mark();
                self.trying = true;
                self.apply(what, sig, with, pass, span);
                let ok = self.info.errors.len() == saved.errors;
                self.trying = false;
                self.undo(&saved);
                if ok {
                    out.push(Note {
                        span: *at,
                        text: format!("repair: wrap this in `{w}(…)`; the checker accepts that"),
                    });
                }
            }
        }
        out
    }

    /// Adds the note at `span` that `text` words to each error from the `from`th on that lacks
    /// it; the note is put into words only when there is such an error, and none while a
    /// repair is tried, since its errors are only counted.
    fn also(&mut self, from: usize, span: Span, text: impl FnOnce(&Self) -> String) {
        if self.trying || self.info.errors.len() <= from {
            return;
        }
        built(1);
        let note = Note {
            span,
            text: text(self),
        };
        for e in &mut self.info.errors[from..] {
            if !e.notes.contains(&note) {
                e.notes.push(note.clone());
            }
        }
    }

    /// Applies `sig` to `args`, a missing one filled by its default. When `pass` holds, as
    /// for an operator or a prelude word, an argument's atoms pass through, two arguments'
    /// merged into `#errs`. Gives the result and the arrows kept.
    fn apply(
        &mut self,
        what: &str,
        sig: &Sig,
        mut args: Vec<Option<Arg>>,
        pass: bool,
        span: Span,
    ) -> (Ty, Vec<usize>) {
        let mut out = Ty::empty();
        let need_args = self.need_args.take();
        if pass {
            let atoms: Vec<Ty> = args
                .iter()
                .flatten()
                .filter(|a| a.lit.is_none())
                .map(|a| a.ty.loose_ty())
                .collect();
            passed(&mut out, atoms.iter());
            for a in args.iter_mut().flatten() {
                a.ty = a.ty.without_loose();
            }
        } else {
            let mut atoms = Vec::new();
            for (i, a) in args.iter_mut().enumerate() {
                let Some(a) = a else {
                    continue;
                };
                let loose = a.ty.loose();
                let from_need = need_args.as_ref().is_some_and(|v| v.get(i) == Some(&true));
                if loose.is_empty() || (a.at.is_none() && !from_need) {
                    continue;
                }
                // Rule 6 treats each region of the argument apart: the atoms every arrow
                // omits pass by, and the rest stay in the argument to select an arrow.
                let refused = self.refused(sig, i, &loose);
                if refused.is_empty() {
                    continue;
                }
                let Some(at) = a.at else {
                    // A check of a need, as of `f(v)` in `ap(f, v) = f(v)`: the atoms pass by
                    // at the call whose argument gave them, which [`Self::apply_one`] finds.
                    atoms.push(a.ty.of_piece(&Piece::Set(refused.clone())));
                    a.ty = a.ty.without(&refused);
                    self.refused.push((what.into(), i, refused));
                    continue;
                };
                if refused == loose {
                    atoms.push(a.ty.loose_ty());
                    a.ty = a.ty.without_loose();
                } else {
                    atoms.push(a.ty.of_piece(&Piece::Set(refused.clone())));
                    a.ty = a.ty.without(&refused);
                }
                self.pass_at(span, at, &refused);
            }
            passed(&mut out, atoms.iter());
        }
        let defer = std::mem::take(&mut self.defer);
        let passing = self.need_passed.len();
        let r = match (sig.arrows.len(), self.first_taking(sig, &args, pass)) {
            (1, _) => self.apply_one(what, sig, 0, &args, defer, span),
            (_, Some(k)) => self.apply_one(what, sig, k, &args, defer, span),
            _ => {
                let r = self.apply_many(what, sig, &mut args, span);
                self.applied = None;
                r
            }
        };
        // What a check of a need left when the application failed before taking it.
        self.need_passed.truncate(passing);
        match r {
            Ok((t, kept)) => (out.union(&t), kept),
            Err(message) => {
                self.applied = None;
                let mut notes = self.applied(what, sig, &args, span);
                let mut seen: HashSet<Note> = notes.iter().cloned().collect();
                for a in args.iter().flatten() {
                    for n in self.reasons(&a.ty) {
                        if seen.insert(n.clone()) {
                            notes.push(n);
                        }
                    }
                }
                notes.extend(self.repairs(what, sig, &args, pass, span));
                self.error_with(span, message, notes);
                (out, Vec::new())
            }
        }
    }

    /// The atoms of `loose` that no arrow of `sig` takes at parameter `i`, which pass through
    /// the call: all of them where the parameter is a variable bounded to carriers, those
    /// its type does not hold where it is a closed type, and none where it is a variable, a
    /// class or `_`. One set difference and one meet per arrow.
    fn refused(&self, sig: &Sig, i: usize, loose: &KType) -> KType {
        let mut out = loose.clone();
        for arrow in &sig.arrows {
            if out.is_empty() {
                break;
            }
            let p = &arrow.params[i];
            out = match p.as_var().and_then(|v| sig.bounds.get(v)) {
                Some(&m) if m & OTHER == 0 => out,
                Some(_) => KType::empty(),
                None if p.dynamic || !p.vars.is_empty() || self.class_of_ty(p).is_some() => {
                    KType::empty()
                }
                None => &out - &p.set,
            };
        }
        out
    }

    /// Whether the parameter `p` of an arrow of `sig` takes none of the atoms `loose`.
    fn refused_at(&self, sig: &Sig, p: &Ty, loose: &KType) -> bool {
        if let Some(&m) = p.as_var().and_then(|v| sig.bounds.get(v)) {
            return m & OTHER == 0;
        }
        !p.dynamic
            && p.vars.is_empty()
            && self.class_of_ty(p).is_none()
            && (&p.set & loose).is_empty()
    }

    /// The first arrow of `sig` that takes the loose atoms of every argument, when `sig` has
    /// more than one arrow and its arrows differ only in the loose atoms of their parameters,
    /// as [`Self::handled_sig`] makes them: the first takes none of a parameter's handled
    /// atoms and gives what the body gives without them, the second takes them. An argument
    /// that may hold one of them selects the second; [`Self::apply_one`] then checks the call
    /// against the arrow selected. `None` leaves a signature of other arrows to
    /// [`Self::apply_many`], and when [`Self::apply`] passes every argument's atoms on.
    fn first_taking(&self, sig: &Sig, args: &[Option<Arg>], pass: bool) -> Option<usize> {
        if pass || !handled_shape(sig) {
            return None;
        }
        // An argument of a type variable of a signature around the call may hold any atom; a
        // class of the function being inferred holds none of its own, so a call `r(x)` of an
        // undeclared `x` takes the first arrow and `x` the carriers it allows, as it did when
        // `r` had the first arrow alone.
        let may = |t: &Ty| {
            let any = t.dynamic || t.vars.iter().any(|v| class_id(v).is_none());
            if any { atoms() } else { t.loose() }
        };
        let loose: Vec<KType> = args
            .iter()
            .map(|a| a.as_ref().map(|a| may(&a.ty)).unwrap_or_else(KType::empty))
            .collect();
        self.taking(sig, &loose)
    }

    /// The first arrow of `sig` whose parameter `i` takes the atoms `loose[i]`, for each `i`
    /// where they are not empty.
    fn taking(&self, sig: &Sig, loose: &[KType]) -> Option<usize> {
        sig.arrows.iter().position(|arrow| {
            arrow
                .params
                .iter()
                .zip(loose)
                .all(|(p, l)| *l == KType::empty() || !self.refused_at(sig, p, l))
        })
    }

    /// The message of an application that does not check: the arguments, each class shown
    /// as the carriers left to it.
    fn rejected(&self, what: &str, args: &[Option<Arg>]) -> String {
        self.rejected_at(what, args, None)
    }

    /// [`Self::rejected`], with argument `i` shown as the piece `p` of it that failed at the
    /// parameter of type `q`, and the cause when that check was refused.
    fn rejected_at(
        &self,
        what: &str,
        args: &[Option<Arg>],
        at: Option<(usize, &Piece, &Ty)>,
    ) -> String {
        let shown: Vec<String> = args
            .iter()
            .enumerate()
            .map(|(i, a)| match (a, at) {
                (_, Some((j, p, _))) if i == j => self.show(&p.ty()),
                (Some(a), _) => self.show(&a.ty),
                (None, _) => "_".into(),
            })
            .collect();
        let why = at
            .and_then(|(i, p, q)| Some(args[i].as_ref()?.ty.of_piece(p).refused(q)))
            .unwrap_or_default();
        format!("{what} does not take ({}){why}", shown.join(", "))
    }

    /// [`Self::apply`] of a signature of one arrow. The arguments at the parameters that are
    /// one bounded variable share a carrier: their classes merge, and their literals adopt
    /// it. Every other argument is checked piece by piece, a class taking the carriers its
    /// parameter allows.
    /// The literal `l` as it joins a class with no other operand, as a call's argument does:
    /// generic if written `kn` ([`Lit::joining`]), except in a check of a generic function's
    /// needs at a call, where the literal is of the function's body, which elaborates once for
    /// every call, and is read as `k`.
    fn joining(&self, l: &Lit) -> Lit {
        match self.replaying {
            0 => l.joining(),
            _ => l.clone(),
        }
    }

    /// The type of the tuple argument `a` at a parameter that is a type variable, with each
    /// literal `kn` written as a component of it, at any depth, made a class of its own that
    /// the literal joins, generic (L1.26a): the component joins the class of what it meets in
    /// the function's body, and takes int where it meets no carrier. `None` outside a
    /// function, and where no such literal is written.
    ///
    /// The tuples nest as deep as the text, so the walk keeps its own stack, as [`adopted`]
    /// does; it costs the size of the tuple's text.
    fn generic_parts(&mut self, a: &Arg) -> Option<Ty> {
        let parts = (a.parts.as_deref()).filter(|_| self.level > 0 && self.replaying == 0)?;
        let comps = only_tuple(&a.ty, parts.len())?;
        let mut stack = vec![OpenTuple {
            parts,
            comps,
            want: Vec::new(),
            out: Vec::new(),
        }];
        let mut made = false;
        loop {
            let open = stack.last_mut().expect("an open tuple");
            let i = open.out.len();
            if i == open.parts.len() {
                let t = Ty::tuple(stack.pop().expect("an open tuple").out);
                match stack.last_mut() {
                    None => return made.then_some(t),
                    Some(up) => up.out.push(t),
                }
                continue;
            }
            let c = &open.comps[i];
            match &open.parts[i] {
                Part::Lit(l) if l.n => {
                    let k = self.generic_class(l);
                    made = true;
                    let open = stack.last_mut().expect("an open tuple");
                    open.out.push(Ty::var(format!("${k}").into()));
                }
                Part::Tuple(inner) => match only_tuple(c, inner.len()) {
                    Some(cs) => stack.push(OpenTuple {
                        parts: inner,
                        comps: cs,
                        want: Vec::new(),
                        out: Vec::new(),
                    }),
                    None => open.out.push(c.clone()),
                },
                _ => open.out.push(c.clone()),
            }
        }
    }

    fn apply_one(
        &mut self,
        what: &str,
        sig: &Sig,
        k: usize,
        args: &[Option<Arg>],
        defer: BTreeSet<Arc<str>>,
        span: Span,
    ) -> Result<(Ty, Vec<usize>), String> {
        let arrow = &sig.arrows[k];
        let fail = |ck: &Self| Err(ck.rejected(what, args));
        let mut binds = Binds::new();
        let mut grouped = vec![false; args.len()];
        // The arguments each bounded variable stands at, in one pass over the arguments: one
        // pass per variable over every argument cost `O(v a)`.
        let mut at_of: HashMap<&str, Vec<usize>> = HashMap::new();
        for (i, (p, a)) in arrow.params.iter().zip(args).enumerate() {
            if let Some(v) = p.as_var().filter(|_| a.is_some()) {
                at_of.entry(&**v).or_default().push(i);
            }
        }
        for (v, &m) in &sig.bounds {
            let at = at_of.remove(&**v).unwrap_or_default();
            let lit_at = at
                .iter()
                .any(|&i| args[i].as_ref().is_some_and(|a| a.lit.is_some()));
            if at.len() < 2 && !lit_at {
                continue;
            }
            let (mut carriers, mut classes, mut lits) = (0u8, Vec::new(), Vec::new());
            for &i in &at {
                grouped[i] = true;
                let a = args[i].as_ref().expect("an argument");
                if let Some(l) = &a.lit {
                    lits.push(l.clone());
                    continue;
                }
                for p in a.ty.pieces() {
                    match (self.class_of(&p), p.carrier()) {
                        (Some(k), _) => classes.push(k),
                        _ if matches!(p, Piece::Var(_)) => {}
                        (None, Some(c)) => carriers |= c.bit(),
                        (None, None) => return fail(self),
                    }
                }
            }
            let bound = match (carriers.count_ones(), classes.first()) {
                (n, _) if n > 1 => return fail(self),
                (1, _) => {
                    let c = Carrier::of_mask(carriers).next().expect("one carrier");
                    if m & carriers == 0 {
                        return fail(self);
                    }
                    for &k in &classes {
                        if !self.restrict(k, c.bit(), what, span) {
                            return fail(self);
                        }
                    }
                    for l in &lits {
                        if lit_carrier(&l.value) != c && !adoptable(l, c) {
                            return fail(self);
                        }
                        self.adopt_to(l, c);
                    }
                    Ty::carrier(c)
                }
                (_, Some(&k)) => {
                    for &j in &classes[1..] {
                        if !self.merge(k, j, what, span) {
                            return fail(self);
                        }
                    }
                    if !self.restrict(k, m, what, span) {
                        return fail(self);
                    }
                    for l in &lits {
                        if !self.join(k, &self.joining(l), false) {
                            return fail(self);
                        }
                    }
                    Ty::var(format!("${}", self.find(k)).into())
                }
                _ if !lits.is_empty() => {
                    // The carrier of the bound its literals adopt fewest times to.
                    let adoptions = |c: Carrier| {
                        lits.iter()
                            .all(|l| adoptable(l, c))
                            .then(|| lits.iter().filter(|l| lit_carrier(&l.value) != c).count())
                    };
                    let Some(c) = Carrier::of_mask(m)
                        .filter_map(|c| adoptions(c).map(|n| (n, c)))
                        .min_by_key(|&(n, _)| n)
                        .map(|(_, c)| c)
                    else {
                        return fail(self);
                    };
                    for l in &lits {
                        self.adopt_to(l, c);
                    }
                    Ty::carrier(c)
                }
                _ => Ty::dynamic(),
            };
            binds.insert(v.clone(), bound);
        }
        for (i, a) in args.iter().enumerate() {
            let Some(a) = a else {
                continue;
            };
            if grouped[i] {
                continue;
            }
            let p = &arrow.params[i];
            let generic = match p.as_var().is_some() {
                true => self.generic_parts(a),
                false => None,
            };
            let a = &match generic {
                Some(ty) => Cow::Owned(Arg {
                    ty,
                    parts: None,
                    ..a.clone()
                }),
                None => Cow::Borrowed(a),
            };
            // A parameter that is a class of the function around: the argument flows into it.
            if let Some(k) = self.class_of_ty(p) {
                let ok = match &a.lit {
                    Some(l) => self.join(k, &self.joining(l), false),
                    None => self.flow(k, &a.ty, what, span),
                };
                if !ok {
                    return fail(self);
                }
                continue;
            }
            let ty = match adopted(a, p) {
                // A literal that cannot adopt is its own error, and the application's none.
                Err((s, m)) => {
                    self.error(s, m);
                    continue;
                }
                Ok(Some((t, ads))) => {
                    for (s, v) in ads {
                        self.put(Undo::Adopt(s, Some(v)));
                    }
                    Cow::Owned(t)
                }
                Ok(None) => Cow::Borrowed(&a.ty),
            };
            if a.lit.is_some() {
                if !self.sub(&ty, p, &mut binds) {
                    let why = ty.refused(p);
                    return Err(format!("{}{why}", self.rejected(what, args)));
                }
                continue;
            }
            for piece in ty.pieces() {
                let ok = match self.class_of(&piece) {
                    _ if piece == Piece::Dyn => p.dynamic,
                    Some(_) if p.dynamic => true,
                    Some(_) if !p.vars.is_empty() => self.sub(&ty.of_piece(&piece), p, &mut binds),
                    Some(k) => {
                        if !p.tuples.is_empty() || !p.fns.is_empty() {
                            let kind = NeedKind::Into {
                                what: what.into(),
                                ty: p.clone(),
                            };
                            self.need(k, kind, false, span);
                        }
                        self.restrict(k, mask_of(p), what, span)
                    }
                    None => match &piece {
                        Piece::Fn(s) if !s.needs.is_empty() && !p.fns.is_empty() => {
                            self.fit_needs(s, p, &mut binds, what, span)
                        }
                        _ => self.sub(&ty.of_piece(&piece), p, &mut binds),
                    },
                };
                if !ok {
                    return Err(self.rejected_at(what, args, Some((i, &piece, p))));
                }
            }
        }
        // The variables of the parameters of a function the call gives, which only its calls
        // bind: the needs on them are its own.
        let partial = !defer.is_empty();
        let mut defer = defer;
        let mut taken = Vars::default();
        arrow.params.iter().for_each(|p| p.vars_in(&mut taken));
        let mut inner = Vars::default();
        for s in &arrow.result.fns {
            s.arrows
                .iter()
                .for_each(|a| a.params.iter().for_each(|p| p.vars_in(&mut inner)));
        }
        defer.extend(inner.order.into_iter().filter(|v| !taken.contains(v)));
        let passing = self.need_passed.len();
        let mut left = self.replay(what, &sig.needs, &mut binds, defer, span);
        // Each bounded variable's binding is within its bound, and of one carrier, or of
        // other values only: the arrows of an operator each take one. So the classes in it
        // merge, and what else it holds flows into them.
        for (v, &m) in &sig.bounds {
            let Some(t) = binds.get(v).cloned() else {
                continue;
            };
            let mut kinds = 0u8;
            let mut class: Option<usize> = None;
            let mut rest = Ty::empty();
            for piece in t.pieces() {
                let ok = match (self.class_of(&piece), piece.carrier()) {
                    (Some(k), _) => {
                        self.restrict(k, m, what, span)
                            && match class {
                                Some(c) => self.merge(c, k, what, span),
                                None => {
                                    class = Some(k);
                                    true
                                }
                            }
                    }
                    _ if piece == Piece::Dyn => false,
                    _ if matches!(piece, Piece::Var(_)) => true,
                    (None, Some(c)) => {
                        kinds |= c.bit();
                        rest = rest.union(&piece.ty());
                        m & c.bit() != 0
                    }
                    (None, None) => {
                        kinds |= OTHER;
                        rest = rest.union(&piece.ty());
                        m & OTHER != 0
                    }
                };
                if !ok || kinds.count_ones() > 1 {
                    return fail(self);
                }
            }
            if let Some(c) = class
                && kinds != 0
                && !self.flow(c, &rest, what, span)
            {
                return fail(self);
            }
        }
        binds.retain(|v, _| !self.is_class(v));
        let mut out = Ty::empty();
        let given: Vec<&Arg> = args.iter().flatten().collect();
        if given.iter().any(|a| a.ty.dynamic) {
            out = out.union(&Ty::dynamic());
        }
        if given
            .iter()
            .all(|a| a.lit.is_some() || a.ty.pieces().iter().any(|p| *p != Piece::Dyn))
        {
            let result = close(&arrow.result.replace(&binds), sig, |v| self.is_class(v));
            out = out.union(&match partial {
                true => result,
                false => {
                    let needs = left.iter().map(|n| n.replace(&binds)).collect();
                    let (held, now) = hold(&result, needs, |v| self.is_class(v));
                    self.replay(what, &now, &mut binds, BTreeSet::new(), span);
                    left.clear();
                    held
                }
            });
        }
        out = out.union(&self.pass_needs(what, &arrow.params, args, passing, span)?);
        self.applied = Some((binds, left));
        Ok((out, vec![0]))
    }

    /// [`Self::apply`] of a signature of several arrows, each over one carrier or a tuple:
    /// an operator, a prelude word, or a section of one. The classes of the arguments merge,
    /// since every arrow takes one carrier for all its parameters, and its literals join
    /// them; without a class, each literal adopts the carrier of its parameter on the
    /// arrows that adopt fewest. Then the arguments' pieces are taken in turn, each state
    /// the arrows still alive: a state per set of arrows, not per combination of pieces.
    fn apply_many(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &mut [Option<Arg>],
        span: Span,
    ) -> Result<(Ty, Vec<usize>), String> {
        let mut class = None;
        for a in args.iter().flatten() {
            for p in a.ty.pieces() {
                if let Some(k) = self.class_of(&p) {
                    match class {
                        None => class = Some(k),
                        Some(c) => {
                            if !self.merge(c, k, what, span) {
                                return Err(self.rejected(what, args));
                            }
                        }
                    }
                }
            }
        }
        let kept: Vec<usize> = match class {
            Some(k) => {
                for a in args.iter().flatten() {
                    if let Some(l) = &a.lit
                        && !self.join(k, l, false)
                    {
                        return Err(self.rejected(what, args));
                    }
                }
                (0..sig.arrows.len()).collect()
            }
            None => match self.fewest(what, sig, args)? {
                Some(kept) => kept,
                None => return Ok((Ty::dynamic(), Vec::new())),
            },
        };
        // The states: the arrows alive, whether a piece was unknown, and the first pieces
        // that reached it, by argument.
        let n = args.len();
        let mut states: Vec<(Vec<usize>, bool, Vec<Option<Piece>>)> =
            vec![(kept.clone(), false, Vec::new())];
        for (i, a) in args.iter().enumerate() {
            let pieces: Vec<Option<Piece>> = match a {
                None => vec![None],
                Some(a) if a.lit.is_some() && class.is_some() => {
                    vec![Some(Piece::Var(format!("${}", class.unwrap()).into()))]
                }
                Some(a) => a.ty.pieces().into_iter().map(Some).collect(),
            };
            let mut next: Vec<(Vec<usize>, bool, Vec<Option<Piece>>)> = Vec::new();
            for (alive, dyn_, path) in &states {
                for p in &pieces {
                    let (alive, dyn_) = match p {
                        None => (alive.clone(), *dyn_),
                        // A class may still take any value its mask allows, so it keeps
                        // every arrow; the restriction after the arguments narrows it.
                        Some(p) if self.class_of(p).is_some() => (alive.clone(), *dyn_),
                        Some(Piece::Var(_)) => (alive.clone(), true),
                        Some(p) => {
                            let alive = alive
                                .iter()
                                .copied()
                                .filter(|&k| {
                                    self.sub(&p.ty(), &sig.arrows[k].params[i], &mut Binds::new())
                                })
                                .collect();
                            (alive, *dyn_)
                        }
                    };
                    if !next.iter().any(|s| s.0 == alive && s.1 == dyn_) {
                        let mut path = path.clone();
                        path.push(p.clone());
                        next.push((alive, dyn_, path));
                    }
                }
            }
            states = next;
        }
        let mut out = Ty::empty();
        for (alive, dyn_, path) in &states {
            let shown = |ck: &Self| {
                let shown: Vec<String> = path
                    .iter()
                    .map(|p| p.as_ref().map_or_else(|| "_".into(), |p| ck.show(&p.ty())))
                    .collect();
                let pieces: Vec<Option<Ty>> =
                    path.iter().map(|p| p.as_ref().map(Piece::ty)).collect();
                let pieces: Vec<Option<&Ty>> = pieces.iter().map(Option::as_ref).collect();
                let why = refused_among(sig, &kept, &pieces);
                format!("{what} does not take ({}){why}", shown.join(", "))
            };
            let at: Vec<usize> = (0..n)
                .filter(|&i| path[i].as_ref().is_some_and(|p| self.class_of(p).is_some()))
                .collect();
            match class {
                Some(k) if !at.is_empty() => {
                    let mask_at =
                        |a: &Arrow| at.iter().fold(EVERY, |m, &i| m & mask_of(&a.params[i]));
                    let m = alive.iter().fold(0, |m, &j| m | mask_at(&sig.arrows[j]));
                    if alive.is_empty() || !self.restrict(k, m, what, span) {
                        return Err(shown(self));
                    }
                    if *dyn_ {
                        out = out.union(&Ty::dynamic());
                        continue;
                    }
                    let r = self.find(k);
                    let km = self.classes[r].mask;
                    let rel: Vec<&Arrow> = alive
                        .iter()
                        .map(|&j| &sig.arrows[j])
                        .filter(|a| mask_at(a) & km != 0)
                        .collect();
                    let follows = rel.iter().all(|a| {
                        let m = mask_at(a);
                        m.count_ones() == 1
                            && Carrier::of_mask(m)
                                .next()
                                .is_some_and(|c| self.subtype(&Ty::carrier(c), &a.result))
                    });
                    if follows {
                        out = out.union(&Ty::var(format!("${r}").into()));
                        for a in &rel {
                            out = out.union(&a.result.of_piece(&Piece::Set(a.result.atoms())));
                        }
                    } else {
                        for a in &rel {
                            out = out.union(&close(&a.result, sig, |v| self.is_class(v)));
                        }
                    }
                }
                _ if *dyn_ => out = out.union(&Ty::dynamic()),
                _ => {
                    let Some(&j) = alive.first() else {
                        return Err(shown(self));
                    };
                    let a = &sig.arrows[j];
                    let mut binds = Binds::new();
                    for (p, t) in path.iter().zip(&a.params) {
                        if let Some(p) = p {
                            self.sub(&p.ty(), t, &mut binds);
                        }
                    }
                    out = out.union(&close(&a.result.subst(&binds), sig, |v| self.is_class(v)));
                }
            }
        }
        Ok((out, kept))
    }

    /// The arrows of `sig` whose adoptions of the literal arguments are fewest, all the
    /// same, with those adoptions made and the arguments retyped.
    /// `None` when a literal adopts no arrow's carrier exactly, which is reported.
    fn fewest(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &mut [Option<Arg>],
    ) -> Result<Option<Vec<usize>>, String> {
        // Per arrow: its adoptions, and each argument a literal of which adopts, retyped.
        type Best = (Adoptions, Vec<(usize, Ty)>);
        let mut best: Option<Best> = None;
        let mut kept = Vec::new();
        let mut adopt_error = None;
        for (k, arrow) in sig.arrows.iter().enumerate() {
            let mut need = Adoptions::new();
            let mut retyped = Vec::new();
            let mut ok = true;
            for (i, (a, p)) in args.iter().zip(&arrow.params).enumerate() {
                let Some(a) = a else {
                    continue;
                };
                // An arrow no other argument can fit is no candidate.
                if a.lit.is_none() && a.parts.is_none() {
                    ok &= a.ty.is_empty() || a.ty.meets(p);
                    continue;
                }
                if self.subtype(&a.ty, p) || p.dynamic {
                    continue;
                }
                match adopted(a, p) {
                    Ok(Some((t, ads))) if self.subtype(&t, p) => {
                        need.extend(ads);
                        retyped.push((i, t));
                    }
                    Err((s, m)) => {
                        adopt_error.get_or_insert((s, m));
                        ok = false;
                    }
                    // Kept as it is, the argument is checked as any argument is.
                    _ => ok &= a.ty.meets(p),
                }
            }
            if !ok {
                continue;
            }
            match &best {
                Some((n, _)) if n.len() < need.len() => {}
                Some((n, _)) if *n == need => kept.push(k),
                Some((n, _)) if n.len() == need.len() => {}
                _ => {
                    best = Some((need, retyped));
                    kept = vec![k];
                }
            }
        }
        let Some((need, retyped)) = best else {
            if let Some((s, m)) = adopt_error {
                self.error(s, m);
                return Ok(None);
            }
            // No arrow met an argument, which may rest on a refused check that it is empty.
            let tys: Vec<Option<&Ty>> = args
                .iter()
                .map(|a| a.as_ref().filter(|a| a.lit.is_none()).map(|a| &a.ty))
                .collect();
            let all: Vec<usize> = (0..sig.arrows.len()).collect();
            let why = refused_among(sig, &all, &tys);
            return Err(format!("{}{why}", self.rejected(what, args)));
        };
        for (i, t) in retyped {
            if let Some(a) = &mut args[i] {
                a.ty = t;
            }
        }
        for (s, v) in need {
            self.put(Undo::Adopt(s, Some(v)));
        }
        Ok(Some(kept))
    }
}

/// The written type `a` as the kernel prints it, which parses back as itself: how a message
/// shows a declared type the checker does not track. `None` for a type that holds a port,
/// which has no kernel type.
pub fn declared_text(a: &Type) -> Option<String> {
    crate::elab::kernel_type(a, &mut Vec::new(), None).map(|k| k.surface().to_string())
}

/// When an application of the arrows `arrows` of `sig` to arguments of the types `args` was
/// rejected: the cause of a refused check of an argument against the parameter of an arrow
/// that no argument rejects by a decided check, since only there the rejection rests on the
/// refusal; nothing if every arrow is rejected by a decided check. On the error path only:
/// arrows times arguments checks.
fn refused_among(sig: &Sig, arrows: &[usize], args: &[Option<&Ty>]) -> String {
    arrows
        .iter()
        .find_map(|&j| {
            let mut cause = None;
            for (a, q) in args.iter().zip(&sig.arrows[j].params) {
                match a.as_ref().map(|a| a.verdict(q)) {
                    Some(Verdict::Inhabited) => return None,
                    Some(Verdict::Refused(r)) => {
                        cause.get_or_insert(r);
                    }
                    _ => {}
                }
            }
            cause
        })
        .map(|r| format!(" (not decided: {})", r.message()))
        .unwrap_or_default()
}

/// The type of the one-parameter word `sig` applied to `t`, its atoms passing through; none
/// when a piece of `t` fits no arrow, an unknown one fitting only an arrow that takes any.
fn converted(sig: &Sig, t: &Ty) -> Option<Ty> {
    let mut out = t.loose_ty();
    for p in t.without_loose().pieces() {
        let arrow = sig.arrows.iter().find(|a| match p {
            Piece::Dyn | Piece::Var(_) => a.params[0].dynamic,
            _ => p.ty().sub(&a.params[0], &mut Binds::new()),
        })?;
        out = out.union(&arrow.result);
    }
    Some(out)
}

/// `out` with the atoms of `ts` added, with their payloads: when two of them hold atoms, also
/// `#errs`, which two distinct failures merge into.
fn passed<'t>(out: &mut Ty, ts: impl Iterator<Item = &'t Ty>) {
    let mut n = 0;
    for t in ts {
        let a = t.atoms();
        if !a.is_empty() {
            n += 1;
            *out = out.union(&t.of_piece(&Piece::Set(a)));
        }
    }
    if n > 1 {
        *out = out.union(&Ty::set(errs()));
    }
}

/// `t` with each of `needs` joined to the functions in it whose types share a variable with
/// the need, those variables becoming the function's own, and the needs no function takes.
/// Whether a function holds a variable is read from its facts ([`Sig::facts`]), and a
/// function no need joins is kept as it is: walking each function whole cost the depth of
/// the functions `g(0)(1)…(n)` returns at each call (CHK-carrier).
fn hold(t: &Ty, needs: Vec<Need>, is_class: impl Fn(&str) -> bool) -> (Ty, Vec<Need>) {
    let mut fns: Vec<Option<Sig>> = vec![None; t.fns.len()];
    let mut now = Vec::new();
    for n in needs {
        let mut v = Vars::default();
        n.vars_in(&mut v);
        let at: Vec<usize> = (0..t.fns.len())
            .filter(|&i| v.order.iter().any(|x| t.fns[i].facts().holds(x)))
            .collect();
        if at.is_empty() {
            now.push(n);
            continue;
        }
        for i in at {
            let own = v
                .order
                .iter()
                .filter(|x| !is_class(x) && !t.vars.contains(*x));
            let s = fns[i].get_or_insert_with(|| (*t.fns[i]).clone());
            s.own.extend(own.cloned());
            s.needs.push(n.clone());
        }
    }
    let held = Ty {
        fns: (t.fns.iter().zip(fns))
            .map(|(was, s)| match s {
                Some(mut s) => {
                    s.note_held();
                    Arc::new(s)
                }
                None => was.clone(),
            })
            .collect(),
        ..t.clone()
    };
    (held, now)
}

/// `t` with the type variables of `sig`'s parameters that no argument bound made unknown.
fn close(t: &Ty, sig: &Sig, is_class: impl Fn(&str) -> bool) -> Ty {
    let mut own = Vars::default();
    for a in &sig.arrows {
        a.params.iter().for_each(|p| p.vars_in(&mut own));
    }
    // A bounded variable no parameter holds is bound by no argument: the call gives a value of
    // some carrier of its bound.
    let unbound: Vec<(Arc<str>, Ty)> = sig
        .bounds
        .iter()
        .filter(|(v, _)| !own.contains(v))
        .map(|(v, &m)| (v.clone(), Ty::of_mask(m)))
        .collect();
    let binds: Binds = own
        .order
        .into_iter()
        .filter(|v| !is_class(v))
        .map(|v| (v, Ty::dynamic()))
        .chain(unbound)
        .collect();
    t.subst(&binds)
}

/// Whether each type variable of `arrow`'s result is one of a parameter itself, not one
/// inside a parameter's tuple or function: then the atoms it takes at a call are those of
/// the argument's own value. `O(v p log w)` for the result's `v` variables, `p` parameters
/// and `w` variables a parameter holds.
fn passes_vars_on(arrow: &Arrow) -> bool {
    arrow
        .result
        .vars
        .iter()
        .all(|v| arrow.params.iter().any(|p| p.vars.contains(v)))
}

/// Whether `sig` has more than one arrow and its arrows differ only in the loose atoms of
/// their parameters, as [`Ck::handled_sig`] makes them.
fn handled_shape(sig: &Sig) -> bool {
    let [first, rest @ ..] = &sig.arrows[..] else {
        return false;
    };
    let bare = |a: &Arrow| -> Vec<Ty> { a.params.iter().map(Ty::without_loose).collect() };
    let shape = bare(first);
    !rest.is_empty() && rest.iter().all(|a| bare(a) == shape)
}

/// The one function `t` is, when it is nothing else.
fn only_fn(t: &Ty) -> Option<Arc<Sig>> {
    match (
        &t.fns[..],
        t.set.is_empty() && t.tuples.is_empty() && t.vars.is_empty() && !t.dynamic,
    ) {
        ([s], true) => Some(s.clone()),
        _ => None,
    }
}

/// A write to one of [`Info`]'s maps: the key and the value, `None` for no entry. In the log,
/// the value is the one the write replaced.
#[derive(Clone)]
enum Undo {
    Adopt(Span, Option<Value>),
    Call(Span, Option<Arc<Sig>>),
    Fit(Span, Option<Fit>),
    Sig(usize, Option<Arc<Sig>>),
    Top(String, Option<Ty>),
    Passes(Span, Option<Vec<(Span, KType)>>),
    Follows(Span, Option<Vec<(Carrier, Value)>>),
    Witness(Span, Option<usize>),
    /// A class, while a repair is tried.
    Class(usize, Box<Class>),
}

/// How long the log and the errors were at a point.
struct Mark {
    log: usize,
    errors: usize,
}

/// Sets `$map[$key]` to `$value`, removing it for `None`, and gives the value it replaces.
macro_rules! set {
    ($map:expr, $key:expr, $value:expr) => {
        match $value {
            Some(v) => $map.insert($key.clone(), v),
            None => $map.remove(&$key),
        }
    };
}

impl Ck<'_, '_> {
    /// Makes the write `w`, logging the value it replaces.
    fn put(&mut self, w: Undo) {
        if self.replaying > 0 {
            return;
        }
        let undo = self.set(w);
        self.log.push(undo);
    }

    /// Makes the write `w` and gives the write that undoes it.
    fn set(&mut self, w: Undo) -> Undo {
        if let Undo::Class(k, c) = w {
            return Undo::Class(k, Box::new(std::mem::replace(&mut self.classes[k], *c)));
        }
        let i = &mut self.info;
        match w {
            Undo::Adopt(k, v) => Undo::Adopt(k, set!(i.adopt, k, v)),
            Undo::Call(k, v) => Undo::Call(k, set!(i.calls, k, v)),
            Undo::Fit(k, v) => Undo::Fit(k, set!(i.fits, k, v)),
            Undo::Sig(k, v) => Undo::Sig(k, set!(i.sigs, k, v)),
            Undo::Top(k, v) => {
                let old = set!(i.tops, k, v);
                Undo::Top(k, old)
            }
            Undo::Passes(k, v) => Undo::Passes(k, set!(i.passes, k, v)),
            Undo::Follows(k, v) => Undo::Follows(k, set!(i.follows, k, v)),
            Undo::Witness(k, v) => Undo::Witness(k, set!(i.witness, k, v)),
            Undo::Class(..) => unreachable!("a class is set above"),
        }
    }

    /// The point the checker is at.
    fn mark(&self) -> Mark {
        Mark {
            log: self.log.len(),
            errors: self.info.errors.len(),
        }
    }

    /// Undoes every write and error since `m`, the latest first.
    fn undo(&mut self, m: &Mark) {
        while self.log.len() > m.log {
            let w = self.log.pop().expect("longer than the mark");
            self.set(w);
        }
        self.info.errors.truncate(m.errors);
    }
}

/// Whether `d`, an `else` default, writes an atom literal, `#ok` or `#ok(…)`: the loose
/// failure the text names, which `_` may drop.
fn named_default(d: &Expr) -> bool {
    match &d.kind {
        ExprKind::Atom(_) => true,
        ExprKind::Call { callee, .. } => matches!(callee.kind, ExprKind::Atom(_)),
        _ => false,
    }
}

/// The parts of `e` whose loose atoms `e` passes on: the operands, the arguments, an index's
/// value and key, the condition and branches of an `if`, a block's export, what an `else`
/// keeps of its value, and its default unless that is an atom the `else` names. A tuple's
/// components are not among them, since an atom in a component is not one of the tuple's.
fn flows(e: &Expr) -> Vec<Span> {
    match &e.kind {
        ExprKind::Unary(_, a) => vec![a.span],
        ExprKind::Binary(_, a, b) => vec![a.span, b.span],
        ExprKind::Call {
            positional, named, ..
        } => positional
            .iter()
            .chain(named.iter().map(|(_, a)| a))
            .map(|a| a.span)
            .collect(),
        ExprKind::Index(of, k) => vec![of.span, k.span],
        ExprKind::Member { of, .. } => vec![of.span],
        ExprKind::Else {
            of,
            pattern,
            default,
        } => {
            // The plain form strips every loose atom of its value.
            let mut out = match pattern {
                None => Vec::new(),
                Some(_) => vec![of.span],
            };
            if !named_default(default) {
                out.push(default.span);
            }
            out
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => vec![cond.span, then.span, otherwise.span],
        ExprKind::Block(stmts) => stmts
            .iter()
            .filter_map(|s| match &s.kind {
                StmtKind::Return(es) if es.len() == 1 => Some(es[0].span),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

/// `e` as a numeric literal, perhaps under one `-`.
fn literal(e: &Expr) -> Option<Lit> {
    let (inner, neg) = match &e.kind {
        ExprKind::Unary("-", a) => (&**a, true),
        _ => (e, false),
    };
    let text = |s: &str| s.chars().filter(|&c| c != '_').collect::<String>();
    let (value, n) = match &inner.kind {
        ExprKind::Int {
            radix,
            digits,
            generic,
        } => (Value::int_text(&text(digits), *radix)?, *generic),
        ExprKind::Float(s) => (Value::float(text(s).parse().ok()?), false),
        _ => return None,
    };
    Some(Lit {
        span: inner.span,
        value,
        neg,
        text: inner.to_string(),
        n,
        generic: false,
        witness: false,
    })
}

/// The literals written in the tuple `e`, by component, at any depth; `None` when `e` is not
/// a tuple or holds no literal. The tuples nest as deep as the text, so the walk keeps its own
/// stack: each open tuple's items, the next one, its parts so far, and whether one is a
/// literal at some depth.
fn parts(e: &Expr) -> Option<Rc<[Part]>> {
    let ExprKind::Tuple(items) = &e.kind else {
        return None;
    };
    let mut stack: Vec<(&[Expr], usize, Vec<Part>, bool)> = vec![(items, 0, Vec::new(), false)];
    loop {
        let (items, next, ps, any) = stack.last_mut().expect("an open tuple");
        let Some(item) = items.get(*next) else {
            let (_, _, ps, any) = stack.pop().expect("an open tuple");
            let ps: Rc<[Part]> = ps.into();
            match stack.last_mut() {
                None => return any.then_some(ps),
                Some(up) => {
                    up.2.push(if any { Part::Tuple(ps) } else { Part::Other });
                    up.3 |= any;
                }
            }
            continue;
        };
        *next += 1;
        match (literal(item), &item.kind) {
            (Some(l), _) => {
                ps.push(Part::Lit(l));
                *any = true;
            }
            (None, ExprKind::Tuple(inner)) => stack.push((inner, 0, Vec::new(), false)),
            (None, _) => ps.push(Part::Other),
        }
    }
}

/// The components of `t` when it is exactly one tuple of length `n` and nothing else.
fn only_tuple(t: &Ty, n: usize) -> Option<&[Ty]> {
    let one = t.set.is_empty() && t.fns.is_empty() && t.vars.is_empty() && !t.dynamic;
    match t.tuples.as_slice() {
        [cs] if one && cs.len() == n => Some(cs),
        _ => None,
    }
}

/// One side of `==` as [`Ck::equal`] reads it: the types its value may have, one per tuple
/// shape it is a component of, the literal it is, if it is one, and the literals written in
/// it, by component, if it is a tuple that holds one.
type Side<'a> = (Vec<&'a Ty>, Option<&'a Lit>, Option<&'a [Part]>);

/// The argument `a` as a side of `==`.
fn side(a: &Arg) -> Side<'_> {
    (vec![&a.ty], a.lit.as_ref(), a.parts.as_deref())
}

/// The components of a side of the types `ts` with the parts `ps`, borrowed: at each, the
/// component's type in every tuple shape of length `n` the types hold ([`shapes`], as
/// [`adopted`] reads an expected type). `None` when they hold no such shape, or a variable or
/// the unknown, which could stand for a tuple of other components.
fn sides<'a>(
    ts: &[&'a Ty],
    ps: Option<&'a [Part]>,
    n: usize,
) -> Option<impl Iterator<Item = Side<'a>>> {
    if ts.iter().any(|t| !t.vars.is_empty() || t.dynamic) {
        return None;
    }
    let want = shapes(ts.iter().copied(), n);
    if want.is_empty() {
        return None;
    }
    let ps = ps.filter(|ps| ps.len() == n);
    Some((0..n).map(move |i| {
        let cs = want.iter().map(|w| &w[i]).collect();
        match ps.map(|ps| &ps[i]) {
            Some(Part::Lit(l)) => (cs, Some(l), None),
            Some(Part::Tuple(ps)) => (cs, None, Some(&ps[..])),
            _ => (cs, None, None),
        }
    }))
}

/// The components of `a` as arguments when it is exactly one tuple of length `n`: a literal
/// written there stays one, and a tuple written there keeps its literals.
fn components(a: &Arg, n: usize) -> Option<Vec<Arg>> {
    let cs = only_tuple(&a.ty, n)?;
    let parts = a.parts.as_ref().filter(|ps| ps.len() == n);
    Some(
        cs.iter()
            .enumerate()
            .map(|(i, c)| match parts.map(|ps| &ps[i]) {
                Some(Part::Lit(l)) => Arg {
                    lit: Some(l.clone()),
                    ..Arg::of(c.clone())
                },
                Some(Part::Tuple(ps)) => Arg {
                    parts: Some(ps.clone()),
                    ..Arg::of(c.clone())
                },
                _ => Arg::of(c.clone()),
            })
            .collect(),
    )
}

/// The literal adoptions an argument (or an operand) makes where a value of type `p` is
/// expected: by span, the value each literal takes.
type Adoptions = Vec<(Span, Value)>;

/// `a` where a value of `p` is expected: a literal adopts `p`'s numeric carrier
/// ([`Ty::numeric_carrier`]), and a literal in a tuple the one carrier its component holds
/// across `p`'s tuple shapes of that length, at any depth (DESIGN.md L1.26, sec:domains):
/// `(1, 2)` at `(f64, f64) | (String, f64)` is `(1.0, 2.0)`. This is the one place an expected
/// type decides a literal's carrier. Gives `a`'s type with the adoptions and the adoptions,
/// `None` when no literal adopts, and the first literal that is not exactly a value of its
/// carrier, or that meets numbers of two or more carriers none of which is its own
/// ([`no_one_carrier`]), with the message.
///
/// The tuples nest as deep as the text, so the walk keeps its own stack: each open tuple's
/// parts, the argument's components, the expected shapes there, and the types so far. The
/// shapes are borrowed from `p`: no union of them is built.
fn adopted(a: &Arg, p: &Ty) -> Result<Option<(Ty, Adoptions)>, (Span, String)> {
    let mut ads = Adoptions::new();
    let lit = |l: &Lit, want: &[&Ty], ads: &mut Adoptions| {
        let cs = carriers_in(l, want);
        let c = match cs[..] {
            [c] => c,
            [_, _, ..] if !cs.contains(&lit_carrier(&l.value)) => {
                let at = Ty::union_all(want.iter().copied());
                return Err((l.span, no_one_carrier(l, &at, &cs)));
            }
            _ => return Ok(None),
        };
        match adopt(l, c) {
            Ok(Some(v)) => {
                let t = lit_ty(&v, l.neg);
                ads.push((l.span, v));
                Ok(Some(t))
            }
            Ok(None) => Ok(None),
            Err(m) => Err((l.span, m)),
        }
    };
    if let Some(l) = &a.lit {
        return Ok(lit(l, &[p], &mut ads)?.map(|t| (t, ads)));
    }
    let Some(parts) = &a.parts else {
        return Ok(None);
    };
    let want = shapes([p], parts.len());
    let Some(comps) = only_tuple(&a.ty, parts.len()).filter(|_| !want.is_empty()) else {
        return Ok(None);
    };
    let mut stack = vec![OpenTuple {
        parts,
        comps,
        want,
        out: Vec::new(),
    }];
    loop {
        let OpenTuple {
            parts: ps,
            comps,
            want,
            out,
        } = stack.last_mut().expect("an open tuple");
        let i = out.len();
        if i == ps.len() {
            let t = Ty::tuple(stack.pop().expect("an open tuple").out);
            match stack.last_mut() {
                None => return Ok((!ads.is_empty()).then_some((t, ads))),
                Some(up) => up.out.push(t),
            }
            continue;
        }
        let c = &comps[i];
        let ws = want.iter().map(|w| &w[i]);
        match &ps[i] {
            Part::Lit(l) => {
                let ws: Vec<&Ty> = ws.collect();
                let t = lit(l, &ws, &mut ads)?.unwrap_or_else(|| c.clone());
                out.push(t);
            }
            Part::Tuple(inner) => {
                let ws = shapes(ws, inner.len());
                match only_tuple(c, inner.len()).filter(|_| !ws.is_empty()) {
                    Some(cs) => stack.push(OpenTuple {
                        parts: inner,
                        comps: cs,
                        want: ws,
                        out: Vec::new(),
                    }),
                    None => out.push(c.clone()),
                }
            }
            Part::Other => out.push(c.clone()),
        }
    }
}

/// The tuple shapes of length `n` of the types `ts`, borrowed.
fn shapes<'a>(ts: impl IntoIterator<Item = &'a Ty>, n: usize) -> Vec<&'a [Ty]> {
    ts.into_iter()
        .flat_map(|t| t.tuples.iter())
        .filter(|cs| cs.len() == n)
        .map(|cs| &cs[..])
        .collect()
}

/// A tuple [`adopted`] has open: its parts as written, the argument's components, the
/// expected shapes there, and the component types so far.
struct OpenTuple<'a> {
    parts: &'a [Part],
    comps: &'a [Ty],
    want: Vec<&'a [Ty]>,
    out: Vec<Ty>,
}

fn run(p: Prim, v: &Value) -> Option<Value> {
    eval(&Term::Prim(p, vec![Term::Lit(v.clone())])).ok()
}

/// The literal value `v`, under `-` when `neg`.
fn neg_value(v: &Value, neg: bool) -> Value {
    match neg {
        true => run(Prim::Neg, v).unwrap_or_else(|| v.clone()),
        false => v.clone(),
    }
}

/// The type of the literal `v`, under `-` when `neg`.
fn lit_ty(v: &Value, neg: bool) -> Ty {
    Ty::lit(&neg_value(v, neg))
}

fn lit_carrier(v: &Value) -> Carrier {
    match v {
        Value::Float(_) => Carrier::F64,
        Value::Rat(_) => Carrier::Rat,
        _ => Carrier::Int,
    }
}

/// The order two literals adopt in: an integer the other's carrier.
fn rank(c: Carrier) -> u8 {
    match c {
        Carrier::Int => 0,
        _ => 1,
    }
}

/// The literal `l` as a `c`: `None` when it is one already, an error when it is not exactly
/// one.
fn adopt(l: &Lit, c: Carrier) -> Result<Option<Value>, String> {
    if lit_carrier(&l.value) == c || !adoptable(l, c) {
        return Ok(None);
    }
    let exact = match &l.value {
        Value::Float(_) => Rat::decimal(&l.text).map(Value::rat),
        v => run(Prim::CastRat, v),
    };
    let not = || Err(format!("`{}` is not {} {}", l.text, article(c), c.name()));
    let Some(exact) = exact else {
        return not();
    };
    let v = match c {
        Carrier::Int => run(Prim::CastInt, &exact),
        Carrier::Rat => Some(exact),
        Carrier::F64 => run(Prim::CastF64, &exact),
        _ => None,
    };
    match v {
        Some(v) if !matches!(v, Value::Atom(_)) => Ok(Some(v)),
        _ => not(),
    }
}

/// Whether `l` may adopt `c`: an integer literal any numeric carrier, a decimal one `f64`
/// and `rat`, which it denotes exactly, and not `int`.
fn adoptable(l: &Lit, c: Carrier) -> bool {
    c.numeric() && !(matches!(l.value, Value::Float(_)) && c == Carrier::Int)
}

/// The message for the literal `l` where `want` holds numbers of the carriers `cs`, two or
/// more, none of them the literal's own.
fn no_one_carrier(l: &Lit, want: &Ty, cs: &[Carrier]) -> String {
    let names: Vec<&str> = cs.iter().map(|c| c.name()).collect();
    let sign = if l.neg { "-" } else { "" };
    let mut m = format!(
        "`{sign}{}` at `{want}` adopts no one carrier: the type holds numbers of {}",
        l.text,
        names.join(" and ")
    );
    // Only an integer literal reaches here, since a decimal one's own f64 or its one other
    // carrier, rat, would be taken; a written radix has no `.0` or `r` form. The forms of
    // `kn` are those of `k`.
    let digits = l.text.strip_suffix('n').filter(|_| l.n).unwrap_or(&l.text);
    let text = format!("{sign}{digits}");
    if digits.chars().all(|c| c.is_ascii_digit()) {
        let forms: Vec<String> = cs
            .iter()
            .filter_map(|c| match c {
                Carrier::F64 => Some(format!("`{text}.0`")),
                Carrier::Rat => Some(format!("`{text}r`")),
                _ => None,
            })
            .collect();
        m += &format!("; write the one meant, as {}", forms.join(" or "));
    }
    m
}

/// The numeric carriers the literal `l` can adopt that one of the types `want` holds, in the
/// order a type prints them: int, rat, f64. None when one of them holds a variable or the
/// unknown, which could stand for any. The literal adopts the one carrier when there is one
/// (DESIGN.md L1.26: the carrier "an operator or a parameter expects"); at two, as `1` at
/// `f64 | rat`, the expected type names no one carrier and the literal keeps its own. Several
/// types are the component of each tuple shape of one length (`adopted`).
fn carriers_in(l: &Lit, want: &[&Ty]) -> Vec<Carrier> {
    if want.iter().any(|w| !w.vars.is_empty() || w.dynamic) {
        return Vec::new();
    }
    [Carrier::Int, Carrier::Rat, Carrier::F64]
        .into_iter()
        .filter(|&c| adoptable(l, c) && want.iter().any(|w| !(&w.set & &c.ty()).is_empty()))
        .collect()
}

fn article(c: Carrier) -> &'static str {
    match c {
        Carrier::Int | Carrier::F64 => "an",
        _ => "a",
    }
}

/// One arrow per carrier in `cs`, of `n` parameters of that carrier, returning `result` or
/// the carrier itself.
fn arrows(cs: &[Carrier], n: usize, result: impl Fn(Carrier) -> Ty) -> Vec<Arrow> {
    cs.iter()
        .map(|&c| Arrow {
            params: vec![Ty::carrier(c); n],
            result: result(c),
        })
        .collect()
}

fn positional(n: usize) -> Vec<SParam> {
    (0..n)
        .map(|i| SParam {
            name: format!("x{i}").into(),
            positional: true,
            default: None,
        })
        .collect()
}

/// An operator's arrows.
fn op_sig(op: &str) -> Sig {
    use Carrier::*;
    let same = |c: Carrier| Ty::carrier(c);
    let bool_ = |_| Ty::carrier(Bool);
    let div0 = |c: Carrier| Ty::carrier(c).union(&Ty::set(KType::atom("divByZero")));
    let (n, arrows) = match op {
        "+" | "-" | "*" => (2, arrows(&[Int, F64, Rat], 2, same)),
        "/" => (
            2,
            [arrows(&[F64], 2, same), arrows(&[Rat], 2, div0)].concat(),
        ),
        "div" | "mod" => (2, arrows(&[Int], 2, div0)),
        "**" => (2, arrows(&[Int, F64], 2, same)),
        "++" => (2, arrows(&[Str], 2, same)),
        "<" => (2, arrows(&[Int, F64, Rat, Str, Bool], 2, bool_)),
        "&&" => (2, arrows(&[Bool], 2, bool_)),
        "!" => (1, arrows(&[Bool], 1, bool_)),
        "neg" => (1, arrows(&[Int, F64, Rat], 1, same)),
        _ => return op_sig("neg"),
    };
    Sig {
        params: positional(n),
        arrows,
        bounds: BTreeMap::new(),
        data: false,
        needs: Vec::new(),
        own: BTreeSet::new(),
        held: BTreeSet::new(),
        named: 0,
        facts: Default::default(),
    }
}

/// The number of operands of the prelude word `w` that [`word_sig`] types: two for `min` and
/// `max`, one for every other.
fn word_arity(w: &str) -> usize {
    match w {
        "min" | "max" => 2,
        _ => 1,
    }
}

/// A prelude word's arrows.
fn word_sig(w: &str) -> Arc<Sig> {
    use Carrier::*;
    let a = |names: &[&str]| {
        names
            .iter()
            .fold(Ty::empty(), |t, n| t.union(&Ty::set(KType::atom(n))))
    };
    let arrow = |from: Carrier, to: Carrier, fails: &[&str]| Arrow {
        params: vec![Ty::carrier(from)],
        result: Ty::carrier(to).union(&a(fails)),
    };
    let arrows = match w {
        "String" => vec![Arrow {
            params: vec![Ty::dynamic()],
            result: Ty::carrier(Str),
        }],
        "int" => vec![
            arrow(Int, Int, &[]),
            arrow(F64, Int, &["inexact", "invalid"]),
            arrow(Rat, Int, &["inexact"]),
            arrow(Str, Int, &["invalid"]),
        ],
        "rat" => vec![
            arrow(Int, Rat, &[]),
            arrow(F64, Rat, &["invalid"]),
            arrow(Rat, Rat, &[]),
            arrow(Str, Rat, &["invalid"]),
        ],
        "f64" => vec![
            arrow(Int, F64, &["inexact"]),
            arrow(F64, F64, &[]),
            arrow(Rat, F64, &["inexact"]),
            arrow(Str, F64, &["inexact", "invalid"]),
        ],
        "abs" => arrows(&[Int, F64, Rat], 1, Ty::carrier),
        "min" | "max" => arrows(&[Int, F64, Rat], 2, Ty::carrier),
        "len" => vec![arrow(Str, Int, &[])],
        "codePoint" => vec![arrow(Str, Int, &["notScalar"])],
        "scalar" => vec![arrow(Int, Str, &["notScalar"])],
        "utf8" => vec![Arrow {
            params: vec![Ty::carrier(Str)],
            result: bytes(),
        }],
        "fromUtf8" => vec![Arrow {
            params: vec![bytes()],
            result: Ty::carrier(Str).union(&a(&["badUtf8"])),
        }],
        _ => vec![arrow(Str, Str, &[])],
    };
    Arc::new(Sig {
        params: positional(word_arity(w)),
        arrows,
        bounds: BTreeMap::new(),
        data: false,
        needs: Vec::new(),
        own: BTreeSet::new(),
        held: BTreeSet::new(),
        named: 0,
        facts: Default::default(),
    })
}

/// The type of the bytes `utf8` gives and `fromUtf8` reads (step L1.39c): a family of ints keyed
/// by ints. The checker has no int-range types before step L10, so neither the keys
/// from 1 nor the bytes in `0 ..< 256` are stated here; the kernel gives `#badUtf8` for an int
/// that is not a byte.
fn bytes() -> Ty {
    Ty::set(KType::partial(KType::int(), KType::int()))
}

/// The primitive of the bit word `w`, if it is one (step L1.39a).
fn bit_prim(w: &str) -> Option<Prim> {
    crate::interp::prim(w).filter(|&p| zed_kernel::bits::is_bit_word(p))
}

/// A bit word's signature: its parameters, every one positional but `width`, each an `int` but
/// the `x` of `f64Bits`, an `f64`, and an `int` result.
fn bit_sig(p: Prim) -> Arc<Sig> {
    let names = zed_kernel::bits::params(p);
    let from = match p {
        Prim::F64Bits => Carrier::F64,
        _ => Carrier::Int,
    };
    Arc::new(Sig {
        params: names
            .iter()
            .map(|&n| SParam {
                name: n.into(),
                positional: n != "width",
                default: None,
            })
            .collect(),
        arrows: vec![Arrow {
            params: vec![Ty::carrier(from); names.len()],
            result: Ty::carrier(Carrier::Int),
        }],
        bounds: BTreeMap::new(),
        data: false,
        needs: Vec::new(),
        own: BTreeSet::new(),
        held: BTreeSet::new(),
        named: 0,
        facts: Default::default(),
    })
}

/// The operands of a call of a bit word `p` in parameter order, the receiver first, or `None`
/// when they do not fit its parameters.
fn bit_operands<'e>(
    p: Prim,
    receiver: Option<&'e Expr>,
    positional: &'e [Expr],
    named: &'e [(String, Expr)],
) -> Option<Vec<&'e Expr>> {
    let names = zed_kernel::bits::params(p);
    let mut slots: Vec<Option<&Expr>> = receiver.into_iter().map(Some).collect();
    slots.extend(positional.iter().map(Some));
    let positional_count = names.iter().filter(|&&n| n != "width").count();
    if slots.len() > positional_count {
        return None;
    }
    slots.resize(names.len(), None);
    for (name, e) in named {
        let j = names.iter().position(|n| n == name && *n == "width")?;
        if slots[j].replace(e).is_some() {
            return None;
        }
    }
    slots.into_iter().collect()
}

/// The integers an operand may be (see `Ck::int_range`).
struct IntRange {
    /// An interval holding them.
    ints: IntervalSet,
    /// The values themselves, when its type lists them or its text shows its value.
    values: Option<Vec<Value>>,
    /// How a message shows them.
    shown: String,
}

impl IntRange {
    /// The largest value, for `Greater`, or the smallest, for `Less`: from the values when
    /// they are known, else the interval's finite end on that side.
    fn extreme(&self, side: std::cmp::Ordering) -> Option<Value> {
        if let Some(vs) = &self.values {
            return vs
                .iter()
                .try_fold(None::<&Value>, |best, v| match best {
                    Some(b) => Some(Some(match v.surface_cmp(b)? == side {
                        true => v,
                        false => b,
                    })),
                    None => Some(Some(v)),
                })?
                .cloned();
        }
        let (lo, hi) = self.ints.bounds()?;
        match (side, lo, hi) {
            (std::cmp::Ordering::Greater, _, Fin(h)) => Some(Value::from(h)),
            (std::cmp::Ordering::Less, Fin(l), _) => Some(Value::from(l)),
            _ => None,
        }
    }
}

/// What the text of an expression shows of its `int` value: an interval holding it and, for an
/// expression built from int literals, the names bound to such expressions, the integer
/// operators and the bit words, the value itself. A call of `codePoint` lies in `0 ..= 1114111`.
#[derive(Clone)]
struct Known {
    ints: IntervalSet,
    value: Option<Value>,
}

impl Known {
    fn top() -> Self {
        Known {
            ints: IntervalSet::top(),
            value: None,
        }
    }

    /// The int `v`, exact at any size.
    fn of(v: Value) -> Self {
        let ints = match &v {
            Value::Int(n) => IntervalSet::single(*n),
            Value::Big(n) => IntervalSet::point(Num::from(&**n)),
            _ => return Known::top(),
        };
        Known {
            ints,
            value: Some(v),
        }
    }
}

/// The integer operator `o` of the text, with its interval transfer and its kernel primitive.
fn int_op(o: &str) -> Option<(Op, Prim)> {
    match o {
        "+" => Some((Op::Add, Prim::Add)),
        "-" => Some((Op::Sub, Prim::Sub)),
        "*" => Some((Op::Mul, Prim::Mul)),
        "div" => Some((Op::Div, Prim::IntDiv)),
        "mod" => Some((Op::Mod, Prim::Mod)),
        _ => None,
    }
}

impl<'a> Ck<'_, 'a> {
    /// What the text of `e` shows of its `int` value (see [`Known`]), from its literals, the
    /// names it uses, its integer operators and its calls of the bit words; any `int` for
    /// anything else. A binder's value is read only when a name of it is read here, so a
    /// constant that no bit word or exponent reads is never folded. Each expression is read
    /// once, by its span, children before parents on an explicit stack, so a nest of `n`
    /// operators or a chain of `n` bindings costs O(n) and no stack depth.
    ///
    /// Complexity tradeoff: the text is read, not the reduced product's cell, so an int that
    /// only a test narrows (`if n >= 0 { popCount(n) }`), a parameter or input is read as any
    /// int, and a bit word on it is rejected as possibly outside its domain. Why: the checker
    /// runs before the store's iteration, and asking the store at each call would run a
    /// fixpoint per call; reading the text is O(1) per node. Trigger: an operand whose sign or
    /// width only a test, a parameter or a component of a tuple shows. Test:
    /// `l01_39a_bit_words::errors::an_operand_not_shown_in_its_domain_is_rejected`. COMPLEXITY.md
    /// row C26. A complete solution needs int-range types on parameters and results (step
    /// L10, ledger BIT-checker-ranges), so a signature can state the domain, or the checker
    /// querying the reduced product's cell for the operand once the store's fixpoint has run.
    fn known(&mut self, e: &'a Expr) -> Known {
        if !self.known.contains_key(&e.span) {
            // Each node is entered once: the graph through binders is acyclic, as statements
            // are checked in dependency order, and the set keeps it finite if not.
            let mut entered = HashSet::new();
            let mut stack = vec![(e, false)];
            while let Some((x, ready)) = stack.pop() {
                if ready {
                    let k = self.known_uncached(x);
                    self.known.insert(x.span, k);
                } else if !self.known.contains_key(&x.span) && entered.insert(x.span) {
                    stack.push((x, true));
                    stack.extend(self.reads(x).into_iter().map(|c| (c, false)));
                }
            }
        }
        self.known[&e.span].clone()
    }

    /// What has been read of `e`; any `int` when it has not been.
    fn memo(&self, e: &Expr) -> Known {
        self.known.get(&e.span).cloned().unwrap_or_else(Known::top)
    }

    /// The expressions [`Ck::known_uncached`] reads to read `e`.
    fn reads(&self, e: &'a Expr) -> Vec<&'a Expr> {
        match &e.kind {
            ExprKind::Name(_) => self.bound_value(e).into_iter().collect(),
            ExprKind::Unary("-", a) => vec![&**a],
            ExprKind::Binary(o, a, b) if *o == "**" || int_op(o).is_some() => vec![&**a, &**b],
            _ => self.bit_call(e).map_or_else(Vec::new, |(_, es)| es),
        }
    }

    /// The value bound to the name `e` by a `name = value` binder.
    fn bound_value(&self, e: &Expr) -> Option<&'a Expr> {
        match self.t.res.uses.get(&e.span) {
            Some(Ref::Bound(ids)) if ids.len() == 1 => self.facts.get(&ids[0]).copied(),
            _ => None,
        }
    }

    // Complexity tradeoff: only a call of `codePoint` written in the text, as the operand or as
    // the value of a `name =` binder, gets the interval `0 ..= 1114111`; one that reaches a bit
    // word through a function's result or a parameter is read as any int, and the bit word
    // rejects it ("`bitAnd` takes `a` in int[0..], and this `a` is int"). Why: as for C26, the
    // checker runs before the store's iteration, and following each call into the body it
    // returns would check that body once per call site, where reading the text is O(1) per
    // node. A memo per function would make that linear, but it would cover only a result that
    // is itself such a call, a special case of the result ranges of step L10. Trigger: a `codePoint` result returned by a user function, as in
    // `f(s) = codePoint(s); x = bitAnd(f(s: "a"), 1);`. Test:
    // `l01_39c_code_points::checks::a_code_point_returned_by_a_function_is_read_as_any_int`.
    // COMPLEXITY.md row C28. A complete solution needs int-range types on results (step L10,
    // ledger BIT-checker-ranges), so `codePoint`'s signature states `int[0..=1114111]` and a
    // function's result type carries it, or the checker reading the reduced product's cell.
    /// Whether `e` calls the prelude word `codePoint` (step L1.39c), `codePoint(s)`, `s.codePoint()`
    /// or `s.codePoint`, whose int value lies in `0 ..= 1114111`.
    fn code_point_call(&self, e: &Expr) -> bool {
        let uses = &self.t.res.uses;
        let member = |x: &Expr| {
            matches!(&x.kind, ExprKind::Member { name, safe: false, .. } if name == "codePoint")
                && !matches!(uses.get(&x.span), Some(Ref::Bound(_)))
        };
        match &e.kind {
            ExprKind::Call {
                callee,
                positional,
                named,
                curry: false,
            } if named.is_empty() => match &callee.kind {
                ExprKind::Name(w) => {
                    w == "codePoint"
                        && positional.len() == 1
                        && matches!(uses.get(&callee.span), Some(Ref::Prelude(_)))
                }
                _ => positional.is_empty() && member(callee),
            },
            _ => member(e),
        }
    }

    /// The bit word `e` calls and its operands in parameter order, when `e` is such a call.
    fn bit_call(&self, e: &'a Expr) -> Option<(Prim, Vec<&'a Expr>)> {
        let ExprKind::Call {
            callee,
            positional,
            named,
            curry: false,
        } = &e.kind
        else {
            return None;
        };
        let uses = &self.t.res.uses;
        let (p, receiver) = match &callee.kind {
            ExprKind::Name(w) if matches!(uses.get(&callee.span), Some(Ref::Prelude(_))) => {
                (bit_prim(w)?, None)
            }
            ExprKind::Member {
                of,
                name,
                safe: false,
            } if !matches!(uses.get(&callee.span), Some(Ref::Bound(_)))
                && crate::resolve::prelude_layer(name) == Some(1) =>
            {
                (bit_prim(name)?, Some(&**of))
            }
            _ => return None,
        };
        Some((p, bit_operands(p, receiver, positional, named)?))
    }

    /// What the text of `e` shows of its `int` value, from what has been read of the
    /// expressions [`Ck::reads`] gives.
    fn known_uncached(&self, e: &'a Expr) -> Known {
        let fold = |p: Prim, args: Vec<Value>| -> Option<Known> {
            let v = eval(&Term::Prim(p, args.into_iter().map(Term::Lit).collect())).ok()?;
            matches!(v, Value::Int(_) | Value::Big(_)).then(|| Known::of(v))
        };
        let nonnegative = IntervalSet::range(End::of(0), PosInf);
        match &e.kind {
            ExprKind::Int { radix, digits, .. } => {
                let digits: String = digits.chars().filter(|&c| c != '_').collect();
                Value::int_text(&digits, *radix).map_or_else(Known::top, Known::of)
            }
            ExprKind::Name(_) => self
                .bound_value(e)
                .map_or_else(Known::top, |v| self.memo(v)),
            ExprKind::Unary("-", a) => {
                let a = self.memo(a);
                match a.value {
                    Some(v) => fold(Prim::Neg, vec![v]).unwrap_or_else(Known::top),
                    None => Known {
                        ints: a.ints.neg(),
                        value: None,
                    },
                }
            }
            ExprKind::Binary("**", a, b) => {
                let (x, n) = (self.memo(a), self.memo(b));
                if let (Some(x), Some(n)) = (&x.value, &n.value) {
                    return fold(Prim::Pow, vec![x.clone(), n.clone()]).unwrap_or_else(Known::top);
                }
                let ints = match n.ints.bounds() {
                    Some((Fin(lo), Fin(hi))) if lo == hi && lo.signum() >= 0 => {
                        forward(&Op::Pow(Int::from(lo).into()), &x.ints, &x.ints)
                    }
                    _ if x.ints.is_subset(&nonnegative) && n.ints.is_subset(&nonnegative) => {
                        nonnegative
                    }
                    _ => IntervalSet::top(),
                };
                Known { ints, value: None }
            }
            ExprKind::Binary(o, a, b) => match int_op(o) {
                Some((o, p)) => {
                    let (a, b) = (self.memo(a), self.memo(b));
                    if let (Some(x), Some(y)) = (&a.value, &b.value) {
                        return fold(p, vec![x.clone(), y.clone()]).unwrap_or_else(Known::top);
                    }
                    Known {
                        ints: forward(&o, &a.ints, &b.ints),
                        value: None,
                    }
                }
                None => Known::top(),
            },
            _ if self.code_point_call(e) => Known {
                ints: IntervalSet::of(0, 1_114_111),
                value: None,
            },
            _ => {
                let Some((p, es)) = self.bit_call(e) else {
                    return Known::top();
                };
                let ks: Vec<Known> = es.into_iter().map(|a| self.memo(a)).collect();
                if let Some(vs) = ks
                    .iter()
                    .map(|k| k.value.clone())
                    .collect::<Option<Vec<_>>>()
                {
                    // A constant call outside its domain is rejected at the call; its value
                    // is then none.
                    return match zed_kernel::bits::word(p, &vs) {
                        Ok(v) => Known::of(v),
                        Err(_) => Known {
                            ints: IntervalSet::empty(),
                            value: None,
                        },
                    };
                }
                let xs: Vec<IntervalSet> = ks.into_iter().map(|k| k.ints).collect();
                Known {
                    ints: bit_word(p, &xs),
                    value: None,
                }
            }
        }
    }
}

/// The atoms the uses of each binder handle, by binder: an alias class of binders, joined by
/// the bindings that are another name (`s = line`), shares one set.
struct Handled {
    /// The class of each binder: the binder that stands for it.
    root: Vec<usize>,
    /// The atoms each class handles, by its root.
    atoms: HashMap<usize, KType>,
}

impl Handled {
    /// The atoms the uses of binder `id` and of the names bound to it handle.
    fn get(&self, id: usize) -> Option<&KType> {
        self.atoms.get(&self.root[id])
    }
}

/// The atoms the uses of each binder handle ([`Resolution::handles`]), through the bindings
/// that are another name ([`Resolution::aliases`]), so `s = line; s else ""` handles them for
/// `line`, in whatever order the block writes its bindings. A union-find over the `B`
/// binders, by size with path halving, joins the `A` aliases; then each of the `H` sites
/// joins its atoms into its class's persistent set at `O(log H)` each, so the whole costs
/// `O(B + A α(B) + H log H)`. Each alias has one value, so a class holds at most one binder
/// that is not an alias, its parameter if it has one.
fn handled(res: &Resolution) -> Handled {
    let n = res.binders.len();
    let mut root: Vec<usize> = (0..n).collect();
    let mut size = vec![1usize; n];
    fn find(root: &mut [usize], mut x: usize) -> usize {
        while root[x] != x {
            root[x] = root[root[x]];
            x = root[x];
        }
        x
    }
    let one = |span: &Span| match res.uses.get(span) {
        Some(Ref::Bound(ids)) if ids.len() == 1 => Some(ids[0]),
        _ => None,
    };
    for (id, span) in &res.aliases {
        let Some(of) = one(span) else { continue };
        let (a, b) = (find(&mut root, *id), find(&mut root, of));
        if a != b {
            let (big, small) = if size[a] >= size[b] { (a, b) } else { (b, a) };
            root[small] = big;
            size[big] += size[small];
        }
    }
    for x in 0..n {
        root[x] = find(&mut root, x);
    }
    let mut atoms_of: HashMap<usize, KType> = HashMap::new();
    for (span, h) in &res.handles {
        let Some(id) = one(span) else { continue };
        let a = match h {
            Handle::Loose => atoms(),
            Handle::Any(n) => any_payload(n),
            Handle::Bare(n) => KType::atom(n),
        };
        let e = atoms_of.entry(root[id]).or_insert_with(KType::empty);
        *e = &*e | &a;
    }
    Handled {
        root,
        atoms: atoms_of,
    }
}

/// The atom `#name` with any payload or none: what a bare pattern `#name` matches.
pub(crate) fn any_payload(name: &str) -> KType {
    KType::union_all([KType::atom(name), KType::atom_with(name, &KType::top())])
}

/// `#ioError(op: String, path: String, why: String)`: a failed read or write, its operation,
/// its path and the operating system's reason.
fn io_error() -> Ty {
    let fields = ["op", "path", "why"]
        .into_iter()
        .map(|f| (Arc::from(f), Ty::carrier(Carrier::Str)))
        .collect();
    let mut t = Ty::set(KType::atom_with("ioError", &KType::top()));
    t.payloads.insert(
        "ioError".into(),
        Some(vec![Shape {
            items: Vec::new(),
            fields,
        }]),
    );
    t
}

/// The type of a port of `main` (L1.19): a `Lines` input is the family of its lines by number
/// from 1, each a `String` or `#ioError(op:, path:, why:)`, and a `Files` input answers a path
/// with its text, `#notFound` or `#ioError(op:, path:, why:)`; a lookup outside the family's
/// keys is `#notFound`. A `CommandLine` input (L1.19a) is the family of the arguments by
/// position from 1, each a `String`. `key` is the key's carrier and `io` whether a read can be
/// `#ioError`; a port keyed by `int` is a family, data, and one keyed by path a lookup.
fn port(key: Carrier, io: bool) -> Ty {
    let mut result = Ty::carrier(Carrier::Str).union(&Ty::set(KType::atom("notFound")));
    if io {
        result = result.union(&io_error());
    }
    Ty::func(Arc::new(Sig {
        params: positional(1),
        arrows: vec![Arrow {
            params: vec![Ty::carrier(key)],
            result,
        }],
        bounds: BTreeMap::new(),
        data: key == Carrier::Int,
        needs: Vec::new(),
        own: BTreeSet::new(),
        held: BTreeSet::new(),
        named: 0,
        facts: Default::default(),
    }))
}

/// The class a type variable names: `$k` is class `k`.
fn class_id(v: &str) -> Option<usize> {
    v.strip_prefix('$')?.parse().ok()
}

/// The `n`th name of a signature's own type variables: `T`, `U`, `V`, `W`, `T5`, ….
pub(super) fn var_name(n: usize) -> Arc<str> {
    match n {
        0..4 => ["T", "U", "V", "W"][n].into(),
        _ => format!("T{}", n + 1).into(),
    }
}

/// The variables of `s`, in order of first appearance.
fn sig_vars(s: &Sig) -> Vec<Arc<str>> {
    let mut out = Vars::default();
    for a in &s.arrows {
        a.params.iter().for_each(|p| p.vars_in(&mut out));
        a.result.vars_in(&mut out);
    }
    s.needs.iter().for_each(|n| n.vars_in(&mut out));
    out.order
}

/// Whether `t`, the type a class was solved to, holds no variable: a carrier.
fn is_solved(t: &Ty) -> bool {
    t.vars.is_empty() && !t.dynamic
}

/// `t` with its variables replaced by `binds`, and each that is not a class and `binds`
/// leaves unbound by the unknown.
fn bound(t: &Ty, binds: &Binds, is_class: impl Fn(&str) -> bool) -> Ty {
    let mut vars = Vars::default();
    t.vars_in(&mut vars);
    let mut b = binds.clone();
    for v in vars.order {
        if !is_class(&v) && !b.contains_key(&v) {
            b.insert(v, Ty::dynamic());
        }
    }
    t.replace(&b)
}

/// The carriers a value of `t` may be of, and [`OTHER`] if it may be a tuple, a function or
/// another value that is no atom: every value if `t` is unknown or has a variable.
fn mask_of(t: &Ty) -> u8 {
    if t.dynamic || !t.vars.is_empty() {
        return EVERY;
    }
    // The parts of the set are read off one split, where a meet with each carrier and a
    // difference with all of them and the atoms would build each part anew.
    let s = t.set.split();
    let mut m = 0;
    for c in Carrier::ALL {
        if s.bases[c.base()].is_some() {
            m |= c.bit();
        }
    }
    if !t.tuples.is_empty() || !t.fns.is_empty() || s.rest.is_some() {
        m |= OTHER;
    }
    m
}

/// The mask of the carriers of the bound `t`, a union of carrier names; `Err` with the first
/// part that is no carrier name.
fn carrier_mask(t: &Type) -> Result<u8, &Type> {
    let mut stack = vec![t];
    let mut mask = 0;
    while let Some(t) = stack.pop() {
        match &t.kind {
            TypeKind::Union(ts) => stack.extend(ts),
            TypeKind::Name(n) => match Carrier::ALL.iter().find(|c| c.name() == n.as_str()) {
                Some(c) => mask |= c.bit(),
                None => return Err(t),
            },
            _ => return Err(t),
        }
    }
    Ok(mask)
}

/// The type a type expression denotes; a name that is no prelude type is a type variable.
pub fn denoted(t: &Type) -> Ty {
    denoted_with(t, &Binds::new())
}

/// The type a type expression denotes, each name `leaves` binds standing for its type before
/// any other reading of the name (OSP-diag: the leaves of layer L10 a printed type holds).
pub fn denoted_with(t: &Type, leaves: &Binds) -> Ty {
    Denote {
        leaves,
        bound: HashMap::new(),
        open: Vec::new(),
    }
    .ty(t)
}

/// One denotation, read from the top down so that each variable a `for` clause bounds is
/// bounded on the outermost signature of the clause whose arrows name it, as resolve finds its
/// home: each use looks up its clause and the function type open at that depth, so the cost is
/// linear in the size of the type, however deeply clauses nest.
struct Denote<'a> {
    leaves: &'a Binds,
    /// Each variable a clause around the place bounds: its mask and the number of function
    /// types open at the clause, which is the index in `open` of its signature.
    bound: HashMap<&'a str, (u8, usize)>,
    /// The function types open around the place, outermost first.
    open: Vec<Reading>,
}

/// A function type [`Denote`] is reading.
#[derive(Default)]
struct Reading {
    /// The bounds of the variables it is the home of.
    bounds: BTreeMap<Arc<str>, u8>,
    /// Those of them a parameter holds, at any depth ([`Sig::held`]).
    held: BTreeSet<Arc<str>>,
    /// Whether the place is in its parameters.
    params: bool,
}

impl<'a> Denote<'a> {
    fn ty(&mut self, t: &'a Type) -> Ty {
        match &t.kind {
            TypeKind::Apply(..) | TypeKind::Record(_) => {
                unreachable!("resolve rejects the forms of layer L2")
            }
            // Resolve rejects a written one until L2.5; the reader of printed types reads one,
            // since the checker builds atoms with payloads from L1 on (L29-print).
            TypeKind::AtomApply(a, ps) => {
                let mut shape = Shape {
                    items: Vec::new(),
                    fields: BTreeMap::new(),
                };
                for p in ps {
                    match &p.name {
                        Some(n) if !p.positional => {
                            shape.fields.insert(n.as_str().into(), self.ty(&p.ty));
                        }
                        _ => shape.items.push(self.ty(&p.ty)),
                    }
                }
                let mut t = Ty::set(KType::atom_with(a, &KType::top()));
                t.payloads.insert(a.as_str().into(), Some(vec![shape]));
                t
            }
            TypeKind::Array(_) => unreachable!("resolve rejects the forms of layer L3"),
            TypeKind::Name(n) if self.leaves.contains_key(n.as_str()) => {
                self.leaves[n.as_str()].clone()
            }
            TypeKind::Name(n) => match n.as_str() {
                "int" => Ty::carrier(Carrier::Int),
                "rat" => Ty::carrier(Carrier::Rat),
                "f64" => Ty::carrier(Carrier::F64),
                "bool" => Ty::carrier(Carrier::Bool),
                "String" => Ty::carrier(Carrier::Str),
                "Lines" => port(Carrier::Int, true),
                "Files" => port(Carrier::Str, true),
                "CommandLine" => port(Carrier::Int, false),
                v => {
                    // A use outside every function type of its clause, as in `int \ T`, bounds
                    // nothing; resolve rejects it.
                    if let Some(&(mask, at)) = self.bound.get(v)
                        && let Some(home) = self.open.get_mut(at)
                    {
                        home.bounds.insert(v.into(), mask);
                        if home.params {
                            home.held.insert(v.into());
                        }
                    }
                    Ty::var(v.into())
                }
            },
            TypeKind::Atom(a) => Ty::set(KType::atom(a)),
            TypeKind::Every(Every::Atom) => Ty::set(ty::atoms()),
            TypeKind::Every(Every::Tuple) => Ty::set(KType::universe(Universe::Tuple)),
            TypeKind::Every(Every::Struct) => Ty::set(KType::universe(Universe::Struct)),
            // The kernel set holds the atom with any payload, and no shape is known.
            TypeKind::AtomAny(a) => Ty::set(KType::atom_with(a, &KType::top())),
            TypeKind::Tuple(ts) => Ty::tuple(ts.iter().map(|t| self.ty(t)).collect()),
            TypeKind::Union(ts) => {
                let ts: Vec<Ty> = ts.iter().map(|t| self.ty(t)).collect();
                Ty::union_all(&ts)
            }
            // Function types that share a parameter list are one function's arrows, in written
            // order, an intersection in parentheses among them included; resolve rejects
            // function types that do not. Each operand is denoted once, so the arrows are
            // gathered in one list.
            TypeKind::And(ts) => {
                let ts = Type::and_operands(ts);
                if Type::overload(&ts) == Ok(true) {
                    let mut sigs = ts.iter().map(|t| self.ty(t)).map(|mut t| {
                        let s = t.fns.pop().expect("a function type denotes one signature");
                        Arc::unwrap_or_clone(s)
                    });
                    let mut sig = sigs.next().expect("an intersection has operands");
                    for s in sigs {
                        sig.arrows.extend(s.arrows);
                        sig.bounds.extend(s.bounds);
                        sig.own.extend(s.own);
                        sig.held.extend(s.held);
                    }
                    return Ty::func(Arc::new(sig));
                }
                let ts: Vec<Ty> = ts.iter().map(|t| self.ty(t)).collect();
                // An intersection of function types of one arity is one function with each
                // of their arrows, in order, as a signature of several arrows prints.
                let sigs: Option<Vec<Arc<Sig>>> = ts.iter().map(only_fn).collect();
                if let Some([first, rest @ ..]) = sigs.as_deref()
                    && rest.iter().all(|s| s.params.len() == first.params.len())
                {
                    let mut sig = (**first).clone();
                    for s in rest {
                        sig.arrows.extend(s.arrows.iter().cloned());
                        sig.bounds
                            .extend(s.bounds.iter().map(|(v, m)| (v.clone(), *m)));
                        sig.own.extend(s.own.iter().cloned());
                        sig.held.extend(s.held.iter().cloned());
                        sig.needs.extend(s.needs.iter().cloned());
                    }
                    return Ty::func(Arc::new(sig));
                }
                let mut ts = ts.into_iter();
                let first = ts.next().unwrap_or_else(Ty::dynamic);
                ts.fold(first, |a, b| a.meet(&b))
            }
            TypeKind::Diff(a, b) => {
                let (a, b) = (self.ty(a), self.ty(b));
                a.diff(&b)
            }
            TypeKind::Arrow { params, result, .. } => {
                self.open_params();
                let tys = params.iter().map(|p| self.ty(&p.ty)).collect();
                self.close_params();
                let result = self.ty(result);
                let names = params
                    .iter()
                    .map(|p| SParam {
                        name: p.name.clone().unwrap_or_default().into(),
                        positional: p.positional || p.name.is_none(),
                        default: None,
                    })
                    .collect();
                self.sig(names, tys, result)
            }
            // Each variable is bounded on the outermost signature that names it, which resolve
            // found to hold its every use: a call of that function binds it to one carrier of
            // the bound (DESIGN.md sec:type_language, sec:checking).
            TypeKind::For { ty, bounds } => {
                let depth = self.open.len();
                let outer: Vec<(&'a str, Option<(u8, usize)>)> = bounds
                    .iter()
                    .map(|b| {
                        let mask = carrier_mask(&b.carriers)
                            .expect("resolve and the reader of printed types check each bound");
                        (
                            b.name.as_str(),
                            self.bound.insert(b.name.as_str(), (mask, depth)),
                        )
                    })
                    .collect();
                let t = self.ty(ty);
                for (v, was) in outer {
                    match was {
                        Some(was) => self.bound.insert(v, was),
                        None => self.bound.remove(v),
                    };
                }
                t
            }
            // This checker keeps one domain per function: the permission.
            TypeKind::Bounded { upper, result, .. } => {
                self.open_params();
                let names = vec![SParam {
                    name: String::new().into(),
                    positional: true,
                    default: None,
                }];
                let tys = vec![self.ty(upper)];
                self.close_params();
                let result = self.ty(result);
                self.sig(names, tys, result)
            }
        }
    }

    /// Opens a function type, at its parameters.
    fn open_params(&mut self) {
        self.open.push(Reading {
            params: true,
            ..Reading::default()
        });
    }

    /// Leaves the parameters of the function type opened last, for its result.
    fn close_params(&mut self) {
        self.open
            .last_mut()
            .expect("each function type is opened first")
            .params = false;
    }

    /// The signature of the function type opened last, with the bounds of the variables it
    /// is the home of.
    fn sig(&mut self, names: Vec<SParam>, tys: Vec<Ty>, result: Ty) -> Ty {
        let open = self.open.pop().expect("each function type is opened first");
        let mut sig = Sig::one(names, tys, result);
        sig.own.extend(open.bounds.keys().cloned());
        sig.bounds = open.bounds;
        sig.held = open.held;
        Ty::func(Arc::new(sig))
    }
}

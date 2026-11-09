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
//!
//! The checker runs from [`walk::check`] and [`walk::check_with`], in `walk.rs` with the walk
//! and the steps of class solving that re-enter it, since those steps and the walk call each
//! other and Zed forbids a cycle between files (ZED_PORT_GAPS.md gap 10). This file holds the
//! checker's types and the steps the walk calls that call nothing of the walk.

pub(crate) use zedc_types::kernel_type;
pub mod read;
pub use zedc_types::ty;
pub mod widen;

mod arms;
pub mod walk;

use std::borrow::Cow;
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::{self, Write as _};
use std::rc::Rc;
use std::sync::Arc;

use zed_kernel::num::TooLarge;
use zed_kernel::types::{Type as KType, Verdict};
use zed_kernel::{Prim, Rat, Term, Universe, Value, eval};

use zedc_base::rejection::Row;
use zedc_int::int::Int;
use zedc_lattice::interval::{
    End::{self, Fin, NegInf, PosInf},
    IntervalSet, Num, bit_word,
};
use zedc_lattice::revision::{Op, forward};
use zedc_preimage::images;
use zedc_resolve::resolve::tables::Tables;
use zedc_resolve::resolve::{Handle, Ref, Resolution};
use zedc_syntax::ast::{
    Error, Every, Expr, ExprKind, Function, Note, Param, Pattern, Stmt, StmtKind, StrPart, Target,
    Type, TypeKind, shown,
};
use zedc_syntax::format::format_type;
use zedc_syntax::lex::{Span, unread_literal};

use kernel_type::kernel_type;
use ty::{
    Arrow, Binds, Carrier, EVERY, IntDomain, Narrow, Need, NeedKind, OTHER, Piece, SParam, Shape,
    Sig, Slot, Ty, VarFacts, Vars, Via, Width, atoms, class_id, errs, mask_text, var_name,
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
pub enum Misfit<'s> {
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
    /// A saturated call that leaves out this parameter, which has no default; `true` when the
    /// parameter is positional, which `...` cannot leave out.
    Missing(&'s str, bool),
    /// A call through a value that leaves out this parameter, whose default reads the other
    /// parameters.
    OpenDefault(&'s str),
}

impl Misfit<'_> {
    /// The row of the rejection table the misfit is a case of, if any.
    pub fn row(self) -> Option<Row> {
        match self {
            Misfit::NoReceiver | Misfit::TooMany(_) | Misfit::NoParam(_) | Misfit::Supplied(_) => {
                None
            }
            Misfit::Named(_) | Misfit::Positional(_) => Some(Row::WrongForm),
            Misfit::CurriedPositional(_) | Misfit::NothingLeftOut => Some(Row::NothingLeftOut),
            Misfit::Missing(..) | Misfit::OpenDefault(_) => Some(Row::MissingArgument),
        }
    }

    /// The message, for the function called `who`.
    pub fn message(self, who: &str) -> String {
        match self {
            Misfit::NoReceiver => format!(
                "this call passes a value before the dot to `{who}`, as `x.{who}(…)` does, but \
                 `{who}` takes no parameters, so the value before the dot has no parameter to go to"
            ),
            Misfit::TooMany(0) => {
                format!("this argument is one more than `{who}` takes: `{who}` takes no arguments")
            }
            Misfit::TooMany(n) => format!(
                "this argument is one more than `{who}` takes: `{who}` takes {n} argument{} by \
                 position, and the arguments before this one already fill {}",
                plural(n),
                match n {
                    1 => "it",
                    _ => "them all",
                }
            ),
            Misfit::Named(name) => format!(
                "this argument is passed by position, and the parameter it reaches, `{name}` of \
                 `{who}`, is a named parameter, which a call passes only by name, as \
                 `{name}: …`"
            ),
            Misfit::Positional(name) => format!(
                "this argument is passed by name, as `{name}: …`, and `{name}` of `{who}` is \
                 positional, so a call passes it only by position"
            ),
            Misfit::NoParam(name) => format!(
                "this argument is passed by the name `{name}`, and `{who}` has no parameter of \
                 that name, so the argument has no parameter to go to"
            ),
            Misfit::Supplied(name) => format!(
                "this argument gives `{name}` of `{who}` a value, and an argument before it \
                 already gave `{name}` one; a call gives each parameter one value"
            ),
            Misfit::CurriedPositional(name) => format!(
                "this call of `{who}` ends in `...`, which makes a function of the named \
                 parameters the call leaves out, and the call also leaves out `{name}`, a \
                 positional parameter, which `...` cannot leave out"
            ),
            Misfit::NothingLeftOut => format!(
                "this call of `{who}` ends in `...`, which makes a function of the named \
                 parameters the call leaves out, and the call gives every named parameter a \
                 value, so `...` has no parameter to leave out"
            ),
            Misfit::Missing(name, _) => format!(
                "this call of `{who}` gives no value to its parameter `{name}`, and `{name}` has \
                 no default, so the call cannot be made"
            ),
            Misfit::OpenDefault(name) => format!(
                "this call goes through a function value and leaves out `{name}`, whose default \
                 reads the function's other parameters; only a call of the declared function \
                 by its name fills such a default, so here `{name}` has no value"
            ),
        }
    }

    /// The menu of the misfit (DESIGN.md sec:diagnostics), in the table's order for a misfit
    /// in a row, each entry a `repair:` note's text, for the function called `who`.
    /// `declared` is whether the call names a declared function: a call through a value, such
    /// as a lambda, has no declaration to edit, so no entry edits one, and `who` is then the
    /// value's type, so no entry writes it as code.
    pub(crate) fn menu(self, who: &str, declared: bool) -> Vec<String> {
        // How a code form names the function called: its name, or `f` for a value.
        let (f, where_f) = match declared {
            true => (who, ""),
            false => ("f", ", where `f` is the function called here"),
        };
        // The repair that a value whose function has no declaration takes in place of editing
        // the declaration: a named function, whose parameters a call may pass by name.
        let named_function = |name: &str| {
            format!(
                "repair: declare a named function in place of this value, as \
                 `f({name}: …) = …;`, and call it by its name; a declared function's parameters \
                 are passed by name unless declared `positional`"
            )
        };
        match (self, declared) {
            (Misfit::NoReceiver, true) => vec![
                format!("repair: call it as `{who}()`, with no value before the dot"),
                format!(
                    "repair: add a first parameter to the declaration of `{who}` for the value \
                     before the dot"
                ),
            ],
            (Misfit::NoReceiver, false) => {
                vec!["repair: call the function with no value before the dot".into()]
            }
            (Misfit::TooMany(_), true) => vec![
                "repair: remove this argument".into(),
                format!("repair: add a parameter for it to the declaration of `{who}`"),
            ],
            (Misfit::TooMany(_), false) => vec!["repair: remove this argument".into()],
            (Misfit::Named(name), true) => vec![
                format!("repair: pass `{name}` by name, as `{name}: …`"),
                format!("repair: declare `{name}` `positional` in `{who}`"),
            ],
            (Misfit::Named(name), false) => {
                vec![format!("repair: pass `{name}` by name, as `{name}: …`")]
            }
            (Misfit::Positional(name), declared) => {
                let mut menu = vec![format!(
                    "repair: pass `{name}` by position: remove `{name}: ` and put the value in \
                     `{name}`'s place among the arguments"
                )];
                menu.push(match declared {
                    true => format!(
                        "repair: remove `positional` from the declaration of `{name}` in `{who}`"
                    ),
                    false => named_function(name),
                });
                menu
            }
            (Misfit::NoParam(name), true) => vec![
                format!("repair: write the name of a parameter of `{who}` in place of `{name}`"),
                "repair: remove this argument".into(),
                format!("repair: add a parameter `{name}` to the declaration of `{who}`"),
            ],
            (Misfit::NoParam(name), false) => {
                vec!["repair: remove this argument".into(), named_function(name)]
            }
            (Misfit::Supplied(name), _) => vec![
                format!("repair: remove this second value for `{name}`"),
                format!("repair: remove the first value for `{name}` and keep this one"),
            ],
            (Misfit::CurriedPositional(name), _) => vec![
                "repair: remove the `...`".into(),
                format!(
                    "repair: leave out the positional `{name}` with a bracket section or a \
                     lambda, as `({name}) -> {f}({name}, …)`{where_f}"
                ),
            ],
            (Misfit::NothingLeftOut, _) => vec!["repair: remove the `...`".into()],
            (Misfit::Missing(name, positional), declared) => {
                let mut menu = vec![format!("repair: pass a value for `{name}` in this call")];
                if declared {
                    menu.push(format!(
                        "repair: give `{name}` a default in the declaration of `{who}`, as \
                         `{name} = …`"
                    ));
                }
                // `...` leaves out named parameters only (DESIGN.md sec:values_morphisms).
                if !positional {
                    menu.push(format!(
                        "repair: end the call in `...`, as `{f}(…, ...)`{where_f}, so that it \
                         gives a function that takes `{name}: …` later"
                    ));
                }
                let pass = match positional {
                    true => name.to_string(),
                    false => format!("{name}: {name}"),
                };
                menu.push(format!(
                    "repair: make a function that takes `{name}` with a lambda, as \
                     `({name}) -> {f}(…, {pass})`{where_f}"
                ));
                menu
            }
            (Misfit::OpenDefault(name), _) => vec![
                format!("repair: pass a value for `{name}` in this call"),
                "repair: call the declared function by its name, so that its default fills the \
                 parameter"
                    .into(),
            ],
        }
    }
}

/// `s` for a count other than one.
fn plural(n: usize) -> &'static str {
    match n {
        1 => "",
        _ => "s",
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
    /// sec:type_resolution), by the call's span and the arguments' spans. A call has an entry
    /// only while one of its arguments passes atoms by.
    pub passes: HashMap<Span, HashMap<Span, KType>>,
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
        let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
        let t = Tables::new(&[], &res);
        let mut ck = Ck::new(&t);
        let (lit, parts) = (literal(&self.e), parts(&self.e));
        let y = (vec![&self.et], lit.as_ref(), parts.as_deref());
        ck.pair((vec![&self.x], None, None), y);
        ck.info.adopt.len()
    }
}

/// A numeric literal: its span, without a `-`, which keys what it adopts; its site, the span
/// of the literal with its `-`, where every message about it points, and which is longer than
/// the span exactly when a `-` is applied to it ([`Lit::neg`]); its value, its text, without
/// the `-`, whether it is written with the suffix `n`, whether it is generic (step L1.26a):
/// written `kn` where it joins a class other than under `==` and `!=`, and whether, generic,
/// it has no other operand to take its carrier from at run time and takes it from a parameter
/// of its class ([`Info::witness`]). Where it joins no class, a `kn` is read as `k`.
#[derive(Clone)]
struct Lit {
    span: Span,
    site: Span,
    value: Value,
    /// The literal as written, made in memory asked for first ([`shown`]) and shared by every
    /// copy of the literal, so a clone copies none of its digits.
    text: Rc<String>,
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

    /// Whether a `-` is applied to the literal.
    fn neg(&self) -> bool {
        self.site != self.span
    }

    /// The literal as the program writes it, with its `-`, written from the shared text when
    /// displayed, so it copies none of the digits.
    fn written(&self) -> impl fmt::Display + '_ {
        let sign = if self.neg() { "-" } else { "" };
        fmt::from_fn(move |f| write!(f, "{sign}{}", self.text))
    }
}

/// An argument: its type, the literal it is, if it is one, the expression it is, if any, and
/// the literals written in it, by component, if it is a tuple that holds one at any depth.
/// `expr` is the expression itself, whose ints a call shows to a parameter with an
/// [`NeedKind::InDomain`] need; `at` is its span, or that of the expression an argument
/// rebuilt from it stands for.
#[derive(Clone)]
struct Arg<'a> {
    ty: Ty,
    lit: Option<Lit>,
    at: Option<Span>,
    expr: Option<&'a Expr>,
    parts: Option<Rc<[Part]>>,
}

impl<'a> Arg<'a> {
    fn of(ty: Ty) -> Arg<'a> {
        Arg {
            ty,
            lit: None,
            at: None,
            expr: None,
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
    Got(Box<Arg<'a>>),
}

/// The positional and named arguments of a call, shared by the frames that read them.
#[derive(Default)]
struct Args<'a> {
    positional: Vec<ArgSrc<'a>>,
    named: Vec<(String, ArgSrc<'a>)>,
}

/// Facts an `is` test makes: binders narrowed to a type, and the test.
type Facts = VecDeque<(usize, Ty, Span)>;

/// What [`Ck::narrow`] changed, for [`Ck::widen`] to restore.
type Saved<'a> = VecDeque<(usize, Option<Ty>, Option<Rc<Origin<'a>>>)>;

/// The items of `a` followed by those of `b`, the shorter list moved onto the longer, at a cost
/// of the shorter's length. An item moves only onto a list at least as long as its own, so it
/// moves at most log2 n times however the joins nest, and a tree of joins of n items costs
/// O(n log n): the facts and narrowings of a chain of `&&` or `||`, nested to the left, to
/// the right or both ways (COMPLEXITY.md IS-chain-quad).
fn joined<T>(mut a: VecDeque<T>, mut b: VecDeque<T>) -> VecDeque<T> {
    if a.len() >= b.len() {
        a.append(&mut b);
        return a;
    }
    while let Some(x) = a.pop_back() {
        b.push_front(x);
    }
    b
}

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
        parts.push(rest.text_in_union());
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

/// A `min` or `max` use's key in [`Class::orders`]: its word, whether the class's value is the
/// first operand, and its site.
type OrderKey = (Arc<str>, bool, Span);

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
    /// The result of each use in `uses` by its kind and whether it gives a value, the first
    /// recorded of equal ones, so a repeated use is found without a scan of `uses`.
    known: HashMap<(NeedKind, bool), Ty>,
    /// The index in `uses` of each `NeedKind::Order` use by its word, its side and its site:
    /// the uses of one site are one use, of the union of their other operands joined one
    /// shape per length, as `min` and `max` join them (DESIGN.md sec:reduction, item 5).
    orders: HashMap<OrderKey, usize>,
    /// The `min` or `max` use whose result it is, if it is one and holds nothing else: the class
    /// of the operand and the use's key in that class's `orders`. Its values are the join of
    /// the operand's and the use's other operand, so a `min` or `max` of the same word and side
    /// applied to it joins the new operand into that use (DESIGN.md sec:reduction, item 5).
    order_of: Option<(usize, OrderKey)>,
    /// Whether `uses` holds a `NeedKind::Data` use.
    data: bool,
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
    /// Whether it is what a use of another class's values gives, as `args[k]` is in the body
    /// of `r(fs, args, k)`: at a call it may hold any atom, and a test narrows it by a need
    /// ([`Ck::narrowed`]). Of a merged class, whether both were. A parameter's class is not:
    /// it holds the atoms its uses handle beside it ([`Ck::param_ty`]).
    given: bool,
    /// The classes of what a test that may leave a value of it gives, `x else d` and the
    /// branches of `x is #a` ([`Ck::narrowed`]), while it may still take other values: each
    /// is its own class, of its values without the atoms the test removes. One that takes a
    /// carrier by the time the function ends joins it ([`Ck::join_narrowed`]): a class of
    /// carriers holds no atom, so the test removed none of its values. Each with the test.
    narrowed_to: Vec<(usize, Span)>,
    /// Whether it is what a test of such a class gave, of [`Self::narrowed_to`] of another:
    /// a test of it is followed as one of that class is.
    narrows: bool,
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
    /// The number of narrowings in place ([`Ck::narrow`]): while it is 0, no name a bound value
    /// reads is narrowed, and [`Ck::narrowed_at`] has nothing to record.
    narrowings: usize,
    /// For each binder `name = e` bound while a narrowing was in place and each name `e` reads
    /// that was narrowed, the name's type there ([`Ck::narrowed_at`]).
    pub(super) narrowed_at: HashMap<(usize, usize), Ty>,
    /// The type each narrowed binder had before its first narrowing in place.
    pub(super) unnarrowed: HashMap<usize, Ty>,
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
    /// The parameters of no declared type of the functions being checked, by binder: a value
    /// of one whose ints a use takes at least 0 is passed on to the calls (CHK-need-bound).
    open_params: HashSet<usize>,
    /// The [`NeedKind::InDomain`] need of each of those parameters that has one, by binder,
    /// its position not yet filled in: the first use that takes its ints at least 0. The
    /// signature of the function takes it with the position.
    floors: HashMap<usize, Need>,
    /// The parameters the next [`Self::apply`] leaves out for a partial call: their
    /// [`NeedKind::InDomain`] needs go to the function of the rest, not to a default.
    leaving: Vec<usize>,
    /// The needs being checked at calls, one inside another.
    open: Vec<Open>,
    /// The variables of the parameters a partial call leaves out: the next application
    /// leaves the needs on them to the function the call gives.
    defer: BTreeSet<Arc<str>>,
    /// What the last application of one arrow bound, and the needs it left.
    applied: Option<(Binds, Vec<Need>)>,
    /// The literals the applications under way refused, each with its message, for
    /// [`Self::apply`] to report with the application's derivation and repairs.
    lit_refused: Vec<(Span, String)>,
    /// The atoms the uses of each binder handle, `else` and `is` on its name or on a name
    /// bound to it: an undeclared parameter's type holds them.
    handled: Handled,
    /// The undeclared parameters whose type in the body holds the atoms its uses handle.
    widened: HashSet<usize>,
    /// Each expression's loose atoms that may reach its value from elsewhere than a parameter
    /// of [`Self::widened`], by its span, as last found: those a call passing that parameter
    /// no atom may still give. No entry is none.
    outside: HashMap<Span, KType>,
    /// For each use made in a function with a parameter of [`Self::widened`], the loose
    /// atoms of each of its arguments that reach it from those parameters only: the atoms
    /// [`Self::outside`] does not keep. Of uses alike, those all of them hold. A parameter's
    /// class that may take other values carries an argument's atoms in its type variable, so
    /// [`Self::generalize`] removes these from the uses that hold it ([`Self::strip_widened`]).
    widened_only: HashMap<NeedKind, Vec<KType>>,
    /// The loose atoms each call gives from outside, by its span, as [`Self::try_outside`]
    /// found them since the call was last seen; `None` for unknown. [`Self::outside_of`]
    /// takes the entry.
    tried: HashMap<Span, Option<KType>>,
    /// The scopes the tests the walk is in make, which narrow the ints a bit word or `^`
    /// reads.
    arms: arms::Arms<'a>,
    /// For each binder read by a binder's value, what its summary read in the scope of its
    /// last such read ([`images::Read`]), from which the next is found.
    reads: HashMap<usize, images::Read<Rc<arms::Summarized>, zedc_preimage::product::Product>>,
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
            narrowings: 0,
            narrowed_at: HashMap::new(),
            unnarrowed: HashMap::new(),
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
            open_params: HashSet::new(),
            floors: HashMap::new(),
            leaving: Vec::new(),
            open: Vec::new(),
            defer: BTreeSet::new(),
            applied: None,
            lit_refused: Vec::new(),
            handled: handled(t.res),
            widened: HashSet::new(),
            outside: HashMap::new(),
            widened_only: HashMap::new(),
            tried: HashMap::new(),
            arms: arms::Arms::new(),
            reads: HashMap::new(),
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

    /// The loose atoms of `t`, the type of the expression at `at`, that reach it only from the
    /// parameters of [`Self::widened`]: those [`Self::outside`] does not keep.
    fn widened_atoms(&self, t: &Ty, at: Option<Span>) -> KType {
        match at.and_then(|at| self.outside.get(&at)) {
            Some(o) => &t.loose() - o,
            None => KType::empty(),
        }
    }

    /// Records the use `kind`, whose arguments are `args`, each a type and where it was
    /// written, in [`Self::widened_only`]. One set difference per argument.
    fn note_widened(&mut self, kind: &NeedKind, args: &[(&Ty, Option<Span>)]) {
        if self.replaying > 0 || self.widened.is_empty() {
            return;
        }
        let w: Vec<KType> = args
            .iter()
            .map(|(t, at)| self.widened_atoms(t, *at))
            .collect();
        match self.widened_only.get_mut(kind) {
            Some(old) => {
                for (o, n) in old.iter_mut().zip(&w) {
                    *o = &*o & n;
                }
            }
            None => {
                self.widened_only.insert(kind.clone(), w);
            }
        }
    }

    /// The class roots of those of the parameters `ids`, of types `tys`, of
    /// [`Self::widened`] whose class may take other values, each with the atoms its uses
    /// handle.
    fn widened_other(&self, ids: &[Option<usize>], tys: &[Ty]) -> Vec<(usize, KType)> {
        ids.iter()
            .zip(tys)
            .filter_map(|(id, t)| {
                let a = self.handled.get((*id)?)?;
                let r = self.find(class_id(t.as_var()?)?);
                (self.classes[r].mask & OTHER != 0).then(|| (r, a.clone()))
            })
            .collect()
    }

    /// The use `n` without the atoms [`Self::widened_only`] records for an argument whose
    /// type holds the type variable of a class of `strip`, of those that class's uses handle:
    /// the variable carries the atoms the parameter's argument holds at each call, and the
    /// atoms its handling added to the parameter's type in the body are none of them.
    fn strip_widened(&self, n: Need, strip: &[(usize, KType)]) -> Need {
        let Some(w) = self.widened_only.get(&n.kind) else {
            return n;
        };
        let cut = |t: &Ty, w: &KType| {
            let mut a = KType::empty();
            for (r, h) in strip {
                if t.vars
                    .iter()
                    .any(|v| class_id(v).is_some_and(|k| self.find(k) == *r))
                {
                    a = &a | &(w & h);
                }
            }
            match a == KType::empty() {
                true => t.clone(),
                false => t.without(&a),
            }
        };
        let kind = match &n.kind {
            NeedKind::Index(t) => NeedKind::Index(cut(t, &w[0])),
            NeedKind::Call {
                what,
                positional,
                named,
                curry,
            } => NeedKind::Call {
                what: what.clone(),
                positional: positional.iter().zip(w).map(|(t, w)| cut(t, w)).collect(),
                named: named
                    .iter()
                    .zip(&w[positional.len()..])
                    .map(|((m, t), w)| (m.clone(), cut(t, w)))
                    .collect(),
                curry: *curry,
            },
            _ => return n,
        };
        Need { kind, ..n }
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
    /// atoms). When a parameter of [`Self::widened`] may hold other values and no atom was
    /// added, the signature has the one arrow, and the loose atoms its uses handle, which
    /// [`Self::widened_other`] names, are not in its result (CHECK-else-notfound).
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
        if !added && !other {
            return Sig::one(params, tys, result);
        }
        let loose = result.loose();
        let kept = &loose & &self.outside_body(body);
        let plain = result
            .without_loose()
            .union(&result.of_piece(&Piece::Set(kept.clone())));
        // Each widened parameter may hold other values, so its type variable carries an
        // argument's atoms to the result, and the atoms its uses handle add none there.
        if !added {
            return Sig::one(params, tys, plain);
        }
        // One difference per function, at its end.
        if other || (&loose - &kept).is_empty() {
            return Sig::one(params, wide, result);
        }
        let mut sig = Sig::one(params, Vec::new(), Ty::empty());
        sig.arrows = vec![
            Arrow {
                params: tys,
                result: plain,
            },
            Arrow {
                params: wide,
                result,
            },
        ];
        sig
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
    /// its permission ([`kernel_type()`]). Every way of checking a program comes
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
                        kernel_type(ty, &mut ports, Some(&mut bad));
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
                        unreachable!(
                            "name resolution rejects every record type and every type applied to arguments before the checker reads the program"
                        )
                    }
                    TypeKind::Array(_) => unreachable!(
                        "name resolution rejects every array type before the checker reads the program"
                    ),
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
    /// derivation of the expression there and then the repairs `menu`, each placed at `span`.
    fn rejects_offering(
        &mut self,
        row: Row,
        span: Span,
        message: impl Into<String>,
        menu: impl IntoIterator<Item = String>,
    ) {
        let mut notes = self.derive(&[span]);
        notes.extend(menu.into_iter().map(|text| Note { span, text }));
        self.rejects_with(row, span, message, notes);
    }

    /// An error at `span` in no row of the rejection table, with the derivation of the
    /// expression there and then the repairs `menu`, each placed at `span`.
    fn error_offering(
        &mut self,
        span: Span,
        message: impl Into<String>,
        menu: impl IntoIterator<Item = String>,
    ) {
        let mut notes = self.derive(&[span]);
        notes.extend(menu.into_iter().map(|text| Note { span, text }));
        self.error_with(span, message, notes);
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
                            ExprKind::Atom(a) => format!("this atom `#{a}` with its payload"),
                            _ => "this call".into(),
                        },
                        _ => "this expression".into(),
                    };
                    let verb = if parts.is_empty() { "is" } else { "gives" };
                    next.push(note(span, format!("{what} {verb} {ty}")));
                    for p in parts {
                        next.push(match literal(p) {
                            Some(l) => {
                                note(p.span, literal_note(l.written(), lit_ty(&l.value, l.neg())))
                            }
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
                let mut why_none = Vec::new();
                self.emptied_of(id, &origin.why, &mut why_none);
                next.extend(why_none.into_iter().map(Work::Show));
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

    /// The steps that say why a part of a type written where the origin `why` of binder `id`
    /// declares it has no value ([`emptied`]): the type of a parameter, or of each parameter of
    /// a declared function. Built only for a derivation that is printed.
    fn emptied_of(&self, id: usize, why: &Why<'a>, out: &mut Vec<Note>) {
        match why {
            Why::Declared(_) => self.declared_emptied(id, out),
            Why::Typed(a, ..) => emptied(a, out),
            _ => {}
        }
    }

    /// [`emptied`] of each parameter type written on the function `id`, in order.
    fn declared_emptied(&self, id: usize, out: &mut Vec<Note>) {
        if let Some(f) = self.t.funcs.get(&id) {
            for a in f.params.iter().filter_map(|p| p.ty.as_ref()) {
                emptied(a, out);
            }
        }
    }

    fn id(&self, span: Span, name: &str) -> usize {
        self.t.id(span, name)
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
    /// its parts give different failures ([`ty::merges`]); any other expression gives all its
    /// loose atoms.
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
            if ty::merges(parts.iter().filter(|p| **p != KType::empty())) {
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
    fn outside_args(&self, args: &[Option<Arg<'a>>]) -> Option<Vec<Option<Arg<'a>>>> {
        let holds = |a: &Arg| a.at.is_some() && a.ty.loose() != KType::empty();
        if !args.iter().flatten().any(holds) {
            return None;
        }
        let cut = |a: &Arg<'a>| match a.at {
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
                _ if zedc_resolve::resolve::prelude_layer(name) == Some(1)
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
                _ if zedc_resolve::resolve::prelude_layer(name) == Some(1) => (name, of.span),
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
        let atoms = self.with_payloads(e.span, dropped);
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
            format!(
                "`_` drops a loose failure {what} may be, {atoms}: `_` drops only a failure the \
                 program names, as the default of an `else` names it, and this one would be \
                 dropped with nothing in the text saying so"
            ),
            notes,
        );
    }

    /// The atoms `atoms` of the value of the expression at `span`, with the payloads its type
    /// gives them, `#errs(#a | #b ->? #a | #b)`; with any payload, `#errs(..)`, where the
    /// expression has no type or the payloads are not in it.
    fn with_payloads(&self, span: Span, atoms: KType) -> Ty {
        match self.seen.get(&span) {
            Some((Some(t), _)) => t.of_piece(&Piece::Set(atoms)),
            _ => Ty::set(atoms),
        }
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
                    let text = format!(
                        "the loose failure {} enters here",
                        self.with_payloads(span, new)
                    );
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
            let text = format!(
                "the loose failure {} enters here",
                self.with_payloads(root, left)
            );
            out.push(Note { span: root, text });
        }
        out
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
            known: HashMap::new(),
            orders: HashMap::new(),
            order_of: None,
            data: false,
            flowed: Vec::new(),
            binder: None,
            generic: false,
            given: false,
            narrowed_to: Vec::new(),
            narrows: false,
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
        let k = match self.info.passes.get(&span).and_then(|m| m.get(&at)) {
            Some(old) if (k - old).is_empty() => return,
            Some(old) => old | k,
            None => k.clone(),
        };
        self.put(Undo::Passes(span, at, Some(k)));
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
            if !self.restrict(
                k,
                m,
                &quoting(&format_args!("the literal {}", l.written()), || {
                    "this literal".into()
                }),
                l.site,
            ) {
                return false;
            }
        }
        let r = self.find(k);
        self.touch(r);
        self.classes[r].lits.push((l.clone(), follower));
        true
    }

    /// Gives class `r` its type: its numeric carrier if a plain literal joined it, which keeps
    /// only the literal's own carrier (`f(x) = x * 2` takes int, as `2` is one), or a generic
    /// one with no other operand and no parameter of the class in scope at it
    /// ([`Info::witness`]), which takes the first of int, f64 and rat the class may take,
    /// every literal adopting it; a type variable if it may take any value; its carrier if
    /// one; a type variable bounded by its carriers if several; else the unknown. A function
    /// meant for every carrier writes the generic literal (step L1.26a): `f(x) = x * 2n` takes
    /// int, f64 and rat, its `2n` taking the carrier of `x` by one `match` at run time.
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
                            Ok(Some(v)) => Some((c, neg_value(&v, l.neg()))),
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
        t.replace(&self.solving(&t.var_facts().classes))
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
        let binds: Binds = (t.var_facts().classes.into_iter())
            .filter_map(|v| self.stale(&v).map(|t| (v, t)))
            .collect();
        t.replace(&binds)
    }

    /// The text of `t` in a message.
    fn text(&self, t: &Ty) -> String {
        self.settled(t).to_string()
    }

    /// The text of `t` in a message as one operand of a union, `T | U`: a function in it is
    /// parenthesized.
    fn text_in_union(&self, t: &Ty) -> String {
        self.settled(t).text_in_union()
    }

    /// [`Self::show`] as one operand of a union, `T | U`: a function in it is parenthesized.
    fn show_in_union(&self, t: &Ty) -> String {
        let t = &self.settled(t);
        match self.masks(t) {
            masks if masks.is_empty() => t.text_in_union(),
            masks => show_with(t, &masks),
        }
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
        t.renamed(&self.names(t.var_facts().classes))
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
            Ok(None) => lit_ty(&l.value, l.neg()),
            Ok(Some(v)) => {
                let t = lit_ty(&v, l.neg());
                self.put(Undo::Adopt(l.span, Some(v)));
                t
            }
            Err(m) => {
                self.error(l.site, m);
                lit_ty(&l.value, l.neg())
            }
        }
    }

    /// The loose atoms of `t`, which flow through `what` unchanged: an atom of a named family
    /// is data, and data that selects no arrow is an error (sec:failure).
    fn passing(&mut self, t: &Ty, what: &str, span: Span) -> Ty {
        if !t.family.is_empty() {
            let atoms = Ty::set(t.family.clone());
            // The first atom, written as a pattern, for the repair.
            let first = t
                .family
                .atom_names()
                .and_then(|mut names| names.next())
                .map(|(name, bare)| match bare {
                    true => format!("#{name}"),
                    false => format!("#{name}(_)"),
                });
            let message = format!(
                "{what} does not take {atoms}, which the value here may be: an atom of a named \
                 family is data like any other value, not a failure that passes through {what} \
                 untouched, and {what} has no case for it"
            );
            let mut menu = Vec::new();
            if let Some(a) = first {
                menu.push(format!(
                    "repair: replace `{a}` by a value {what} takes before the value gets here, as \
                     `v else {a} -> d`, where `v` is the value and `d` the value to use instead"
                ));
            }
            menu.push(
                "repair: test the value with `match` and handle each atom in its own arm"
                    .to_string(),
            );
            self.error_offering(span, message, menu);
        }
        t.loose_ty()
    }

    /// Narrows the binders of `facts`, each origin now the test; gives what to restore.
    fn narrow(&mut self, facts: &Facts) -> Saved<'a> {
        self.narrowings += facts.len();
        facts
            .iter()
            .map(|(b, t, test)| {
                let old = self.whence.get(b).cloned();
                let first = !old
                    .as_ref()
                    .is_some_and(|o| matches!(o.why, Why::Narrowed(_)));
                if first && let Some(t) = self.env.get(b) {
                    self.unnarrowed.insert(*b, t.clone());
                }
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
    fn widen(&mut self, saved: Saved<'a>) {
        self.narrowings -= saved.len();
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

    /// Reports an index `shown` at `span` that names no component of the tuple `tuple`, of `n`
    /// components.
    fn no_component(&mut self, tuple: &str, n: usize, shown: &str, span: Span) {
        let (why, menu) = match n {
            0 => (
                "the empty tuple has no components at all".to_string(),
                "repair: index a tuple that has components".to_string(),
            ),
            _ => (
                format!("its components are at the positions 0 to {}", n - 1),
                format!("repair: use an index from 0 to {}", n - 1),
            ),
        };
        self.error_offering(
            span,
            format!("{tuple} has no component {shown}: {why}, and this index is {shown}"),
            [menu],
        );
    }

    /// Reports `what`, a use that does not take every value, of a value of type `_`, which may
    /// be any: an `is` test narrows it first (DESIGN.md, Soundness).
    fn any(&mut self, what: &str, span: Span) {
        let message = format!(
            "{what} does not take every value, and this value is `_`, which may be any value: the \
             checker cannot show that it is one {what} takes"
        );
        let menu = [
            "repair: test the value with `is` first, as `if v is int { … } else { … }`, so that \
             inside the branch it has the type tested"
                .to_string(),
            "repair: write the type of the value where it is bound, as `x: int = …`, so that it \
             is no longer `_`"
                .to_string(),
        ];
        self.error_offering(span, message, menu);
    }

    /// Checks that a value of `t` may be pushed to a `Lines` port (L1.19): a `String` or a
    /// family of strings. A failure is disposed of before it reaches a port (sec:failure). A
    /// family writes its stored entries, so the `#notFound` of a key it lacks is not pushed;
    /// at L1 the families are the `Lines` and `CommandLine` ports, which store no `#notFound`.
    fn pushed(&mut self, t: &Ty, port: &str, span: Span) {
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
            let message = format!(
                "a `Lines` port takes a `String` or a family of strings, not {}: the port \
                 `{port}` writes each value pushed to it as one line of text, and the value \
                 pushed here may be something other than text",
                self.show(t)
            );
            let menu = [
                format!(
                    "repair: write the value into a string, as `{port} <- \"${{v}}\";`, where `v` \
                     is the value"
                ),
                "repair: handle the values that are not text first, with `match` or with `else`, \
                 as `v else #notFound -> \"\"`"
                    .to_string(),
            ];
            self.error_offering(span, message, menu);
        }
    }

    /// `==` and `!=`: any two values; a literal meets the other side's type by the rule of a
    /// parameter ([`Ck::follow`], [`expected`]), so `x == 1` with `x: f64` is rejected and
    /// `x == 1n` is true at `1.0`; of two literals a generic one takes the other's carrier, and
    /// two plain ones of two carriers are rejected (`1 == 1.0`). Two tuples of one length are
    /// paired component by component, at any depth, across every tuple shape of that length a
    /// side's type holds, as [`adopted`] pairs them: `p == (1n, 2n)` with
    /// `p: (f64, f64) | (String, f64)` reads both literals at `f64`.
    ///
    /// The tuples nest as deep as the text, so the pairs wait on a stack, each with whether it
    /// is inside a tuple. Each side borrows its component types, one per shape, so a tuple
    /// nested d deep at s shapes costs O(d·s) and not a copy of each level's type.
    fn equal(&mut self, x: &Arg, y: &Arg) {
        let from = self.info.errors.len();
        self.pair(side(x), side(y));
        if !self.trying {
            self.equal_repairs(from, x, y);
            self.equal_repairs(from, y, x);
        }
    }

    /// The derivation and repairs of the rejection, among the errors from the `from`th on, of
    /// the plain literal `l` compared by `==` with the value `v` of other carriers in the row
    /// of two numbers with no common carrier (`n == 1.0` with `n: int`): `v`'s derivation, the
    /// literal, and each cast of `v` with which the comparison checks, tried with the
    /// checker's state restored after, `f64(n)`. One trial per cast word.
    fn equal_repairs(&mut self, from: usize, l: &Arg, v: &Arg) {
        let (Some(lit), None, Some(at)) = (&l.lit, &v.lit, v.at) else {
            return;
        };
        let Some(k) = (from..self.info.errors.len()).find(|&k| {
            let e = &self.info.errors[k];
            e.span == lit.site && e.row == Some(Row::NoCommonCarrier)
        }) else {
            return;
        };
        let mut notes = self.derive(&[at]);
        notes.push(Note {
            span: lit.span,
            text: literal_note(lit.written(), lit_ty(&lit.value, lit.neg())),
        });
        let held = match self.class_of_ty(&v.ty) {
            Some(r) if self.classes[r].mask & OTHER == 0 => Ty::of_mask(self.classes[r].mask),
            _ => v.ty.clone(),
        };
        let t = self.t;
        let name = match self.seen.get(&at) {
            Some((_, Src::Name(id))) => Some(&t.res.binders[*id].name),
            _ => None,
        };
        for w in ["int", "rat", "f64"] {
            let Some(r) = converted(&word_sig(w), &held) else {
                continue;
            };
            let cast = Arg {
                at: Some(at),
                ..Arg::of(r)
            };
            let saved = self.mark();
            self.trying = true;
            self.equal(l, &cast);
            let ok = self.info.errors.len() == saved.errors;
            self.trying = false;
            self.undo(&saved);
            if ok {
                let text = match name {
                    Some(n) => format!("repair: write `{w}({n})`; the checker accepts that"),
                    None => format!("repair: wrap this in `{w}(…)`; the checker accepts that"),
                };
                notes.push(Note { span: at, text });
            }
        }
        self.info.errors[k].notes = notes;
    }

    /// [`Ck::equal`] of the two sides `x` and `y`.
    fn pair(&mut self, x: Side<'_>, y: Side<'_>) {
        let mut stack = vec![(x, y, false)];
        while let Some(((xt, xl, xp), (yt, yl, yp), inner)) = stack.pop() {
            match (xl, yl) {
                (Some(l), Some(m)) => {
                    let (lc, mc) = (lit_carrier(&l.value), lit_carrier(&m.value));
                    // A generic literal takes the other's carrier; of two plain ones of two
                    // carriers, the integer, or else the decimal, is rejected at the other's.
                    let m_takes = match (l.n, m.n) {
                        (_, true) => true,
                        (true, false) => false,
                        _ => mc == Carrier::Int || mc == Carrier::F64 && lc != Carrier::Int,
                    };
                    match (lc == mc, m_takes) {
                        (true, _) => {}
                        // Two plain literals of two carriers: two numbers with no common
                        // carrier, the one rejected at the other's carrier.
                        (false, takes) if !l.n && !m.n => {
                            let (r, c) = if takes { (m, lc) } else { (l, mc) };
                            let notes = [l, m]
                                .map(|l| Note {
                                    span: l.span,
                                    text: literal_note(l.written(), lit_ty(&l.value, l.neg())),
                                })
                                .to_vec();
                            self.rejects_with(Row::NoCommonCarrier, r.site, menu(r, &[c]), notes);
                        }
                        (false, true) => {
                            self.adopt_to(m, lc);
                        }
                        (false, false) => {
                            self.adopt_to(l, mc);
                        }
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

    /// The literal `l` compared with a value of one of the types `ts`, as at a parameter
    /// ([`expected`]). With a lone `ts` that is a class, a plain literal joins it as an operand
    /// does, keeping only the literal's carrier; a generic one outside a tuple follows the
    /// class's carrier without narrowing it, and one in a tuple joins it as a plain one does,
    /// since the elaborator's rewrite that follows the class's carrier at run time
    /// (`Info::follows`) is built for an operand of `==` only.
    fn follow(&mut self, l: &Lit, ts: &[&Ty], inner: bool) {
        if let [t] = ts
            && let Some(k) = self.class_of_ty(t)
        {
            if !self.join(k, l, l.n && !inner) {
                let mask = self.classes[self.find(k)].mask;
                let held: Vec<Carrier> = [Carrier::Int, Carrier::Rat, Carrier::F64]
                    .into_iter()
                    .filter(|c| mask & c.bit() != 0)
                    .collect();
                let m = match held.is_empty() {
                    false => menu(l, &held),
                    true => {
                        let own = lit_carrier(&l.value);
                        let sign = if l.neg() { "-" } else { "" };
                        let names: Vec<&str> = Carrier::of_mask(mask).map(|c| c.name()).collect();
                        let (what, carrier, names) = (article(own), own.name(), names.join(" | "));
                        let text = &l.text;
                        quoting(
                            &format_args!(
                                "`{sign}{text}` is {what} {carrier}, compared with a value of \
                                 `{names}`, which holds no number"
                            ),
                            || {
                                format!(
                                    "this literal is {what} {carrier}, compared with a value of \
                                     `{names}`, which holds no number"
                                )
                            },
                        )
                    }
                };
                self.compared(l, ts, m);
            }
            return;
        }
        match expected(l, ts) {
            Ok(Some(c)) => {
                self.adopt_to(l, c);
            }
            Ok(None) => {}
            Err(m) => self.compared(l, ts, m),
        }
    }

    /// Reports the literal `l`, compared by `==` with a value of one of the types `ts`,
    /// rejected with the message `m`: in the row of two numbers with no common carrier where
    /// `l` is plain and every value of `ts` is a number of other carriers (`n == 1.0` with
    /// `n: int`), whose derivation and repairs [`Self::equal_repairs`] adds; in no row
    /// otherwise.
    fn compared(&mut self, l: &Lit, ts: &[&Ty], m: String) {
        let numbers = (ts.iter()).try_fold(0, |acc, t| self.numbers_in(t).map(|m| acc | m));
        match numbers {
            Some(n) if !l.n && n != 0 && n & lit_carrier(&l.value).bit() == 0 => {
                let notes = self.derive(&[l.site]);
                self.rejects_with(Row::NoCommonCarrier, l.site, m, notes)
            }
            _ => self.error(l.site, m),
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

    /// The error for operand `name` of `w`, at `operand`, outside `needs` for the width at
    /// `width`; each is the operand's place and how it is shown.
    fn width_error(
        &mut self,
        w: &str,
        name: &str,
        needs: &str,
        (ax, sx): (Span, &str),
        (aw, sw): (Span, &str),
        span: Span,
    ) {
        let mut notes = vec![
            Note {
                span: ax,
                text: format!("`{name}` is this operand, {sx}"),
            },
            Note {
                span: aw,
                text: format!("`width` is this operand, {sw}"),
            },
        ];
        self.derive_into(&[ax, aw], &mut notes);
        let menu = [
            format!(
                "repair: pass a `{name}` in {needs}, or test it with `is` first, so that inside \
                 the branch it lies there"
            ),
            "repair: pass a larger `width`, if the operation is meant on a wider word".to_string(),
        ];
        notes.extend(menu.into_iter().map(|text| Note { span, text }));
        self.error_with(
            span,
            format!(
                "`{w}` takes `{name}` in {needs}, and this `{name}` is {sx} with `width` {sw}: \
                 `{w}` is defined only for such a `{name}`, and the checker found that this one \
                 may lie outside it"
            ),
            notes,
        );
    }

    /// The tuple `cs` at the computed key `x`, by the `m[k]` row of DESIGN.md sec:types: a
    /// tuple's keys are the positions `0..<n`, each guaranteed (sec:types, the tuple/struct
    /// distinction), so the result is the union of the components the key's integers select,
    /// with `#notFound` when the key may lie outside `0..<n`; a key that selects no component
    /// is an error, as a literal one is. The key's loose atoms pass. Listed integers are read
    /// once each and a cofinite set is tested at each of the `n` positions, so this costs
    /// `O((n + m) log m)` for a key of `m` listed integers.
    fn tuple_at(&mut self, cs: &ty::Row, x: &Arg, span: Span) -> Ty {
        let n = cs.len();
        let ints = &x.ty.set & &KType::int();
        let unknown = x.ty.dynamic || !x.ty.vars.is_empty();
        let picked: Vec<usize> = if unknown {
            (0..n).collect()
        } else {
            match ints.ints_listed() {
                Some(vs) => {
                    let mut js: Vec<usize> = vs
                        .iter()
                        .filter_map(|v| match v {
                            Value::Int(i) => usize::try_from(*i).ok().filter(|j| *j < n),
                            _ => None,
                        })
                        .collect();
                    js.sort_unstable();
                    js
                }
                None => (0..n)
                    .filter(|j| i64::try_from(*j).is_ok_and(|j| ints.contains(&Value::Int(j))))
                    .collect(),
            }
        };
        let mut out = self.passing(&x.ty, "a tuple index", span);
        let key = x.ty.without_atoms();
        // A key that is only failures selects nothing and passes them.
        if key.is_empty() {
            return out;
        }
        if picked.is_empty() && !unknown {
            let tuple = self.text(&Ty::of_row(cs.clone()));
            let shown = self.text(&key);
            self.no_component(&tuple, n, &shown, span);
            return out;
        }
        let keys = KType::union_all(
            picked
                .iter()
                .filter_map(|j| i64::try_from(*j).ok())
                .filter_map(|j| KType::lit(&Value::Int(j))),
        );
        let outside = unknown || !self.subtype(&key, &Ty::set(keys));
        out = out.union(&Ty::union_all(picked.iter().map(|j| &cs[*j])));
        if outside {
            out = out.union(&Ty::set(KType::atom("notFound")));
        }
        out
    }

    /// The derivation of an application `apply` rejects: each argument's, in order, then each
    /// arrow of `sig`, the constraints it failed.
    fn applied(&self, what: &str, sig: &Sig, args: &[Option<Arg>], span: Span) -> Vec<Note> {
        let mut out = Vec::new();
        for a in args.iter().flatten() {
            match (&a.lit, a.at) {
                (Some(l), Some(at)) => out.push(Note {
                    span: at,
                    text: literal_note(l.written(), self.text(&a.ty)),
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
                word: None,
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

    /// Adds the note at `span` that `text` words to each error from the `from`th on that lacks
    /// it; the note is put into words only when there is such an error, and none while a
    /// repair is tried, since its errors are only counted.
    fn also(&mut self, from: usize, span: Span, text: impl FnOnce(&Self) -> String) {
        self.also_notes(from, |ck| {
            built(1);
            vec![Note {
                span,
                text: text(ck),
            }]
        });
    }

    /// [`Self::also`] of the notes `notes` makes, in order: each error from the `from`th on
    /// gets those it lacks, in `O(m + k)` for its `m` notes and the `k` added.
    fn also_notes(&mut self, from: usize, notes: impl FnOnce(&Self) -> Vec<Note>) {
        if self.trying || self.info.errors.len() <= from {
            return;
        }
        let notes = notes(self);
        for e in &mut self.info.errors[from..] {
            let have: HashSet<&Note> = e.notes.iter().collect();
            let new: Vec<Note> = (notes.iter())
                .filter(|n| !have.contains(n))
                .cloned()
                .collect();
            // A witness goes before the menu, which ends the notes.
            let menu = (e.notes.iter())
                .position(|n| n.text.starts_with("repair: "))
                .unwrap_or(e.notes.len());
            e.notes.splice(menu..menu, new);
        }
    }

    /// Whether `what` is an operator and an operand's type, one closed type, shares no value
    /// with the parameter of any arrow at its place: `7 / 2`, whose `int` operands no arrow
    /// of `/` takes, and not `r + x` of a `rat` and an `f64`, each of which an arrow takes.
    /// One meet per operand and arrow.
    fn no_arrow_at_carrier(&self, what: &str, sig: &Sig, args: &[Option<Arg>]) -> bool {
        let op = what.trim_matches('`');
        let operator = matches!(
            op,
            "+" | "-"
                | "*"
                | "/"
                | "div"
                | "mod"
                | "^"
                | "++"
                | "<"
                | "<="
                | ">"
                | ">="
                | "&&"
                | "||"
                | "!"
        );
        operator
            && args.iter().enumerate().any(|(i, a)| {
                a.as_ref().is_some_and(|a| {
                    let t = &a.ty;
                    !t.dynamic
                        && t.vars.is_empty()
                        && !t.set.is_empty()
                        && sig
                            .arrows
                            .iter()
                            .all(|arrow| (&t.set & &arrow.params[i].set).is_empty())
                })
            })
    }

    /// Whether two of `args` are numbers with no carrier in common and no arrow of `sig`
    /// takes all the numbers of `args` together, though some arrow takes each alone: `r + x`
    /// of a `rat` and an `f64`, `q + 1.5` of an `int` and an `f64` literal, `max(r, x)`. A
    /// bounded variable stands for one carrier at all its places (sec:type_resolution), so
    /// `f(a: T, b: T)` takes no `rat` and `f64` together. An argument whose values are not
    /// all numbers of known carriers, a generic literal `kn` among them, decides nothing.
    /// One pass over the arguments per arrow, and the pairs of the seven sets of numeric
    /// carriers, a constant.
    fn no_common_carrier(&self, sig: &Sig, args: &[Option<Arg>]) -> bool {
        let masks: Vec<Option<u8>> = args
            .iter()
            .map(|a| a.as_ref().and_then(|a| self.numbers_of(a)))
            .collect();
        // The sets of carriers the arguments take, each a bit: a mask is below 16.
        let kinds = masks.iter().flatten().fold(0u16, |k, &m| k | 1 << m);
        let has = |m: u8| kinds & 1 << m != 0;
        let disjoint = (1..16u8).any(|m| has(m) && (1..16u8).any(|n| has(n) && m & n == 0));
        if !disjoint {
            return false;
        }
        let takes = |p: &Ty, m: u8| m & self.param_mask(sig, p);
        let each = masks.iter().enumerate().all(|(i, m)| {
            m.is_none_or(|m| {
                (sig.arrows.iter()).any(|ar| ar.params.get(i).is_some_and(|p| takes(p, m) != 0))
            })
        });
        each && !sig.arrows.iter().any(|ar| {
            let mut common: HashMap<&str, u8> = HashMap::new();
            masks.iter().zip(&ar.params).all(|(m, p)| {
                let Some(m) = *m else {
                    return true;
                };
                let t = takes(p, m);
                match p.as_var().filter(|v| sig.bounds.contains_key(*v)) {
                    _ if t == 0 => false,
                    Some(v) => {
                        let c = common.entry(&**v).or_insert(EVERY);
                        *c &= t;
                        *c != 0
                    }
                    None => true,
                }
            })
        })
    }

    /// The numeric carriers a value of the argument `a` may be of, `None` unless every value
    /// is a number of a known carrier: a plain literal's own carrier, and otherwise those of
    /// its type ([`Self::numbers_in`]); a generic literal `kn` may take any.
    fn numbers_of(&self, a: &Arg) -> Option<u8> {
        match &a.lit {
            Some(l) if l.n => None,
            Some(l) => Some(lit_carrier(&l.value).bit()),
            None => self.numbers_in(&a.ty),
        }
    }

    /// The numeric carriers a value of `t` may be of, `None` unless every value is a number
    /// of a known carrier, a class's carriers where it holds numbers only. Atoms, which pass
    /// by, are not read. One split of the set and one lookup per variable.
    fn numbers_in(&self, t: &Ty) -> Option<u8> {
        let numbers = Carrier::Int.bit() | Carrier::Rat.bit() | Carrier::F64.bit();
        if t.dynamic || !t.tuples.is_empty() || !t.fns.is_empty() {
            return None;
        }
        let s = t.set.split();
        if s.rest.is_some() {
            return None;
        }
        let mut m = Carrier::ALL
            .into_iter()
            .filter(|c| s.bases[c.base()].is_some())
            .fold(0, |m, c| m | c.bit());
        for v in &t.vars {
            m |= self.classes[self.class_of(&Piece::Var(v.clone()))?].mask;
        }
        (m != 0 && m & !numbers == 0).then_some(m)
    }

    /// The carriers a parameter `p` of `sig` takes: a bounded variable's bound, a class's
    /// carriers, and those of a closed type; every value for a variable or `_`.
    fn param_mask(&self, sig: &Sig, p: &Ty) -> u8 {
        if let Some(&b) = p.as_var().and_then(|v| sig.bounds.get(v)) {
            return b;
        }
        match self.class_of_ty(p) {
            Some(r) => self.classes[r].mask,
            None => mask_of(p),
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

    /// Whether the parameter `p` of an arrow of `sig` takes every one of the atoms `loose`.
    fn takes_all(&self, sig: &Sig, p: &Ty, loose: &KType) -> bool {
        if let Some(&m) = p.as_var().and_then(|v| sig.bounds.get(v)) {
            return m & OTHER != 0;
        }
        p.dynamic
            || !p.vars.is_empty()
            || self.class_of_ty(p).is_some()
            || (loose - &p.set).is_empty()
    }

    /// The first arrow of `sig` whose parameter `i` takes every atom of `loose[i]`, for each
    /// `i` where they are not empty, or else the first that takes some of them. The first rule
    /// keeps a key `#a | #b` of `#a .. #a | #b -> V`, whose arrows are `(#a) -> V` and
    /// `(#a | #b) -> V | #notFound`, from the arrow that takes `#a` alone (rule 6 of DESIGN.md
    /// sec:type_resolution: the region `#b` has the second arrow only).
    fn taking(&self, sig: &Sig, loose: &[KType]) -> Option<usize> {
        let first = |fits: &dyn Fn(&Ty, &KType) -> bool| {
            sig.arrows.iter().position(|arrow| {
                (arrow.params.iter().zip(loose)).all(|(p, l)| *l == KType::empty() || fits(p, l))
            })
        };
        first(&|p, l| self.takes_all(sig, p, l))
            .or_else(|| first(&|p, l| !self.refused_at(sig, p, l)))
    }

    /// The message of an application that does not check: the arguments, each class shown
    /// as the carriers left to it.
    fn rejected(&self, what: &str, args: &[Option<Arg>]) -> String {
        self.rejected_at(what, args, None)
    }

    /// [`Self::rejected`] when the check was not decided, `why` saying why: the message then
    /// says that, and not that no arrow takes the arguments.
    fn rejected_because(&self, what: &str, args: &[Option<Arg>], why: &str) -> String {
        self.message_of(what, args, None, why)
    }

    /// [`Self::rejected`], with argument `i` shown as the piece `p` of it that failed at the
    /// parameter of type `q`, and the cause when that check was refused.
    fn rejected_at(
        &self,
        what: &str,
        args: &[Option<Arg>],
        at: Option<(usize, &Piece, &Ty)>,
    ) -> String {
        self.message_of(what, args, at, "")
    }

    /// The message of [`Self::rejected_at`], `why` given as the cause when the check was not
    /// decided: with no cause, the arguments' types and that no arrow of `what` takes them all,
    /// which the derivation then shows arrow by arrow.
    fn message_of(
        &self,
        what: &str,
        args: &[Option<Arg>],
        at: Option<(usize, &Piece, &Ty)>,
        why: &str,
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
            .filter(|w| !w.is_empty())
            .unwrap_or_else(|| why.to_string());
        does_not_take(what, &shown.join(", "), &why)
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
            let mut error = None;
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
                    Err(e) => {
                        error.get_or_insert(e);
                    }
                    // Kept as it is, the argument is checked as any argument is.
                    _ => ok &= a.ty.meets(p),
                }
            }
            // The message names a literal's rejection at an arrow the other arguments fit:
            // `x + 0.1` with `x: rat` at rat, not at int; and of two literals of two
            // carriers, as at `==`, the integer's, or else the decimal's: `1 + 0.5` at `1`.
            if let Some(e) = error {
                let rank = |s: Span| {
                    args.iter()
                        .flatten()
                        .filter_map(|a| a.lit.as_ref())
                        .find(|l| l.site == s)
                        .map_or(3, |l| match lit_carrier(&l.value) {
                            Carrier::Int => 0,
                            Carrier::F64 => 1,
                            _ => 2,
                        })
                };
                if ok
                    && adopt_error
                        .as_ref()
                        .is_none_or(|(t, _)| rank(e.0) < rank(*t))
                {
                    adopt_error = Some(e);
                }
                continue;
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
                self.lit_refused.push((s, m));
                return Ok(None);
            }
            // No arrow met an argument, which may rest on a refused check that it is empty.
            let tys: Vec<Option<&Ty>> = args
                .iter()
                .map(|a| a.as_ref().filter(|a| a.lit.is_none()).map(|a| &a.ty))
                .collect();
            let all: Vec<usize> = (0..sig.arrows.len()).collect();
            let why = refused_among(sig, &all, &tys);
            return Err(self.rejected_because(what, args, &why));
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
    kernel_type(a, &mut Vec::new(), None).map(|k| k.surface().to_string())
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
        .map(|r| ty::undecided(&r.message()))
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

/// `out` with the atoms of `ts` added, with their payloads: when two of them can carry
/// different failures at once ([`ty::merges`]), also `#errs(E ->? E)`, which they merge into,
/// with `E` the failures that meet and the members of an operand's own `#errs` in place of
/// it, since the merge flattens (DESIGN.md sec:failure). That `#errs` holds the operands'
/// own, whose members are in `E`, so theirs is not added; a chain carries one `#errs`, not one
/// per step. An `#errs` whose members are not known leaves those of the merge unknown.
fn passed<'t>(out: &mut Ty, ts: impl Iterator<Item = &'t Ty>) {
    let mut holding = Vec::new();
    for t in ts {
        let a = t.atoms();
        if !a.is_empty() {
            // A `KType` is one `Arc`, so the clone is a count, not a copy of the type.
            holding.push((t, a));
        }
    }
    if !ty::merges(holding.iter().map(|(_, a)| a)) {
        for (t, a) in holding {
            *out = out.union(&t.of_piece(&Piece::Set(a)));
        }
        return;
    }
    let mut members = Some(Ty::empty());
    for (t, a) in holding {
        let loose = t.of_piece(&Piece::Set(&a - &errs()));
        *out = out.union(&loose);
        members = members.map(|m| m.union(&loose));
        if ty::holds_errs(&a) {
            members = members.zip(ty::errs_members(t)).map(|(m, e)| m.union(&e));
        }
    }
    *out = out.union(&members.map_or_else(|| Ty::set(errs()), ty::errs_of));
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

/// Where a path of [`Ck::apply_many`] puts the arguments' class: `None` where no piece of
/// it is the class, else by arrow the carriers that arrow's parameters at the class's
/// pieces all allow (read at the arrows alive).
type ClassAt = Option<Vec<u8>>;

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
    /// The atoms the call at the first span passes by at its argument at the second.
    Passes(Span, Span, Option<KType>),
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
            Undo::Passes(k, at, v) => {
                // One argument's entry, so that a write costs one entry and not the call's
                // whole list (PASS-at-args); a call whose last entry goes has none.
                let call = i.passes.entry(k).or_default();
                let old = set!(call, at, v);
                if call.is_empty() {
                    i.passes.remove(&k);
                }
                Undo::Passes(k, at, old)
            }
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

/// `e` as a numeric literal, perhaps under one `-`; `None` also where the system refuses the
/// memory to read it, which [`Ck::expr_of`] reports through [`read_literal`].
fn literal(e: &Expr) -> Option<Lit> {
    read_literal(e).ok().flatten()
}

/// `e` as a numeric literal, perhaps under one `-`; [`TooLarge`] when the system refuses the
/// memory to read its digits or to copy its text. The lexer has removed the `_` from the
/// digits, so they are read where they are, not copied.
fn read_literal(e: &Expr) -> Result<Option<Lit>, TooLarge> {
    let inner = match &e.kind {
        ExprKind::Unary("-", a) => &**a,
        _ => e,
    };
    let (value, n) = match &inner.kind {
        ExprKind::Int {
            radix,
            digits,
            generic,
        } => match Value::int_text(digits, *radix)? {
            Some(v) => (v, *generic),
            None => return Ok(None),
        },
        ExprKind::Float(s) => match s.parse() {
            Ok(x) => (Value::float(x), false),
            Err(_) => return Ok(None),
        },
        _ => return Ok(None),
    };
    Ok(Some(Lit {
        span: inner.span,
        site: e.span,
        value,
        text: Rc::new(shown(inner)?),
        n,
        generic: false,
        witness: false,
    }))
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
fn side<'b>(a: &'b Arg<'_>) -> Side<'b> {
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
fn components<'a>(a: &Arg<'a>, n: usize) -> Option<Vec<Arg<'a>>> {
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

/// `a` where a value of `p` is expected: a generic literal `kn` takes `p`'s one numeric
/// carrier, and one in a tuple the one carrier its component holds across `p`'s tuple shapes
/// of that length, at any depth (DESIGN.md L1.26, sec:domains): `(1n, 2n)` at
/// `(f64, f64) | (String, f64)` is `(1.0, 2.0)`. A plain literal takes no carrier, and where
/// the expected type holds numbers but not its own carrier is rejected ([`expected`]): `(1, 2)`
/// at `(f64, f64)`. This is the one place an expected type decides a literal's carrier. Gives
/// `a`'s type with the adoptions and the adoptions, `None` when no literal adopts, and the
/// first literal that is rejected or is not exactly a value of its carrier, with the message.
///
/// The tuples nest as deep as the text, so the walk keeps its own stack: each open tuple's
/// parts, the argument's components, the expected shapes there, and the types so far. The
/// shapes are borrowed from `p`: no union of them is built.
fn adopted(a: &Arg, p: &Ty) -> Result<Option<(Ty, Adoptions)>, (Span, String)> {
    let mut ads = Adoptions::new();
    let lit = |l: &Lit, want: &[&Ty], ads: &mut Adoptions| {
        let Some(c) = expected(l, want).map_err(|m| (l.site, m))? else {
            return Ok(None);
        };
        match adopt(l, c) {
            Ok(Some(v)) => {
                let t = lit_ty(&v, l.neg());
                ads.push((l.span, v));
                Ok(Some(t))
            }
            Ok(None) => Ok(None),
            Err(m) => Err((l.site, m)),
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

/// The literal `l` as a `c`: `None` when it is one already or `c` is not a number, an error
/// when it is a plain literal, which takes no other carrier ([`menu`]), or is not exactly a
/// `c`.
fn adopt(l: &Lit, c: Carrier) -> Result<Option<Value>, String> {
    if lit_carrier(&l.value) == c || !c.numeric() {
        return Ok(None);
    }
    if !adoptable(l, c) {
        return Err(menu(l, &[c]));
    }
    let exact = match &l.value {
        Value::Float(_) => Rat::decimal(&l.text)
            .map_err(|r| unread_literal(&r))?
            .map(Value::rat),
        v => run(Prim::CastRat, v),
    };
    let not = || {
        let (a, name) = (article(c), c.name());
        // Why, and the repair, after the literal or the words that stand for it.
        let why = format!(
            ": a literal written with `n` takes the carrier expected only when it is exactly a \
             number of that carrier, and no {name} is exactly this number; write a literal that \
             is exactly {a} {name}, or write the number followed by `r` if the exact rational \
             is meant"
        );
        Err(quoting(
            &format_args!("`{}` is not {a} {name}{why}", l.written()),
            || format!("this literal is not {a} {name}{why}"),
        ))
    };
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

/// Whether `l` may take the carrier `c`: a generic literal `kn` any numeric carrier, and a
/// plain literal only its own, since a plain literal adopts no carrier (DESIGN.md
/// sec:domains, L1.26: a plain integer literal is `int` and a decimal one `f64`, whatever
/// is expected).
fn adoptable(l: &Lit, c: Carrier) -> bool {
    c.numeric() && (l.n || c == lit_carrier(&l.value))
}

/// The literal `l` where a value of one of the types `want` is expected: the carrier it
/// takes there, `None` when it keeps its own, or the rejection. A plain literal keeps its
/// own carrier and is rejected with a menu of the forms to write ([`menu`]) where the types
/// hold numbers but none of its carrier; a generic literal `kn` takes the one numeric carrier
/// they hold, and at two or more that are not `int` is rejected ([`no_one_carrier`]). A type
/// that holds a variable or the unknown could stand for any number, and decides nothing.
fn expected(l: &Lit, want: &[&Ty]) -> Result<Option<Carrier>, String> {
    if want.iter().any(|w| !w.vars.is_empty() || w.dynamic) {
        return Ok(None);
    }
    let held: Vec<Carrier> = [Carrier::Int, Carrier::Rat, Carrier::F64]
        .into_iter()
        .filter(|&c| want.iter().any(|w| !(&w.set & &c.ty()).is_empty()))
        .collect();
    let own = lit_carrier(&l.value);
    match held[..] {
        [] => Ok(None),
        _ if held.contains(&own) && !(l.n && held.len() == 1) => Ok(None),
        _ if !l.n => Err(menu(l, &held)),
        [c] => Ok(Some(c)),
        _ => Err(no_one_carrier(
            l,
            &Ty::union_all(want.iter().copied()),
            &held,
        )),
    }
}

/// The message for the plain literal `l` where a number of one of the carriers `held` is
/// expected, one or more, none of them the literal's own: Zed converts no value, so the
/// literal is rejected, with the forms to write of those carriers, in the order `1.0`, `1r`,
/// `1n` (DESIGN.md sec:domains). A form is offered only where it is the same number exactly:
/// `1.0` and `1n` where the literal is exactly an `f64`; `1n` only at one carrier, since at
/// two it takes neither; and of a literal written in another radix, which has no `.0` or `r`
/// form, only `kn`.
fn menu(l: &Lit, held: &[Carrier]) -> String {
    let own = lit_carrier(&l.value);
    let sign = if l.neg() { "-" } else { "" };
    let names = held
        .iter()
        .map(|c| c.name())
        .collect::<Vec<_>>()
        .join(" | ");
    let decimal = l.text.chars().all(|c| c.is_ascii_digit() || c == '_');
    // The clone shares the literal's text, so it copies none of its digits.
    let exact = |c: Carrier| {
        let n = Lit {
            n: true,
            ..l.clone()
        };
        adopt(&n, c).is_ok()
    };
    let has = |c: Carrier| held.contains(&c);
    // Each form is the literal followed by one of these, written into the message only.
    let mut forms = Vec::new();
    match own {
        Carrier::Int => {
            if decimal && has(Carrier::F64) && exact(Carrier::F64) {
                forms.push(".0");
            }
            if decimal && has(Carrier::Rat) {
                forms.push("r");
            }
            if let [c] = held
                && exact(*c)
            {
                forms.push("n");
            }
        }
        _ if has(Carrier::Rat) => forms.push("r"),
        _ => {}
    }
    let (what, carrier) = (article(own), own.name());
    let text = &l.text;
    quoting(
        &fmt::from_fn(|f| {
            write!(
                f,
                "`{sign}{text}` is {what} {carrier} where `{names}` is expected; a literal takes \
                 no other carrier"
            )?;
            write_forms(f, "; write ", &forms, |f, s| write!(f, "`{sign}{text}{s}`"))
        }),
        || {
            let mut m = format!(
                "this literal is {what} {carrier} where `{names}` is expected; a literal takes \
                 no other carrier"
            );
            let _ = write_forms(&mut m, "; write it followed by ", &forms, |m, s| {
                write!(m, "`{s}`")
            });
            m
        },
    )
}

/// The literals of the other carriers that are exactly the number of `e` when `e` is a `rat`
/// literal, `k` or `-k` with `k` written `1r` or `0.5r`, each with its type and the repair
/// that writes it, in the order of [`menu`]: the `f64` literal, `1.0` or `0.5`, where the
/// number is an `f64` exactly, then the `int` literal, `1`, where it is written without a
/// point; `None` when `e` is no `rat` literal. A literal has no length limit, so a repair
/// that quotes it is written in memory asked for first ([`quoting`]).
fn rat_forms(e: &Expr) -> Option<Vec<(Ty, String)>> {
    let (neg, digits) = match &e.kind {
        ExprKind::Rat(d) => (false, d),
        ExprKind::Unary("-", a) => match &a.kind {
            ExprKind::Rat(d) => (true, d),
            _ => return None,
        },
        _ => return None,
    };
    let v = neg_value(&Value::rat(Rat::decimal(digits).ok()??), neg);
    let sign = if neg { "-" } else { "" };
    let point = digits.contains('.');
    let mut out = Vec::new();
    for (prim, carrier, suffix) in [
        (Prim::CastF64, Carrier::F64, if point { "" } else { ".0" }),
        (Prim::CastInt, Carrier::Int, ""),
    ] {
        if carrier == Carrier::Int && point {
            continue;
        }
        let Some(x) = run(prim, &v).filter(|x| !matches!(x, Value::Atom(_))) else {
            continue;
        };
        let text = quoting(
            &format_args!("repair: write `{sign}{digits}{suffix}`; the checker accepts that"),
            || {
                format!(
                    "repair: write this literal as {} {} literal; the checker accepts that",
                    article(carrier),
                    carrier.name()
                )
            },
        );
        out.push((Ty::lit(&x), text));
    }
    Some(out)
}

/// The message for the literal `l` where `want` holds numbers of the carriers `cs`, two or
/// more, none of them the literal's own.
fn no_one_carrier(l: &Lit, want: &Ty, cs: &[Carrier]) -> String {
    let names = cs
        .iter()
        .map(|c| c.name())
        .collect::<Vec<_>>()
        .join(" and ");
    let sign = if l.neg() { "-" } else { "" };
    // Only an integer literal reaches here, since a decimal one's own f64 or its one other
    // carrier, rat, would be taken; a written radix has no `.0` or `r` form. The forms of
    // `kn` are those of `k`.
    let digits = l.text.strip_suffix('n').filter(|_| l.n).unwrap_or(&l.text);
    let forms: Vec<&str> = match digits.chars().all(|c| c.is_ascii_digit()) {
        true => cs
            .iter()
            .filter_map(|c| match c {
                Carrier::F64 => Some(".0"),
                Carrier::Rat => Some("r"),
                _ => None,
            })
            .collect(),
        false => Vec::new(),
    };
    let text = &l.text;
    quoting(
        &fmt::from_fn(|f| {
            write!(
                f,
                "`{sign}{text}` at `{want}` adopts no one carrier: the type holds numbers of \
                 {names}"
            )?;
            or_forms(f, "; write the one meant, as ", &forms, |f, s| {
                write!(f, "`{sign}{digits}{s}`")
            })
        }),
        || {
            let mut m = format!(
                "this literal at `{want}` adopts no one carrier: the type holds numbers of {names}"
            );
            let _ = or_forms(
                &mut m,
                "; write the one meant, followed by ",
                &forms,
                |m, s| write!(m, "`{s}`"),
            );
            m
        },
    )
}

/// The note that the literal written `text` is `ty`, quoting the literal when the system gives
/// the memory for it ([`quoting`]).
fn literal_note(text: impl fmt::Display, ty: impl fmt::Display) -> String {
    quoting(&format_args!("this literal, {text}, is {ty}"), || {
        format!("this literal is {ty}")
    })
}

/// The message `m`, which quotes a literal's text, written in memory the system gives first
/// ([`shown`]); when it refuses, `instead`, which does not quote it. A literal has no length
/// limit, and a message copied without asking would abort the checker on a long one.
fn quoting(m: &impl fmt::Display, instead: impl FnOnce() -> String) -> String {
    shown(m).unwrap_or_else(|_| instead())
}

/// Writes `lead` and the forms `forms`, each by `form`, as a list `a`, `a or b` or
/// `a, b or c`; nothing when there are none.
fn write_forms<W: fmt::Write>(
    w: &mut W,
    lead: &str,
    forms: &[&str],
    form: impl Fn(&mut W, &str) -> fmt::Result,
) -> fmt::Result {
    let Some((last, init)) = forms.split_last() else {
        return Ok(());
    };
    w.write_str(lead)?;
    for (i, s) in init.iter().enumerate() {
        if i > 0 {
            w.write_str(", ")?;
        }
        form(w, s)?;
    }
    if !init.is_empty() {
        w.write_str(" or ")?;
    }
    form(w, last)
}

/// Writes `lead` and the forms `forms`, each by `form`, joined by ` or `; nothing when there
/// are none.
fn or_forms<W: fmt::Write>(
    w: &mut W,
    lead: &str,
    forms: &[&str],
    form: impl Fn(&mut W, &str) -> fmt::Result,
) -> fmt::Result {
    if forms.is_empty() {
        return Ok(());
    }
    w.write_str(lead)?;
    for (i, s) in forms.iter().enumerate() {
        if i > 0 {
            w.write_str(" or ")?;
        }
        form(w, s)?;
    }
    Ok(())
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
        "^" => (2, arrows(&[Int, F64], 2, same)),
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
        word: None,
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
        word: Some(w.into()),
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
    zedc_base::interp::prim(w).filter(|&p| zed_kernel::bits::is_bit_word(p))
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
        word: None,
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
    /// Whether a test the walk is in narrowed them.
    narrowed: bool,
}

/// The ints at least 0, `int[0..]`.
fn at_least_zero() -> IntervalSet {
    IntervalSet::range(End::of(0), PosInf)
}

/// The domain `d` as a type, `int[0..]` or `int[0..<2^w]`.
fn domain_text(d: &IntDomain) -> String {
    match &d.below_two_pow {
        None => "int[0..]".into(),
        Some(w) => format!("int[0..<2^{}]", w.0),
    }
}

/// Whether the int `v` is in the domain `d`.
fn value_in(d: &IntDomain, v: &Value) -> bool {
    v.surface_cmp(&Value::Int(0))
        .is_some_and(|o| o != std::cmp::Ordering::Less)
        && (d.below_two_pow.as_ref()).is_none_or(|w| zed_kernel::bits::below_two_pow(v, &w.0))
}

/// Whether the interval `ints` lies in the domain `d`: below `2 ^ w` when its largest value is.
fn ints_in(d: &IntDomain, ints: &IntervalSet) -> bool {
    if !ints.is_subset(&at_least_zero()) {
        return false;
    }
    let Some(w) = &d.below_two_pow else {
        return true;
    };
    match ints.bounds() {
        None => true,
        Some((_, Fin(h))) => zed_kernel::bits::below_two_pow(&Value::from(h), &w.0),
        Some(_) => false,
    }
}

/// Whether the ints `r` holds are in the domain `d`.
fn range_in(d: &IntDomain, r: &IntRange) -> bool {
    match &r.values {
        Some(vs) => vs.iter().all(|v| value_in(d, v)),
        None => ints_in(d, &r.ints),
    }
}

/// Whether `ints`, an int type, lists its values and each is in the domain `d`.
fn listed_in(d: &IntDomain, ints: &KType) -> bool {
    ints.ints_listed()
        .is_some_and(|vs| vs.iter().all(|v| value_in(d, v)))
}

/// Whether `ints`, an int type, lists its values and each is at least 0.
fn listed_at_least_zero(ints: &KType) -> bool {
    let zero = Value::Int(0);
    ints.ints_listed().is_some_and(|vs| {
        vs.iter().all(|v| {
            v.surface_cmp(&zero)
                .is_some_and(|o| o != std::cmp::Ordering::Less)
        })
    })
}

/// Whether every value `r` holds is shown to be a multiple of 8: its listed values each are, or
/// its interval is one such value.
fn whole_bytes(r: &IntRange) -> bool {
    let eight = |v: &Value| {
        v.as_integer()
            .is_some_and(|n| Num::from(&*n).mod_floor(&Num::from(8)).is_zero())
    };
    match (&r.values, r.ints.bounds()) {
        (Some(vs), _) => vs.iter().all(eight),
        (None, Some((Fin(a), Fin(b)))) if a == b => eight(&Value::from(a)),
        _ => false,
    }
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
    /// Complexity tradeoff: the text is read, not the reduced product's cell after the store's
    /// fixpoint, so a parameter, an input or a tuple component is read as any int where no test
    /// bounds it, and a bit word on it is rejected as possibly outside its domain. Under a test
    /// the read is met with the scope that the tests make ([`Ck::ints_here`], `arms.rs`), so
    /// `if n >= 0 { popCount(n) }` is accepted. Why: the checker runs before the store's
    /// iteration, and asking the store at each call would run a fixpoint per call; reading the
    /// text is O(1) per node, and each test's scope is one narrowing of its parent's. Trigger:
    /// an operand whose sign or width only a caller, the input or a tuple component shows.
    /// Test: `l01_39a_bit_words::errors::an_operand_not_shown_in_its_domain_is_rejected`.
    /// COMPLEXITY.md row C26. A complete solution needs int-range types on parameters and
    /// results (step L10, ledger BIT-checker-ranges), so a signature can state the domain.
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
            ExprKind::Binary(o, a, b) if *o == "^" || int_op(o).is_some() => vec![&**a, &**b],
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
                && zedc_resolve::resolve::prelude_layer(name) == Some(1) =>
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
            ExprKind::Int { radix, digits, .. } => Value::int_text(digits, *radix)
                .ok()
                .flatten()
                .map_or_else(Known::top, Known::of),
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
            ExprKind::Binary("^", a, b) => {
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

/// The atoms the uses of each binder handle, by binder.
struct Handled {
    /// The atoms each binder's uses handle, `None` for none.
    atoms: Vec<Option<KType>>,
}

impl Handled {
    /// The atoms the uses of binder `id` handle, through every name bound to a value they
    /// pass into.
    fn get(&self, id: usize) -> Option<&KType> {
        self.atoms[id].as_ref()
    }
}

/// The atoms the uses of each binder handle (DESIGN.md sec:type_resolution, the author's Q5:
/// inference runs after bubbling). A binder's uses handle what the regions they flow into
/// ([`Resolution::flows`]) handle; a region handles its own handler's atoms, what the region
/// its value passes on to handles, and, for the value of `s = e`, what the uses of `s`
/// handle. So `s = trim(line); s else ""` handles every loose atom for `line`, in whatever
/// order the block writes its bindings, while in `{ s = a + b; a else 0 }` the `else` handles
/// nothing for `b`: a binding passes atoms from its name to its value, not back.
///
/// The `B` binders and `R` regions are the nodes of a graph whose `E` edges run from each
/// node to the nodes whose atoms it takes. Tarjan's algorithm, with an explicit stack, finds
/// its strongly connected components with every component a node takes from finished
/// first, and gives each component the union of its own handlers and what it takes, so
/// the whole is `O(B + R + E)` unions; a cycle, such as a name bound to a value that uses
/// it, is one component and shares one set. A set only gains atoms along the way.
// Complexity tradeoff: each union joins two sets of atoms, whose cost grows with the distinct
// atoms the unit's handlers name (`#a` in `else #a ->`, `is #a`, `== #a`), not with the unit;
// `Handle::Loose` gives every loose atom at once. Bounding it by the unit's size alone would
// need sets keyed by the handlers rather than by their atoms, which the checker would then
// have to expand at each parameter anyway.
fn handled(res: &Resolution) -> Handled {
    const NONE: usize = usize::MAX;
    let (b, total) = (res.binders.len(), res.binders.len() + res.regions.len());
    // The edges in compressed rows: `to[from[v]..from[v + 1]]` are the nodes `v` takes from.
    let mut edges: Vec<(usize, usize)> = Vec::with_capacity(res.flows.len() + res.regions.len());
    for (r, region) in res.regions.iter().enumerate() {
        edges.extend(region.parent.map(|p| (b + r, b + p)));
        edges.extend(region.into.map(|s| (b + r, s)));
    }
    for (span, r) in &res.flows {
        if let Some(Ref::Bound(ids)) = res.uses.get(span)
            && ids.len() == 1
        {
            edges.push((ids[0], b + r));
        }
    }
    let mut from = vec![0usize; total + 1];
    for &(v, _) in &edges {
        from[v + 1] += 1;
    }
    for v in 0..total {
        from[v + 1] += from[v];
    }
    let mut to = vec![0usize; edges.len()];
    let mut fill = from.clone();
    for &(v, w) in &edges {
        to[fill[v]] = w;
        fill[v] += 1;
    }
    let own = |v: usize| -> Option<KType> {
        let region = res.regions.get(v.checked_sub(b)?)?;
        region
            .handles
            .iter()
            .map(|h| match h {
                Handle::Loose => atoms(),
                Handle::Any(n) => any_payload(n),
                Handle::Bare(n) => KType::atom(n),
            })
            .reduce(|x, y| &x | &y)
    };
    let join = |acc: Option<KType>, a: Option<&KType>| match (acc, a) {
        (Some(x), Some(y)) => Some(&x | y),
        (acc, None) => acc,
        (None, Some(y)) => Some(y.clone()),
    };
    let mut value: Vec<Option<KType>> = vec![None; total];
    let (mut index, mut low, mut on) = (vec![NONE; total], vec![0usize; total], vec![false; total]);
    let (mut next, mut open, mut members) = (0usize, Vec::new(), Vec::new());
    // The nodes being visited, each with the next of its edges to follow.
    let mut call: Vec<(usize, usize)> = Vec::new();
    for s in 0..total {
        if index[s] != NONE {
            continue;
        }
        index[s] = next;
        low[s] = next;
        next += 1;
        open.push(s);
        on[s] = true;
        call.push((s, from[s]));
        while let Some(&mut (v, ref mut i)) = call.last_mut() {
            if *i < from[v + 1] {
                let w = to[*i];
                *i += 1;
                if index[w] == NONE {
                    index[w] = next;
                    low[w] = next;
                    next += 1;
                    open.push(w);
                    on[w] = true;
                    call.push((w, from[w]));
                } else if on[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            call.pop();
            if let Some(&(u, _)) = call.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] != index[v] {
                continue;
            }
            members.clear();
            while let Some(w) = open.pop() {
                on[w] = false;
                members.push(w);
                if w == v {
                    break;
                }
            }
            // The component's own nodes have no value yet, so only finished ones join.
            let mut acc = None;
            for &w in &members {
                acc = join(acc, own(w).as_ref());
                for &d in &to[from[w]..from[w + 1]] {
                    acc = join(acc, value[d].as_ref());
                }
            }
            for &w in &members {
                value[w].clone_from(&acc);
            }
        }
    }
    value.truncate(b);
    Handled { atoms: value }
}

/// The atom `#name` with any payload or none: what a bare pattern `#name` matches.
pub fn any_payload(name: &str) -> KType {
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
    t.payloads
        .insert("ioError".into(), Some(vec![Shape::new(Vec::new(), fields)]));
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
        word: None,
        needs: Vec::new(),
        own: BTreeSet::new(),
        held: BTreeSet::new(),
        named: 0,
        facts: Default::default(),
    }))
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
/// leaves unbound by the unknown. Those are added to `binds` for the replacement and removed
/// after it, so `binds` is as it was and each need costs the size of `t` and `log` of the
/// size of `binds`, not a copy of `binds`.
fn bound(t: &Ty, binds: &mut Binds, is_class: impl Fn(&str) -> bool) -> Ty {
    let vars = t.var_facts();
    let add: Vec<_> = (vars.classes.iter().chain(&vars.names))
        .filter(|v| !is_class(v) && !binds.contains_key(*v))
        .collect();
    for v in &add {
        binds.insert((*v).clone(), Ty::dynamic());
    }
    let out = t.replace(binds);
    for v in add {
        binds.remove(v);
    }
    out
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
        empty: None,
    }
    .ty(t)
}

/// The steps that say why each part of the written type `t` that is written as a tuple type, an
/// atom with a payload, a union, an intersection or a difference has no value, and so is
/// printed `Never` (DESIGN.md sec:diagnostics: a message names every step from the cause to
/// what it prints). A part inside one so explained is explained only where it is the cause:
/// each step names its cause, a part written `Never` by name or the part explained in the
/// step before it, so the steps run from the cause to the part `t` holds.
///
/// Built only for a message that is printed. One denotation of `t` that keeps the span of
/// each part with no value, and one walk of `t`, each with its own stack: the time is linear
/// in the size of `t`. Each step quotes no part it names but a name, an operand of the one
/// intersection or difference whose operands all have values, which no other step quotes,
/// so the text is linear in the size of `t` too.
fn emptied(t: &Type, out: &mut Vec<Note>) {
    let mut d = Denote {
        leaves: &Binds::new(),
        bound: HashMap::new(),
        open: Vec::new(),
        empty: Some(HashSet::new()),
    };
    d.ty(t);
    let empty = d.empty.unwrap_or_default();
    // A `for` clause has the value of the type it bounds.
    fn bare(mut t: &Type) -> &Type {
        while let TypeKind::For { ty, .. } = &t.kind {
            t = ty;
        }
        t
    }
    let none = |t: &Type| empty.contains(&bare(t).span);
    // What the step after the one that explains `c` calls it.
    let cause = |c: &Type| match &bare(c).kind {
        TypeKind::Name(n) => format!("`{n}`"),
        TypeKind::Tuple(_) => "the tuple type of the step before".into(),
        TypeKind::AtomApply(..) => "the atom type of the step before".into(),
        TypeKind::Union(_) => "the union of the step before".into(),
        TypeKind::And(_) => "the intersection of the step before".into(),
        _ => "the difference of the step before".into(),
    };
    enum Work<'t> {
        /// Explain the parts of this type with no value that no explained part holds.
        Find(&'t Type),
        /// Explain why this type has no value, its causes first.
        Explain(&'t Type),
        Say(Note),
    }
    let mut stack = vec![Work::Find(t)];
    while let Some(w) = stack.pop() {
        let t = match w {
            Work::Say(n) => {
                built(1);
                out.push(n);
                continue;
            }
            Work::Find(t) => {
                let t = bare(t);
                let parts: Vec<&Type> = match &t.kind {
                    TypeKind::Tuple(_)
                    | TypeKind::AtomApply(..)
                    | TypeKind::Union(_)
                    | TypeKind::And(_)
                    | TypeKind::Diff(..)
                        if none(t) =>
                    {
                        stack.push(Work::Explain(t));
                        continue;
                    }
                    TypeKind::Name(_)
                    | TypeKind::Atom(_)
                    | TypeKind::Every(_)
                    | TypeKind::AtomAny(_) => Vec::new(),
                    TypeKind::Tuple(ts) | TypeKind::Union(ts) => ts.iter().collect(),
                    TypeKind::And(ts) => Type::and_operands(ts),
                    TypeKind::Diff(a, b) => vec![a, b],
                    TypeKind::Arrow { params, result, .. } => {
                        (params.iter().map(|p| &p.ty)).chain([&**result]).collect()
                    }
                    TypeKind::Bounded {
                        lower,
                        upper,
                        result,
                    } => vec![lower, upper, result],
                    TypeKind::Apply(_, ps) | TypeKind::AtomApply(_, ps) => {
                        ps.iter().map(|p| &p.ty).collect()
                    }
                    TypeKind::Record(fs) => fs.iter().map(|(_, t)| t).collect(),
                    TypeKind::Array(t) => vec![t],
                    TypeKind::For { .. } => unreachable!("`bare` takes off each `for` clause"),
                };
                stack.extend(parts.into_iter().rev().map(Work::Find));
                continue;
            }
            Work::Explain(t) => t,
        };
        // The step for `t`, then the steps for the parts it names as its causes that are
        // explained in turn, pushed reversed so that they pop first and in written order.
        let mut causes: Vec<&Type> = Vec::new();
        let why = match &t.kind {
            TypeKind::Tuple(ts) => {
                let (i, c) = (ts.iter().enumerate())
                    .find(|(_, c)| none(c))
                    .expect("a tuple type with no value has a component with none");
                causes.push(c);
                format!(
                    "this tuple type has no value, since its component {i}, {}, has none",
                    cause(c)
                )
            }
            TypeKind::AtomApply(a, ps) => {
                let (i, p) = (ps.iter().enumerate())
                    .find(|(_, p)| none(&p.ty))
                    .expect("an atom type with no value has a payload component with none");
                causes.push(&p.ty);
                let part = match &p.name {
                    Some(n) if !p.positional => format!("field `{n}`"),
                    _ => format!("component {i}"),
                };
                format!(
                    "this atom type `#{a}` has no value, since its payload's {part}, {}, has none",
                    cause(&p.ty)
                )
            }
            TypeKind::Union(ts) => {
                causes.extend(ts);
                "this union has no value, since none of its members has one".into()
            }
            TypeKind::And(ts) => {
                let ts = Type::and_operands(ts);
                match ts.iter().find(|c| none(c)) {
                    Some(c) => {
                        causes.push(c);
                        format!(
                            "this intersection has no value, since its operand, {}, has none",
                            cause(c)
                        )
                    }
                    None => {
                        let shown: Vec<String> = (ts.iter())
                            .map(|c| format!("`{}`", format_type(c)))
                            .collect();
                        format!(
                            "this intersection has no value, since no value is in all of {}",
                            and_list(&shown)
                        )
                    }
                }
            }
            TypeKind::Diff(a, _) if none(a) => {
                causes.push(a);
                format!(
                    "this difference has no value, since its left operand, {}, has none",
                    cause(a)
                )
            }
            TypeKind::Diff(a, b) => format!(
                "this difference has no value, since each value of `{}` is also in `{}`",
                format_type(a),
                format_type(b)
            ),
            _ => unreachable!("`Find` explains only a part written with parts"),
        };
        stack.push(Work::Say(Note {
            span: t.span,
            text: format!("{why}, so it is `Never`"),
        }));
        stack.extend(
            (causes.into_iter().rev())
                .map(bare)
                .filter(|c| !matches!(c.kind, TypeKind::Name(_)))
                .map(Work::Explain),
        );
    }
}

/// `items` joined as a list in a sentence: `a`, `a and b`, `a, b and c`.
fn and_list(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [one] => one.clone(),
        [rest @ .., last] => format!("{} and {last}", rest.join(", ")),
    }
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
    /// The span of each part read whose type lists no value, kept only by [`emptied`], which
    /// explains them in a message.
    empty: Option<HashSet<Span>>,
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

/// A step of [`Denote::ty`], on the stack it keeps: a written type nests as deep as the program,
/// so the walk keeps its own stack rather than the thread's.
enum Step<'a> {
    /// Denote this type, pushing its value or the steps that make it.
    Ty(&'a Type),
    /// Make the value of this type from the values of its parts, the last on the value stack.
    Make(&'a Type),
    /// Make the value of this intersection from the values of its operands, the given number
    /// last on the value stack, as one function's arrows if the flag says so.
    And(&'a Type, usize, bool),
    /// [`Denote::open_params`].
    Open,
    /// [`Denote::close_params`].
    Close,
    /// Restore what the variables of a `for` clause were bounded by around it.
    Unbind(Vec<(&'a str, Option<(u8, usize)>)>),
}

impl<'a> Denote<'a> {
    /// The type `t` denotes. The parts of each type are denoted in written order and each type
    /// is made after its parts, as a recursive walk would, on a stack of steps and a stack of
    /// values: the time is linear in the size of `t`, and the thread's stack does not grow with
    /// its depth.
    fn ty(&mut self, t: &'a Type) -> Ty {
        // Complexity tradeoff: the same order, at a constant factor in instructions. With
        // `Sig::facts`, `Sig::digest` and the drop of a signature, which keep stacks of their own
        // too (TY-write-stack), checking three function types written 64,000 deep took 54.1 G
        // instructions against 52.8 G recursive (+2.6%, perf stat, whole test, 2026-11-07).
        let mut steps = vec![Step::Ty(t)];
        let mut vals: Vec<Ty> = Vec::new();
        while let Some(step) = steps.pop() {
            match step {
                Step::Ty(t) => self.enter(t, &mut steps, &mut vals),
                Step::Make(t) => {
                    let v = self.make(t, &mut vals);
                    self.push(t, v, &mut vals);
                }
                Step::And(t, n, overload) => {
                    let ts = vals.split_off(vals.len() - n);
                    self.push(t, and(ts, overload), &mut vals);
                }
                Step::Open => self.open_params(),
                Step::Close => self.close_params(),
                Step::Unbind(outer) => {
                    for (v, was) in outer {
                        match was {
                            Some(was) => self.bound.insert(v, was),
                            None => self.bound.remove(v),
                        };
                    }
                }
            }
        }
        let t = vals.pop().expect("a type denotes one value");
        debug_assert!(vals.is_empty(), "each part's value is taken by its type");
        t
    }

    /// Pushes the value of `t` to `vals` if it has no parts, or else the steps that denote its
    /// parts and make it to `steps`, last step first.
    fn enter(&mut self, t: &'a Type, steps: &mut Vec<Step<'a>>, vals: &mut Vec<Ty>) {
        let leaf = match &t.kind {
            TypeKind::Apply(..) | TypeKind::Record(_) => {
                unreachable!(
                    "name resolution rejects every record type and every type applied to arguments before the checker reads the program"
                )
            }
            // Resolve rejects a written one until L2.5; the reader of printed types reads one,
            // since the checker builds atoms with payloads from L1 on (L29-print).
            TypeKind::AtomApply(_, ps) => {
                steps.push(Step::Make(t));
                steps.extend(ps.iter().rev().map(|p| Step::Ty(&p.ty)));
                return;
            }
            TypeKind::Array(_) => unreachable!(
                "name resolution rejects every array type before the checker reads the program"
            ),
            TypeKind::Name(n) if self.leaves.contains_key(n.as_str()) => {
                self.leaves[n.as_str()].clone()
            }
            TypeKind::Name(n) => match n.as_str() {
                "int" => Ty::carrier(Carrier::Int),
                "rat" => Ty::carrier(Carrier::Rat),
                "f64" => Ty::carrier(Carrier::F64),
                "bool" => Ty::carrier(Carrier::Bool),
                "String" => Ty::carrier(Carrier::Str),
                "Never" => Ty::empty(),
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
            TypeKind::Tuple(ts) | TypeKind::Union(ts) => {
                steps.push(Step::Make(t));
                steps.extend(ts.iter().rev().map(Step::Ty));
                return;
            }
            // Function types that share a parameter list are one function's arrows, in written
            // order, an intersection in parentheses among them included; resolve rejects
            // function types that do not. Each operand is denoted once, so the arrows are
            // gathered in one list.
            TypeKind::And(ts) => {
                let ts = Type::and_operands(ts);
                steps.push(Step::And(t, ts.len(), Type::overload(&ts) == Ok(true)));
                steps.extend(ts.into_iter().rev().map(Step::Ty));
                return;
            }
            TypeKind::Diff(a, b) => {
                steps.extend([Step::Make(t), Step::Ty(b), Step::Ty(a)]);
                return;
            }
            TypeKind::Arrow { params, result, .. } => {
                steps.extend([Step::Make(t), Step::Ty(result), Step::Close]);
                steps.extend(params.iter().rev().map(|p| Step::Ty(&p.ty)));
                steps.push(Step::Open);
                return;
            }
            // Each variable is bounded on the outermost signature that names it, which resolve
            // found to hold its every use: a call of that function binds it to one carrier of
            // the bound (DESIGN.md sec:type_language, sec:type_resolution).
            TypeKind::For { ty, bounds } => {
                let depth = self.open.len();
                let outer = bounds
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
                steps.extend([Step::Unbind(outer), Step::Ty(ty)]);
                return;
            }
            TypeKind::Bounded {
                lower,
                upper,
                result,
            } => {
                steps.extend([
                    Step::Make(t),
                    Step::Ty(result),
                    Step::Close,
                    Step::Ty(upper),
                    Step::Ty(lower),
                    Step::Open,
                ]);
                return;
            }
        };
        self.push(t, leaf, vals);
    }

    /// Pushes `v`, the value of `t`, to `vals`, noting `t` if it is kept and `v` lists no value.
    fn push(&mut self, t: &Type, v: Ty, vals: &mut Vec<Ty>) {
        if let Some(empty) = &mut self.empty
            && v.lists_nothing()
        {
            empty.insert(t.span);
        }
        vals.push(v);
    }

    /// The value of `t`, a type with parts, made from the values of its parts, which are the
    /// last on `vals` and are taken from it.
    fn make(&mut self, t: &'a Type, vals: &mut Vec<Ty>) -> Ty {
        match &t.kind {
            TypeKind::AtomApply(a, ps) => {
                let (mut items, mut fields) = (Vec::new(), BTreeMap::new());
                for (p, v) in ps.iter().zip(vals.drain(vals.len() - ps.len()..)) {
                    match &p.name {
                        Some(n) if !p.positional => {
                            fields.insert(n.as_str().into(), v);
                        }
                        _ => items.push(v),
                    }
                }
                Ty::atom_of(a, items, fields)
            }
            TypeKind::Tuple(ts) => Ty::tuple(vals.split_off(vals.len() - ts.len())),
            TypeKind::Union(ts) => {
                let from = vals.len() - ts.len();
                let t = Ty::union_all(&vals[from..]);
                vals.truncate(from);
                t
            }
            TypeKind::Diff(..) => {
                let b = vals.pop().expect("a difference's operands are denoted");
                let a = vals.pop().expect("a difference's operands are denoted");
                a.diff(&b)
            }
            // A partial map `K ->? V` promises no key, so a lookup is `V | #notFound`
            // (DESIGN.md sec:type_language); this checker keeps one domain per function, so
            // that is the result of its arrow.
            TypeKind::Arrow {
                params, partial, ..
            } => {
                let mut result = vals.pop().expect("a function type's result is denoted");
                if *partial {
                    result = result.union(&Ty::set(KType::atom("notFound")));
                }
                let tys = vals.split_off(vals.len() - params.len());
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
            // A morphism `L .. U -> V` answers `V` on a key of its guarantee `L`, and only
            // `V | #notFound` on a key of its permission `U` (DESIGN.md sec:type_language, lookup
            // typing). This checker keeps one domain per arrow, so it is the arrow `(L) -> V`
            // and then `(U) -> V | #notFound`: rule 6 takes the first for a key within `L`. With
            // an empty guarantee only the second is left, which is `U ->? V`; with the guarantee
            // equal to the permission only the first, which is `U -> V`.
            TypeKind::Bounded { .. } => {
                let result = vals.pop().expect("a bounded function's result is denoted");
                let upper = vals
                    .pop()
                    .expect("a bounded function's permission is denoted");
                let lower = vals
                    .pop()
                    .expect("a bounded function's guarantee is denoted");
                let names = vec![SParam {
                    name: String::new().into(),
                    positional: true,
                    default: None,
                }];
                let missed = result.union(&Ty::set(KType::atom("notFound")));
                let arrows = if lower == upper {
                    vec![Arrow {
                        params: vec![upper],
                        result,
                    }]
                } else if lower == Ty::empty() {
                    vec![Arrow {
                        params: vec![upper],
                        result: missed,
                    }]
                } else {
                    vec![
                        Arrow {
                            params: vec![lower],
                            result,
                        },
                        Arrow {
                            params: vec![upper],
                            result: missed,
                        },
                    ]
                };
                self.sig_of(names, arrows)
            }
            _ => unreachable!("only a type with parts is made from them"),
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
        self.sig_of(
            names,
            vec![Arrow {
                params: tys,
                result,
            }],
        )
    }

    /// [`Self::sig`], of the arrows `arrows`, each with a type for each of `names`.
    fn sig_of(&mut self, names: Vec<SParam>, arrows: Vec<Arrow>) -> Ty {
        let open = self.open.pop().expect("each function type is opened first");
        let mut arrows = arrows.into_iter();
        let first = arrows.next().expect("a function type has an arrow");
        let mut sig = Sig::one(names, first.params, first.result);
        sig.arrows.extend(arrows);
        sig.own.extend(open.bounds.keys().cloned());
        sig.bounds = open.bounds;
        sig.held = open.held;
        Ty::func(Arc::new(sig))
    }
}

/// The value of an intersection of the types `ts`, its operands in written order: one function
/// with each operand's arrows if `overload` says they share a parameter list ([`Type::overload`]),
/// and otherwise their meet.
fn and(ts: Vec<Ty>, overload: bool) -> Ty {
    if overload {
        let mut sigs = ts.into_iter().map(|mut t| {
            let s = t.fns.pop().expect("a function type denotes one signature");
            Arc::unwrap_or_clone(s)
        });
        let mut sig = sigs.next().expect("an intersection has operands");
        for mut s in sigs {
            sig.arrows.append(&mut s.arrows);
            sig.bounds.append(&mut s.bounds);
            sig.own.append(&mut s.own);
            sig.held.append(&mut s.held);
        }
        return Ty::func(Arc::new(sig));
    }
    // An intersection of function types of one arity is one function with each of their
    // arrows, in order, as a signature of several arrows prints.
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

/// `t` with its tuple shapes of each length joined into one, position by position, and so on
/// down through the components: the type of `min` or `max` of two tuples.
// Complexity tradeoff: the union of the shapes keeps which components go together, but a chain
// `a(i) = min(a(i - 1), (i, 0.5, i))` then holds i shapes at step i and checking it is O(n^2):
// 100 and 800 links allocated 36.9 MB and 1966.5 MB, 53.4 times (2026-11-07). Joined, each
// result has one shape per length and the chain is linear; what is lost is only which
// components went together, which `min` and `max` of numbers and tuples never test.
//
// The types are joined after their components, on a stack of their own, since a tuple type
// nests as deep as the program; and each distinct type once, kept in `done` by its value, since
// the components of a type share their parts, and `t(k + 1) = (t(k), t(k))` joined part by part
// would cost 2^k.
fn one_shape_per_length(t: &Ty) -> Ty {
    enum Step {
        /// Join this type: its components first.
        Enter(Ty),
        /// Join this type from the joins of its components, the last on `out`: one shape for
        /// each of these lengths, in order.
        Exit(Ty, Vec<usize>),
    }
    let mut done: HashMap<Ty, Ty> = HashMap::new();
    let mut out: Vec<Ty> = Vec::new();
    let mut stack = vec![Step::Enter(t.clone())];
    while let Some(step) = stack.pop() {
        match step {
            Step::Enter(t) if t.tuples.is_empty() => out.push(t),
            Step::Enter(t) => {
                if let Some(joined) = done.get(&t) {
                    out.push(joined.clone());
                    continue;
                }
                let mut by_len: BTreeMap<usize, Vec<&[Ty]>> = BTreeMap::new();
                for row in &t.tuples {
                    by_len.entry(row.len()).or_default().push(row);
                }
                let lens: Vec<usize> = by_len.keys().copied().collect();
                // The union at each position of the shapes of each length, in order, so that
                // their joins are on `out` in order when `t` is joined.
                let parts: Vec<Ty> = by_len
                    .into_values()
                    .flat_map(|rows| {
                        (0..rows[0].len()).map(move |i| Ty::union_all(rows.iter().map(|r| &r[i])))
                    })
                    .collect();
                stack.push(Step::Exit(t, lens));
                stack.extend(parts.into_iter().rev().map(Step::Enter));
            }
            Step::Exit(mut t, lens) => {
                let mut parts = out
                    .split_off(out.len() - lens.iter().sum::<usize>())
                    .into_iter();
                let rows: Vec<Ty> = (lens.iter())
                    .map(|&n| Ty::tuple(parts.by_ref().take(n).collect()))
                    .collect();
                let tuples = std::mem::take(&mut t.tuples);
                let joined = t.union(&Ty::union_all(&rows));
                t.tuples = tuples;
                out.push(joined.clone());
                done.insert(t, joined);
            }
        }
    }
    out.pop().expect("the type is joined")
}

/// The message that `what` takes none of the argument types `shown`: `why` is the cause when
/// one is known, and with none, the message says that no arrow of `what` takes them all,
/// which the derivation then shows arrow by arrow.
pub(crate) fn does_not_take(what: &str, shown: &str, why: &str) -> String {
    match why.is_empty() {
        true => format!(
            "{what} does not take ({shown}): these are the types of its arguments here, and \
             {what} has no arrow that takes them all"
        ),
        false => format!("{what} does not take ({shown}){why}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span(start: usize) -> Span {
        Span {
            start,
            end: start + 1,
        }
    }

    /// A branch the checker rolls back, as [`Ck::try_outside`] and [`Ck::repairs`] roll back a
    /// trial, leaves [`Info::passes`] as it found it (PASS-at-args): a call whose entry held
    /// fewer arguments before the branch keeps exactly those, with their atoms, including
    /// those the branch did not write, and a call first recorded in the branch has no entry
    /// after it.
    #[test]
    fn a_rolled_back_branch_restores_the_passed_atoms() {
        let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
        let t = Tables::new(&[], &res);
        let mut ck = Ck::new(&t);
        let (a, b, c) = (KType::atom("a"), KType::atom("b"), KType::atom("c"));
        let (call, other, fresh) = (span(100), span(200), span(300));
        ck.pass_at(call, span(1), &a);
        ck.pass_at(call, span(3), &c);
        ck.pass_at(other, span(11), &b);
        let before = ck.info.passes.clone();
        let saved = ck.mark();
        // The call's entry grows: one argument gains an atom, another is new; the same
        // argument written twice logs twice and must come back to its first value.
        ck.pass_at(call, span(1), &b);
        ck.pass_at(call, span(2), &c);
        ck.pass_at(call, span(2), &a);
        // A write that adds nothing logs nothing.
        let len = ck.log.len();
        ck.pass_at(other, span(11), &b);
        assert_eq!(ck.log.len(), len);
        // A call first recorded in the branch.
        ck.pass_at(fresh, span(21), &a);
        ck.pass_at(fresh, span(22), &b);
        assert_eq!(ck.info.passes[&call].len(), 3);
        assert_eq!(ck.info.passes[&call][&span(1)], &a | &b);
        ck.undo(&saved);
        assert_eq!(ck.info.passes, before);
        assert_eq!(ck.info.passes[&call].len(), 2);
        assert_eq!(ck.info.passes[&call][&span(1)], a);
        assert_eq!(ck.info.passes[&call][&span(3)], c);
        assert!(!ck.info.passes.contains_key(&fresh));
        // Rolling back to before the first write leaves no entry at all.
        ck.undo(&Mark { log: 0, errors: 0 });
        assert!(ck.info.passes.is_empty());
    }

    /// The tuple type `(... ((leaf, 1), 2) ..., depth)`.
    fn nested(leaf: Ty, depth: usize) -> Ty {
        (1..=depth).fold(leaf, |t, k| {
            Ty::tuple(vec![t, Ty::lit(&Value::int(k.into()))])
        })
    }

    /// Its hash, which is read from the digests of its rows, so two types nested deep are
    /// compared without walking them.
    fn digest(t: &Ty) -> u64 {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        BuildHasherDefault::<DefaultHasher>::default().hash_one(t)
    }

    /// The type of `min` of two tuples nested 200,000 deep, one with an `int` at the bottom and
    /// one with an `f64`, is joined at every level on the 8 MiB stack of a main thread: one
    /// shape per level, `int | f64` at the bottom. Joined by recursion, once per level, it
    /// overflowed that stack.
    #[test]
    fn one_shape_per_length_joins_a_tuple_nested_deep_on_a_main_sized_stack() {
        const DEPTH: usize = 20_000;
        let (int, f64) = (Ty::carrier(Carrier::Int), Ty::carrier(Carrier::F64));
        let both = nested(int.clone(), DEPTH).union(&nested(f64.clone(), DEPTH));
        assert_eq!(both.tuples.len(), 2);
        let want = digest(&nested(int.union(&f64), DEPTH));
        let joined = std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn(move || {
                let joined = one_shape_per_length(&both);
                (joined.tuples.len(), digest(&joined))
            })
            .expect("starting the thread")
            .join()
            .expect("joining on an 8 MiB stack");
        assert_eq!(joined, (1, want));
    }

    /// The steps `emptied` gives for the written type `text`, each with the text it is placed
    /// at.
    fn why_none(text: &str) -> Vec<(String, String)> {
        let tokens = zedc_syntax::lex::lex(text).expect("lexing a type");
        let tree = zedc_syntax::parse::parse(text, &tokens, "Type", zedc_syntax::parse::TOP)
            .expect("parsing a type");
        let t = zedc_syntax::ast::ty(text, &tokens, &tree).expect("reading a type");
        let mut out = Vec::new();
        emptied(&t, &mut out);
        (out.into_iter())
            .map(|n| (text[n.span.start..n.span.end].to_string(), n.text))
            .collect()
    }

    /// An atom with a payload, which layer L1 programs cannot write yet, names the payload
    /// part with no value by its position or its field name.
    #[test]
    fn an_atom_with_an_empty_payload_names_the_part() {
        let pair = |s: &str, w: &str| (s.to_string(), w.to_string());
        assert_eq!(
            why_none("#a(Never, int)"),
            [pair(
                "#a(Never, int)",
                "this atom type `#a` has no value, since its payload's component 0, `Never`, \
                 has none, so it is `Never`"
            )]
        );
        assert_eq!(
            why_none("#a(x: int, y: (bool, Never))"),
            [
                pair(
                    "(bool, Never)",
                    "this tuple type has no value, since its component 1, `Never`, has none, so \
                     it is `Never`"
                ),
                pair(
                    "#a(x: int, y: (bool, Never))",
                    "this atom type `#a` has no value, since its payload's field `y`, the tuple \
                     type of the step before, has none, so it is `Never`"
                ),
            ]
        );
    }

    /// A `for` clause has the value of the type it bounds, so it is explained there; a type
    /// with values gets no step.
    #[test]
    fn a_for_clause_is_explained_at_the_type_it_bounds() {
        assert_eq!(
            why_none("(a, Never) for a in int"),
            [(
                "(a, Never)".to_string(),
                "this tuple type has no value, since its component 1, `Never`, has none, so it \
                 is `Never`"
                    .to_string()
            )]
        );
        assert_eq!(why_none("(a, (int, bool)) for a in int | f64"), []);
    }
}

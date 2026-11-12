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
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;

use zed_kernel::num::{TooLarge, literal_f64};
use zed_kernel::types::{Spell, Spelled, Type as KType, Universes, Verdict, defs};
use zed_kernel::{Prim, Rat, Term, Universe, Value, eval};

use zedc_base::rejection::Row;
use zedc_int::int::Int;
use zedc_lattice::interval::{
    End::{self, Fin, NegInf, PosInf},
    IntervalSet, Num, bit_word,
};
use zedc_lattice::revision::{Op, forward};
use zedc_preimage::images;
use zedc_preimage::product::{Kept, Refused};
use zedc_resolve::resolve::tables::Tables;
use zedc_resolve::resolve::{Handle, Ref, Resolution};
use zedc_syntax::ast::{
    BinaryOp, Error, Every, Expr, ExprKind, Function, Note, Param, Pattern, Stmt, StmtKind,
    StrPart, Target, Type, TypeKind, UnaryOp, shown,
};
use zedc_syntax::format::format_type;
use zedc_syntax::lex::{Span, Tok, lex, unread_literal};

use kernel_type::kernel_type;
use ty::{
    Arrow, Binds, Carrier, EVERY, IntDomain, Names, Narrow, Need, NeedKind, NodeId, OTHER, Piece,
    PowerUse, SParam, Shape, Sig, Slot, Ty, VarFacts, Vars, Via, Width, atoms, carriers_text,
    class_id, errs, fresh_name, mask_text,
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
    /// A call whose type lists numeric literal values alone, as `g(c)` with `g(positional c:
    /// bool) = if c { 2 } else { 1 }`, at a parameter of the one numeric carrier recorded:
    /// each value is read at that carrier, and every one of them is exactly a value of it
    /// (L1.26a: "`z: f64 = g(c)` read both branches at `f64`"). Elaboration casts the call's
    /// value to the carrier, which the check proved exact for each value the call can give.
    Read(Carrier),
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

/// The warning for `r`, a question the integer solver left undecided, asked at `span`, with
/// the sets `kept` it left its variables: its headline, and each step of its derivation and
/// each repair as a note at `span`. The question is printed as the program wrote it, with no
/// position of its own, so every note points at the test or read that asked it.
fn refused_warning(span: Span, r: &Refused, kept: &Kept) -> Error {
    let w = r.warning(kept);
    Error {
        span,
        message: w.message,
        notes: (w.steps.into_iter())
            .map(|text| Note { span, text })
            .collect(),
        menu: String::new(),
        row: None,
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
    /// generic literal operand of an operator in such a class (L1.26a), by its span: the
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
    /// Each read `v[k]` whose receiver is a family, by the read's span: whether every
    /// function the receiver may be is a family whose keys are one integer interval, every key
    /// present ([`Sig::dense`]), so that a miss there is `#outOfBounds` (DESIGN.md
    /// sec:type_language, the `m[k]` row). A read checked more than once is such a read only
    /// if it is one each time.
    pub dense: HashMap<Span, bool>,
    /// The type errors.
    pub errors: Vec<Error>,
    /// A warning for each question the integer solver left undecided while the checker
    /// narrowed by a test or read under one, placed at that test or read, with its derivation:
    /// in order of place, then of the question (DESIGN.md L1.39).
    pub warnings: Vec<Error>,
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
}

/// A numeric literal: its span, without a `-`, which keys what it adopts; its site, the span
/// of the literal with its `-`, where every message about it points, and which is longer than
/// the span exactly when a `-` is applied to it ([`Lit::neg`]); its value, its text, without
/// the `-`, whether it is written without a suffix, whether it is generic (step L1.26a):
/// written without a suffix where it joins a class other than under `==` and `!=`, and whether, generic,
/// it has no other operand to take its carrier from at run time and takes it from a parameter
/// of its class ([`Info::witness`]). Where it joins no class, it keeps its own carrier.
#[derive(Clone)]
struct Lit {
    span: Span,
    site: Span,
    value: Value,
    /// The literal as the lexer reads it, without the `_` that separate its digits, from which
    /// its value is read; made in memory asked for first ([`shown`]) and shared by every copy
    /// of the literal, so a clone copies none of its digits.
    text: Rc<String>,
    /// The literal as the program's text writes it, where that differs from `text`: where it
    /// separates its digits with `_`, as `1_000.5`. A message quotes this ([`Lit::spelling`]);
    /// `None` where the two are the same or the program's text is not known.
    // Complexity tradeoff: a copy of the literal's text, O(its length), made only for a
    // literal with a `_`, the one case where `text` cannot stand for it. Keeping the span
    // alone and reading the program's text when printing copies nothing, but needs the text
    // at each of the many places a message about a literal is written, most of which are
    // given the literal alone.
    spelled: Option<Rc<String>>,
    bare: bool,
    generic: bool,
    witness: bool,
}

impl Lit {
    /// The literal as it joins a class with no other operand: generic, taking its carrier
    /// from a parameter of the class, if it is written without a suffix.
    fn joining(&self) -> Lit {
        Lit {
            generic: self.bare,
            witness: self.bare,
            ..self.clone()
        }
    }

    /// Whether a `-` is applied to the literal.
    fn neg(&self) -> bool {
        self.site != self.span
    }

    /// The literal as the program's text writes it, without its `-`: `1_000.5`, `0xF_F`.
    fn spelling(&self) -> &str {
        self.spelled.as_deref().unwrap_or(&self.text)
    }

    /// The literal as the program writes it, with its `-`, written from the shared text when
    /// displayed, so it copies none of the digits.
    fn written(&self) -> impl fmt::Display + '_ {
        let sign = if self.neg() { "-" } else { "" };
        fmt::from_fn(move |f| write!(f, "{sign}{}", self.spelling()))
    }
}

/// Which arguments an application needs the values of. Evaluation is neither strict nor lazy
/// (DESIGN.md sec:non_goals), so an argument with no value, of type `Never`, leaves the call
/// with no value only where the call needs that argument's value; elsewhere the call has the
/// result its arrow gives.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Demand {
    /// Every argument, as an operator, a prelude word or a lookup in a family needs.
    All,
    /// The first: `&&` and `||` read the second operand only where the first does not decide.
    First,
    /// What the function's body reads: its substituted result says where an argument with no
    /// value reaches it, as `(x, 1)` does and `y` in `k(x, y) = y` does not.
    Body,
}

impl Demand {
    /// Whether the argument at `i` is needed for the call to give a value.
    fn needs(self, i: usize) -> bool {
        match self {
            Demand::All => true,
            Demand::First => i == 0,
            Demand::Body => false,
        }
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
    parts: Option<Rc<[Part<'a>]>>,
    /// The literals the argument's value comes from, when it is an `if` whose every branch,
    /// at any depth of `if`, is a numeric literal or an operation on literals alone that
    /// keeps its value there, as `if c { 2 } else { 1 }` or `if c { 2 + 1 } else { 1 }`:
    /// each is fixed where the argument is used as it would be alone (L1.26a).
    branches: Option<Rc<[Branch<'a>]>>,
}

/// A branch of an `if` of [`Arg::branches`].
#[derive(Clone)]
enum Branch<'a> {
    Lit(Lit),
    /// An operation on integer literals alone with no `/`, as `2 + 1`, which keeps its value
    /// in the `if` ([`Ck::kept`]): the operation, its value as an `int`, its literals, and the
    /// class of literals it makes, which nothing else joins. Where the `if` meets a class,
    /// the class merges with it, as the operation alone would; at a declared carrier the
    /// operation takes that carrier, as it would alone.
    Op {
        e: &'a Expr,
        value: Value,
        lits: Rc<[Lit]>,
        class: usize,
    },
}

impl Branch<'_> {
    /// The value the branch has where nothing fixes its carrier.
    fn value(&self) -> &Value {
        match self {
            Branch::Lit(l) => &l.value,
            Branch::Op { value, .. } => value,
        }
    }
}

impl<'a> Arg<'a> {
    fn of(ty: Ty) -> Arg<'a> {
        Arg {
            ty,
            lit: None,
            at: None,
            expr: None,
            parts: None,
            branches: None,
        }
    }
}

/// A construct being checked ([`Ck::written`]): what it applies, its arguments as the program
/// writes them, before the check reads them at a carrier, and its span.
struct Written<'a> {
    form: Construct<'a>,
    args: Vec<Option<Arg<'a>>>,
    span: Span,
}

/// A fix, by what it writes, of the rejection [`Found::id`] in the construct being checked
/// ([`Ck::fixes_checked`], [`Ck::repairs`]), whose check as written gave the construct the
/// type `ty` and added errors only at `needs`, each inside an argument the fix does not edit,
/// as `f(1, 1.0f64)` for `f(1.0f64, 1.0f64)` with `int` parameters: the fix is kept where the
/// construct's own check rejects each of `needs` too, apart from the rejection the fix is
/// for, and dropped where it does not. A fix kept whose `ty` is not the type the construct's
/// own check gives is checked again in the construct the first one is an argument of
/// ([`Ck::carried`]), as `1.0r` in `min(1.0r, 0.5r) + 2.5f64`, which is then dropped.
struct Pending {
    id: usize,
    offer: Offer,
    needs: Vec<Span>,
    ty: Ty,
}

/// The fixes kept in a construct that give it the type `ty` in place of the type its own check
/// gives ([`Ck::carried`]), checked together in the construct around it: they give it the
/// same argument, so one check settles them all.
struct Carry {
    ty: Ty,
    fixes: Vec<Pending>,
}

/// What a [`Pending`] fix writes: the edits of a fix of a menu ([`Ck::fixes_checked`]), or a
/// note that writes a repair ([`Ck::repairs`]), by its span and text, as the note that writes
/// `0.5` for `0.5r`.
#[derive(PartialEq)]
enum Offer {
    Edits(Vec<(Span, String)>),
    Note(Span, String),
}

/// What a construct of [`Written`] applies: a binary operator other than `&&` and `||`, with
/// its second operand as written, a prelude word applied to one argument, or a function,
/// named as a message names it, called with its arguments in the order of its parameters.
#[derive(Clone)]
enum Construct<'a> {
    Binary(BinaryOp, &'a Expr),
    Word(&'a str),
    Call(Rc<str>, Arc<Sig>),
}

impl Construct<'_> {
    /// The name of what it applies as an application names it: `` `+` `` or `` `int` ``.
    fn what(&self) -> String {
        match self {
            Construct::Binary(op, _) => format!("`{op}`"),
            Construct::Word(w) => format!("`{w}`"),
            Construct::Call(what, _) => what.to_string(),
        }
    }
}

/// What a fix writes in a construct's arguments ([`Ck::fix_args`]): the arguments it gives,
/// one whose application fails where the fix writes it, as `int(0.5)`, or text the checker
/// does not read alone, so the fix is not checked here.
enum Mapped<'a> {
    Args(Vec<Option<Arg<'a>>>),
    Fails,
    Unread,
}

/// The text of `src` in `at` with each edit of `edits`, which lie in `at` apart and in the
/// order of the text, written in place of its span; `None` where a span is not in `src` or
/// the system refuses the memory. It costs the length of `at` and of the edits.
fn edited(src: &str, at: Span, edits: &[&(Span, String)]) -> Option<String> {
    let mut parts = Vec::with_capacity(2 * edits.len() + 1);
    let mut i = at.start;
    for (s, with) in edits {
        parts.push(src.get(i..s.start)?);
        parts.push(with.as_str());
        i = s.end;
    }
    parts.push(src.get(i..at.end)?);
    shown(&fmt::from_fn(|f| {
        parts.iter().try_for_each(|p| f.write_str(p))
    }))
    .ok()
}

/// A component of a tuple argument as written: a numeric literal, an `if` of literals, a
/// tuple holding one of them at some depth, or anything else. A literal in a tuple adopts the
/// carrier the type its tuple meets gives its component, as a literal argument adopts its
/// parameter's, and so does each branch of an `if` of literals there, as the branches of an
/// argument do ([`Arg::branches`]): `(if c { 2 + 1 } else { 1 }, 1)` at `(f64, f64)` is
/// `(3.0 | 1.0, 1.0)`.
#[derive(Clone)]
enum Part<'a> {
    Lit(Lit),
    Branches(Rc<[Branch<'a>]>),
    Tuple(Rc<[Part<'a>]>),
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
// Complexity tradeoff (COMPLEXITY.md row IS-chain-quad): naive version, `a` then `b` copied
// into a new list at each join, and each level of a chain narrowing every fact again, O(k^2)
// for a chain of k sides in time and bytes. Used: small onto large, O(k log k) for any tree of
// joins, with the narrowing a side left in place handed on (`Ck::narrow_side`). Tradeoff: a
// `VecDeque` in place of a `Vec`, so that the shorter list can go on either end.
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
// Complexity tradeoff (COMPLEXITY.md row F80): naive version, each origin, class reason and
// call note put into words when recorded, O(size of the type printed) per binder and per call
// whether or not an error is reported (a repair trial built the derivation of each error it
// dropped). Used: data recorded in O(1), words only when a reported rejection's derivation
// reaches it, at the cost of what it walks. Tradeoff: the data holds its types and signatures
// alive until the check ends.
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
fn show_with(t: &Ty, masks: &Masks, spell: Spell<'_>) -> String {
    if masks.is_empty() {
        return t.text_spelled(false, spell);
    }
    // One union, printed in the order of a union (`order::cmp`, DESIGN.md sec:diagnostics), so
    // that the carriers stand among the other members as in a type written with them.
    let mut rest = t.clone();
    let mut narrowed = 0;
    for (v, m) in masks {
        narrowed |= m;
        rest.vars.remove(v);
    }
    rest.union(&Ty::of_mask(narrowed))
        .text_spelled(false, spell)
}

/// Where a repair note that writes types in code says to declare the definitions those
/// types use ([`lay_out`]): a Unicode noncharacter, which no user text in a message holds
/// (see `zed_kernel::types::defs`).
const DECLARE: &str = "\u{FDD8}";

/// Writes the types of one message, its text, its notes and its menu, in one numbering, in
/// the order they are printed: each part written more than once gets one definition, named
/// `T1`, `T2`, … with no name the program binds or the message writes ([`fresh_name`]), and
/// the definitions stand after the sentence on lines of their own (module `defs` of the
/// kernel), before the notes. A repair note whose code names one says, where it
/// wrote [`DECLARE`], to declare them at the top level; elsewhere [`DECLARE`] is dropped. A
/// message with no part written twice is as it was.
fn lay_out(message: &mut String, notes: &mut [Note], menu: &mut String) {
    let mut texts: Vec<&mut String> = std::iter::once(&mut *message)
        .chain(notes.iter_mut().map(|n| &mut n.text))
        .chain(std::iter::once(menu))
        .collect();
    let (lifted, holding) = defs::lift_holding(&mut texts, true, &|_| false);
    // Whether each note names a definition: the texts are the message, the notes, the menu.
    let code: Vec<bool> = holding[1..=notes.len()].to_vec();
    let these = match lifted.len() {
        1 => "the declaration above",
        _ => "the declarations above",
    };
    for (n, code) in notes.iter_mut().zip(code) {
        if n.text.contains(DECLARE) {
            let declare = format!(
                ", with {these} written first at the top level of the file, before the function"
            );
            n.text = n.text.replace(DECLARE, if code { &declare } else { "" });
        }
    }
    defs::under(message, &lifted);
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
///
/// Complexity tradeoff: naive version, the search over signatures, contexts and combinations
/// of carriers it replaced (COMPLEXITY.md F6, F18), exponential in the parameters and nesting
/// and stopped by caps. Used: a union-find by rank, each class merged or narrowed at most
/// (values + 6 × classes) times, O(log N) a step, O(N log N) in all; the lists of a merged
/// pair move shorter into longer ([`Ck::merge`]). Tradeoffs: no path compression, so a find
/// is O(log N), not nearly O(1); a tried repair undoes its changes from a log of the roots it
/// touched ([`Ck::touch`]), which compression would extend to every node on a path.
/// COMPLEXITY.md row "undeclared parameters (check), `apply`".
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
    // Complexity tradeoff (COMPLEXITY.md row F90): naive version, a scan of `uses` for each
    // new use, O(n) a use and O(n^2) for n uses of one class (a parameter destructured into n
    // names). Used: a hash map by kind, O(1) a use plus hashing the kind; classes merge the
    // smaller map into the larger. Tradeoff: one entry per distinct use beside `uses`.
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
    /// Whether its values are those of generic literals only, as of `1 + 1` inside a function: of a merged
    /// class, whether both were. An `if` merges it with the class of its other branch.
    generic: bool,
    /// Whether a use asked it for a carrier, as the bounded variable of an operator or of a
    /// function does: its values are then any of the carrier it takes, which the use may
    /// compute, not only the literals that joined it ([`Ck::resolve_top_parts`]). A literal's
    /// own join does not ask. Of a merged class, whether either was.
    asked: bool,
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
    /// The errors found so far, in the order found, each with its fixes not yet written; they
    /// are written into `info`'s errors when the check ends ([`Self::finish`]).
    errors: Vec<Found>,
    /// Each write to `info`'s maps, and to a class while a repair is tried, with the value
    /// it replaced, so that a repair is undone by what it wrote.
    // Complexity tradeoff (COMPLEXITY.md F6): the naive way to try a repair is to clone
    // `info` and restore the clone, O(size of the unit's findings) per try; the log makes a
    // try cost what it writes, at one entry of memory per write until the try is kept or
    // undone.
    log: Vec<Undo>,
    /// Each expression's type, by its span, as last found.
    seen: HashMap<Span, Seen<'a>>,
    /// Each bare literal written as an operand of `==` or `!=`, by its site: the operator, the
    /// span of the other operand, and whether the literal is the left one. A literal that a
    /// class of strings or `bool` follows is rejected when the class takes its type
    /// ([`Ck::never_equal`]); the entry only names the comparison, so an entry a repair's
    /// trial wrote is harmless.
    eq_sides: HashMap<Span, (BinaryOp, Option<Span>, bool)>,
    /// The span of each operation on bare literals alone, as `1 + 2`, `7 / 2`, `2 ^ 3` or
    /// `(1 + 2) * 3`: at the top level it is typed as it is walked, `int` where its arrows take
    /// one, and where it then meets an operand of one other numeric carrier, the carrier
    /// reaches each of its literals ([`Ck::lit_op_meets`]). Which operations are such is read
    /// off the text alone, so an entry a repair's trial wrote is harmless.
    lit_ops: HashSet<Span>,
    /// The operations of [`Ck::lit_ops`] whose value has no type in the program until it
    /// meets a carrier: those holding a `/`, which has no arrow at `int`, or a decimal literal
    /// with no suffix, which is never an `int`, as `1 / 2`, `(1 + 2) / (3 + 4)` and
    /// `0.5 * 2`, and the operations in those, as `1 + 2` there ([`Ck::lit_open_within`]).
    /// The type the walk found for one is the arrow kept after its rejection, an `int` the
    /// operation has only where nothing at all gives it a carrier, or no value, and not the
    /// type the program gives it there, so a step of a derivation names none for it
    /// ([`Ck::derive_into`]). An operation that takes a carrier leaves the set
    /// ([`Ck::lit_takes`]).
    lit_open: HashSet<Span>,
    /// Each operation on integer literals alone that is a branch of an `if` and keeps its
    /// value there ([`Ck::kept`]), by its span: the class of literals it makes. Written when
    /// the `if` is typed, just before the `if`, as an argument, reads it (`branch_lits` in
    /// `walk.rs`), so an entry a repair's trial or an earlier check of the function wrote is
    /// replaced before it is read again.
    kept_ops: HashMap<Span, usize>,
    /// The errors that each operation of [`Ck::lit_ops`] at the top level wrote as it was
    /// walked, by its span, as a range of indices into the errors: a `/` of integer literals
    /// is rejected there, as `7 / 2`, since no arrow of `/` takes `int`, and so is a negative
    /// exponent of the `int` power, `2 ^ -1`. They stand only where nothing gives the
    /// operation a carrier; where it meets one they move to [`Ck::lit_dropped`]
    /// ([`Ck::lit_op_meets`]). The entries last one statement ([`Ck::drop_met`]).
    lit_written: HashMap<Span, std::ops::Range<usize>>,
    /// The spans of [`Ck::lit_written`] in the order they were written, so that the ranges
    /// of a statement, which come after those of the statements around it, are the last.
    lit_order: Vec<Span>,
    /// The ranges of [`Ck::lit_written`] of operations that met a carrier, start to end,
    /// whose errors [`Ck::drop_met`] removes when the statement ends.
    lit_dropped: BTreeMap<usize, usize>,
    /// The `==` or `!=` whose operands are being paired, so that a literal component of a
    /// tuple compared with a component that holds no number names the comparison
    /// ([`Ck::never_equal_component`]), and two values with no common carrier are rejected
    /// at it ([`Ck::apart`]).
    comparing: Option<Comparison<'a>>,
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
    /// The expressions whose value is the result of `main`, its exit status ([`Ck::main_tails`]).
    main_tails: HashSet<Span>,
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
    /// The construct being checked, with its arguments as written, whose rejections' fixes
    /// are checked by checking it again with each fix in place ([`Ck::fixes_checked`]);
    /// `None` outside one and while a repair is tried.
    written: Option<Rc<Written<'a>>>,
    /// What checks the fixes of each rejection as written ([`Self::reject`]): the walk's
    /// [`Ck::fixes_checked`], which checks the construct being checked again with each fix in
    /// place. It is given as a value by whoever makes the check ([`Ck::new`]), since that
    /// check is code of `walk.rs`, which imports this file, and a call from here would make
    /// the two files import each other.
    check_fixes: fn(&mut Ck<'t, 'a>, Span, &mut Msg),
    /// The fixes kept for rejections in the constructs being checked whose checks as written
    /// added errors only inside other arguments ([`Pending`]), settled when the construct's
    /// check ends ([`Ck::pending_settled`]).
    pending_fixes: Vec<Pending>,
    /// The fixes kept in a construct whose type they change ([`Pending`]), by the construct's
    /// span, one [`Carry`] per type they give it, for the construct it is an argument of to
    /// check with that type in its place.
    carried: HashMap<Span, Vec<Carry>>,
    /// The [`Found::id`] the next error gets.
    next_found: usize,
    /// Whether the repair being tried ([`Ck::tried`]) makes an operation on literals alone
    /// whose value has no type until it meets a carrier, as `1 ^ 2.5`: the trial does not see
    /// where the value goes, so it fails.
    opened: bool,
    /// Whether a repair is being tried, so its errors offer none.
    trying: bool,
    /// Whether a repair's rewritten call is being tried ([`Ck::repaired`]), so a decimal
    /// literal at `rat` takes the type `rat` and its digits are not read ([`adopted`]).
    rough: bool,
    /// The output ports declared `Lines`.
    lines_out: HashSet<String>,
    /// The classes; class `k` is the type variable `$k`.
    classes: Vec<Class>,
    /// The rows and payload shapes [`Self::data`] entered, each holding no unknown: every class
    /// they hold at any depth had a data need from it, which the class keeps, so a later check
    /// of data that meets one again has nothing to add and does not enter it. Kept in the log
    /// while a repair is tried, since a trial undoes the classes' needs.
    data_checked: HashSet<NodeId>,
    /// The rows and payload shapes [`Self::bound`] found to hold only classes at any depth,
    /// each with the level it was at and that level's count of ends (`gens`): a class stays a
    /// class until the function of its level ends and names it, and a class's level only goes
    /// down, so the entry holds while that level has not ended since. A later replay that
    /// meets one has no variable in it to make unknown and does not enter it. Kept in the log
    /// while a repair is tried, since a trial undoes the classes it joined.
    clean: HashMap<NodeId, (usize, u64)>,
    /// For each level, the count of ends ([`Self::generalize`]) when it last ended, 0 for none.
    gens: Vec<u64>,
    /// The count of ends so far.
    ends: u64,
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
    /// The calls whose needs are being checked, innermost last, each with, for each
    /// positional argument, the variables of its parameter and the argument
    /// (MSG-forwarded-repair). A check of a value that flowed into a class has a frame of no
    /// arguments, so that it names none of a call around it.
    call_frames: Vec<CallFrame<'a>>,
    /// For the application a check of a need is about to make, the argument of the call whose
    /// need it is that each of its positional arguments came from, as `-1` in `ap(h, -1)` is
    /// `v` of `g(v)` in `ap(g, v) = g(v)`: a repair at that call names it, not `v`.
    need_from: Option<Vec<Option<Forwarded<'a>>>>,
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
    lit_refused: Vec<(Span, Msg)>,
    /// What each operation on literals alone that a repair's trial gave a carrier is at that
    /// carrier ([`Ck::lit_fit`]), by its span and the carrier: read off the text alone, as
    /// [`Ck::lit_ops`] is, so it is kept after the trial.
    lit_fits: HashMap<(Span, Carrier), LitFit>,
    /// The classes [`Self::generic_parts`] made outside every function, for [`Self::apply`] to
    /// give their types once the application has met them ([`Self::resolve_top_parts`]).
    top_parts: Vec<usize>,
    /// The declared functions whose bodies can end in a decimal literal with no suffix
    /// ([`Self::tail_reach`]), found when first asked.
    tail_reach: Option<HashSet<usize>>,
    /// The decimal literals with no suffix that a call outside every function ends in, by
    /// the function called, whether the call is in a payload, and the type at the call
    /// ([`Self::call_tails`]).
    tail_calls: HashMap<(usize, bool, Ty), Rc<[&'a Expr]>>,
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
    /// Each question the integer solver left undecided while a scope of [`Self::arms`] was
    /// narrowed or read, by where the program asks it and the question, with the sets it left
    /// its variables ([`Ck::place_refusals`]): a warning each once the walk is done.
    refused_at: BTreeMap<(Span, Refused), Kept>,
    /// For each binder read by a binder's value, what its summary read in the scope of its
    /// last such read ([`images::Read`]), from which the next is found.
    reads: HashMap<usize, images::Read<Rc<arms::Summarized>, zedc_preimage::product::Product>>,
    /// Each numeric literal the program writes: its value, without its `-`, and where each
    /// literal of that value starts, to where it ends, a zero under `-` with its `-`
    /// ([`Self::spells`]); a message prints the value as one of them ([`Self::spelling`]).
    // Complexity tradeoff: one entry per literal, found by the value's hash, O(the value's
    // size), then O(log n) in the n literals of that value to record one or to find the first
    // at or after a place; each spelling is a span into the text, so no literal is copied until
    // printed. Ordering the values themselves in one tree, as a first version did, compares a
    // rat such as `1e-Nr` with `10eNr` at a cost above linear in the digits of `N`. The naive
    // way, keeping each literal's text in its type, would make equal types print apart and the
    // printed text depend on which literal was met first.
    spelled: HashMap<Value, BTreeMap<usize, usize>>,
    /// The literal values the program spells in more than one way, as `31` and `0x1F`: a
    /// message prints such a value as written near it, so a type printed with one is printed
    /// anew for each message ([`zed_kernel::types::Spelled::everywhere`]).
    mixed: HashSet<Value>,
    /// The span of the text a message being written is about, whose own literals it prints as
    /// they are written there ([`Self::near`]).
    near: std::cell::Cell<Option<Span>>,
}

/// Atoms that a function value applied in a check of a need passed by (rule 6 of
/// sec:type_resolution): the value's name, the variables of the need's argument, the atoms.
type NeedPass = (Arc<str>, Vec<Arc<str>>, KType);

/// A call whose needs are being checked ([`Ck::call_frames`]): its positional arguments, where
/// the call shows them, and the parameter that holds each variable.
#[derive(Default)]
struct CallFrame<'a> {
    args: Vec<Option<Forwarded<'a>>>,
    /// For each variable of a parameter, the parameter's position, or `None` where two or
    /// more parameters hold it.
    by_var: HashMap<Arc<str>, Option<usize>>,
}

impl<'a> CallFrame<'a> {
    /// The frame of the arguments `args` at the parameters `params`.
    fn new(params: &[Ty], args: Vec<Option<Forwarded<'a>>>) -> Self {
        let mut by_var = HashMap::new();
        for (i, p) in params.iter().enumerate().take(args.len()) {
            for v in &p.vars {
                by_var
                    .entry(v.clone())
                    .and_modify(|at| {
                        if *at != Some(i) {
                            *at = None;
                        }
                    })
                    .or_insert(Some(i));
            }
        }
        Self { args, by_var }
    }

    /// The argument that a value of type `t` came from: that of the one parameter that holds
    /// its variables, where one alone does. Complexity tradeoff: naive, a test of `t`'s
    /// variables against every parameter's, O(p) set tests for p parameters, so O(p^2) for a
    /// need of every parameter (l01_26 scaling); used, a lookup of each variable of `t` in
    /// [`Self::by_var`], built once for the call in O(v) for v variables of its parameters.
    fn from(&self, t: &Ty) -> Option<Forwarded<'a>> {
        let mut one = None;
        for v in &t.vars {
            match self.by_var.get(v) {
                None => {}
                Some(None) => return None,
                Some(&Some(i)) if one.is_none_or(|j| j == i) => one = Some(i),
                Some(Some(_)) => return None,
            }
        }
        self.args[one?]
    }
}

/// An argument of a call written in the program ([`Ck::need_from`]): the call's span, the
/// argument's span, and its expression.
#[derive(Clone, Copy)]
struct Forwarded<'a> {
    call: Span,
    at: Span,
    expr: Option<&'a Expr>,
}

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
    /// A check with the binder tables `t`, whose rejections' fixes `check_fixes` checks as
    /// written ([`Self::check_fixes`]).
    fn new(t: &'t Tables<'a>, check_fixes: fn(&mut Self, Span, &mut Msg)) -> Self {
        Ck {
            t,
            env: HashMap::new(),
            info: Info::default(),
            errors: Vec::new(),
            log: Vec::new(),
            seen: HashMap::new(),
            eq_sides: HashMap::new(),
            lit_ops: HashSet::new(),
            lit_open: HashSet::new(),
            kept_ops: HashMap::new(),
            lit_written: HashMap::new(),
            lit_order: Vec::new(),
            lit_dropped: BTreeMap::new(),
            comparing: None,
            unnamed: HashMap::new(),
            made: HashMap::new(),
            alias: HashMap::new(),
            known: HashMap::new(),
            facts: HashMap::new(),
            main_tails: HashSet::new(),
            whence: HashMap::new(),
            narrowings: 0,
            narrowed_at: HashMap::new(),
            unnarrowed: HashMap::new(),
            written: None,
            check_fixes,
            pending_fixes: Vec::new(),
            carried: HashMap::new(),
            next_found: 0,
            opened: false,
            trying: false,
            rough: false,
            lines_out: HashSet::new(),
            classes: Vec::new(),
            data_checked: HashSet::new(),
            clean: HashMap::new(),
            gens: Vec::new(),
            ends: 0,
            level: 0,
            pending: vec![Vec::new()],
            needs: 0,
            replaying: 0,
            refused: Vec::new(),
            need_passed: Vec::new(),
            need_args: None,
            call_frames: Vec::new(),
            need_from: None,
            open_params: HashSet::new(),
            floors: HashMap::new(),
            leaving: Vec::new(),
            open: Vec::new(),
            defer: BTreeSet::new(),
            applied: None,
            lit_refused: Vec::new(),
            lit_fits: HashMap::new(),
            top_parts: Vec::new(),
            tail_reach: None,
            tail_calls: HashMap::new(),
            handled: handled(t.res),
            widened: HashSet::new(),
            outside: HashMap::new(),
            widened_only: HashMap::new(),
            tried: HashMap::new(),
            arms: arms::Arms::new(),
            refused_at: BTreeMap::new(),
            reads: HashMap::new(),
            spelled: HashMap::new(),
            mixed: HashSet::new(),
            near: std::cell::Cell::new(None),
        }
    }

    /// Records that the program writes the literal value `v`, without its `-`, at `span`; or,
    /// for a zero under one `-`, as `-0r`, with its `-`, at the span of the `-` and the
    /// literal: zero is its own negation, so the value alone does not keep the sign the
    /// program writes ([`signed_number_at`]).
    /// A value it records spelled otherwise than at its first record is mixed ([`Self::mixed`]),
    /// and the parts printed so far are forgotten, since they spell literals as they were
    /// ([`defs::forget_printed`]).
    // Complexity tradeoff: the new spelling is compared with the first, O(the literal's length),
    // which reading it cost already; comparing it with every spelling recorded would cost O(k)
    // for the k recorded, and the first is enough to tell one spelling from two.
    fn spells(&mut self, v: &Value, span: Span) {
        defs::forget_printed();
        match self.spelled.get_mut(v) {
            Some(at) => {
                if let Some(text) = self.t.text.filter(|_| !self.mixed.contains(v)) {
                    let (&start, &end) = at.first_key_value().expect("an entry holds a span");
                    if signed_number_at(text, Span { start, end }) != signed_number_at(text, span) {
                        self.mixed.insert(v.clone());
                    }
                }
                at.insert(span.start, span.end)
            }
            None => (self.spelled.entry(v.clone()).or_default()).insert(span.start, span.end),
        };
    }

    /// `f` of the checker, writing a message about the text at `span`: a literal value written
    /// there is printed as it is written there.
    fn near<T>(&self, span: Option<Span>, f: impl FnOnce(&Self) -> T) -> T {
        let was = self.near.replace(span);
        let out = f(self);
        self.near.set(was);
        out
    }

    /// The text whose literals a message about the expression at `span` prints as they are
    /// written there ([`Self::near`]): the expression, or, where it is a name, the expression
    /// that writes its value ([`Self::value_at`]), followed through each name to one that is
    /// no such name: `-0r` for `z` in `y = -0r; z = y;`. `memo` keeps the end found for each
    /// name passed, for the other calls of one message.
    // Complexity tradeoff (COMPLEXITY.md F165): the naive walk, from `span` to the end of its
    // chain at every call, costs O(n) per step of a derivation that steps through a chain of n
    // names, O(n²) for the message; a first version took one step only, O(1), and printed a
    // name defined as a name as the first literal of its value anywhere in the text. Used: the
    // walk records the end for every name it passes, so the calls of one message pass each name
    // once, O(n) for the message, two hash lookups and two inserts per name. A visited set of
    // the names on the walk stops it on a chain that comes back to a name it passed; zedc
    // refuses such definitions as recursion before it checks them, so none reaches here. The
    // memo lives for one message only: a name's origin can change as the check goes on (a test
    // narrows it), and an end kept across messages would make what one prints depend on which
    // was printed first.
    fn written_at(&self, span: Span, memo: &mut HashMap<Span, Span>) -> Span {
        let mut passed = HashSet::new();
        let mut at = span;
        let end = loop {
            if let Some(&end) = memo.get(&at) {
                break end;
            }
            let next = match self.seen.get(&at) {
                Some((_, Src::Name(id))) => (self.whence.get(id)).and_then(|o| self.value_at(o)),
                _ => None,
            };
            match next {
                Some(next) if passed.insert(at) => at = next,
                _ => break at,
            }
        };
        memo.extend(passed.into_iter().map(|s| (s, end)));
        end
    }

    /// The expression that writes the value of a binder whose type comes from `o`: the
    /// expression it is defined as, or, for a component of a tuple written out, as `q` in
    /// `p, q = (0r, -0r)`, that component's item; `None` for any other origin, and for a
    /// component of a tuple that is not written out there.
    fn value_at(&self, o: &Origin<'a>) -> Option<Span> {
        match o.why {
            Why::Defined(_) => Some(o.span),
            Why::Component(i, _) => match self.seen.get(&o.span) {
                Some((_, Src::Other(e))) => match &e.kind {
                    ExprKind::Tuple(items) => items.get(i).map(|x| x.span),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// The program's spelling of the literal value `v`: a literal with that value, or `-` and
    /// one with the negated value; one written in the span of the message being written
    /// ([`Self::near`]) if there is one, else the first in the text. `None` when the program
    /// writes neither, or its text is not known; the value is then printed in canonical form.
    // Complexity tradeoff: two hash lookups, O(the value's size), which printing it costs
    // anyway, and in each two range lookups, O(log n) in the n literals of the value. The naive
    // way, a scan of the literals for one inside the span, costs O(n) per value printed.
    /// It is the spelling wherever a message is written unless the program spells the value,
    /// or its negation, in more than one way ([`Self::mixed`]).
    fn spelling(&self, v: &Value) -> Spelled<'a> {
        let everywhere = self.mixed.is_empty()
            || !(self.mixed.contains(v) || self.mixed.contains(&neg_value(v, true)));
        Spelled {
            text: self.spelled_text(v),
            everywhere,
        }
    }

    /// The text of [`Self::spelling`].
    fn spelled_text(&self, v: &Value) -> Option<Cow<'a, str>> {
        let text = self.t.text?;
        if !matches!(
            v,
            Value::Int(_) | Value::Big(_) | Value::Rat(_) | Value::Float(_)
        ) {
            return None;
        }
        let find = |v: &Value| {
            let at = self.spelled.get(v)?;
            let first = |from: usize, to: usize| {
                (at.range(from..to).next())
                    .filter(|&(_, &end)| end <= to)
                    .and_then(|(&start, &end)| signed_number_at(text, Span { start, end }))
            };
            (self.near.get().and_then(|s| first(s.start, s.end))).or_else(|| first(0, usize::MAX))
        };
        if let Some(s) = find(v) {
            return Some(s);
        }
        let s = find(&neg_value(v, true))?;
        Some(Cow::Owned(format!("-{s}")))
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

    /// A class of its own, of generic literals only, that the literal `l`, written without a suffix, joins
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
        self.reject(Some(row), span, Msg::from(message.into()), notes);
    }

    fn error_with(&mut self, span: Span, message: impl Into<String>, notes: Vec<Note>) {
        self.reject(None, span, Msg::from(message.into()), notes);
    }

    /// An error at `span`, in the row `row` of the rejection table if any, with the message
    /// and fixes of `m` and the notes `notes`. Every error of the checker is pushed here. The
    /// fixes are written as the menu ([`Msg::written`]) when the check ends, with each fix the
    /// corrected line of this unit's text where the checker has it, and the menu stands after
    /// the notes (DESIGN.md sec:diagnostics).
    ///
    /// Complexity tradeoff: writing the menu here, as each error is found, costs the length
    /// of the lines its fixes touch for every error, kept or not: an error a later step drops
    /// ([`Self::rejects_unfixed`], or the undo after a tried repair) has had its lines written
    /// for nothing, and `y = (1 / 1) * … * (1 / 1)`, whose n `/` are each rejected as they are
    /// walked and then dropped for the binding's one rejection, cost O(n²) (a line of length
    /// of order n for each of n errors). Used: the error keeps its `Msg`, whose fixes are
    /// the edits alone, and the lines are written once, for the errors left at the end
    /// ([`Found::written`]), O(length of the lines) per error kept and O(1) per error
    /// dropped. The message is the same: [`Msg::written`] reads only the `Msg` and the unit's
    /// text, which does not change during the check. Memory: each error holds its edits
    /// until the end in place of its written menu. Test:
    /// `l01_26a_generic_literals::scaling::a_menu_that_writes_a_literal_in_each_of_many_divisions_scales`;
    /// COMPLEXITY.md F150.
    ///
    /// The fixes of a rejection inside the construct being checked are each checked as
    /// written first, and those that do not check are dropped ([`Self::check_fixes`]).
    fn reject(&mut self, row: Option<Row>, span: Span, mut m: Msg, notes: Vec<Note>) {
        if !self.trying && !m.fixes.is_empty() {
            (self.check_fixes)(self, span, &mut m);
        }
        self.errors.push(Found {
            id: self.next_found,
            row,
            span,
            m,
            notes,
            also: Vec::new(),
        });
        // A trial's errors are undone after it, so they take no number of their own: the
        // number of the error a repair checked before it is found stays the one it gets.
        if !self.trying {
            self.next_found += 1;
        }
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
        // Complexity tradeoff (COMPLEXITY.md F29): a scan of the notes shown before each new
        // one is O(R²) for R notes; the set of the notes shown makes each test O(1) expected,
        // for one copy of each note.
        let mut shown: HashSet<Note> = out.iter().cloned().collect();
        let mut visited = HashSet::new();
        // The end of each chain of names the steps have followed ([`Ck::written_at`]).
        let mut written = HashMap::new();
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
            // A step prints a literal value as the program writes it in the expression the
            // step is about, `-0r` for `x / -0r` and `0r` for its `0r` ([`Ck::spelling`]).
            let at = Some(self.written_at(span, &mut written));
            let ty = match (kept, src) {
                (Some(t), _) => self.near(at, |ck| ck.show(t)),
                (None, Src::Other(e)) => match self.tuple_seen(e) {
                    Some(t) => self.near(at, |ck| ck.show(&t)),
                    None => continue,
                },
                (None, _) => continue,
            };
            // What this expression shows, in order; pushed reversed so it pops in order.
            let mut next = Vec::new();
            let id = match src {
                Src::Name(id) => {
                    let name = &self.t.res.binders[*id].name;
                    next.push(note(
                        span,
                        match self.defined_open(*id) {
                            false => format!("`{name}` is {ty} here"),
                            true => format!(
                                "`{name}` is read here; it is defined as an operation on \
                                 literals alone, so it takes the carrier of what it meets"
                            ),
                        },
                    ));
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
                        ExprKind::Unary(op, _) => format!("this `{op}`"),
                        ExprKind::Binary(op, _, _) => format!("this `{op}`"),
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
                    // An operation on literals alone that met no carrier has no type in the
                    // program yet ([`Ck::lit_open`]); the type found for it is not the
                    // program's, so the step names none (DESIGN.md sec:diagnostics, "A `/`
                    // of integer literals").
                    let text = match (&e.kind, self.lit_open.contains(&span)) {
                        (_, false) => format!("{what} {verb} {ty}"),
                        (ExprKind::Binary(BinaryOp::Div, ..), true) => format!(
                            "{what} is an operation on literals alone, so it is a literal too \
                             and takes the carrier of what it meets; `/` has no arrow at `int`"
                        ),
                        (_, true) => format!(
                            "{what} is an operation on literals alone, so it is a literal too \
                             and takes the carrier of what it meets"
                        ),
                    };
                    next.push(note(span, text));
                    for p in parts {
                        next.push(match literal(p, self.t.text) {
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
                let said = match (&origin.why, origin.from) {
                    (Why::Defined(_), Some(f)) if self.lit_open.contains(&f) => {
                        let b = &self.t.res.binders[id].name;
                        format!("`{b}` is defined as this expression")
                    }
                    // Its value printed as the expression that writes it does, followed
                    // through any names: `-0r` for `z = y` with `y = -0r`.
                    _ => {
                        let at = (self.value_at(origin)).map(|s| self.written_at(s, &mut written));
                        self.near(at.or(Some(origin.span)), |ck| ck.said(id, &origin.why))
                    }
                };
                next.push(note(origin.span, said));
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

    /// Whether binder `id` is defined, as its one origin, by an operation on literals alone
    /// that met no carrier ([`Ck::lit_open`]): the type found for it is then not the
    /// program's, and a step that reads `id` names none (DESIGN.md sec:diagnostics, "A `/` of
    /// integer literals"). One lookup.
    fn defined_open(&self, id: usize) -> bool {
        self.whence.get(&id).is_some_and(|o| {
            o.then.is_none()
                && matches!(o.why, Why::Defined(_))
                && o.from.is_some_and(|f| self.lit_open.contains(&f))
        })
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
            Why::Declared(sig) => self.declared_step(id, sig),
            Why::Defined(v) => format!("`{b}` is defined as this expression, {}", self.text(v)),
            Why::Component(i, c) => {
                format!("`{b}` is {}, component {i} of this tuple", self.text(c))
            }
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
                    format!(
                        "`{b}` is declared `{}`",
                        show_with(&t, &masks, &|v| self.spelling(v))
                    )
                }
            },
            Why::Default(t) => format!("`{b}` is {}, the type of its default", self.text(t)),
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

    /// The step that says the function `id`, of signature `sig`, is declared here (DESIGN.md
    /// sec:diagnostics). It names the parameters written with no type and says that the type it
    /// shows is the one the checker found, not one written: `` `k` is declared here with no
    /// type written for `x`, `y` or its result; the type the checker found for `k` is
    /// `(_, T) -> T` ``, where `T` shows the places that have the same type at each call.
    /// A declaration writes no result type at this layer (the syntax tree has none), so the
    /// result is always among the types not written, and the step never shows a type as
    /// written.
    fn declared_step(&self, id: usize, sig: &Sig) -> String {
        let f = self.t.funcs[&id];
        let mut unwritten: Vec<String> = (f.params.iter())
            .filter(|p| p.ty.is_none())
            .map(|p| format!("`{}`", p.name))
            .collect();
        unwritten.push("its result".into());
        let sig = sig.solved_with(&|v| self.stale(v));
        let name = &f.name;
        format!(
            "`{name}` is declared here with no type written for {}; the type the checker found \
             for `{name}` is `{sig}`",
            or_list(&unwritten)
        )
    }

    /// [`emptied`] of each parameter type written on the function `id`, in order.
    fn declared_emptied(&self, id: usize, out: &mut Vec<Note>) {
        if let Some(f) = self.t.funcs.get(&id) {
            for a in f.params.iter().filter_map(|p| p.ty.as_ref()) {
                emptied(a, out);
            }
        }
    }

    /// The steps that say which arguments of a refused call of the function `id`, written
    /// `positional` and `named`, are in the part a difference takes away: for a parameter
    /// whose type is written `a \ b`, an argument whose value is a value of `b`. Positional
    /// arguments fill the parameters in order and named ones the parameter of their name, as
    /// the call placed them. `b` with a variable is skipped, since it holds no value fixed
    /// here. Built only for a message that is printed: one denotation of each `b`, linear in
    /// its size, and one subtype check per such parameter.
    fn subtracted_args(
        &self,
        id: usize,
        positional: &[Expr],
        named: &[(String, Expr)],
        out: &mut Vec<Note>,
    ) {
        let Some(f) = self.t.funcs.get(&id) else {
            return;
        };
        for (j, p) in f.params.iter().enumerate() {
            let Some(w) = &p.ty else {
                continue;
            };
            let TypeKind::Diff(_, b) = &bare(w).kind else {
                continue;
            };
            let e = match named.iter().find(|(n, _)| *n == p.name) {
                Some((_, e)) => e,
                None => match positional.get(j) {
                    Some(e) => e,
                    None => continue,
                },
            };
            let v = match self.seen.get(&e.span) {
                Some((Some(t), _)) => t.clone(),
                _ => match self.tuple_seen(e) {
                    Some(t) => t,
                    None => continue,
                },
            };
            let taken = denoted(b);
            if v.is_empty() || taken.dynamic || !taken.vars.is_empty() || !self.subtype(&v, &taken)
            {
                continue;
            }
            let shown = self.near(Some(e.span), |ck| ck.show(&v));
            out.push(Note {
                span: e.span,
                text: format!(
                    "`{shown} : {}` is in the part `\\` takes away from `{} : {}`",
                    format_type(b),
                    p.name,
                    format_type(w)
                ),
            });
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
            (ExprKind::Unary(op, _), _) => made(&op_sig(Operator::Unary(*op)).arrows),
            (ExprKind::Binary(op, _, _), _) => made(&op_sig(Operator::Binary(*op)).arrows),
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
            (ExprKind::Unary(op, _), _) => made(&op_sig(Operator::Unary(*op)).arrows, flows(e)),
            (ExprKind::Binary(op, _, _), _) => {
                made(&op_sig(Operator::Binary(*op)).arrows, flows(e))
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
            asked: false,
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
    /// false, changing nothing, if none would be left. A mask of carriers alone asks the
    /// class for a carrier ([`Class::asked`]), even where it removes none.
    fn restrict(&mut self, k: usize, mask: u8, what: &str, span: Span) -> bool {
        self.restrict_asking(k, mask, what, span, mask & OTHER == 0)
    }

    /// [`Self::restrict`], which asks the class for a carrier if `asks`.
    fn restrict_asking(&mut self, k: usize, mask: u8, what: &str, span: Span, asks: bool) -> bool {
        let r = self.find(k);
        let m = self.classes[r].mask & mask;
        if m == self.classes[r].mask {
            if asks && !self.classes[r].asked {
                self.touch(r);
                self.classes[r].asked = true;
            }
            return true;
        }
        if m == 0 {
            return false;
        }
        self.touch(r);
        let c = &mut self.classes[r];
        c.mask = m;
        c.asked |= asks;
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
    /// hold it exactly: `9007199254740993` removes `f64`.
    fn join(&mut self, k: usize, l: &Lit, follower: bool) -> bool {
        if !follower {
            let m = Carrier::ALL
                .into_iter()
                .filter(|&c| adoptable(l, c) && (!l.generic || fits(l, c)))
                .fold(0, |m, c| m | c.bit());
            // The literal's own carriers do not ask the class for one.
            if !self.restrict_asking(
                k,
                m,
                &quoting(&format_args!("the literal {}", l.written()), || {
                    "this literal".into()
                }),
                l.site,
                false,
            ) {
                return false;
            }
        }
        let r = self.find(k);
        self.touch(r);
        self.classes[r].lits.push((l.clone(), follower));
        true
    }

    /// Gives class `r` its type: its numeric carrier if a literal with a suffix joined it,
    /// which keeps only the literal's own carrier, or a literal with no other operand and no
    /// parameter of the class in scope at it ([`Info::witness`]), which takes `int` where the
    /// class may take it and is rejected where it may take two or more other carriers, every
    /// literal adopting the carrier; a type variable if it may take any value; its carrier if
    /// one; a type variable bounded by its carriers if several; else the unknown. So
    /// `f(x) = x * 2` takes int, f64 and rat, its `2` taking the carrier of `x` by one `match`
    /// at run time (step L1.26a), and `three() = 1 + 2` is `() -> int`.
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
        // Literals that nothing gives a carrier: an integer literal is an `int` where the
        // class may be one, and otherwise, as for a decimal literal or a `/` of integer
        // literals, nothing chooses among the carriers left, and the first decimal literal,
        // or else the first literal, is rejected (steps L1.26a and L1.26b).
        let left: Vec<Carrier> = Carrier::of_mask(mask).filter(|c| c.numeric()).collect();
        if numeric.is_some() && mask & Carrier::Int.bit() == 0 && left.len() > 1 {
            let mut joined = lits.iter().filter(|(_, follows)| !follows).map(|(l, _)| l);
            let first = joined.clone().next();
            if let Some(l) = joined
                .find(|l| lit_carrier(&l.value) == Carrier::F64)
                .or(first)
            {
                let notes = self.derive(&[l.site]);
                let m = unfixed(l, &left, None);
                self.reject(Some(Row::UnfixedDecimal), l.site, m, notes);
            }
        }
        // A bare literal compared with values of the class follows it without narrowing it, so
        // whether the class holds strings or `bool` and no number is known only now, whatever
        // order the body's uses come in (A15).
        let numbers = Carrier::Int.bit() | Carrier::Rat.bit() | Carrier::F64.bit();
        let others = Carrier::Str.bit() | Carrier::Bool.bit();
        if mask & (numbers | OTHER) == 0 && mask & others != 0 {
            let held = Ty::of_mask(mask);
            for (l, _) in lits.iter().filter(|(l, follows)| *follows && l.bare) {
                self.never_equal(l, &held);
            }
        }
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

    /// The root of the class of the variable `v`, unless that class was made a type variable
    /// of a signature ([`Self::resolve`] gave it its own variable as its type): `v` then stands
    /// for whatever type the caller passes, as a variable of a signature does, and a use that
    /// read the class's type in its place would read `v` again without end.
    fn class_root(&self, v: &str) -> Option<usize> {
        let r = self.find(class_id(v).filter(|&k| k < self.classes.len())?);
        let resolved = self.classes[r].resolved.as_ref();
        let own = resolved.and_then(Ty::as_var).and_then(|w| class_id(w));
        (own.map(|k| self.find(k)) != Some(r)).then_some(r)
    }

    /// The class `t` is, if it is one and nothing else.
    fn class_of_ty(&self, t: &Ty) -> Option<usize> {
        match t.pieces().as_slice() {
            [p] => self.class_of(p),
            _ => None,
        }
    }

    /// The class `t` is, beside atoms only: `T` in `T | #divByZero`, the type of `(1 + x) /
    /// (x * y)`. It costs the number of `t`'s pieces.
    fn class_beside_atoms(&self, t: &Ty) -> Option<usize> {
        let mut found = None;
        for p in t.pieces() {
            if p.is_atoms() {
                continue;
            }
            match (found, self.class_of(&p)) {
                (None, Some(k)) => found = Some(k),
                _ => return None,
            }
        }
        found
    }

    /// `t` shown with each class narrowed to some carriers shown as their union.
    fn show(&self, t: &Ty) -> String {
        let t = &self.as_literals(&self.settled(t));
        show_with(t, &self.masks(t), &|v| self.spelling(v))
    }

    /// `t` with each class of generic literals alone, not yet resolved, replaced by its
    /// literals, as written: `(1, 2, 3)`, not `(_, _, _)`, for the argument of
    /// `g((1, 2, 3))` with `g(positional a) = min(a, (1, 2))` in a message.
    fn as_literals(&self, t: &Ty) -> Ty {
        let lits: Binds = (t.var_facts().classes.into_iter())
            .filter_map(|v| {
                let r = self.find(class_id(&v).filter(|&k| k < self.classes.len())?);
                let c = &self.classes[r];
                (c.generic && c.resolved.is_none() && !c.lits.is_empty()).then(|| {
                    let ty = (c.lits.iter())
                        .fold(Ty::empty(), |t, (l, _)| t.union(&lit_ty(&l.value, l.neg())));
                    (v, ty)
                })
            })
            .collect();
        t.replace(&lits)
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
        // Complexity tradeoff (COMPLEXITY.md F29): the naive dedup looks for each reason among
        // the notes kept before it, O(R²) for R reasons; a hash set of the notes kept makes it
        // O(R) expected, at the cost of one more copy of each note in memory.
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
        self.as_literals(&self.settled(t))
            .text_spelled(false, &|v| self.spelling(v))
    }

    /// The text of `t` in a message as one operand of a union, `T | U`: a function in it is
    /// parenthesized.
    fn text_in_union(&self, t: &Ty) -> String {
        self.as_literals(&self.settled(t))
            .text_spelled(true, &|v| self.spelling(v))
    }

    /// [`Self::show`] as one operand of a union, `T | U`: a function in it is parenthesized.
    fn show_in_union(&self, t: &Ty) -> String {
        let t = &self.as_literals(&self.settled(t));
        match self.masks(t) {
            masks if masks.is_empty() => t.text_spelled(true, &|v| self.spelling(v)),
            masks => show_with(t, &masks, &|v| self.spelling(v)),
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
                    let name: Arc<str> =
                        fresh_name(Names::Variables, &mut n, |name| used.contains(name));
                    used.insert(name.clone());
                    name
                })
                .clone();
            *t = t.subst(&[(v, Ty::var(to))].into());
        }
        s.replace(&b)
    }

    /// Puts each class's type in place of its variable in what the checker found. Each
    /// signature is settled first ([`Sig::settle`]): the signatures of calls through values
    /// share the functions they hold, as `g(0)(1)…(n)` does, and are settled once each, not
    /// once for each signature that holds them. Each message then writes the definitions its
    /// types share once, below its sentence, named apart from the program's names ([`lay_out`]).
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
        let text = self.t.text;
        let mut errors: Vec<Error> = (std::mem::take(&mut self.errors).into_iter())
            .map(|f| f.written(text))
            .collect();
        for e in &mut errors {
            e.message = self.named(&e.message);
            for n in &mut e.notes {
                n.text = self.named(&n.text);
            }
            e.menu = self.named(&e.menu);
            lay_out(&mut e.message, &mut e.notes, &mut e.menu);
        }
        self.info.errors = errors;
        self.info.warnings = (std::mem::take(&mut self.refused_at).into_iter())
            .map(|((span, r), kept)| refused_warning(span, &r, &kept))
            .collect();
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
                self.reject(Some(Row::LiteralCarrier), l.site, m, Vec::new());
                lit_ty(&l.value, l.neg())
            }
        }
    }

    /// The loose atoms of `t`, which flow through `what` unchanged: an atom of a named family
    /// is data, and data that selects no arrow is an error (sec:failure). `of`, where known,
    /// is the span of the value as written, which the headline shows with its type and the
    /// repairs rewrite; elsewhere they write it `v`. The headline ends with the first repair
    /// (sec:diagnostics). The repairs handle every atom of the family the value may be, one
    /// `else` pattern or one `match` arm each, so their text is linear in the number of those
    /// atoms.
    fn passing(&mut self, t: &Ty, what: &str, span: Span, of: Option<Span>) -> Ty {
        if !t.family.is_empty() {
            let atoms = Ty::set(t.family.clone());
            let code = (self.t.text.zip(of))
                .map(|(s, at)| s[at.start..at.end].trim())
                .filter(|c| !c.is_empty() && !c.contains('\n'));
            let mut notes = Vec::new();
            if code.is_none() {
                notes.push(format!("`v` is the value {what} reads"));
            }
            let c = code.unwrap_or("v");
            // The value in parentheses unless it is a name, a call or an access, so that
            // `else` applies to all of it.
            let v = match c
                .chars()
                .all(|ch| ch.is_alphanumeric() || "_.:[]()".contains(ch))
            {
                true => c.to_string(),
                false => format!("({c})"),
            };
            notes.push(format!(
                "an atom of a named family is data, not a failure, so it does not pass through \
                 {what}"
            ));
            // Each atom as a bare pattern, which handles the atom with any payload or none;
            // a pattern with a payload would leave the atom in the type (step L1.27).
            let mut repairs = Vec::new();
            match t.family.atom_names() {
                Some(names) => {
                    let names: Vec<String> = names.map(|(name, _)| format!("#{name}")).collect();
                    let chain: String = names.iter().map(|a| format!(" else {a} -> d")).collect();
                    let mut arms: Vec<String> = names.iter().map(|a| format!("{a} -> d")).collect();
                    // The value may hold more than the family's atoms: a last arm keeps the rest.
                    if !t.diff(&atoms).is_empty() {
                        arms.push("rest -> rest".to_string());
                    }
                    notes.push(match names.len() {
                        1 => "`d` is the value to use in place of the atom".to_string(),
                        _ => "each `d` is the value to use in place of the atom before it"
                            .to_string(),
                    });
                    repairs.push(format!("({v}{chain})"));
                    repairs.push(format!("match {v} {{ {} }}", arms.join(", ")));
                }
                // A family of every atom but some cannot be listed.
                None => notes.push(format!(
                    "repair: a `match` on `{v}` with one arm for each atom of `{atoms}`"
                )),
            }
            let then = (repairs.first()).map_or(String::new(), |r| format!(" Try `{r}` instead."));
            let message = format!("No case for `{atoms}` in {what}: `{c} : {t}`.{then}");
            notes.extend(repairs.iter().map(|r| format!("repair: `{r}`")));
            // In the row "Atom of a named family reaching …" of the rejection table, named from
            // L2.5, when a source program can raise it and so have a near miss (step L1.29).
            self.error_offering(span, message, notes);
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

    /// Checks that `main`, `f` with the signature `sig`, gives an exit status (DESIGN.md
    /// sec:ports, step L1.19): an `int`, or nothing, when its body exports nothing, which exits
    /// with 0. A failure that bubbles out of the body exits with 1 and is not part of the
    /// status, so the result's loose atoms are left out. That each `int` it gives is in
    /// `0..=255` is checked where the walk reads it ([`Ck::status_in_range`]).
    pub(super) fn exit_status(&mut self, f: &Function, sig: &Sig) {
        let nothing = Ty::tuple(Vec::new());
        for a in &sig.arrows {
            let r = a.result.without_loose();
            let rest = r.without(&KType::int());
            if rest.is_empty() || rest.subtype(&nothing) {
                continue;
            }
            let span = match &f.body.kind {
                ExprKind::Block(stmts) => stmts.last().map_or(f.body.span, |s| s.span),
                _ => f.body.span,
            };
            let code = self.t.text.map_or("the body", |t| &t[span.start..span.end]);
            let message = format!(
                "`main` gives `{code}`, which is {}, and the result of `main` is the program's \
                 exit status, an `int` from 0 to 255",
                self.show(&r)
            );
            let menu = [
                "repair: give the status as an int, as `0` for success".to_string(),
                "repair: write the text to the output, as `m.stdout <- text`, and give no result"
                    .to_string(),
            ];
            self.error_offering(span, message, menu);
            return;
        }
    }

    /// Records the expressions whose value is the result of `main`, the body `body`: the
    /// export of a block, and the branches of an `if`, a `match` and an `else`, each read for
    /// the exit status where the walk reaches it ([`Ck::status_in_range`]). Each expression
    /// is visited once, on an explicit stack, so the cost is linear in the body's branches.
    pub(super) fn main_tails(&mut self, body: &Expr) {
        let mut stack = vec![body];
        while let Some(e) = stack.pop() {
            match &e.kind {
                ExprKind::Block(stmts) => {
                    if let Some(Stmt {
                        kind: StmtKind::Return(es),
                        ..
                    }) = stmts.last()
                        && let [one] = es.as_slice()
                    {
                        stack.push(one);
                    }
                }
                ExprKind::If {
                    then, otherwise, ..
                } => stack.extend([&**then, &**otherwise]),
                ExprKind::Else { of, default, .. } => stack.extend([&**of, &**default]),
                ExprKind::Match { arms, .. } => stack.extend(arms.iter().map(|a| &a.body)),
                _ => {
                    self.main_tails.insert(e.span);
                }
            }
        }
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
            // The example handler names an atom the value holds, so that it applies as written.
            let atom = t
                .set
                .atom_names()
                .and_then(|mut names| names.find(|&(_, bare)| bare).map(|(n, _)| n))
                .unwrap_or("notFound");
            let menu = [
                format!(
                    "repair: write the value into a string, as `{port} <- \"${{v}}\";`, where `v` \
                     is the value"
                ),
                format!(
                    "repair: handle the values that are not text first, with `match` or with \
                     `else`, as `v else #{atom} -> \"\"`"
                ),
            ];
            self.error_offering(span, message, menu);
        }
    }

    /// The literal `l` compared with a value of one of the types `ts`, as at a parameter
    /// ([`expected`]). With a lone `ts` that is a class, a plain literal joins it as an operand
    /// does, keeping only the literal's carrier; a generic one outside a tuple follows the
    /// class's carrier without narrowing it, and one in a tuple joins it as a plain one does,
    /// since the elaborator's rewrite that follows the class's carrier at run time
    /// (`Info::follows`) is built for an operand of `==` only. `other` is the index, in
    /// [`Ck::comparing`], of the operand on the other side from `l`.
    fn follow(&mut self, l: &Lit, ts: &[&Ty], inner: bool, other: usize) {
        if let [t] = ts
            && let Some(k) = self.class_of_ty(t)
        {
            if !self.join(k, l, l.bare && !inner) {
                let mask = self.classes[self.find(k)].mask;
                let held: Vec<Carrier> = [Carrier::Int, Carrier::Rat, Carrier::F64]
                    .into_iter()
                    .filter(|c| mask & c.bit() != 0)
                    .collect();
                let m: Msg = match held.is_empty() {
                    false => menu(l, &held),
                    true => {
                        let own = lit_carrier(&l.value);
                        let names = carriers_text(Carrier::of_mask(mask));
                        let (what, carrier) = (article(own), own.name());
                        let text = l.written();
                        quoting(
                            &format_args!(
                                "`{text}` is {what} {carrier}, compared with a value of \
                                 `{names}`, which holds no number"
                            ),
                            || {
                                format!(
                                    "this literal is {what} {carrier}, compared with a value of \
                                     `{names}`, which holds no number"
                                )
                            },
                        )
                        .into()
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
            Ok(None) => {
                // A component of a tuple operand; the literal written as an operand itself is
                // judged by the operator, which knows its other operand ([`Ck::never_equal`]).
                if inner
                    && l.bare
                    && let Some(Comparison { op, ats, .. }) = self.comparing
                    && holds_no_number(ts)
                {
                    self.never_equal_component(l, ts, op, ats[other]);
                }
            }
            Err(m) => self.compared(l, ts, m),
        }
    }

    /// Rejects the literal `l`, written without a suffix and compared by `==` or `!=` with a
    /// value of `t`, which holds values and no number ([`holds_no_number`]): no carrier of a
    /// number literal is a string, a `bool` or a tuple, so the comparison always gives the
    /// same answer (author decision, 2026-11-09, A15). The fixes fit what `t` holds, and the
    /// checker accepts each: the text, `x == "1"`, where `t` holds strings, and no cast of the
    /// string, which `#invalid` makes narrowing (DESIGN.md sec:diagnostics); `x == true` and `x == false` where it holds
    /// `bool`; `x[i] == 1` for each component `i` of its tuples that may be the number; and,
    /// where none of these fits, the answer the comparison always gives in its place. Each is
    /// the corrected source line ([`Msg::written`]). A comparison with an atom stays legal and
    /// does not come here. Each component is read once in each shape, so the cost is linear
    /// in the size of `t`'s tuples.
    fn never_equal(&mut self, l: &Lit, t: &Ty) {
        let (op, at, left) =
            self.eq_sides
                .get(&l.site)
                .copied()
                .unwrap_or((BinaryOp::Eq, None, false));
        let tables = self.t;
        let name = at.and_then(|at| match self.seen.get(&at) {
            Some((_, Src::Name(id))) => Some(tables.res.binders[*id].name.as_str()),
            _ => None,
        });
        let values = t.without_atoms();
        let u = values.set.universes();
        // `x[i]` takes a tuple of more than `i` components, and no other value but a loose
        // atom, which passes by.
        let tuples_only = !u.bases.iter().any(|&b| b) && !u.rest && t.family.is_empty();
        let width = (values.tuples.iter().map(|r| r.len()).min())
            .filter(|_| tuples_only)
            .unwrap_or(0);
        let components = (0..width)
            .filter(|&i| takes_number(l, &values.tuples.iter().map(|r| &r[i]).collect::<Vec<_>>()))
            .map(Repair::Component)
            .collect();
        let groups = [texts(&u), bools(&u), components];
        let answer = groups.iter().all(|rs| rs.is_empty());
        let ty = self.shown(&values);
        let a = article_of(&ty, &ty);
        let lit = l.written();
        let message = quoting(
            &fmt::from_fn(|f| {
                // The comparison as code, the literal where the program writes it,
                // `n : Utf8String == 1`.
                write!(f, "No number equals {a}`{ty}`: ")?;
                match (name, left) {
                    (Some(n), true) => write!(f, "`{lit} {op} {n} : {ty}`")?,
                    (Some(n), false) => write!(f, "`{n} : {ty} {op} {lit}`")?,
                    (None, _) => write!(f, "`{lit}` compared by `{op}` with {a}`{ty}`")?,
                }
                match answer {
                    true => write!(f, " is always `{}`", op != BinaryOp::Eq),
                    false => f.write_str(" always gives the same answer"),
                }
            }),
            || {
                format!(
                    "No number equals {a}`{ty}`: this literal compared by `{op}` with it always gives the same answer"
                )
            },
        );
        // The comparison with `a` and `b` as its operands, in the order the program writes
        // them, for a message written without the program's text.
        let pair = |a: &dyn fmt::Display, b: &dyn fmt::Display| -> String {
            let pair = fmt::from_fn(|f| match left {
                true => write!(f, "{b} {op} {a}"),
                false => write!(f, "{a} {op} {b}"),
            });
            shown(&pair).unwrap_or_default()
        };
        let text = fmt::from_fn(|f| write!(f, "\"{lit}\""));
        let mut fixes = Vec::new();
        for r in groups.iter().flatten() {
            fixes.push(match (*r, at) {
                (Repair::Text, _) => Rewrite::new(
                    &[(l.site, &text)],
                    &"compares the text",
                    &match name {
                        Some(n) => pair(&n, &text),
                        None => shown(&text).unwrap_or_default(),
                    },
                ),
                (Repair::Bool(b), _) => Rewrite::new(
                    &[(l.site, &b)],
                    &"compares with a truth value",
                    &match name {
                        Some(n) => pair(&n, &b),
                        None => b.to_string(),
                    },
                ),
                (Repair::Component(i), Some(at)) => Rewrite::new(
                    &[(point(at.end), &format_args!("[{i}]"))],
                    &format_args!("compares component {i}"),
                    &match name {
                        Some(n) => pair(&format_args!("{n}[{i}]"), &lit),
                        None => format!("[{i}]"),
                    },
                ),
                _ => None,
            });
        }
        // The answer in place of the whole comparison, which spans both operands.
        if answer && let Some(at) = at {
            let whole = Span {
                start: at.start.min(l.site.start),
                end: at.end.max(l.site.end),
            };
            let a = op != BinaryOp::Eq;
            fixes.push(Rewrite::new(
                &[(whole, &a)],
                &"the answer the comparison always gives",
                &a,
            ));
        }
        let notes = self.derive(&[at.unwrap_or(l.site)]);
        self.reject(
            Some(Row::LiteralCarrier),
            l.site,
            Msg::new(message, fixes),
            notes,
        );
    }

    /// Rejects the literal `l`, written without a suffix as a component of a tuple that `op`
    /// compares with a tuple whose components there, of the types `ts`, hold no number
    /// ([`holds_no_number`]), as [`Ck::never_equal`] rejects a literal written as an operand:
    /// `p == (1, 2)` with `p: (String, int)`. `at` is the span of the other operand. The
    /// fixes write in the literal's place the text, `"1"`, where the component holds
    /// strings, and `true` or `false` where it holds `bool`; with neither, the message asks
    /// for a value of the component's type.
    fn never_equal_component(&mut self, l: &Lit, ts: &[&Ty], op: BinaryOp, at: Option<Span>) {
        let tables = self.t;
        let name = at.and_then(|at| match self.seen.get(&at) {
            Some((_, Src::Name(id))) => Some(tables.res.binders[*id].name.as_str()),
            _ => None,
        });
        let values = Ty::union_all(ts.iter().copied()).without_atoms();
        let u = values.set.universes();
        let repairs: Vec<Repair> = texts(&u).into_iter().chain(bools(&u)).collect();
        let shown = self.shown(&values);
        let a = article_of(&shown, &shown);
        let lit = l.written();
        let message = quoting(
            &fmt::from_fn(|f| {
                write!(
                    f,
                    "No number equals {a}`{shown}`: `{lit}` compared by `{op}` with "
                )?;
                match name {
                    Some(n) => write!(f, "a component of `{n}`")?,
                    None => f.write_str("a component")?,
                }
                f.write_str(" always gives the same answer")?;
                match repairs.is_empty() {
                    true => write!(f, ". Write a value of `{shown}` in place of `{lit}`."),
                    false => Ok(()),
                }
            }),
            || {
                format!(
                    "No number equals {a}`{shown}`: this literal compared by `{op}` with a \
                     component always gives the same answer"
                )
            },
        );
        let text = fmt::from_fn(|f| write!(f, "\"{lit}\""));
        let fixes = (repairs.iter())
            .map(|r| match *r {
                Repair::Bool(b) => {
                    Rewrite::new(&[(l.site, &b)], &"compares with a truth value", &b)
                }
                _ => Rewrite::new(&[(l.site, &text)], &"compares the text", &text),
            })
            .collect();
        let notes = self.derive(&[at.unwrap_or(l.site)]);
        self.reject(
            Some(Row::LiteralCarrier),
            l.site,
            Msg::new(message, fixes),
            notes,
        );
    }

    /// Reports the literal `l`, compared by `==` with a value of one of the types `ts`,
    /// rejected with the message `m`: in the row of a literal at a carrier it cannot take
    /// where `ts` holds numbers (`n == 1.5` with `n: int`), whose derivation and repairs
    /// [`Self::equal_repairs`] adds; in no row otherwise.
    fn compared(&mut self, l: &Lit, ts: &[&Ty], m: Msg) {
        let numbers = (ts.iter()).try_fold(0, |acc, t| self.numbers_in(t).map(|m| acc | m));
        let row = match numbers {
            Some(n) if n != 0 => Some(Row::LiteralCarrier),
            _ => None,
        };
        let notes = self.derive(&[l.site]);
        self.reject(row, l.site, m, notes);
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
    /// with `#outOfBounds` when the key may lie outside `0..<n`, since those keys are one
    /// integer interval, every key present (the `m[k]` row); a key that selects no component
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
        let mut out = self.passing(&x.ty, "a tuple index", span, x.at);
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
            out = out.union(&Ty::set(KType::atom("outOfBounds")));
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
                dense: sig.dense,
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
        if self.trying || self.errors.len() <= from {
            return;
        }
        let notes = notes(self);
        for e in &mut self.errors[from..] {
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
        // `==` and `!=` are not in the row: [`Ck::equal`] checks them, not their arrows.
        let operator = match Operator::of_label(what) {
            None | Some(Operator::Binary(BinaryOp::Eq | BinaryOp::Ne)) => false,
            Some(Operator::Unary(UnaryOp::Neg | UnaryOp::Not))
            | Some(Operator::Binary(
                BinaryOp::Or
                | BinaryOp::And
                | BinaryOp::Lt
                | BinaryOp::Le
                | BinaryOp::Gt
                | BinaryOp::Ge
                | BinaryOp::Add
                | BinaryOp::Sub
                | BinaryOp::Concat
                | BinaryOp::Mul
                | BinaryOp::Div
                | BinaryOp::IntDiv
                | BinaryOp::Mod
                | BinaryOp::Pow,
            )) => true,
        };
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
    /// all numbers of known carriers, an integer literal without a suffix among them, decides
    /// nothing.
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
    /// its type ([`Self::numbers_in`]). An integer literal without a suffix may take any, and
    /// a decimal one any but `int`, which a decimal never is.
    fn numbers_of(&self, a: &Arg) -> Option<u8> {
        match &a.lit {
            Some(l) if l.bare && lit_carrier(&l.value) == Carrier::F64 => {
                Some(Carrier::F64.bit() | Carrier::Rat.bit())
            }
            Some(l) if l.bare => None,
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
        // The arguments' literals are printed as written there: in the text from the first
        // argument's start to the last's end.
        let spans = || args.iter().filter_map(|a| a.as_ref()?.at);
        let near = (spans().map(|s| s.start).min())
            .zip(spans().map(|s| s.end).max())
            .map(|(start, end)| Span { start, end });
        let shown: Vec<String> = self.near(near, |ck| {
            (args.iter().enumerate())
                .map(|(i, a)| match (a, at) {
                    (_, Some((j, p, _))) if i == j => ck.show(&p.ty()),
                    (Some(a), _) => ck.show(&a.ty),
                    (None, _) => "_".into(),
                })
                .collect()
        });
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
    /// generic if written without a suffix ([`Lit::joining`]), except in a check of a generic function's
    /// needs at a call, where the literal is of the function's body, which elaborates once for
    /// every call, and keeps its own carrier.
    fn joining(&self, l: &Lit) -> Lit {
        match self.replaying {
            0 => l.joining(),
            _ => l.clone(),
        }
    }

    /// Gives each class [`Self::generic_parts`] made outside every function since `from`, of
    /// the literals of a tuple argument, its type, now that the application has met it. A
    /// class a use asked for a carrier ([`Class::asked`]), as a bounded variable does,
    /// stands for one carrier of the bound, as the variable does at a call (DESIGN.md
    /// L1.26a), and the body's operators make new values of that carrier from the literals,
    /// so the class is the whole carrier: `int` in `r = h((1, 2))` with `h(positional p) =
    /// p[0] + p[1]`, whose value is `3`, and `rat` for `2` in `y = f(x: 1r, p: (2, 1))` with
    /// `f(x, p) = x + p[0]`. The carrier is chosen as for literals alone at a bounded
    /// variable: `int` for integer literals where the class holds it, the one carrier left,
    /// and with two or more the first literal is rejected, unless a decimal literal is in
    /// the class, which is rejected where the arguments are read ([`Self::unfixed_args`]).
    /// The literals adopt the carrier. A class no use asked, as `p` in `h(p) = p[0]`,
    /// keeps its literals' own types, `1` for `h((1, 2))`, since only a copy of a literal
    /// can come out of it. Each class is read once: the cost is the number of its literals.
    fn resolve_top_parts(&mut self, from: usize) {
        for k in self.top_parts.split_off(from) {
            let r = self.find(k);
            if self.classes[r].resolved.is_some() {
                continue;
            }
            let mask = self.classes[r].mask;
            let lits: Vec<Lit> = (self.classes[r].lits.iter())
                .map(|(l, _)| l.clone())
                .collect();
            let takes: Vec<Carrier> = Carrier::of_mask(mask)
                .filter(|&c| c.numeric() && lits.iter().all(|l| fits(l, c)))
                .collect();
            let ints = lits.iter().all(|l| lit_carrier(&l.value) == Carrier::Int);
            let c = match takes[..] {
                _ if !self.classes[r].asked => None,
                [] => None,
                _ if ints && takes.contains(&Carrier::Int) => Some(Carrier::Int),
                [c] => Some(c),
                [c, ..] => {
                    let decimal = lits.iter().any(|l| lit_carrier(&l.value) == Carrier::F64);
                    if !decimal && let Some(l) = lits.first() {
                        let notes = self.derive(&[l.site]);
                        let m = unfixed(l, &takes, None);
                        self.reject(Some(Row::UnfixedDecimal), l.site, m, notes);
                    }
                    Some(c)
                }
            };
            let ty = match c {
                Some(c) => {
                    for l in &lits {
                        self.adopt_to(l, c);
                    }
                    Ty::carrier(c)
                }
                None => Ty::union_all(
                    &(lits.iter())
                        .map(|l| lit_ty(&l.value, l.neg()))
                        .collect::<Vec<_>>(),
                ),
            };
            self.touch(r);
            self.classes[r].resolved = Some(ty);
        }
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

/// The type of the cast `w` applied to `t` where the cast cannot fail or lose information on
/// any value of `t`, as `rat(n)` of an `int`: none where it may give an atom `t` does not hold,
/// as `f64(n)` (`#inexact`) or `int(r)` (`#inexact`), so that a repair never narrows a type
/// (DESIGN.md sec:diagnostics).
///
/// Complexity tradeoff (COMPLEXITY.md row MSG-concise-casts): naive version, apply the cast to
/// each value `t` may hold and check each result exactly, O(the values of `t`), unbounded for
/// an `int`; this version reads the cast's arrows once per piece of `t` ([`converted`]) and
/// compares the atoms of the result with those of `t`, O(the size of `t`), the cost of printing
/// `t` in the message that offers the cast.
/// The type of the cast `w` of a value of the type `t`, where the cast cannot fail or lose
/// information on any value of `t` ([`cast_widening`]), with `f64` of an int the checker proves
/// lies within ±2^53 (`exact`, [`Comparison::exact`]) exact, as [`Ck::word_end`] applies it:
/// `f64(n)` of an `int` under `if n >= 0 && n <= 100`, which a repair menu then offers
/// (DESIGN.md sec:diagnostics, "A repair never narrows a type"). Cost: [`cast_widening`], or
/// one conversion by the signature of the exact cast.
fn widening(w: &str, t: &Ty, exact: bool) -> Option<Ty> {
    match w == "f64" && exact {
        true => converted(&f64_of_exact_int_sig(), t).filter(|r| r.atoms() == t.atoms()),
        false => cast_widening(w, t),
    }
}

fn cast_widening(w: &str, t: &Ty) -> Option<Ty> {
    converted(&word_sig(w), t).filter(|r| r.atoms() == t.atoms())
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
    /// Whether a row or payload shape is among [`Ck::data_checked`], while a repair is tried.
    DataChecked(NodeId, bool),
    /// The entry of a row or payload shape in [`Ck::clean`], while a repair is tried.
    Clean(NodeId, Option<(usize, u64)>),
}

/// How long the log and the errors were at a point.
struct Mark {
    log: usize,
    errors: usize,
    top_parts: usize,
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
        if let Undo::DataChecked(n, now) = w {
            let was = match now {
                true => !self.data_checked.insert(n),
                false => self.data_checked.remove(&n),
            };
            return Undo::DataChecked(n, was);
        }
        if let Undo::Clean(n, v) = w {
            return Undo::Clean(n, set!(self.clean, n, v));
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
            Undo::Class(..) | Undo::DataChecked(..) | Undo::Clean(..) => unreachable!("set above"),
        }
    }

    /// The point the checker is at.
    fn mark(&self) -> Mark {
        Mark {
            log: self.log.len(),
            errors: self.errors.len(),
            top_parts: self.top_parts.len(),
        }
    }

    /// Undoes every write and error since `m`, the latest first.
    fn undo(&mut self, m: &Mark) {
        while self.log.len() > m.log {
            let w = self.log.pop().expect("longer than the mark");
            self.set(w);
        }
        self.errors.truncate(m.errors);
        self.top_parts.truncate(m.top_parts);
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

/// The number `src` writes in `span`, the span of a literal, which holds the literal's grouping
/// parentheses where it has some (`(1_000)`): the text of the number alone, as the program
/// writes it; `None` where `span` is not in `src` or holds no number.
// Complexity tradeoff: a literal without parentheses is its span, O(1); one with them is lexed,
// O(the length of its span), which is at most the text a message quoting it prints. The naive
// way, a number token recorded at each literal, would cost the syntax tree a span per literal.
fn number_at(src: &str, span: Span) -> Option<&str> {
    let s = src.get(span.start..span.end)?;
    if !s.starts_with('(') {
        return Some(s);
    }
    let tokens = lex(s).ok()?;
    let t = (tokens.iter()).find(|t| {
        matches!(
            t.tok,
            Tok::Int { .. } | Tok::Float { .. } | Tok::Rat(_) | Tok::Keyword(_)
        )
    })?;
    s.get(t.span.start..t.span.end)
}

/// The number `src` writes in `span`, as [`number_at`] reads it, and with its `-` where `span`
/// holds one before the number: the span of a zero literal under one `-`, as `-0r`, `-(0r)` or
/// `(-0)`, which [`Ck::spells`] records with its sign.
// Complexity tradeoff: a span that starts with neither `-` nor `(` is its text, O(1); one that
// does is lexed, O(the length of its span), as in [`number_at`].
fn signed_number_at(src: &str, span: Span) -> Option<Cow<'_, str>> {
    let s = src.get(span.start..span.end)?;
    if !s.starts_with(['-', '(']) {
        return Some(Cow::Borrowed(s));
    }
    let tokens = lex(s).ok()?;
    let i = (tokens.iter()).position(|t| {
        matches!(
            t.tok,
            Tok::Int { .. } | Tok::Float { .. } | Tok::Rat(_) | Tok::Keyword(_)
        )
    })?;
    let number = s.get(tokens[i].span.start..tokens[i].span.end)?;
    match tokens[..i].iter().any(|t| matches!(t.tok, Tok::Op("-"))) {
        true => Some(Cow::Owned(format!("-{number}"))),
        false => Some(Cow::Borrowed(number)),
    }
}

/// `e` as a numeric literal, perhaps under one `-`; `None` also where the system refuses the
/// memory to read it, which [`Ck::expr_of`] reports through [`read_literal`]. `src` is the
/// program's text, from which a message quotes the literal ([`Lit::spelling`]); `None` where
/// only the literal's value and kind are read.
fn literal(e: &Expr, src: Option<&str>) -> Option<Lit> {
    read_literal(e, src).ok().flatten()
}

/// `e` as a numeric literal, perhaps under one `-`; [`TooLarge`] when the system refuses the
/// memory to read its digits or to copy its text. The lexer has removed the `_` from the
/// digits, so they are read where they are, not copied; the literal as `src`, the program's
/// text, writes it is kept where it has a `_` ([`Lit::spelled`]).
fn read_literal(e: &Expr, src: Option<&str>) -> Result<Option<Lit>, TooLarge> {
    let inner = match &e.kind {
        ExprKind::Unary(UnaryOp::Neg, a) => &**a,
        _ => e,
    };
    let (value, bare) = match &inner.kind {
        ExprKind::Int { radix, digits } => match Value::int_text(digits, *radix)? {
            Some(v) => (v, true),
            None => return Ok(None),
        },
        ExprKind::Float { digits: s, forced } => match literal_f64(s) {
            Ok(x) => (Value::float(x), !forced),
            Err(_) => return Ok(None),
        },
        _ => return Ok(None),
    };
    let text = shown(inner)?;
    // The lexer keeps every character of a number but the `_`, so the two differ in length
    // exactly where the program writes a `_`.
    let spelled = match src.and_then(|s| number_at(s, inner.span)) {
        Some(s) if s.len() != text.len() => Some(Rc::new(shown(&s)?)),
        _ => None,
    };
    Ok(Some(Lit {
        span: inner.span,
        site: e.span,
        value,
        text: Rc::new(text),
        spelled,
        bare,
        generic: false,
        witness: false,
    }))
}

/// The components of `t` when it is exactly one tuple of length `n` and nothing else.
fn only_tuple(t: &Ty, n: usize) -> Option<&[Ty]> {
    let one = t.set.is_empty() && t.fns.is_empty() && t.vars.is_empty() && !t.dynamic;
    match t.tuples.as_slice() {
        [cs] if one && cs.len() == n => Some(cs),
        _ => None,
    }
}

/// `t`, the type of a tuple written with the parts `parts`, with each literal there that has
/// adopted a carrier (`adopt`, by span) typed as the value it takes: `(0.5f64, 1)` once the
/// `1` adopts `f64` is `(0.5f64, 1.0f64)`. A component that is not exactly one tuple of its
/// parts' length is left as it is. The tuples nest as deep as the text, so the walk keeps its
/// own stack: each open tuple's parts, its components and the types so far.
fn with_adoptions(t: &Ty, parts: &[Part], adopt: &HashMap<Span, Value>) -> Ty {
    let Some(cs) = only_tuple(t, parts.len()) else {
        return t.clone();
    };
    let mut stack: Vec<(&[Part], &[Ty], Vec<Ty>)> = vec![(parts, cs, Vec::new())];
    loop {
        let (ps, cs, out) = stack.last_mut().expect("an open tuple");
        let i = out.len();
        if i == ps.len() {
            let t = Ty::tuple(stack.pop().expect("an open tuple").2);
            match stack.last_mut() {
                None => return t,
                Some(up) => up.2.push(t),
            }
            continue;
        }
        let c = &cs[i];
        match &ps[i] {
            Part::Lit(l) => out.push(match adopt.get(&l.span) {
                Some(v) => lit_ty(v, l.neg()),
                None => c.clone(),
            }),
            // Each branch as it adopted, as [`adopted`] types it; one that adopted nothing
            // leaves the component as it is.
            Part::Branches(bs) => {
                let at = |b: &Branch| match b {
                    Branch::Lit(l) => adopt.get(&l.span).map(|v| lit_ty(v, l.neg())),
                    Branch::Op { e, .. } => adopt.get(&e.span).map(Ty::lit),
                };
                out.push(match bs.iter().any(|b| at(b).is_some()) {
                    true => Ty::union_all(
                        &(bs.iter())
                            .map(|b| at(b).unwrap_or_else(|| Ty::lit(b.value())))
                            .collect::<Vec<_>>(),
                    ),
                    false => c.clone(),
                })
            }
            Part::Tuple(inner) => match only_tuple(c, inner.len()) {
                Some(ics) => stack.push((inner, ics, Vec::new())),
                None => out.push(c.clone()),
            },
            Part::Other => out.push(c.clone()),
        }
    }
}

/// An `==` or `!=` whose operands [`Ck::equal`] pairs: the operator, the span and the expression
/// of each operand, left then right, the span of the comparison, and the number of errors before its operands
/// were checked, so that two values with no common carrier are rejected there only where
/// nothing else rejected the comparison first ([`Ck::apart`]).
#[derive(Clone, Copy)]
struct Comparison<'a> {
    op: BinaryOp,
    ats: [Option<Span>; 2],
    exprs: [Option<&'a Expr>; 2],
    /// Whether each operand is an int the checker proves lies within ±2^53, so its cast to
    /// `f64` is exact and a repair may offer it ([`widening`]); computed where the walk sets
    /// [`Ck::comparing`], and only where such a cast could repair the comparison.
    exact: [bool; 2],
    span: Span,
    from: usize,
}

/// One side of `==` as [`Ck::equal`] reads it: the types its value may have, one per tuple
/// shape it is a component of, the literal it is, if it is one, and the literals written in
/// it, by component, if it is a tuple that holds one.
type Side<'a> = (Vec<&'a Ty>, Option<&'a Lit>, Option<&'a [Part<'a>]>);

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
    ps: Option<&'a [Part<'a>]>,
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
                Some(Part::Branches(bs)) => Arg {
                    branches: Some(bs.clone()),
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

/// `a` where a value of `p` is expected: a literal without a suffix takes `p`'s one numeric
/// carrier, and one in a tuple the one carrier its component holds across `p`'s tuple shapes
/// of that length, at any depth (DESIGN.md L1.26, sec:domains): `(1, 2)` at
/// `(f64, f64) | (String, f64)` is `(1.0, 2.0)`. A literal written with a suffix takes no
/// other carrier, and where the expected type holds numbers but not its own carrier is
/// rejected ([`expected`]): `(1.0f64, 2.0f64)` at `(rat, rat)`. This is the one place an expected type decides a literal's carrier. Gives
/// `a`'s type with the adoptions and the adoptions, `None` when no literal adopts, and the
/// first literal that is rejected or is not exactly a value of its carrier, with the message.
///
/// The tuples nest as deep as the text, so the walk keeps its own stack: each open tuple's
/// parts, the argument's components, the expected shapes there, and the types so far. The
/// shapes are borrowed from `p`: no union of them is built.
///
/// When `rough` holds, as while a repair is tried, a decimal literal at `rat` takes the type
/// `rat`, and its adoption keeps the literal's own value: its digits are not read.
fn adopted(a: &Arg, p: &Ty, rough: bool) -> Result<Option<(Ty, Adoptions)>, (Span, Msg)> {
    let mut ads = Adoptions::new();
    let lit = |l: &Lit, want: &[&Ty], ads: &mut Adoptions| {
        let Some(c) = expected(l, want).map_err(|m| (l.site, m))? else {
            return Ok(None);
        };
        // Complexity tradeoff: reading a decimal's digits as a `rat` costs O(n^1.47) in its
        // length (COMPLEXITY.md K41), and a tried repair, `rat(n) + 0.5` for `n + 0.5` with
        // `n` an int, needs only whether the call checks. Typed `rat`, the literal is read in
        // O(n) ([`fits`] read its syntax); a repair whose check needs the literal's value, as
        // at a parameter that takes only positive numbers, is not offered.
        if rough && c == Carrier::Rat && lit_carrier(&l.value) == Carrier::F64 {
            ads.push((l.span, l.value.clone()));
            return Ok(Some(Ty::carrier(c)));
        }
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
    // The branches of an `if` of literals, `if c { 2 } else { 1 }`, each adopt as a lone
    // literal would, and the argument is the union of what they become: `2.0 | 1.0` at `f64`.
    // Complexity tradeoff: one adoption per branch, then the n singletons joined in pairs by
    // `Ty::union_all`, O(n log n); joining them one at a time costs O(n^2), since each union
    // copies the type so far. The naive form, the type `2 | 1` tested against the parameter,
    // fixes no literal and rejects the call. Tests:
    // `l01_26a_generic_literals::lit_branches::scaling`. A branch that is an operation on
    // literals alone, `if c { 2 + 1 } else { 1 }`, takes the carrier as the operation alone
    // would at the parameter ([`Ck::lit_args_take`]): each of its literals adopts it, which
    // rejects one that is not exactly a value of it, and the operation, folded at it
    // ([`folded`]), adopts its value whole, `3.0`. That walks each operation once, O(its
    // size), and an operation is the branch of one `if`.
    // The same holds for an `if` of literals written as a component of a tuple, at the
    // types its component has across the expected tuple shapes, as for a literal there.
    let branched = |ls: &[Branch], want: &[&Ty], ads: &mut Adoptions| {
        let from = ads.len();
        let mut ts = Vec::with_capacity(ls.len());
        for b in ls.iter() {
            let t = match b {
                Branch::Lit(l) => lit(l, want, ads)?.unwrap_or_else(|| lit_ty(&l.value, l.neg())),
                Branch::Op { e, value, lits, .. } => {
                    let mut each = Adoptions::new();
                    for l in lits.iter() {
                        lit(l, want, &mut each)?;
                    }
                    let at = each.first().map(|(_, v)| lit_carrier(v));
                    match at.and_then(|c| folded(e, c)) {
                        Some(v) => {
                            let t = Ty::lit(&v);
                            ads.push((e.span, v));
                            t
                        }
                        None => Ty::lit(value),
                    }
                }
            };
            ts.push(t);
        }
        Ok((ads.len() > from).then(|| Ty::union_all(&ts)))
    };
    if let Some(ls) = &a.branches {
        return Ok(branched(ls, &[p], &mut ads)?.map(|t| (t, ads)));
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
            Part::Branches(ls) => {
                let ws: Vec<&Ty> = ws.collect();
                let t = branched(ls, &ws, &mut ads)?.unwrap_or_else(|| c.clone());
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
    parts: &'a [Part<'a>],
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
/// ([`menu`]) when it cannot take `c`, being a decimal at `int` or written with a suffix, or is
/// not exactly a `c`.
fn adopt(l: &Lit, c: Carrier) -> Result<Option<Value>, Msg> {
    if lit_carrier(&l.value) == c || !c.numeric() {
        return Ok(None);
    }
    if !adoptable(l, c) {
        return Err(menu(l, &[c]));
    }
    let exact = match &l.value {
        Value::Float(_) => Rat::decimal(&l.text)
            .map_err(|r| Msg::from(unread_literal(&r)))?
            .map(Value::rat),
        v => run(Prim::CastRat, v),
    };
    let v = exact.and_then(|exact| match c {
        Carrier::Int => run(Prim::CastInt, &exact),
        Carrier::Rat => Some(exact),
        Carrier::F64 => run(Prim::CastF64, &exact),
        _ => None,
    });
    match v {
        Some(v) if !matches!(v, Value::Atom(_)) => Ok(Some(v)),
        _ => Err(menu(l, &[c])),
    }
}

/// Whether [`adopt`] takes `l` at `c`. A decimal literal without a suffix is exactly a
/// `rat` whenever its text reads as a number, so that case scans the text and reads none of
/// its digits: reading them is O(n^1.47) (COMPLEXITY.md K41), and a literal is tried at
/// every arrow and repair that holds `rat`. The digits are read when the literal adopts.
fn fits(l: &Lit, c: Carrier) -> bool {
    match lit_carrier(&l.value) == Carrier::F64 && c == Carrier::Rat {
        true => adoptable(l, c) && Rat::is_decimal(&l.text),
        false => adopt(l, c).is_ok(),
    }
}

/// Whether `l` may take the carrier `c`, leaving aside whether it is exactly a value of it: a
/// literal with no suffix any numeric carrier, but a decimal one never `int`, and a literal
/// written with a suffix only the carrier it names (DESIGN.md sec:domains, steps L1.26a and
/// L1.26b).
fn adoptable(l: &Lit, c: Carrier) -> bool {
    let own = lit_carrier(&l.value);
    c.numeric() && (c == own || l.bare && !(own == Carrier::F64 && c == Carrier::Int))
}

/// The literal `l` where a value of one of the types `want` is expected: the carrier it
/// takes there, `None` when it keeps its own, or the rejection. Of the numeric carriers the
/// types hold, it takes the ones it can be exactly: with none it is rejected with the forms
/// to write ([`menu`]); with one it takes that one; with two or more an integer literal is an
/// `int` where `int` is one of them, and is otherwise rejected, as a decimal one is, since
/// nothing chooses among them ([`no_one_carrier`]). A type that holds a variable or the
/// unknown could stand for any number, and decides nothing.
fn expected(l: &Lit, want: &[&Ty]) -> Result<Option<Carrier>, Msg> {
    if want.iter().any(|w| !w.vars.is_empty() || w.dynamic) {
        return Ok(None);
    }
    let held: Vec<Carrier> = [Carrier::Int, Carrier::Rat, Carrier::F64]
        .into_iter()
        .filter(|&c| want.iter().any(|w| !(&w.set & &c.ty()).is_empty()))
        .collect();
    if held.is_empty() {
        return Ok(None);
    }
    let takes: Vec<Carrier> = (held.iter().copied()).filter(|&c| fits(l, c)).collect();
    let own = lit_carrier(&l.value);
    match takes[..] {
        [] => Err(menu(l, &held)),
        [c] => Ok((c != own).then_some(c)),
        _ if own == Carrier::Int && takes.contains(&Carrier::Int) => Ok(None),
        _ => Err(no_one_carrier(
            l,
            &Ty::union_all(want.iter().copied()),
            &takes,
        )),
    }
}

/// Whether the declared types `ts` hold values and none of them a number: strings, `bool` or
/// tuples, with any atoms beside, so a number literal compared with one of their values is
/// never equal to it (A15). A type of atoms alone, or of no value, is left alone, as are a
/// variable and the unknown, which could stand for a number; a function, and every tuple or
/// struct as `(..)` and `{..}` write them, are left to the check that `==` takes data.
fn holds_no_number(ts: &[&Ty]) -> bool {
    let mut values = false;
    for t in ts {
        if t.dynamic || !t.vars.is_empty() || !t.fns.is_empty() {
            return false;
        }
        let u = t.set.universes();
        let numeric = [Carrier::Int, Carrier::Rat, Carrier::F64];
        if numeric.iter().any(|c| u.bases[c.base()]) {
            return false;
        }
        values |=
            u.bases[Carrier::Str.base()] || u.bases[Carrier::Bool.base()] || !t.tuples.is_empty();
    }
    values
}

/// The values of `t` at their carriers, without its atoms: each scalar widened to its whole
/// carrier, in tuple components too ([`Ty::carriers`]), so two types meet there when a value
/// of one may be compared with a value of the other, whatever values each holds. None where
/// `t` holds the unknown, a type variable or a function, which could be anything.
fn widened(t: &Ty) -> Option<Ty> {
    match t.dynamic || !t.vars.is_empty() || !t.fns.is_empty() {
        true => None,
        false => Some(t.without_atoms().carriers()),
    }
}

/// Whether a value of `t` may be compared with one of `other`, already [`widened`].
fn widened_meets(t: &Ty, other: &Ty) -> bool {
    widened(t).is_none_or(|t| t.meets(other))
}

/// Whether `==` between a value of `a` and one of `b` always gives the same answer: both hold
/// values other than atoms, and their carriers share none ([`widened`]). An atom on either
/// side, `x == #none`, is a value that side may be, compared as any other; a side that holds
/// only atoms is not judged here.
///
/// Complexity tradeoff: the naive check compares each arm of one side with each arm of the
/// other, carrier by carrier, recursing into tuple components pairwise: O(|a| · |b|). Here
/// each side is widened once in O(|a|) and O(|b|) ([`Ty::carriers`], memoized by shape), and
/// the widened types are met once ([`Ty::meets`]), which files the tuples of one side by their
/// components and compares each tuple of the other only with those filed near it (COMPLEXITY.md
/// F132): O(|a| + |b|) in all, at the cost of building the two widened types.
fn no_common_carrier(a: &Ty, b: &Ty) -> bool {
    match (widened(a), widened(b)) {
        (Some(a), Some(b)) => !a.is_empty() && !b.is_empty() && !a.meets(&b),
        _ => false,
    }
}

/// Whether the values of `t`, without its atoms, are all numbers, `int`, `rat` or `f64`.
fn only_numbers(t: &Ty) -> bool {
    let v = t.without_atoms();
    let u = v.set.universes();
    let numeric = [Carrier::Int, Carrier::Rat, Carrier::F64].map(|c| c.base());
    v.tuples.is_empty()
        && !u.rest
        && numeric.iter().any(|&i| u.bases[i])
        && (u.bases.iter().enumerate()).all(|(i, &b)| !b || numeric.contains(&i))
}

/// An operand of `==` that a message names as the program writes it.
#[derive(Clone, Copy)]
enum Operand<'e> {
    /// A name.
    Name(&'e str),
    /// A number or truth-value literal, with or without a `-` ([`is_literal`]), and the
    /// program's text, which writes it, where it is known.
    Literal(&'e Expr, Option<&'e str>),
}

impl fmt::Display for Operand<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (mut e, src) = match self {
            Operand::Name(n) => return f.write_str(n),
            Operand::Literal(e, src) => (*e, *src),
        };
        if let ExprKind::Unary(UnaryOp::Neg, a) = &e.kind {
            f.write_str("-")?;
            e = a;
        }
        // The literal as the program writes it, `1_000`, where its text is known; else as the
        // lexer reads it, without the `_`.
        if let Some(s) = src.and_then(|s| number_at(s, e.span)) {
            return f.write_str(s);
        }
        match &e.kind {
            ExprKind::Int { radix, digits } => {
                let prefix = match radix {
                    2 => "0b",
                    8 => "0o",
                    16 => "0x",
                    _ => "",
                };
                write!(f, "{prefix}{digits}")
            }
            ExprKind::Float { digits, forced } => {
                write!(f, "{digits}{}", if *forced { "f64" } else { "" })
            }
            ExprKind::Rat(digits) => write!(f, "{digits}r"),
            ExprKind::Bool(b) => write!(f, "{b}"),
            _ => unreachable!("an operand named as written is a literal ([`is_literal`])"),
        }
    }
}

/// Whether `e` is a number or truth-value literal, with or without a `-`, which a message
/// names as written ([`Operand::Literal`]).
fn is_literal(e: &Expr) -> bool {
    let e = match &e.kind {
        ExprKind::Unary(UnaryOp::Neg, a) => a,
        _ => e,
    };
    matches!(
        e.kind,
        ExprKind::Int { .. } | ExprKind::Float { .. } | ExprKind::Rat(_) | ExprKind::Bool(_)
    )
}

/// A place in a tuple, as the indices that reach it written `[0][1]`.
struct Place<'p>(&'p [usize]);

impl fmt::Display for Place<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.iter().try_for_each(|i| write!(f, "[{i}]"))
    }
}

/// The article, with the space after it, that a message writes before the text `text` of the
/// type `t`: none for a type of one value, as `true`, `3`, `"km"`, `#a`, `#a(1)` or
/// `(#a(1), 2)`, which the text names
/// as that value (`x` is `true`); `an ` before a type written with a vowel sound first,
/// `int`, `f64`, `(..)` not; `a ` else.
fn article_of(t: &Ty, text: &impl fmt::Display) -> &'static str {
    if t.is_one_value() {
        return "";
    }
    /// Keeps the first two characters written, then stops the writing.
    struct First(Vec<char>);
    impl fmt::Write for First {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            self.0.extend(s.chars().take(2 - self.0.len()));
            match self.0.len() {
                2 => Err(fmt::Error),
                _ => Ok(()),
            }
        }
    }
    let mut first = First(Vec::with_capacity(2));
    // The writing stops with an error once it has the two characters.
    let _ = fmt::write(&mut first, format_args!("{text}"));
    match first.0[..] {
        ['a' | 'e' | 'i' | 'o', ..] | ['f', '0'..='9', ..] => "an ",
        _ => "a ",
    }
}

/// A repair of an `==` whose operands share no value ([`Ck::apart`]): a cast by the word of
/// the operand at a side, 0 left and 1 right, or that operand's component at an index
/// compared in its place.
#[derive(Clone, Copy)]
enum Fix {
    Cast(usize, &'static str),
    Component(usize, usize),
}

/// Whether the literal `l` compared with a value of one of the types `cs` checks and may be
/// equal to it: they hold a number `l` can be, or a variable or the unknown, which could
/// stand for one.
fn takes_number(l: &Lit, cs: &[&Ty]) -> bool {
    let open = cs.iter().any(|c| c.dynamic || !c.vars.is_empty());
    let numbers = [Carrier::Int, Carrier::Rat, Carrier::F64]
        .into_iter()
        .any(|n| cs.iter().any(|c| !(&c.set & &n.ty()).is_empty()));
    (open || numbers) && expected(l, cs).is_ok()
}

/// A repair of a number literal compared with a value that holds no number
/// ([`Ck::never_equal`]): the literal written as text, the literal replaced by a `bool`, or
/// the other operand's component at an index compared in its place.
#[derive(Clone, Copy)]
enum Repair {
    Text,
    Bool(bool),
    Component(usize),
}

/// The text repair where the values of the universes `u` hold strings.
fn texts(u: &Universes) -> Vec<Repair> {
    match u.bases[Carrier::Str.base()] {
        true => vec![Repair::Text],
        false => Vec::new(),
    }
}

/// The two `bool` repairs where the values of the universes `u` hold `bool`.
fn bools(u: &Universes) -> Vec<Repair> {
    match u.bases[Carrier::Bool.base()] {
        true => vec![Repair::Bool(true), Repair::Bool(false)],
        false => Vec::new(),
    }
}

/// Writes the repairs of `groups`, each a list of repairs and what they do, as one list: the
/// repairs written by `form` and separated by `, `, the last by ` or `, and each group's
/// followed by what they do.
fn write_repairs<R: Copy>(
    f: &mut fmt::Formatter<'_>,
    groups: &[(Vec<R>, &str)],
    form: impl Fn(&mut fmt::Formatter<'_>, R) -> fmt::Result,
) -> fmt::Result {
    let total: usize = groups.iter().map(|(rs, _)| rs.len()).sum();
    let mut k = 0;
    for (rs, what) in groups {
        for &r in rs {
            if k > 0 {
                f.write_str(if k + 1 == total { " or " } else { ", " })?;
            }
            form(f, r)?;
            k += 1;
        }
        if !rs.is_empty() {
            write!(f, " {what}")?;
        }
    }
    Ok(())
}

/// The digits of the literal `l` as the lexer reads them, without its `-`, the `_` that
/// separate them and the suffix `f64`, from which its value is read.
fn lit_digits(l: &Lit) -> &str {
    l.text.strip_suffix("f64").unwrap_or(&l.text)
}

/// The digits of the literal `l` as the program writes them, with the `_` that separate them,
/// without its `-` and the suffix `f64`: what a fix that rewrites the literal prints.
fn spelled_digits(l: &Lit) -> &str {
    let s = l.spelling();
    s.strip_suffix("f64").unwrap_or(s)
}

/// The digits before the point of the decimal literal `l` when every digit after it is `0`
/// and it has no exponent, as `2` for `2.0`, as the program writes them, `1_000` for
/// `1_000.0`: the integer literal of the same value.
fn whole_part(l: &Lit) -> Option<&str> {
    let (_, frac) = lit_digits(l).split_once('.')?;
    let (whole, _) = spelled_digits(l).split_once('.')?;
    frac.bytes().all(|b| b == b'0').then_some(whole)
}

/// The empty span at the byte `at`, where a fix inserts text.
fn point(at: usize) -> Span {
    Span { start: at, end: at }
}

/// A fix of a rejected literal (DESIGN.md sec:diagnostics): the edits to the program's text,
/// each a span and the text written in its place, apart and in the order of the text; what
/// the program then holds; and the fix in a short form, for a message written without the
/// program's text. Each string is made in memory the system gives first ([`shown`]), since a
/// literal has no length limit.
struct Rewrite {
    edits: Vec<(Span, String)>,
    holds: String,
    alone: String,
}

impl Rewrite {
    /// The fix of the edits `edits`; `None` where the system refuses the memory for it.
    fn new(
        edits: &[(Span, &dyn fmt::Display)],
        holds: &dyn fmt::Display,
        alone: &dyn fmt::Display,
    ) -> Option<Rewrite> {
        let edits = (edits.iter())
            .map(|(s, w)| shown(w).map(|w| (*s, w)))
            .collect::<Result<_, _>>()
            .ok()?;
        Some(Rewrite {
            edits,
            holds: shown(&holds).ok()?,
            alone: shown(&alone).ok()?,
        })
    }

    /// The fix that writes `with` in place of the literal `l`, after its `-`.
    fn lit(l: &Lit, with: &dyn fmt::Display, holds: &dyn fmt::Display) -> Option<Rewrite> {
        let sign = if l.neg() { "-" } else { "" };
        Rewrite::new(&[(l.span, with)], holds, &format_args!("{sign}{with}"))
    }

    /// The lines of `source` that the edits touch, with each edit applied, without the
    /// whitespace at either end and without a comment after the line's last token: the
    /// corrected source line. The text after the last edit starts after a token, so it is
    /// lexed on its own; where that fails, as for a string or a block comment that the line
    /// opens and a later line closes, it is kept whole. `None` where an edit's span does not
    /// lie in `source` after the one before it, or where the system refuses the memory. It
    /// costs the length of those lines.
    fn line(&self, source: &str) -> Option<String> {
        let first = self.edits.first()?.0;
        let last = self.edits.last()?.0;
        let start = (source.get(..first.start)?.rfind('\n')).map_or(0, |i| i + 1);
        let end = (source.get(last.end..)?.find('\n')).map_or(source.len(), |i| last.end + i);
        let end = match lex(source.get(last.end..end)?) {
            Ok(tokens) => last.end + tokens.last().map_or(0, |t| t.span.end),
            Err(_) => end,
        };
        let mut parts = Vec::with_capacity(2 * self.edits.len() + 1);
        let mut at = start;
        for (s, with) in &self.edits {
            parts.push(source.get(at..s.start)?);
            parts.push(with);
            at = s.end;
        }
        parts.push(source.get(at..end)?);
        let mut line = shown(&fmt::from_fn(|f| {
            parts.iter().try_for_each(|p| f.write_str(p))
        }))
        .ok()?;
        line.truncate(line.trim_end().len());
        line.drain(..line.len() - line.trim_start().len());
        Some(line)
    }
}

/// An error as the checker finds it: its row of the rejection table if any, its span, its
/// message and fixes not yet written ([`Ck::reject`]), and its notes; and its number in the
/// order the checker found the errors in, which [`Ck::errors`] keeps.
struct Found {
    id: usize,
    row: Option<Row>,
    span: Span,
    m: Msg,
    notes: Vec<Note>,
    /// The places of the other literals of an error that reports several in one call
    /// ([`grouped`]): a fix of one of them, checked as written, rejects the others alone
    /// ([`Ck::pending_settled`]).
    also: Vec<Span>,
}

impl Found {
    /// The error with its message and menu written against `source`, the unit's text
    /// ([`Msg::written`]). A note that writes a repair, one that starts `repair:`, offers a
    /// fix too, so the message does not say that none is offered.
    fn written(mut self, source: Option<&str>) -> Error {
        if self.notes.iter().any(|n| n.text.starts_with("repair:")) {
            self.m.dropped = false;
        }
        let (message, menu) = self.m.written(source);
        Error {
            row: self.row,
            span: self.span,
            message,
            notes: self.notes,
            menu,
        }
    }
}

/// The message of a rejection and the fixes it offers, written out by [`Msg::written`].
pub(crate) struct Msg {
    text: String,
    fixes: Vec<Rewrite>,
    /// Whether fixes or repair notes were made and each was dropped as it does not check where
    /// it is written ([`Ck::fixes_checked`], [`Ck::pending_settled`]), so the message says that
    /// none is offered.
    dropped: bool,
}

impl From<String> for Msg {
    fn from(text: String) -> Msg {
        Msg {
            text,
            fixes: Vec::new(),
            dropped: false,
        }
    }
}

impl Msg {
    /// The message `text` with the fixes of `fixes` the system gave the memory for.
    fn new(text: String, fixes: Vec<Option<Rewrite>>) -> Msg {
        Msg {
            text,
            fixes: fixes.into_iter().flatten().collect(),
            dropped: false,
        }
    }

    /// The message and, apart from it, the menu of its fixes, which the diagnostic writes
    /// after the steps of its derivation (DESIGN.md sec:diagnostics). With `source`, the
    /// program's text, the menu is a heading line, then each fix as the corrected source line,
    /// followed by what the program then holds, one fix to a line:
    ///
    /// ```text
    ///   fixes, each checked here:
    ///     half = f64(1) / 2;    half is 0.5
    ///     half = 1.0f64 / 2;    half is 0.5
    ///     half = 1r / 2;        half is 1r/2r
    /// ```
    ///
    /// Without the text, or where a fix's span does not lie in it, the short forms end the
    /// headline, as `. Try `0.5f64` or `0.5r` instead.`, and the menu is empty. Written in
    /// memory the system gives first; where it refuses, the message alone and no menu. It costs
    /// the length of the message and of the lines the fixes touch. Where every fix the
    /// checker made was dropped, since none checks where it is written
    /// ([`Ck::fixes_checked`]), the message says that it offers none.
    fn written(mut self, source: Option<&str>) -> (String, String) {
        // A headline is a sentence and ends with a period, with a repair or without one
        // (DESIGN.md sec:diagnostics, "A short headline").
        if !self.text.ends_with('.') {
            self.text.push('.');
        }
        if self.fixes.is_empty() {
            let text = match self.dropped {
                true => {
                    let head = self.text.strip_suffix('.').unwrap_or(&self.text);
                    let text = shown(&format_args!(
                        "{head}. No fix is offered: each one the checker tried is rejected too."
                    ));
                    text.unwrap_or_else(|_| self.text.clone())
                }
                false => self.text,
            };
            return (text, String::new());
        }
        let lines = source.and_then(|s| {
            (self.fixes.iter())
                .map(|x| x.line(s))
                .collect::<Option<Vec<_>>>()
        });
        let written = match &lines {
            Some(lines) => {
                let last = |l: &str| l.rsplit('\n').next().unwrap_or(l).chars().count();
                let width = lines.iter().map(|l| last(l)).max().unwrap_or(0) + 4;
                let menu = shown(&fmt::from_fn(|f| {
                    f.write_str("\n  fixes, each checked here:")?;
                    for (l, x) in lines.iter().zip(&self.fixes) {
                        for part in l.split('\n') {
                            write!(f, "\n    {}", part.trim_end())?;
                        }
                        let pad = width - last(l);
                        // Not a width in the format, which takes at most 2^16 - 1.
                        (0..pad).try_for_each(|_| fmt::Write::write_char(f, ' '))?;
                        f.write_str(&x.holds)?;
                    }
                    Ok(())
                }));
                // The headline ends with the first fix, the corrected source line in full,
                // where it is one line (DESIGN.md sec:diagnostics, "A short headline").
                let first = lines[0].trim().trim_end_matches([';', ',']);
                let text = (!first.contains('\n')).then(|| {
                    let head = self.text.strip_suffix('.').unwrap_or(&self.text);
                    format!("{head}. Try `{first}` instead.")
                });
                menu.map(|menu| (text, menu))
            }
            None => shown(&fmt::from_fn(|f| {
                let head = self.text.strip_suffix('.').unwrap_or(&self.text);
                write!(f, "{head}. Try ")?;
                let n = self.fixes.len();
                for (i, x) in self.fixes.iter().enumerate() {
                    let sep = match i {
                        0 => "",
                        _ if i + 1 == n => " or ",
                        _ => ", ",
                    };
                    write!(f, "{sep}`{}`", x.alone)?;
                }
                f.write_str(" instead.")
            }))
            .map(|text| (Some(text), String::new())),
        };
        match written {
            Ok((text, menu)) => (text.unwrap_or(self.text), menu),
            Err(_) => (self.text, String::new()),
        }
    }
}

/// The one message `head` for the rejections `parts` of literals in one construct, two or
/// more, each its place and its message, in the order of the text: literals that nothing
/// gives a carrier in the value of a binding, the arguments of a call or the holes of a
/// string (step L1.26b), or literal arguments of one call at carriers they cannot take. The
/// head counts the parts; each part's own message is a step at its place; and each fix makes
/// the fix of that rank of every part at once, `y = (0.5f64, 0.25f64);    y[0] is 0.5; y[1]
/// is 0.25`, which checks since the parts are apart. A part with fewer fixes than another
/// leaves the fixes it lacks out, and a part with none, as the decimal `0.5` at an `int`, has
/// only its step, so `k(1.0f64, 0.5)` at `(rat, int)` offers `k(1.0, 0.5)` with `0.5` still
/// named. What a fix holds is written once where the parts before it hold the same; an edit
/// two parts make alike is made once, and a fix whose edits of two parts overlap otherwise
/// is left out.
///
/// Complexity tradeoff: the naive way, one message for each part, quotes the line once per
/// message and rewrites it once per fix, so `n` decimals on one line of length `O(n)` give
/// `Θ(n²)` bytes. One message shows each line once for all its steps (the diagnostic's
/// layout), and each fix rewrites the line once, so the bytes are linear in the parts and
/// the line. The edits of a fix are sorted once, O(e log e) for `e` edits.
fn grouped(head: String, parts: Vec<(Span, Msg)>) -> (Msg, Vec<Note>) {
    let n = parts.len();
    let ranks = (parts.iter().map(|(_, m)| m.fixes.len()))
        .filter(|&k| k > 0)
        .min()
        .unwrap_or(0);
    let mut fixes: Vec<Rewrite> = (0..ranks)
        .map(|_| Rewrite {
            edits: Vec::new(),
            holds: String::new(),
            alone: String::new(),
        })
        .collect();
    let mut held: Vec<String> = vec![String::new(); ranks];
    let mut notes = Vec::with_capacity(n);
    for (at, m) in parts {
        for (k, x) in m.fixes.into_iter().take(ranks).enumerate() {
            fixes[k].edits.extend(x.edits);
            if x.holds != held[k] {
                let sep = if fixes[k].holds.is_empty() { "" } else { "; " };
                fixes[k].holds.push_str(sep);
                fixes[k].holds.push_str(&x.holds);
                held[k] = x.holds;
            }
            let sep = if fixes[k].alone.is_empty() {
                ""
            } else {
                "`, `"
            };
            fixes[k].alone.push_str(sep);
            fixes[k].alone.push_str(&x.alone);
        }
        notes.push(Note {
            span: at,
            text: m.text,
        });
    }
    // The edits in the order of the text, as a corrected line writes them ([`Rewrite::line`]).
    for x in &mut fixes {
        x.edits.sort_by_key(|(s, _)| (s.start, s.end));
        x.edits.dedup();
    }
    fixes.retain(|x| x.edits.windows(2).all(|w| w[0].0.end <= w[1].0.start));
    let dropped = ranks > 0 && fixes.is_empty();
    (
        Msg {
            text: head,
            fixes,
            dropped,
        },
        notes,
    )
}

/// The message `head` about the literal `l`, then `why`. `head` is given the words "the
/// literal" and the literal as the program writes it, in memory the system gives first
/// ([`quoting`]); when it refuses, the words "this literal" in their place.
fn literal_message(
    l: &Lit,
    head: impl Fn(&mut dyn fmt::Write, &dyn fmt::Display) -> fmt::Result,
    why: &str,
) -> String {
    quoting(
        &fmt::from_fn(|f| {
            head(f, &format_args!("the literal `{}`", l.written()))?;
            f.write_str(why)
        }),
        || {
            let mut m = String::new();
            let _ = head(&mut m, &"this literal");
            m + why
        },
    )
}

/// The carriers `cs` written as a type, `int` or `f64 | rat`.
fn carrier_names(cs: &[Carrier]) -> String {
    carriers_text(cs.iter().copied())
}

/// The value of the literal `l`, with its `-`, at the carrier `c`; `None` where it is not
/// exactly a value of `c`, or is a decimal at `int`. A decimal's digits are read at `rat`,
/// which costs O(n^1.47) in their number (COMPLEXITY.md K41).
fn lit_value(l: &Lit, c: Carrier) -> Option<Value> {
    let v = match (lit_carrier(&l.value), c) {
        (own, c) if own == c => l.value.clone(),
        (Carrier::F64, Carrier::Rat) => Value::rat(Rat::decimal(lit_digits(l)).ok()??),
        (Carrier::Int, Carrier::F64) => run(Prim::CastF64, &l.value)?,
        (Carrier::Int, Carrier::Rat) => run(Prim::CastRat, &l.value)?,
        _ => return None,
    };
    (!matches!(v, Value::Atom(_))).then(|| neg_value(&v, l.neg()))
}

/// What the literal `l` is once a fix writes it with the carrier `c`, for a fix with no
/// binder to name: `the literal is then the f64 0.5`, or `exactly 0.5, a rat`. A `rat` is
/// named by the literal's own digits, with its `-` and without its suffix, which it is
/// exactly, so none are read.
fn lit_holds(l: &Lit, c: Carrier) -> impl fmt::Display + '_ {
    let sign = if l.neg() { "-" } else { "" };
    let d = spelled_digits(l);
    fmt::from_fn(move |f| match c {
        Carrier::F64 => match lit_value(l, c) {
            Some(v) => write!(f, "the literal is then the f64 {v}"),
            None => write!(f, "the literal is then the f64 nearest {sign}{d}"),
        },
        Carrier::Rat => write!(f, "the literal is then exactly {sign}{d}, a rat"),
        c => write!(f, "the literal is then the {} {sign}{d}", c.name()),
    })
}

/// What the name `n`, bound to the operation on literals `e`, holds once a fix gives its
/// literals the carrier `c`: `half is 0.5` ([`folded`]), or `half is an f64` where the
/// operation gives no value of `c`.
fn binder_holds<'a>(n: impl fmt::Display + 'a, e: &Expr, c: Carrier) -> impl fmt::Display + 'a {
    let v = folded(e, c);
    fmt::from_fn(move |f| match &v {
        Some(v) => write!(f, "{n} is {v}"),
        None => write!(f, "{n} is {} {}", article(c), c.name()),
    })
}

/// The value of `e`, an operation on literals alone under `+`, `-`, `*`, `/`, `^` and a `-`, or
/// a comparison of two of them ([`unfixed_binding`]), with every literal at the carrier `c`: a
/// fix that gives one of them that carrier gives it to all. The literals are folded as A54
/// permits, each operation by the kernel's one evaluator ([`eval()`]); the checker runs no code
/// of the program. `None` where a literal is not exactly a `c` or an operation gives an atom,
/// as `1 / 0`. The walk keeps its own stack, since the operations nest as deep as the text;
/// it costs one operation per node of `e`, and the reading of its literals ([`lit_value`]).
fn folded(e: &Expr, c: Carrier) -> Option<Value> {
    enum Step<'e> {
        Visit(&'e Expr),
        Apply(Prim, usize),
    }
    let mut todo = vec![Step::Visit(e)];
    let mut values: Vec<Value> = Vec::new();
    while let Some(step) = todo.pop() {
        match step {
            Step::Visit(x) => {
                if let Some(l) = literal(x, None) {
                    values.push(lit_value(&l, c)?);
                    continue;
                }
                match &x.kind {
                    ExprKind::Binary(op, a, b) => {
                        let p = binary_prim(*op)?;
                        todo.extend([Step::Apply(p, 2), Step::Visit(b), Step::Visit(a)]);
                    }
                    ExprKind::Unary(UnaryOp::Neg, a) => {
                        todo.extend([Step::Apply(Prim::Neg, 1), Step::Visit(a)]);
                    }
                    // A `rat` literal, `2r`, is a value of `rat` alone.
                    ExprKind::Rat(d) if c == Carrier::Rat => {
                        values.push(Value::rat(Rat::decimal(d).ok()??));
                    }
                    _ => return None,
                }
            }
            Step::Apply(p, n) => {
                let args = values.split_off(values.len().checked_sub(n)?);
                values.push(prim_folded(p, args)?);
            }
        }
    }
    values.pop()
}

/// The kernel's operation for the operator `op` where [`folded`] folds it: the arithmetic
/// operators and the comparisons.
fn binary_prim(op: BinaryOp) -> Option<Prim> {
    Some(match op {
        BinaryOp::Add => Prim::Add,
        BinaryOp::Sub => Prim::Sub,
        BinaryOp::Mul => Prim::Mul,
        BinaryOp::Div => Prim::Div,
        BinaryOp::Pow => Prim::Pow,
        BinaryOp::Eq => Prim::Eq,
        BinaryOp::Ne => Prim::Ne,
        BinaryOp::Lt => Prim::Lt,
        BinaryOp::Le => Prim::Le,
        BinaryOp::Gt => Prim::Gt,
        BinaryOp::Ge => Prim::Ge,
        BinaryOp::Or | BinaryOp::And | BinaryOp::Concat | BinaryOp::IntDiv | BinaryOp::Mod => {
            return None;
        }
    })
}

/// The operation `p` on the values `args` by the kernel's one evaluator ([`eval()`]), as
/// [`folded`] folds it: `None` where it gives an atom, as `1 / 0` does.
fn prim_folded(p: Prim, args: Vec<Value>) -> Option<Value> {
    let v = eval(&Term::Prim(p, args.into_iter().map(Term::Lit).collect())).ok()?;
    (!matches!(v, Value::Atom(_))).then_some(v)
}

/// What an operation on literals alone is at one carrier ([`Ck::lit_fit`]): its value there,
/// as [`folded`] gives it; whether it holds a `/`; whether it holds a `^`; and
/// the first of its literals that is not exactly a value of the carrier.
#[derive(Clone)]
struct LitFit {
    value: Option<Value>,
    div: bool,
    pow: bool,
    refused: Option<Lit>,
}

/// The literal `l` written with the carrier `c`: with its suffix, `0.5f64`, `1.0f64` or
/// `0.5r`, where it is written in decimal digits, and otherwise in a cast, `f64(0xFF)`, since
/// a literal in another base takes no suffix.
fn with_carrier(l: &Lit, c: Carrier) -> impl fmt::Display + '_ {
    let decimal = lit_carrier(&l.value) == Carrier::F64;
    let digits = decimal || lit_digits(l).bytes().all(|b| b.is_ascii_digit());
    let d = spelled_digits(l);
    fmt::from_fn(move |f| match (digits, c) {
        (true, Carrier::Rat) => write!(f, "{d}r"),
        (true, _) if decimal => write!(f, "{d}f64"),
        (true, _) => write!(f, "{d}.0f64"),
        (false, c) => write!(f, "{}({d})", c.name()),
    })
}

/// The message for the literal `l` where a number of one of the carriers `held` is expected,
/// one or more, none of which it can take: a decimal literal at `int`, which a decimal never
/// is; a literal written with the suffix `f64` at other carriers, since the suffix fixes its
/// carrier; or an integer literal at a format that holds no value equal to it, as
/// `9007199254740993` at `f64` (DESIGN.md sec:domains). Zed converts no value, so the literal
/// is rejected, with the fixes that write a literal of the same number instead: the integer
/// literal where `int` is expected and a decimal without a suffix has only zeros after its point, the `r`
/// form where `rat` is, and at `f64`, for an integer, the nearest `f64` as an integer
/// literal, by ties to even.
fn menu(l: &Lit, held: &[Carrier]) -> Msg {
    let names = carrier_names(held);
    let has = |c: Carrier| held.contains(&c);
    let sign = if l.neg() { "-" } else { "" };
    let mut fixes = Vec::new();
    if lit_carrier(&l.value) == Carrier::Int {
        let nearest = Some(lit_digits(l))
            .filter(|d| has(Carrier::F64) && d.bytes().all(|b| b.is_ascii_digit()))
            .and_then(|d| literal_f64(d).ok());
        if let Some(x) = nearest {
            let v = neg_value(&Value::float(x), l.neg());
            fixes.push(Rewrite::lit(
                l,
                &format_args!("{x:.0}"),
                &format_args!("the literal is then {v}, the nearer f64 by ties to even"),
            ));
        }
        // The reason, that an integer literal takes a carrier only where it is exact, is the
        // derivation's first note.
        let m = literal_message(l, |f, w| write!(f, "No `{names}` equals {w}"), "");
        return Msg::new(m, fixes);
    }
    // Only a decimal without a suffix: `2.0f64` without its suffix is `2.0`, which is never
    // an `int`, so a forced literal at `int` is offered nothing (DESIGN.md sec:diagnostics, row
    // "Two numeric values with no common carrier").
    if l.bare
        && has(Carrier::Int)
        && let Some(whole) = whole_part(l)
    {
        fixes.push(Rewrite::lit(
            l,
            &whole,
            &format_args!("the literal is then the int {sign}{whole}"),
        ));
    }
    if l.bare {
        let even = match fixes.is_empty() {
            true => "",
            false => ", even with an integer value",
        };
        let m = literal_message(
            l,
            |f, w| write!(f, "A decimal literal is never an `{names}`{even}: {w}"),
            "",
        );
        return Msg::new(m, fixes);
    }
    if has(Carrier::Rat) {
        // The same literal without its suffix first, `1.5` for `1.5f64` beside a `rat`: a
        // decimal literal without a suffix is exactly a `rat` (DESIGN.md sec:diagnostics, row
        // "Two numeric values with no common carrier"); then the `r` form, `1.5r`.
        let holds = lit_holds(l, Carrier::Rat);
        fixes.push(Rewrite::lit(l, &spelled_digits(l), &holds));
        fixes.push(Rewrite::lit(l, &with_carrier(l, Carrier::Rat), &holds));
    }
    let m = literal_message(
        l,
        |f, w| write!(f, "The suffix makes {w} an `f64`, never `{names}`"),
        "",
    );
    Msg::new(m, fixes)
}

/// The message for the decimal literal `l` beside an operand of carrier `int` of the operator
/// `what`, as in `x * 2.0` with `x: int` (DESIGN.md sec:diagnostics, the worked example at an
/// operator). `name` is the operand's name and span where it is a name, and `op` the
/// operator's symbol and whether the literal is its left operand. Where both are known, the
/// fixes rewrite the operation: `x * 2` where the literal's value is an integer and the
/// operator has an arrow at `int`, then `rat(x) * 2.0`; otherwise the fix is the integer literal
/// alone, `2`. With `exact`, where the checker proves the operand lies within ±2^53, also
/// `f64(x) * 2.0` ([`f64_cast_fix`]). The headline shows the operation as code with the
/// operand's type.
fn decimal_at_int(
    l: &Lit,
    what: &str,
    name: Option<(&str, Span)>,
    op: Option<(BinaryOp, bool)>,
    exact: bool,
) -> Msg {
    let sign = if l.neg() { "-" } else { "" };
    let lit = l.written();
    let mut fixes = Vec::new();
    match (name, op) {
        (Some((n, at)), Some((op, left))) => {
            if op != BinaryOp::Div
                && let Some(w) = whole_part(l)
            {
                let alone = fmt::from_fn(|f| match left {
                    true => write!(f, "{sign}{w} {op} {n}"),
                    false => write!(f, "{n} {op} {sign}{w}"),
                });
                fixes.push(Rewrite::new(
                    &[(l.span, &w)],
                    &format_args!("{sign}{w} takes the int of {n}"),
                    &alone,
                ));
            }
            // The cast of the operand to `rat`, which a decimal literal takes (DESIGN.md L1.26b)
            // and which takes `+`, `-`, `*`, `/` and the orderings at two of it. `f64(x)` only
            // where `exact` holds, since it is inexact above 2^53 in magnitude: a repair never
            // narrows a type (DESIGN.md sec:diagnostics).
            let alone = fmt::from_fn(|f| match left {
                true => write!(f, "{lit} {op} rat({n})"),
                false => write!(f, "rat({n}) {op} {lit}"),
            });
            fixes.push(Rewrite::new(
                &[(point(at.start), &"rat("), (point(at.end), &")")],
                &format_args!("{n} is cast to rat, and {what} takes two rat"),
                &alone,
            ));
            if exact {
                fixes.push(f64_cast_fix(l, n, at, op, left));
            }
        }
        _ => fixes.extend(whole_part(l).map(|w| {
            Rewrite::lit(
                l,
                &w,
                &format_args!("the literal is then the int {sign}{w}"),
            )
        })),
    }
    // The operation as code with the type of the operand, `x : int * 2.0`.
    let m = quoting(
        &fmt::from_fn(|f| match (name, op) {
            (Some((n, _)), Some((op, true))) => write!(
                f,
                "A decimal literal is never an `int`: `{lit} {op} {n} : int`."
            ),
            (Some((n, _)), Some((op, false))) => write!(
                f,
                "A decimal literal is never an `int`: `{n} : int {op} {lit}`."
            ),
            _ => write!(
                f,
                "A decimal literal is never an `int`: `{lit}` meets {what}, which expects \
                 `int`."
            ),
        }),
        || format!("A decimal literal is never an `int`, and {what} expects `int`."),
    );
    Msg::new(m, fixes)
}

/// The fix that casts the operand `n`, at `at`, to `f64` beside the decimal literal `l` of the
/// operator `op`, `f64(n) * 2.0` or `f64(n) + 1.5f64`, where `l` is the left operand when
/// `left` holds. Offered only where the checker proves `n` lies within ±2^53, where the cast is
/// exact (DESIGN.md "Casts are domain proofs"); `op` is an arithmetic operator or an ordering,
/// each of which has an arrow at two `f64`.
fn f64_cast_fix(l: &Lit, n: &str, at: Span, op: BinaryOp, left: bool) -> Option<Rewrite> {
    let lit = l.written();
    let alone = fmt::from_fn(|f| match left {
        true => write!(f, "{lit} {op} f64({n})"),
        false => write!(f, "f64({n}) {op} {lit}"),
    });
    Rewrite::new(
        &[(point(at.start), &"f64("), (point(at.end), &")")],
        &format_args!("{n} is cast to f64, exactly, since it lies within ±2^53"),
        &alone,
    )
}

/// The message for the literal `l`, which nothing gives a carrier, of the carriers `cs` that
/// what it meets takes, two or more and no `int`: a decimal literal alone (`y = 0.1`), a
/// decimal or an integer literal in an operation on literals alone (`y = 0.5 * 2`,
/// `half() = 1 / 2`), or a call of a generic function with literal arguments only
/// (`y = inc(x: 2.5)`). The fixes write the literal with each carrier, `0.1f64` or `0.1r`,
/// and for an integer `1.0f64` or `1r`; an integer literal in another base takes no suffix,
/// so it is written in a cast, `f64(0xFF)` or `rat(0xFF)`. With `bound`, the name the value
/// `e` is bound to, each fix names the value that name then holds, `y is 0.1`; otherwise the
/// literal's.
fn unfixed(l: &Lit, cs: &[Carrier], bound: Option<(&str, &Expr)>) -> Msg {
    let decimal = lit_carrier(&l.value) == Carrier::F64;
    let sign = if l.neg() { "-" } else { "" };
    let mut fixes = Vec::new();
    let carriers = [Carrier::F64, Carrier::Rat].into_iter();
    for c in carriers.filter(|&c| cs.contains(&c) && (c != Carrier::Rat || !decimal || l.bare)) {
        let with = with_carrier(l, c);
        // The binding rewritten, `y = 0.1f64`, where the literal is the whole value.
        let alone = fmt::from_fn(|f| match bound {
            Some((n, e)) if literal(e, None).is_some() => write!(f, "{n} = {sign}{with}"),
            _ => write!(f, "{sign}{with}"),
        });
        fixes.push(match bound {
            Some((n, e)) => Rewrite::new(&[(l.span, &with)], &binder_holds(n, e, c), &alone),
            None => Rewrite::new(&[(l.span, &with)], &lit_holds(l, c), &alone),
        });
    }
    let names = carrier_names(cs);
    let m = match decimal {
        true => literal_message(l, |f, w| write!(f, "Nothing gives {w} a carrier"), ""),
        false => literal_message(
            l,
            |f, w| write!(f, "Nothing gives {w} a carrier of `{names}`"),
            "",
        ),
    };
    Msg::new(m, fixes)
}

/// The pairs of components that `==` compares in the tuple displays `a` and `b`, of one
/// shape, the components that are no tuple displays, in the order of the text; `None` where
/// the shapes differ. The walk keeps its own stack, since displays nest as deep as the text;
/// it costs the size of the displays.
fn paired<'e>(a: &'e Expr, b: &'e Expr) -> Option<Vec<(&'e Expr, &'e Expr)>> {
    let mut out = Vec::new();
    let mut todo = vec![(a, b)];
    while let Some((x, y)) = todo.pop() {
        match (&x.kind, &y.kind) {
            (ExprKind::Tuple(xs), ExprKind::Tuple(ys)) if xs.len() == ys.len() => {
                todo.extend(xs.iter().zip(ys).rev());
            }
            (ExprKind::Tuple(_), _) | (_, ExprKind::Tuple(_)) => return None,
            _ => out.push((x, y)),
        }
    }
    Some(out)
}

/// The `int` and `f64` literals of `e`, with or without a suffix, in the order of the text,
/// whether it holds a `rat` literal, `2r`, and whether it holds a `^`, where `e` is an
/// operation on literals alone under `+`, `-`, `*`, `^` and a `-`; `None` otherwise, and for
/// a `/`, whose rejection where nothing gives it a carrier is the `/`'s own, as it is walked
/// ([`Ck::apply`]). It costs the size of `e`.
fn literals_alone(e: &Expr, src: Option<&str>) -> Option<(Vec<Lit>, bool, bool)> {
    let mut out = Vec::new();
    let (mut rat, mut pow) = (false, false);
    let mut todo = vec![e];
    while let Some(x) = todo.pop() {
        if let Some(l) = literal(x, src) {
            out.push(l);
            continue;
        }
        match &x.kind {
            ExprKind::Rat(_) => rat = true,
            ExprKind::Binary(
                op @ (BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Pow),
                a,
                b,
            ) => {
                pow |= *op == BinaryOp::Pow;
                todo.extend([&**b, &**a]);
            }
            ExprKind::Unary(UnaryOp::Neg, a) => todo.push(a),
            _ => return None,
        }
    }
    Some((out, rat, pow))
}

/// The rejection of a comparison `a == b` or `a != b` of two tuple displays of one shape whose
/// components are operations on literals alone ([`literals_alone`]), where nothing gives a
/// carrier to a decimal in a pair of components that `==` compares: a pair of literals with
/// no suffix alone, one of them a decimal. As where the value is no tuple
/// ([`unfixed_binding`]), the first such decimal in the text is rejected, and each fix writes
/// it with a carrier and names the value `place` then holds (DESIGN.md sec:diagnostics, "The
/// value a fix names": the binder is named "where the binder's value is a literal or an
/// operation on literals"): in `y = (1, (2, 3)) == (1.0, (2r, 3))`, `y = (1, (2, 3)) ==
/// (1.0f64, (2r, 3)); y is true`. Each pair takes the carrier of its literals with a suffix,
/// the fixed decimal's among them, or `int` where it has none, and `==` is true where every
/// pair is equal; where the pairs' literals take no one carrier, the fix names the literal
/// instead ([`lit_holds`]). `None` for any other value, which [`unfixed_binding`] then reads.
/// It costs the size of `e` ([`folded`]).
fn unfixed_comparison(
    e: &Expr,
    place: &dyn fmt::Display,
    src: Option<&str>,
) -> Option<(Span, Msg)> {
    let ExprKind::Binary(op @ (BinaryOp::Eq | BinaryOp::Ne), a, b) = &e.kind else {
        return None;
    };
    let pairs = paired(a, b)?;
    if pairs.len() == 1 && std::ptr::eq(pairs[0].0, &**a) {
        return None;
    }
    // The literals of each pair, and whether it holds a `rat` literal; and whether a pair
    // with a `rat` literal holds a `^`.
    let mut rat_pow = false;
    let lits: Vec<(Vec<Lit>, Vec<Lit>, bool)> = (pairs.iter())
        .map(|(x, y)| {
            let ((xs, r, p), (ys, s, q)) = (literals_alone(x, src)?, literals_alone(y, src)?);
            rat_pow |= (r || s) && (p || q);
            Some((xs, ys, r || s))
        })
        .collect::<Option<_>>()?;
    // A comparison of tuples carries the carrier of a component into the operation on
    // literals alone it is compared with ([`Ck::lit_pairs`]): in
    // `y = (1 + 2, 0) == (3.0f64, 0)`, `1 + 2` is an `f64`, so each pair is folded at its
    // carrier below. But a `rat` reaches no `^`, which has no arrow at `rat`, so a value with
    // such a pair is left to [`unfixed_binding`].
    if rat_pow {
        return None;
    }
    let decimal = |l: &&Lit| l.bare && lit_carrier(&l.value) == Carrier::F64;
    let open = |(xs, ys, rat): &&(Vec<Lit>, Vec<Lit>, bool)| {
        !rat && xs.iter().chain(ys).all(|l| l.bare) && xs.iter().chain(ys).any(|l| decimal(&l))
    };
    // The components of `a` come before those of `b` in the text.
    let l = (lits
        .iter()
        .filter(open)
        .flat_map(|(xs, _, _)| xs)
        .find(decimal))
    .or_else(|| {
        lits.iter()
            .filter(open)
            .flat_map(|(_, ys, _)| ys)
            .find(decimal)
    })?;
    // Whether the two sides are equal once `l` is written with `c`.
    let equal = |c: Carrier| -> Option<bool> {
        let mut all = true;
        for ((x, y), (xs, ys, rat)) in pairs.iter().zip(&lits) {
            let mut at = rat.then_some(Carrier::Rat);
            for m in xs.iter().chain(ys) {
                let own = match m.site == l.site {
                    true => c,
                    false if m.bare => continue,
                    false => lit_carrier(&m.value),
                };
                if at.is_some_and(|k| k != own) {
                    return None;
                }
                at = Some(own);
            }
            let at = at.unwrap_or(Carrier::Int);
            let (u, v) = (folded(x, at)?, folded(y, at)?);
            all &= eval(&Term::Prim(Prim::Eq, vec![Term::Lit(u), Term::Lit(v)])).ok()?
                == Value::Bool(true);
        }
        Some(if *op == BinaryOp::Eq { all } else { !all })
    };
    let mut m = unfixed(l, &[], None);
    let sign = if l.neg() { "-" } else { "" };
    m.fixes = [Carrier::F64, Carrier::Rat]
        .into_iter()
        .filter_map(|c| {
            let with = with_carrier(l, c);
            let alone = format_args!("{sign}{with}");
            match equal(c) {
                Some(v) => {
                    Rewrite::new(&[(l.span, &with)], &format_args!("{place} is {v}"), &alone)
                }
                None => Rewrite::new(&[(l.span, &with)], &lit_holds(l, c), &alone),
            }
        })
        .collect();
    Some((l.site, m))
}

/// The literals of the operations on literals `roots` (a value, or the two sides of a
/// comparison) that a fix of [`unfixed_binding`] writes with a carrier, besides the literal at
/// `written`, in the order of the text. The checker carries a carrier across `+`, `-`, `*`,
/// `/` and the comparisons to an operation on literals alone ([`Ck::lit_op_meets`]), and from
/// outside into each literal of it, a `^` among them; but not across a `^`, whose exponent
/// need not have the carrier of its base, and `^` has no arrow that takes an `f64` and an
/// `int`. So where the literal written lies in one operand of a `^` and the other operand is
/// an operation, that operand's first literal is written too, and so on inside it: `1` in
/// `y = 2 ^ (1 + 1) / 2`, written `y = 2.0f64 ^ (1.0f64 + 1) / 2`. One walk down the path from
/// the root to each literal written, on its own stack, since the operations nest as deep as
/// the text: each node is on one path at most, so O(|e|), and O(k log k) to sort the k
/// literals it returns.
///
/// Complexity tradeoff: the naive test walks each operation to see whether a written literal
/// reaches it, O(|e| · depth), O(|e|²) for `((1 ^ 2) ^ 3) ^ …`; here only the operations on
/// the path to a written literal are visited, and the paths lie in disjoint operands.
fn unreached(roots: &[&Expr], written: Span, src: Option<&str>) -> Vec<Lit> {
    let holds = |x: &Expr, at: usize| x.span.start <= at && at < x.span.end;
    let mut out: Vec<Lit> = Vec::new();
    let mut todo: Vec<(&Expr, usize)> = (roots.iter())
        .filter(|r| holds(r, written.start))
        .map(|&r| (r, written.start))
        .collect();
    while let Some((x, at)) = todo.pop() {
        if literal(x, None).is_some() {
            continue;
        }
        match &x.kind {
            ExprKind::Binary(op, a, b) => {
                let (with, other) = match holds(a, at) {
                    true => (&**a, &**b),
                    false => (&**b, &**a),
                };
                todo.push((with, at));
                if *op == BinaryOp::Pow
                    && literal(other, None).is_none()
                    && let Some(l) = first_literal(other, src)
                {
                    todo.push((other, l.span.start));
                    out.push(l);
                }
            }
            ExprKind::Unary(UnaryOp::Neg, a) => todo.push((a, at)),
            _ => {}
        }
    }
    out.sort_by_key(|l| l.span.start);
    out
}

/// The first literal of `e` in the order of the text, down its left operands; it costs the
/// depth of that path.
fn first_literal(mut e: &Expr, src: Option<&str>) -> Option<Lit> {
    loop {
        if let Some(l) = literal(e, src) {
            return Some(l);
        }
        e = match &e.kind {
            ExprKind::Binary(_, a, _) | ExprKind::Unary(_, a) => a,
            _ => return None,
        };
    }
}

/// The rejection of the value `e` bound to the name `n` outside a function when nothing gives
/// its literals a carrier (DESIGN.md step L1.26b): `e` is literals with no suffix alone, under
/// `+`, `-`, `*`, `/`, `^` and a `-`, with a decimal among them or a `/`; with a `^` among them
/// the fixes give `f64` alone, since `^` has no arrow at `rat`. Each fix writes one literal
/// with a carrier ([`leaves_with`]), and the operators carry it to the rest, since an
/// operation on literals alone takes the carrier of what it meets ([`Ck::lit_op_meets`]): the
/// first decimal, which the message names ([`unfixed`]), `y = 0.5f64` and `y = 0.5r`, and
/// `y = 0.5f64 * (1 + 2)`; or else, for a `/` of integer literals, which is rejected at the
/// `/`, the first literal of the value (DESIGN.md sec:diagnostics, "A `/` of integer
/// literals": "the menu writes the carrier at the first literal of the value"):
/// `half = 1.0f64 / 2`, `half = 1r / 2` and `half = f64(1) / 2`, the suffixes first, as
/// DESIGN's menu for `q = (1 + 2) / (3 + 4)` lists them: `y = 1.0f64 + 7 / 2`. Where a carrier
/// written there would not reach the other operand of a `^` ([`unreached`]), the fix writes
/// the first literal of that operand too: `y = 2.0f64 ^ (1.0f64 + 1) / 2`. Each fix
/// names the value `n` then holds ([`folded`]). A comparison of two
/// such operations, `y = 1 == 1.0`, is taken too, at the top of `e` alone, since a comparison
/// gives a `bool`, which no operation here takes; it joins the carriers of its sides as the
/// operations do, and `y` then holds `true` or `false`. `None` for any other value. The walks
/// keep their own stacks, since the operations nest as deep as the text; they cost the size of
/// `e`, and the fixes the length of the line.
///
/// `e` is a part of the value of `n` ([`unfixed_parts`]): the whole value where `whole`, and
/// otherwise a component of a tuple or a payload of an atom in it, as `0.5` in
/// `y = (0.5, "a")`. Each fix names the value `place` then holds, `y[0] is 0.5`; a part is
/// named by its own text, not as the binding `y = …`, in the message and the short fixes.
fn unfixed_binding(
    e: &Expr,
    n: &str,
    place: &dyn fmt::Display,
    whole: bool,
    src: Option<&str>,
) -> Option<(Span, Msg)> {
    if let Some(r) = unfixed_comparison(e, place, src) {
        return Some(r);
    }
    let mut stack = match &e.kind {
        ExprKind::Binary(
            BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge,
            a,
            b,
        ) => vec![&**b, &**a],
        _ => vec![e],
    };
    let roots = stack.clone();
    let mut lits = Vec::new();
    let mut div = None;
    let mut pow = false;
    while let Some(x) = stack.pop() {
        match &x.kind {
            ExprKind::Binary(
                op
                @ (BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Pow),
                a,
                b,
            ) => {
                if *op == BinaryOp::Div && div.is_none() {
                    div = Some(x);
                }
                pow |= *op == BinaryOp::Pow;
                stack.extend([&**b, &**a]);
            }
            ExprKind::Unary(UnaryOp::Neg, a) if literal(x, None).is_none() => stack.push(a),
            _ => {
                let l = literal(x, src).filter(|l| l.bare)?;
                lits.push(l);
            }
        }
    }
    // `^` has no arrow at `rat`, so with a `^` in the value only `f64` checks.
    let forms = [
        Form::Suffix(Carrier::F64),
        Form::Suffix(Carrier::Rat),
        Form::Cast,
    ];
    let forms = forms
        .into_iter()
        .filter(|f| !pow || f.carrier() != Carrier::Rat);
    // The literals come in the order of the text: the stack takes the left operand first.
    let is_decimal = |l: &&Lit| lit_carrier(&l.value) == Carrier::F64;
    if let Some(l) = lits.iter().find(is_decimal) {
        let mut m = unfixed(l, &[], Some((n, e)));
        let forms = forms.filter(|f| *f != Form::Cast);
        let mut leaves = unreached(&roots, l.span, src);
        leaves.push(l.clone());
        leaves.sort_by_key(|l| l.span.start);
        m.fixes = forms
            .filter_map(|f| leaves_with(&leaves, f, place, whole.then_some(n), e, None))
            .collect();
        return Some((l.site, m));
    }
    let d = div?;
    let ExprKind::Binary(_, a, b) = &d.kind else {
        unreachable!("a `/`")
    };
    let two = lits.len() == 2 && literal(a, None).is_some() && literal(b, None).is_some();
    let why = match pow {
        false => "Nothing gives the integer literals a carrier, and `/` has none at `int`",
        true => {
            "Nothing gives the integer literals a carrier, `/` has none at `int`, and `^` none \
             at `rat`"
        }
    };
    // The value as code: the binding, `q = (1 + 2) / (3 + 4)`, where the value is the whole
    // of it, else the `/` in it.
    let text = |at: Span| src.and_then(|s| s.get(at.start..at.end));
    let m = quoting(
        &fmt::from_fn(|f| match (whole, text(e.span), text(d.span)) {
            (true, Some(v), _) => write!(f, "{why}: `{n} = {v}`."),
            (_, _, Some(v)) => write!(f, "{why}: `{v}` in the value of `{n}`."),
            _ => write!(f, "{why}, in the value of `{n}`."),
        }),
        || format!("{why}, in the value of `{n}`."),
    );
    // The first literal of the value, whose carrier reaches the rest ([`unreached`]), in a
    // cast, `f64(1)`; with the suffix, `1.0f64`, where each is written in decimal digits,
    // since otherwise that form is the cast; and at `rat`, but for a `^`.
    let mut leaves = unreached(&roots, lits[0].span, src);
    leaves.insert(0, lits[0].clone());
    let leaves = &leaves[..];
    let digits = (leaves.iter()).all(|p| lit_digits(p).bytes().all(|b| b.is_ascii_digit()));
    let forms = forms.filter(|f| digits || *f != Form::Suffix(Carrier::F64));
    // Without decimal digits both forms are casts, written `f64(0xFF)` then `rat(0xFF)`.
    let mut forms: Vec<Form> = forms.collect();
    if !digits {
        forms.sort_by_key(|f| *f != Form::Cast);
    }
    let divisor = literal(b, src).filter(|_| two);
    let bound = whole.then_some(n);
    let fixes =
        (forms.into_iter()).map(|f| leaves_with(leaves, f, place, bound, e, divisor.as_ref()));
    Some((d.span, Msg::new(m, fixes.collect())))
}

/// The type variables of a signature in sets that its needs tie together, each set marked
/// fixed where a value other than a literal with no suffix reaches it ([`Ck::unfixed_args`]):
/// a union-find by size with path halving.
#[derive(Default)]
struct VarSets {
    /// Each variable's number.
    ix: HashMap<Arc<str>, usize>,
    /// Each variable by its number.
    names: Vec<Arc<str>>,
    /// The number of the variable toward the root of each set.
    up: Vec<usize>,
    /// The size of each root's set.
    size: Vec<usize>,
    /// Whether each root's set is fixed.
    fixed: Vec<bool>,
    /// The place that first fixed each root's set ([`VarSets::fix_by`]), `0` for a fix from
    /// no one place.
    by: Vec<usize>,
    /// Whether two places fixed each root's set.
    many: Vec<bool>,
}

impl VarSets {
    /// The number of `v`, given one in a set of its own where it has none.
    fn id(&mut self, v: &Arc<str>) -> usize {
        if let Some(&i) = self.ix.get(v) {
            return i;
        }
        let i = self.up.len();
        self.ix.insert(v.clone(), i);
        self.names.push(v.clone());
        self.up.push(i);
        self.size.push(1);
        self.fixed.push(false);
        self.by.push(0);
        self.many.push(false);
        i
    }

    /// The root of the set of `i`.
    fn find(&mut self, mut i: usize) -> usize {
        while self.up[i] != i {
            self.up[i] = self.up[self.up[i]];
            i = self.up[i];
        }
        i
    }

    /// The sets of `a` and `b` made one, fixed where either was.
    fn union(&mut self, a: usize, b: usize) {
        let (a, b) = (self.find(a), self.find(b));
        if a == b {
            return;
        }
        let (big, small) = if self.size[a] < self.size[b] {
            (b, a)
        } else {
            (a, b)
        };
        self.up[small] = big;
        self.size[big] += self.size[small];
        match (self.fixed[big], self.fixed[small]) {
            (false, true) => {
                self.by[big] = self.by[small];
                self.many[big] = self.many[small];
            }
            (true, true) => {
                self.many[big] |= self.many[small] || self.by[big] != self.by[small];
            }
            _ => {}
        }
        self.fixed[big] |= self.fixed[small];
    }

    /// The set of `i` marked fixed, from no one place: for every literal.
    fn fix(&mut self, i: usize) {
        self.fix_by(i, 0);
    }

    /// The set of `i` marked fixed from the place `by`: for the literals that reach it from
    /// other places ([`VarSets::fixed_for`]); `0` is no one place, and fixes it for all.
    fn fix_by(&mut self, i: usize, by: usize) {
        let r = self.find(i);
        match self.fixed[r] {
            false => self.by[r] = by,
            true => self.many[r] |= self.by[r] != by || by == 0,
        }
        self.fixed[r] = true;
    }

    /// Whether the set of the root `r` is fixed for a literal that reaches it from the place
    /// `from`: by another place, or by none in particular.
    fn fixed_for(&self, r: usize, from: usize) -> bool {
        self.fixed[r] && (self.many[r] || self.by[r] != from)
    }

    /// The set of each variable of `t` marked fixed.
    fn fix_all(&mut self, t: &Ty) {
        let mut vs = Vars::default();
        t.vars_in(&mut vs);
        for v in &vs.order {
            let i = self.id(v);
            self.fix(i);
        }
    }
}

/// One step from a value to a part of it ([`value_parts`]).
#[derive(Clone, Copy)]
enum PartStep<'e> {
    /// The component `i` of a tuple display.
    Component(usize),
    /// The payload of the atom `#a`: its one item, `None`, or its item `i` of several.
    Item(&'e str, Option<usize>),
    /// The field `x` of the payload of the atom `#a`.
    Field(&'e str, &'e str),
}

/// The parts of a value written as tuple displays and atoms with a payload, nested in any
/// way: `(0.5, "a")`, `#bad(0.5)`, `#bad(x: (1, 0.5))`.
struct ValueParts<'e> {
    /// Each step from a part to one of its parts, with the step to that part, if any.
    steps: Vec<(Option<usize>, PartStep<'e>)>,
    /// Each part that is neither a tuple display nor an atom with a payload, with the step to
    /// it, in the order of the text; the whole value alone, with no step, where it is neither.
    leaves: Vec<(&'e Expr, Option<usize>)>,
}

/// The parts of the value `e`.
///
/// Complexity tradeoff: the naive way names each part by its path, written out as each part
/// is reached, which costs the depth at every part and the square of the depth over a deeply
/// nested tuple. Here each part keeps only the step to it and the step before that, so the
/// walk costs one step per node of the displays, linear in the size of `e`; a path is
/// written ([`ValueParts::place`]) only for a part that is rejected, at the cost of its
/// depth, the length of the name it writes. The walk keeps its own stack, since displays
/// nest as deep as the text.
fn value_parts(e: &Expr) -> ValueParts<'_> {
    let mut steps = Vec::new();
    let mut leaves = Vec::new();
    let mut todo = vec![(e, None)];
    while let Some((x, at)) = todo.pop() {
        let base = steps.len();
        match &x.kind {
            ExprKind::Tuple(items) => {
                steps.extend((0..items.len()).map(|i| (at, PartStep::Component(i))));
                let next = items.iter().enumerate().map(|(i, it)| (it, Some(base + i)));
                todo.extend(next.rev());
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                curry: false,
            } if matches!(callee.kind, ExprKind::Atom(_)) => {
                let ExprKind::Atom(a) = &callee.kind else {
                    unreachable!("an atom")
                };
                let one = positional.len() == 1;
                let items = (0..positional.len()).map(|i| PartStep::Item(a, (!one).then_some(i)));
                let fields = named.iter().map(|(x, _)| PartStep::Field(a, x));
                steps.extend(items.chain(fields).map(|s| (at, s)));
                // The fields come after the items, in the text and in `steps`; the stack takes
                // the last first.
                let k = positional.len();
                let fields = named
                    .iter()
                    .enumerate()
                    .map(|(i, (_, v))| (v, Some(base + k + i)));
                todo.extend(fields.rev());
                let items = positional.iter().enumerate();
                todo.extend(items.map(|(i, v)| (v, Some(base + i))).rev());
            }
            _ => leaves.push((x, at)),
        }
    }
    ValueParts { steps, leaves }
}

impl ValueParts<'_> {
    /// The name of the part the step `at` reaches in the value of `root`, the binder, or of
    /// an unnamed value where `root` is `None`. Along tuple components it is written as Zed
    /// indexes them, `y[0]` or `y[1][0]`; through the payload of an atom in words, `the
    /// payload of `#bad``, `component 1 of the payload of `#bad`` or `the field `x` of
    /// `#bad``; in an unnamed value `the value` or `component 0 of the value`. It costs the
    /// depth of the part.
    fn place<'p>(&'p self, root: Option<&'p str>, at: Option<usize>) -> impl fmt::Display + 'p {
        fmt::from_fn(move |f| {
            // The steps from the part back to the root.
            let mut path = Vec::new();
            let mut k = at;
            while let Some(i) = k {
                let (up, s) = self.steps[i];
                path.push(s);
                k = up;
            }
            let payload = path
                .iter()
                .position(|s| !matches!(s, PartStep::Component(_)));
            if let (None, Some(n)) = (payload, root) {
                f.write_str(n)?;
                for s in path.iter().rev() {
                    if let PartStep::Component(i) = s {
                        write!(f, "[{i}]")?;
                    }
                }
                return Ok(());
            }
            for s in &path[..payload.unwrap_or(path.len())] {
                if let PartStep::Component(i) = s {
                    write!(f, "component {i} of ")?;
                }
            }
            match payload.map(|k| path[k]) {
                Some(PartStep::Item(a, None)) => write!(f, "the payload of `#{a}`"),
                Some(PartStep::Item(a, Some(i))) => {
                    write!(f, "component {i} of the payload of `#{a}`")
                }
                Some(PartStep::Field(a, x)) => write!(f, "the field `{x}` of `#{a}`"),
                _ => f.write_str("the value"),
            }
        })
    }
}

/// The rejections of the value `e` bound to `n` outside a function, `_` where nothing names
/// it, when nothing gives the literals of a part of it a carrier ([`unfixed_binding`]): the
/// whole value, or each component of a tuple display and each payload of an atom in it, as
/// `0.5` in `y = (0.5, "a")` (DESIGN.md step L1.26b: an unfixed decimal is rejected wherever
/// it stands). Each rejection is the part, the place of the error and the message, in the
/// order of the text; each fix rewrites that part alone and names the value of its place,
/// `y[0] is 0.5`. `whole` is whether `e` is the whole value of `n`, not one component of a
/// tuple bound to several names. It costs the size of `e` ([`value_parts`]), and the fixes
/// the length of the line and the depth of each rejected part.
fn unfixed_parts(e: &Expr, n: &str, whole: bool, src: Option<&str>) -> Vec<(Span, Span, Msg)> {
    let parts = value_parts(e);
    let root = (n != "_").then_some(n);
    let mut out = Vec::new();
    for &(x, at) in &parts.leaves {
        let place = parts.place(root, at);
        if let Some((s, m)) = unfixed_binding(x, n, &place, whole && at.is_none(), src) {
            out.push((x.span, s, m));
        }
    }
    out
}

/// What a value ends in, one step down ([`Ck::tail_of`]).
enum Tail<'e> {
    /// A numeric literal.
    Lit(Lit),
    /// The branches of an `if`, or the one value of a block.
    Branches(Vec<&'e Expr>),
    /// The components of a tuple display, or the values of a block's `return` of several, with
    /// whether it is a block.
    Components(&'e [Expr], bool),
    /// The components of a tuple display that is indexed.
    Indexed(&'e [Expr]),
    /// The payload of an atom: its items, then its fields' values.
    Payload(Vec<&'e Expr>),
    /// A call of the declared function of this binder.
    Call(usize),
    /// None of these.
    None,
}

/// Whether `t` holds, at any depth of its tuples, some `f64` values but not every one, or
/// the payload of an atom: the type at a place holds a decimal literal that nothing gave a
/// carrier only if it does ([`Ck::unfixed_tails`]), since a literal in a payload is no
/// operand and nothing gives it one. The walk keeps its own stack, and reads each shared
/// row once.
fn decimal_alone(t: &Ty) -> bool {
    let f = Ty::carrier(Carrier::F64);
    let mut seen: HashSet<*const Ty> = HashSet::new();
    let mut todo = vec![t];
    while let Some(t) = todo.pop() {
        let s = Ty::set(t.set.clone()).meet(&f);
        if !t.payloads.is_empty() || (!s.is_empty() && !f.subtype(&s)) {
            return true;
        }
        for row in &t.tuples {
            if seen.insert(row.as_ptr()) {
                todo.extend(row.iter());
            }
        }
    }
    false
}

/// One way to write a literal with a carrier: in a cast to `f64`, `f64(1)`; or with the
/// suffix of the carrier, `1.0f64`, `0.5f64` or `1r`, which is a cast where the literal is
/// written in another base ([`with_carrier`]).
#[derive(Clone, Copy, PartialEq)]
enum Form {
    Cast,
    Suffix(Carrier),
}

impl Form {
    fn carrier(self) -> Carrier {
        match self {
            Form::Cast => Carrier::F64,
            Form::Suffix(c) => c,
        }
    }
}

/// The fix of the binding of a name to a value with the part `e` that writes each of the
/// literals `leaves` in the form `form`, naming the value `place` then holds
/// ([`binder_holds`]): `y is 0.5`, or `y[0] is 0.5` for a component. Its short form, for a
/// message written without the program's text, is the binding rewritten where `e` is the
/// whole value of `bound` and one literal, `y = 0.5f64`, or the division of two literals by
/// `divisor`, `half = f64(1) / 2`; otherwise each literal's new text and the literal it
/// replaces. It costs the length of those texts.
fn leaves_with(
    leaves: &[Lit],
    form: Form,
    place: &dyn fmt::Display,
    bound: Option<&str>,
    e: &Expr,
    divisor: Option<&Lit>,
) -> Option<Rewrite> {
    let c = form.carrier();
    let texts: Vec<_> = (leaves.iter())
        .map(|p| {
            let with = with_carrier(p, c);
            fmt::from_fn(move |f| match form {
                Form::Cast => write!(f, "f64({})", spelled_digits(p)),
                Form::Suffix(_) => write!(f, "{with}"),
            })
        })
        .collect();
    let edits: Vec<(Span, &dyn fmt::Display)> = (leaves.iter().zip(&texts))
        .map(|(p, t)| (p.span, t as &dyn fmt::Display))
        .collect();
    let alone = fmt::from_fn(|f| match (leaves, &texts[..]) {
        ([p], [t]) => {
            let sign = if p.neg() { "-" } else { "" };
            match (divisor, bound) {
                (Some(y), Some(n)) if y.site != p.site => {
                    write!(f, "{n} = {sign}{t} / {}", y.written())
                }
                (Some(y), None) if y.site != p.site => write!(f, "{sign}{t} / {}", y.written()),
                (_, Some(n)) if literal(e, None).is_some() => write!(f, "{n} = {sign}{t}"),
                _ => write!(f, "{sign}{t}"),
            }
        }
        // Each part is quoted: the message writes the short form between backticks.
        _ => {
            for (i, (p, t)) in leaves.iter().zip(&texts).enumerate() {
                let sep = if i == 0 { "" } else { "`, `" };
                write!(f, "{sep}{t}` for `{}", p.written())?;
            }
            Ok(())
        }
    });
    Rewrite::new(&edits, &binder_holds(place, e, c), &alone)
}

/// The literals of the other carriers that are exactly the number of `e` when `e` is a `rat`
/// literal, `k` or `-k` with `k` written `1r` or `0.5r`, each with its type and the repair
/// that writes it and the literal it writes, in the order of [`menu`]: the `f64` literal,
/// `1.0` or `0.5`, where the number is an `f64` exactly, then the `int` literal, `1`, where it
/// is written without a point; `None` when `e` is no `rat` literal. A repair writes the
/// literal's digits as `src`, the program's text, writes them, `1_000.0` for `1_000r`, where it is known. A literal has
/// no length limit, so a repair that quotes it is written in memory asked for first
/// ([`quoting`]).
fn rat_forms(e: &Expr, src: Option<&str>) -> Option<Vec<(Ty, Option<String>, String)>> {
    let (neg, inner) = match &e.kind {
        ExprKind::Unary(UnaryOp::Neg, a) => (true, &**a),
        _ => (false, e),
    };
    let ExprKind::Rat(digits) = &inner.kind else {
        return None;
    };
    let v = neg_value(&Value::rat(Rat::decimal(digits).ok()??), neg);
    let sign = if neg { "-" } else { "" };
    let point = digits.contains('.');
    let written = src.and_then(|s| number_at(s, inner.span));
    let digits = written.and_then(|w| w.strip_suffix('r')).unwrap_or(digits);
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
        let lit = shown(&format_args!("{sign}{digits}{suffix}")).ok();
        out.push((Ty::lit(&x), lit, text));
    }
    Some(out)
}

/// The message for the literal `l` where `want` holds numbers of the carriers `cs`, two or
/// more, each of which it can take and none of them `int`: nothing chooses one, so it is
/// rejected with a fix that writes the literal with each carrier, `1r` or `1.0f64`, `0.5r` or
/// `0.5f64` (DESIGN.md step L1.26). A literal written in another radix takes no suffix, so it
/// is written in a cast to each carrier, `rat(0xFF)` or `f64(0xFF)`.
fn no_one_carrier(l: &Lit, want: &Ty, cs: &[Carrier]) -> Msg {
    let carriers = [Carrier::Rat, Carrier::F64].into_iter();
    let fixes = (carriers.filter(|c| cs.contains(c)))
        .map(|c| Rewrite::lit(l, &with_carrier(l, c), &lit_holds(l, c)))
        .collect();
    let m = literal_message(
        l,
        |f, w| write!(f, "Nothing chooses one carrier of `{want}` for {w}"),
        "",
    );
    Msg::new(m, fixes)
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

/// An operator of an expression, binary or unary, as `op_sig` types it. It prints as the
/// operator is written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operator {
    /// An operator between two operands, `a + b`.
    Binary(BinaryOp),
    /// An operator before one operand, `-a` or `!a`.
    Unary(UnaryOp),
}

impl Operator {
    /// The text of the operator, as it is written.
    pub fn as_str(self) -> &'static str {
        match self {
            Operator::Binary(o) => o.as_str(),
            Operator::Unary(o) => o.as_str(),
        }
    }

    /// The operator that `what`, the label [`Ck::apply`] is given, names as `` `op` ``: the
    /// binary one where a symbol is both, `-`.
    fn of_label(what: &str) -> Option<Self> {
        let op = what.strip_prefix('`')?.strip_suffix('`')?;
        (BinaryOp::of_token(op).map(Operator::Binary))
            .or_else(|| UnaryOp::of_token(op).map(Operator::Unary))
    }
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// An operator's arrows.
fn op_sig(op: Operator) -> Sig {
    use Carrier::*;
    let same = |c: Carrier| Ty::carrier(c);
    let bool_ = |_| Ty::carrier(Bool);
    let div0 = |c: Carrier| Ty::carrier(c).union(&Ty::set(KType::atom("divByZero")));
    let (n, arrows) = match op {
        Operator::Binary(BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul) => {
            (2, arrows(&[Int, F64, Rat], 2, same))
        }
        Operator::Binary(BinaryOp::Div) => (
            2,
            [arrows(&[F64], 2, same), arrows(&[Rat], 2, div0)].concat(),
        ),
        Operator::Binary(BinaryOp::IntDiv | BinaryOp::Mod) => (2, arrows(&[Int], 2, div0)),
        // A `rat` takes an integer exponent of either sign, exactly; `0r` to a negative power
        // is `#divByZero`, which the walk drops where the base holds no `0r` or the exponent
        // is shown at least 0.
        Operator::Binary(BinaryOp::Pow) => (
            2,
            [
                arrows(&[Int, F64], 2, same),
                vec![Arrow {
                    params: vec![Ty::carrier(Rat), Ty::carrier(Int)],
                    result: div0(Rat),
                }],
            ]
            .concat(),
        ),
        Operator::Binary(BinaryOp::Concat) => (2, arrows(&[Str], 2, same)),
        // The order of the carriers, and whether two values may be equal: the operator makes
        // no atom. `==` and `!=` are checked by [`Ck::equal`]; these arrows say only what they
        // make.
        Operator::Binary(
            BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge,
        ) => (2, arrows(&[Int, F64, Rat, Str, Bool], 2, bool_)),
        Operator::Binary(BinaryOp::And | BinaryOp::Or) => (2, arrows(&[Bool], 2, bool_)),
        Operator::Unary(UnaryOp::Not) => (1, arrows(&[Bool], 1, bool_)),
        Operator::Unary(UnaryOp::Neg) => (1, arrows(&[Int, F64, Rat], 1, same)),
    };
    Sig {
        params: positional(n),
        arrows,
        bounds: BTreeMap::new(),
        data: false,
        dense: false,
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
        dense: false,
        word: Some(w.into()),
        needs: Vec::new(),
        own: BTreeSet::new(),
        held: BTreeSet::new(),
        named: 0,
        facts: Default::default(),
    })
}

/// The largest magnitude of the contiguous run of integers every one of which `f64` holds
/// exactly, 2^53 (DESIGN.md "Casts are domain proofs": "`f64(n)` is exact when `|n| ≤ 2^53`").
const F64_EXACT_INT: i64 = 1 << 53;

/// `f64`'s signature at an operand whose ints the checker proves lie within ±2^53: its arrow at
/// `int` gives no `#inexact`, since each such int has an exact `f64` (DESIGN.md "Casts are
/// domain proofs"). Its other arrows are those of [`word_sig`].
fn f64_of_exact_int_sig() -> Arc<Sig> {
    let mut sig = word_sig("f64");
    let int = Ty::carrier(Carrier::Int);
    for a in &mut Arc::make_mut(&mut sig).arrows {
        if a.params[0] == int {
            a.result = Ty::carrier(Carrier::F64);
        }
    }
    sig
}

/// The type of the bytes `utf8` gives and `fromUtf8` reads (step L1.39c): a family of ints keyed
/// by ints. The checker has no int-range types before step L10, so neither the keys
/// from 0 nor the bytes in `0 ..< 256` are stated here; the kernel gives `#badUtf8` for an int
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
        dense: false,
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

/// The integer operator `o`, with its interval transfer and its kernel primitive; `None` for
/// an operator with no `int` arithmetic, and for `^`, whose transfer takes its exponent.
fn int_op(o: BinaryOp) -> Option<(Op, Prim)> {
    match o {
        BinaryOp::Add => Some((Op::Add, Prim::Add)),
        BinaryOp::Sub => Some((Op::Sub, Prim::Sub)),
        BinaryOp::Mul => Some((Op::Mul, Prim::Mul)),
        BinaryOp::IntDiv => Some((Op::Div, Prim::IntDiv)),
        BinaryOp::Mod => Some((Op::Mod, Prim::Mod)),
        BinaryOp::Or
        | BinaryOp::And
        | BinaryOp::Eq
        | BinaryOp::Ne
        | BinaryOp::Lt
        | BinaryOp::Le
        | BinaryOp::Gt
        | BinaryOp::Ge
        | BinaryOp::Concat
        | BinaryOp::Div
        | BinaryOp::Pow => None,
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
            ExprKind::Unary(UnaryOp::Neg, a) => vec![&**a],
            ExprKind::Binary(o, a, b) if *o == BinaryOp::Pow || int_op(*o).is_some() => {
                vec![&**a, &**b]
            }
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
            ExprKind::Unary(UnaryOp::Neg, a) => {
                let a = self.memo(a);
                match a.value {
                    Some(v) => fold(Prim::Neg, vec![v]).unwrap_or_else(Known::top),
                    None => Known {
                        ints: a.ints.neg(),
                        value: None,
                    },
                }
            }
            ExprKind::Binary(BinaryOp::Pow, a, b) => {
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
            ExprKind::Binary(o, a, b) => match int_op(*o) {
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
// Naive version: each binder's set gathered by its own walk of the graph, O(B + R + E)
// unions per binder (inferred); used: one pass of Tarjan's algorithm, O(B + R + E) unions in all
// (COMPLEXITY.md rows F117 and F74, whose union-find this replaced).
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

/// The type of a port of `main` (L1.19): a `Lines` input is the family of its lines keyed
/// from 0, each a `String` or `#ioError(op:, path:, why:)`, and a `Files` input answers a path
/// with its text, `#notFound` or `#ioError(op:, path:, why:)`; a lookup outside the family's
/// keys is `#notFound` in its arrows, and `#outOfBounds` at a read `v[k]` of an `int`-keyed
/// port, whose keys are one interval, every key present ([`Sig::dense`]). A `CommandLine`
/// input (L1.19a) is the family of the arguments keyed from 0, each a `String`. `key` is the key's carrier and `io` whether a read can be
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
        dense: key == Carrier::Int,
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

/// A row or payload shape, as [`Ck::unbound`] walks them.
#[derive(Clone, Copy)]
enum Inner<'t> {
    Row(&'t ty::Row),
    Shape(&'t Shape),
}

impl<'t> Inner<'t> {
    /// The rows and payload shapes of `t` at its outer level that hold a variable.
    fn of(t: &'t Ty) -> impl Iterator<Item = Inner<'t>> {
        let rows = t.tuples.iter().filter(|r| r.holds_vars()).map(Inner::Row);
        let shapes = t.payloads.values().flatten().flatten();
        rows.chain(shapes.filter(|s| s.holds_vars()).map(Inner::Shape))
    }

    fn node(self) -> NodeId {
        match self {
            Inner::Row(r) => r.node(),
            Inner::Shape(s) => s.node(),
        }
    }

    /// Its components, and its fields.
    fn tys(self) -> impl Iterator<Item = &'t Ty> {
        let (items, fields) = match self {
            Inner::Row(r) => (r.iter(), None),
            Inner::Shape(s) => (s.items.iter(), Some(s.fields.values())),
        };
        items.chain(fields.into_iter().flatten())
    }
}

impl Ck<'_, '_> {
    /// `t` with its variables replaced by `binds`, and each that is not a class and `binds`
    /// leaves unbound by the unknown. Those are added to `binds` for the replacement and
    /// removed after it, so `binds` is as it was and each need costs the size of `t` and `log`
    /// of the size of `binds`, not a copy of `binds`; a row or shape of `t` that an earlier
    /// call found to hold only classes is not entered ([`Self::clean`]).
    fn bound(&mut self, t: &Ty, binds: &mut Binds) -> Ty {
        let add = self.unbound(t, binds);
        for v in &add {
            binds.insert(v.clone(), Ty::dynamic());
        }
        let out = t.replace(binds);
        for v in &add {
            binds.remove(v);
        }
        out
    }

    /// The variables of `t` at any depth that are not classes and that `binds` leaves unbound.
    /// Each row and payload shape that holds a variable and is not known to hold only classes
    /// is entered once, its parts before it, and is recorded in [`Self::clean`] if it holds
    /// only classes that last ([`Self::lasting`]): of the rows `p(s, v) = (s, (s, v))` called
    /// `n` times nests, the `k`th call's replay meets the `k` rows of `s`, which the call before
    /// recorded, so the calls cost `O(n)` in all and not `O(n^2)`.
    fn unbound(&mut self, t: &Ty, binds: &Binds) -> BTreeSet<Arc<str>> {
        let mut out = BTreeSet::new();
        self.outer_vars(t, binds, &mut out);
        // The parts in an order that puts each after the parts it holds.
        let mut seen = HashSet::new();
        let mut order = Vec::new();
        let mut stack: Vec<(Inner, bool)> = self.parts(t).map(|p| (p, false)).collect();
        while let Some((p, done)) = stack.pop() {
            if done {
                order.push(p);
                continue;
            }
            if !seen.insert(p.node()) {
                continue;
            }
            stack.push((p, true));
            for c in p.tys() {
                let new = self.parts(c).filter(|q| !seen.contains(&q.node()));
                stack.extend(new.map(|q| (q, false)));
            }
        }
        let mut found: HashMap<NodeId, bool> = HashMap::new();
        for p in order {
            let mut clean = true;
            for c in p.tys() {
                let outer = self.outer_vars(c, binds, &mut out);
                clean = clean && outer && self.parts(c).all(|q| found[&q.node()]);
            }
            found.insert(p.node(), clean);
        }
        #[cfg(debug_assertions)]
        self.check_clean(t, binds, &out);
        if self.gens.len() <= self.level {
            self.gens.resize(self.level + 1, 0);
        }
        let at = (self.level, self.gens[self.level]);
        for (n, _) in found.into_iter().filter(|&(_, clean)| clean) {
            let was = self.clean.insert(n, at);
            if self.trying {
                self.log.push(Undo::Clean(n, was));
            }
        }
        out
    }

    /// The rows and payload shapes of `t` at its outer level that hold a variable and are not
    /// known to hold only classes that last.
    fn parts<'t>(&self, t: &'t Ty) -> impl Iterator<Item = Inner<'t>> {
        Inner::of(t).filter(|p| !self.is_clean(p.node()))
    }

    /// Whether the row or shape `n` is known to hold only classes that last: it was found to
    /// at a level that has not ended since.
    fn is_clean(&self, n: NodeId) -> bool {
        self.clean
            .get(&n)
            .is_some_and(|&(l, g)| l <= self.level && self.gens.get(l) == Some(&g))
    }

    /// Adds to `out` the variables of `t` at its outer level, and in the functions it holds,
    /// that are not classes and that `binds` leaves unbound; gives whether each is a class that
    /// lasts.
    fn outer_vars(&self, t: &Ty, binds: &Binds, out: &mut BTreeSet<Arc<str>>) -> bool {
        let held = t.fns.iter().flat_map(|s| {
            let f = s.facts();
            f.classes.iter().chain(&f.names)
        });
        let mut all = true;
        for v in t.vars.iter().chain(held) {
            if self.lasting(v) {
                continue;
            }
            all = false;
            if !self.is_class(v) && !binds.contains_key(v) {
                out.insert(v.clone());
            }
        }
        all
    }

    /// Whether `v` is the variable of a class that stays one while the level now has not
    /// ended: its root is unnamed and of this level or one around it, and a root is named only
    /// when its level ends ([`Self::generalize`]), and a class's level only goes down.
    fn lasting(&self, v: &str) -> bool {
        class_id(v)
            .filter(|&k| k < self.classes.len())
            .is_some_and(|k| {
                let c = &self.classes[self.find(k)];
                c.name.is_none() && c.level <= self.level
            })
    }

    /// The check of [`Self::clean`] (debug builds, with `ZEDC_CHECK_CLEAN` naming a file; see
    /// [`clean_check`]): walks every row and shape of `t`, the memo ignored, and asserts that
    /// each one the memo holds holds only classes that last, at any depth, and that the walk
    /// finds the variables `out`, what [`Self::unbound`] found with the memo, holds. Called
    /// before `unbound` records what it found.
    #[cfg(debug_assertions)]
    fn check_clean(&self, t: &Ty, binds: &Binds, out: &BTreeSet<Arc<str>>) {
        if clean_check::path().is_none() {
            return;
        }
        let mut full = BTreeSet::new();
        self.outer_vars(t, binds, &mut full);
        let mut seen = HashSet::new();
        let mut order = Vec::new();
        let mut stack: Vec<(Inner, bool)> = Inner::of(t).map(|p| (p, false)).collect();
        while let Some((p, done)) = stack.pop() {
            if done {
                order.push(p);
                continue;
            }
            if !seen.insert(p.node()) {
                continue;
            }
            stack.push((p, true));
            for c in p.tys() {
                let new = Inner::of(c).filter(|q| !seen.contains(&q.node()));
                stack.extend(new.map(|q| (q, false)));
            }
        }
        let mut found: HashMap<NodeId, bool> = HashMap::new();
        let mut held = 0;
        for p in order {
            let mut clean = true;
            for c in p.tys() {
                let outer = self.outer_vars(c, binds, &mut full);
                clean = clean && outer && Inner::of(c).all(|q| found[&q.node()]);
            }
            if self.is_clean(p.node()) {
                held += 1;
                assert!(
                    clean,
                    "the memo of clean rows holds {:?}, which holds a variable that is not a \
                     lasting class",
                    p.node()
                );
            }
            found.insert(p.node(), clean);
        }
        assert_eq!(
            &full, out,
            "the walk with the memo of clean rows finds other variables than the walk without it"
        );
        clean_check::count(held);
    }
}

/// The check of the memo of rows that hold only lasting classes ([`Ck::clean`]), compiled only
/// in a debug build and run only when the environment variable `ZEDC_CHECK_CLEAN` names a
/// file: each [`Ck::unbound`] then also walks the whole type without the memo
/// ([`Ck::check_clean`]), and each check appends to the file a line with how many queries it
/// checked and how many rows and shapes it found in the memo.
#[cfg(debug_assertions)]
mod clean_check {
    use std::cell::Cell;
    use std::io::Write;
    use std::path::{Path, PathBuf};
    use std::sync::OnceLock;

    static PATH: OnceLock<Option<PathBuf>> = OnceLock::new();

    thread_local! {
        /// The queries checked and the rows and shapes found in the memo, since the last flush.
        static COUNTS: Cell<(u64, u64)> = const { Cell::new((0, 0)) };
    }

    /// The file the counts go to, if the check is on.
    pub(super) fn path() -> Option<&'static Path> {
        PATH.get_or_init(|| std::env::var_os("ZEDC_CHECK_CLEAN").map(PathBuf::from))
            .as_deref()
    }

    /// Counts one query, in which `held` rows and shapes were found in the memo.
    pub(super) fn count(held: u64) {
        COUNTS.with(|c| {
            let (q, h) = c.get();
            c.set((q + 1, h + held));
        });
    }

    /// Appends the counts since the last flush to the file, when the check is on.
    pub(super) fn flush() {
        let Some(p) = path() else { return };
        let (q, h) = COUNTS.replace((0, 0));
        let mut f = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(p)
            .unwrap_or_else(|e| panic!("{}: {e}", p.display()));
        writeln!(f, "queries {q} held {h}").unwrap_or_else(|e| panic!("{}: {e}", p.display()));
    }
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
    denoted_free(t, leaves, &HashSet::new())
}

/// [`denoted_with`], each name of `free` that no clause around it bounds and no binding of
/// `leaves` reads being a variable of the outermost function type around it, the signature's
/// own (DESIGN.md sec:type_resolution, rule 4: free names in a signature are the scheme's
/// variables). A printed type writes such a name for a variable that stands in two places or
/// more (UNDERSCORE-print), which only `parse_type` reads back.
pub fn denoted_free(t: &Type, leaves: &Binds, free: &HashSet<Arc<str>>) -> Ty {
    Denote {
        leaves,
        free,
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
/// step before it, so the steps run from the cause to the part `t` holds. A part found to have
/// no value for a reason no part of it shows gets a step that says what is known, and the walk
/// never stops ([`explain_empty`]).
///
/// Built only for a message that is printed. One denotation of `t` that keeps the span of
/// each part with no value, and one walk of `t`, each with its own stack: the time is linear
/// in the size of `t`. Each step quotes no part it names but a name, an operand of the one
/// intersection or difference whose operands all have values, which no other step quotes,
/// so the text is linear in the size of `t` too.
fn emptied(t: &Type, out: &mut Vec<Note>) {
    let mut d = Denote {
        leaves: &Binds::new(),
        free: &HashSet::new(),
        bound: HashMap::new(),
        open: Vec::new(),
        empty: Some(HashSet::new()),
    };
    d.ty(t);
    let empty = d.empty.unwrap_or_default();
    explain_empty(t, |p| empty.contains(&p.span), out);
}

/// `t` with each `for` clause around it taken off: a clause has the value of the type it bounds.
fn bare(mut t: &Type) -> &Type {
    while let TypeKind::For { ty, .. } = &t.kind {
        t = ty;
    }
    t
}

/// The steps of [`emptied`], with `found` saying which parts of `t`, each without the `for`
/// clauses around it, the denotation found to have no value.
///
/// The walk is total: it asks `found` only about the part it is explaining and its own parts,
/// and relies on no link between the answers. A tuple type or an atom with a payload found
/// to have no value though no part of it was (which the present denotation never finds, since
/// it empties such a type only for an empty part, but a meet, a recursive type or a named type
/// read in full could), a union some member of which was not found empty, and a part of a
/// kind that has values each get a step of their own, and the walk never stops.
fn explain_empty(t: &Type, found: impl Fn(&Type) -> bool, out: &mut Vec<Note>) {
    let none = |t: &Type| found(bare(t));
    // What the step after the one that explains `c` calls it.
    let cause = |c: &Type| match &bare(c).kind {
        TypeKind::Name(n) => format!("`{n}`"),
        TypeKind::Tuple(_) => "the tuple type of the step before".into(),
        TypeKind::AtomApply(..) => "the atom type of the step before".into(),
        TypeKind::Union(_) => "the union of the step before".into(),
        TypeKind::And(_) => "the intersection of the step before".into(),
        TypeKind::Diff(..) => "the difference of the step before".into(),
        _ => "the type of the step before".into(),
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
                    TypeKind::For { ty, .. } => vec![ty],
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
            TypeKind::Tuple(ts) => match (ts.iter().enumerate()).find(|(_, c)| none(c)) {
                Some((i, c)) => {
                    causes.push(c);
                    format!(
                        "this tuple type has no value, since its component {i}, {}, has none",
                        cause(c)
                    )
                }
                // A tuple of values is a value, so one component has none, for a reason no
                // part written in it shows.
                None => "this tuple type has no value, since one of its components has none".into(),
            },
            TypeKind::AtomApply(a, ps) => {
                match (ps.iter().enumerate()).find(|(_, p)| none(&p.ty)) {
                    Some((i, p)) => {
                        causes.push(&p.ty);
                        let part = match &p.name {
                            Some(n) if !p.positional => format!("field `{n}`"),
                            _ => format!("component {i}"),
                        };
                        format!(
                            "this atom type `#{a}` has no value, since its payload's {part}, {}, \
                         has none",
                            cause(&p.ty)
                        )
                    }
                    None => format!(
                        "this atom type `#{a}` has no value, since a part of its payload has none"
                    ),
                }
            }
            // Each member is in the union, so each has no value; those found so are explained.
            TypeKind::Union(ts) => {
                causes.extend(ts.iter().filter(|m| none(m)));
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
            // A part of another kind, named as the cause of the part that holds it: an atom, a
            // kind-wide type or a function type, each of which has values as this checker
            // reads them.
            _ => "this type has no value".into(),
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

/// `items` joined as a list of choices in a sentence: `a`, `a or b`, `a, b or c`.
fn or_list(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [one] => one.clone(),
        [rest @ .., last] => format!("{} or {last}", rest.join(", ")),
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
    /// The names read as variables of the outermost function type around them where no clause
    /// bounds them ([`denoted_free`]).
    free: &'a HashSet<Arc<str>>,
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
    /// The free names of [`Denote::free`] it is the home of, with no bound.
    free: BTreeSet<Arc<str>>,
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
                    if let Some(&(mask, at)) = self.bound.get(v) {
                        if let Some(home) = self.open.get_mut(at) {
                            home.bounds.insert(v.into(), mask);
                            if home.params {
                                home.held.insert(v.into());
                            }
                        }
                    } else if self.free.contains(v)
                        && let Some(home) = self.open.first_mut()
                    {
                        home.free.insert(v.into());
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
        sig.own.extend(open.free);
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
        true => format!("{what} does not take ({shown}): no arrow of {what} takes these types"),
        false => format!("{what} does not take ({shown}){why}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A check with the binder tables `t` that keeps the fixes of its rejections as they are.
    /// These tests record no construct ([`Ck::written`]), and with none recorded
    /// [`Ck::fixes_checked`], which `walk.rs` defines, keeps them as they are too.
    fn checker<'t, 'a>(t: &'t Tables<'a>) -> Ck<'t, 'a> {
        Ck::new(t, |_, _, _| {})
    }

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
        let mut ck = checker(&t);
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
        ck.undo(&Mark {
            log: 0,
            errors: 0,
            top_parts: 0,
        });
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
        why_none_with(text, emptied)
    }

    /// The steps `explain` gives for the written type `text`, each with the text it is placed
    /// at.
    fn why_none_with(text: &str, explain: impl Fn(&Type, &mut Vec<Note>)) -> Vec<(String, String)> {
        let tokens = zedc_syntax::lex::lex(text).expect("lexing a type");
        let tree = zedc_syntax::parse::parse(text, &tokens, "Type", zedc_syntax::parse::TOP)
            .expect("parsing a type");
        let t = zedc_syntax::ast::ty(text, &tokens, &tree).expect("reading a type");
        let mut out = Vec::new();
        explain(&t, &mut out);
        (out.into_iter())
            .map(|n| (text[n.span.start..n.span.end].to_string(), n.text))
            .collect()
    }

    /// The steps `explain_empty` gives for the written type `text` when the denotation is
    /// taken to have found exactly the parts written as `found` to have no value: what a
    /// denotation that reads more than the parts (a meet, a recursive type, a named type read
    /// in full) may find.
    fn why_found(text: &str, found: &[&str]) -> Vec<(String, String)> {
        why_none_with(text, |t, out| {
            explain_empty(t, |p| found.contains(&&text[p.span.start..p.span.end]), out)
        })
    }

    /// A pair of the text a step is placed at and the step.
    fn step(at: &str, text: &str) -> (String, String) {
        (at.to_string(), text.to_string())
    }

    /// A tuple type found to have no value, none of whose components was, gets a step that
    /// says one of its components has none, and the walk does not stop.
    #[test]
    fn a_tuple_found_empty_with_no_empty_component_gets_a_step() {
        assert_eq!(
            why_found("(int, bool)", &["(int, bool)"]),
            [step(
                "(int, bool)",
                "this tuple type has no value, since one of its components has none, so it is \
                 `Never`"
            )]
        );
        // The component found empty by a meet its parts do not show is explained in turn.
        assert_eq!(
            why_found(
                "((int, int) & (bool, int), int)",
                &[
                    "((int, int) & (bool, int), int)",
                    "(int, int) & (bool, int)"
                ]
            ),
            [
                step(
                    "(int, int) & (bool, int)",
                    "this intersection has no value, since no value is in all of `(int, int)` \
                     and `(bool, int)`, so it is `Never`"
                ),
                step(
                    "((int, int) & (bool, int), int)",
                    "this tuple type has no value, since its component 0, the intersection of \
                     the step before, has none, so it is `Never`"
                ),
            ]
        );
    }

    /// The same for an atom with a payload.
    #[test]
    fn an_atom_found_empty_with_no_empty_payload_part_gets_a_step() {
        assert_eq!(
            why_found("#a(int, x: bool)", &["#a(int, x: bool)"]),
            [step(
                "#a(int, x: bool)",
                "this atom type `#a` has no value, since a part of its payload has none, so it \
                 is `Never`"
            )]
        );
    }

    /// A union found to have no value is explained by the members found so, and a member not
    /// found so, here a function type, is not explained.
    #[test]
    fn a_union_explains_only_the_members_found_empty() {
        assert_eq!(
            why_found(
                "(int, Never) | ((int) -> int)",
                &["(int, Never) | ((int) -> int)", "(int, Never)", "Never"]
            ),
            [
                step(
                    "(int, Never)",
                    "this tuple type has no value, since its component 1, `Never`, has none, so \
                     it is `Never`"
                ),
                step(
                    "(int, Never) | ((int) -> int)",
                    "this union has no value, since none of its members has one, so it is `Never`"
                ),
            ]
        );
    }

    /// A part of a kind that has values, found to have none as the cause of the part that
    /// holds it, gets a step of its own at the part.
    #[test]
    fn a_part_of_a_kind_with_values_found_empty_gets_a_step() {
        assert_eq!(
            why_found("(#a, int)", &["(#a, int)", "#a"]),
            [
                step("#a", "this type has no value, so it is `Never`"),
                step(
                    "(#a, int)",
                    "this tuple type has no value, since its component 0, the type of the step \
                     before, has none, so it is `Never`"
                ),
            ]
        );
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

    /// An atom of a named family is data: where a call, an index, a condition or `sum` takes
    /// a value that may be one, [`Ck::passing`] rejects it with a repair, and passes on only
    /// the loose atoms beside it. No source form names a family until `type` declarations
    /// do (step L2.5), so the rule is read from a type `Ty::named` makes, as `l01_27_absences`
    /// reads the other family rules.
    #[test]
    fn a_family_atom_reaching_a_call_is_rejected_with_its_repairs() {
        let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
        let t = Tables::new(&[], &res);
        let mut ck = checker(&t);
        let atoms = |names: &[&str]| {
            (names.iter()).fold(Ty::empty(), |t, n| t.union(&Ty::set(KType::atom(n))))
        };
        let color = atoms(&["red", "green", "blue"]).named();
        let read = color.union(&atoms(&["ioError"]));
        let out = ck.passing(&read, "a call", span(0), None);
        assert_eq!(out, atoms(&["ioError"]));
        let messages: Vec<(String, Vec<String>)> = (ck.errors.into_iter())
            .map(|f| {
                let mut e = f.written(t.text);
                lay_out(&mut e.message, &mut e.notes, &mut e.menu);
                (e.message, e.notes.into_iter().map(|n| n.text).collect())
            })
            .collect();
        assert_eq!(
            messages,
            [(
                "No case for `#blue | #green | #red` in a call: \
                 `v : #blue | #green | #ioError | #red`. Try \
                 `(v else #blue -> d else #green -> d else #red -> d)` instead."
                    .to_string(),
                vec![
                    "`v` is the value a call reads".to_string(),
                    "an atom of a named family is data, not a failure, so it does not pass \
                     through a call"
                        .to_string(),
                    "each `d` is the value to use in place of the atom before it".to_string(),
                    "repair: `(v else #blue -> d else #green -> d else #red -> d)`".to_string(),
                    "repair: `match v { #blue -> d, #green -> d, #red -> d, rest -> rest }`"
                        .to_string(),
                ]
            )]
        );
        // The same atoms written inline are loose: they pass through with no error.
        let mut ck = checker(&t);
        assert_eq!(
            ck.passing(&read.written(), "a call", span(0), None),
            read.written()
        );
        assert!(ck.errors.is_empty());
    }
}

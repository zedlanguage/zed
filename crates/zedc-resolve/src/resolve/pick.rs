//! Which overload of a set a call can select, read from the call's arguments before type
//! checking, so that the dependency order waits on that overload only ([`super::tables`]).
//!
//! DESIGN.md sec:type_resolution, rule 6: "of the applicable arrows, drop each one that another
//! applicable arrow is strictly more specific than, and run the earliest declared of those
//! left". A call depends on the overloads it can run, not on every overload of its name: a
//! call `f(1)` with `f(positional n: int)` and `f(positional s: bool)` runs the `int` overload
//! only, so it is no use of the `bool` overload, and a `bool` overload that calls `f(1)` is not
//! recursion (dependency theorem, proof (1): dispatch is "a choice among arms").
//!
//! Each argument and each parameter type is read as a set of carriers, a bit mask: an argument
//! whose carriers the text fixes (a literal, a comparison, a parameter with a written type) and
//! a parameter type written with the prelude's names. Anything else is every carrier, so the
//! masks over-approximate what an overload admits: an overload whose mask misses an argument's
//! cannot run the call. When exactly one overload can admit the call, the call waits on it;
//! when none can, the call is an error the checker reports and waits on nothing; when two or
//! more can, which one runs is fixed by type checking (step L2.6), and until then the call waits
//! on none of them, so the order reports no cycle through an overload the call may not run.

use std::collections::HashMap;

use zedc_syntax::ast::{BinaryOp, Every, Expr, ExprKind, Function, Param, Type, TypeKind, UnaryOp};
use zedc_syntax::lex::Span;

use crate::resolve::{Kind, Ref, Resolution};

/// A set of carriers, one bit each.
pub(crate) type Mask = u16;

const INT: Mask = 1 << 0;
const RAT: Mask = 1 << 1;
const F64: Mask = 1 << 2;
const F32: Mask = 1 << 3;
const F16: Mask = 1 << 4;
const BF16: Mask = 1 << 5;
const BOOL: Mask = 1 << 6;
/// Every text type.
const TEXT: Mask = 1 << 7;
/// Every atom.
const ATOM: Mask = 1 << 8;
/// Every other value: a tuple, a struct, a function, an array, a prelude value such as `Lines`.
const OTHER: Mask = 1 << 9;
/// The number of bits.
const BITS: usize = 10;
/// Every carrier: what an argument or a parameter type the text does not fix may be.
const ALL: Mask = (1 << BITS) - 1;
/// The formats a decimal literal may take.
const FLOATS: Mask = F64 | F32 | F16 | BF16;
/// The carriers an integer literal may take (sec:type_resolution, rule 2: "a numeric literal
/// takes the carrier expected").
const NUMERIC: Mask = INT | RAT | FLOATS;

/// The carriers of the prelude type named `name`, or [`ALL`] for any other name, which may be a
/// type variable or a declared type.
fn named(name: &str) -> Mask {
    match name {
        "int" => INT,
        "rat" => RAT,
        "f64" => F64,
        "f32" => F32,
        "f16" => F16,
        "bf16" => BF16,
        "bool" => BOOL,
        "String" | "Utf8String" | "Utf16String" | "Utf32String" => TEXT,
        "Lines" | "Files" | "CommandLine" => OTHER,
        "Never" => 0,
        _ => ALL,
    }
}

/// The carriers of the written type `t`. Its parts are read with a stack, so a deep type does
/// not grow the thread's stack.
fn of_type(t: &Type) -> Mask {
    let mut mask = 0;
    let mut todo = vec![t];
    while let Some(t) = todo.pop() {
        mask |= match &t.kind {
            TypeKind::Name(n) => named(n),
            TypeKind::Atom(_) | TypeKind::AtomAny(_) | TypeKind::AtomApply(..) => ATOM,
            TypeKind::Every(Every::Atom) => ATOM,
            TypeKind::Every(Every::Tuple | Every::Struct)
            | TypeKind::Tuple(_)
            | TypeKind::Record(_)
            | TypeKind::Array(_)
            | TypeKind::Arrow { .. } => OTHER,
            TypeKind::Union(arms) => {
                todo.extend(arms);
                0
            }
            _ => ALL,
        };
    }
    mask
}

/// The carriers of the argument `e`: those its text fixes, else [`ALL`]. `param_ty` holds the
/// written type of each parameter, by the parameter's text.
fn of_arg(e: &Expr, res: &Resolution, param_ty: &HashMap<Span, &Type>) -> Mask {
    match &e.kind {
        ExprKind::Int { .. } => NUMERIC,
        ExprKind::Float {
            forced: Some(f), ..
        } => named(f.name()),
        ExprKind::Float { forced: None, .. } => RAT | FLOATS,
        ExprKind::Rat(_) => RAT,
        ExprKind::Bool(_) | ExprKind::Is { .. } => BOOL,
        ExprKind::Str(_) => TEXT,
        ExprKind::Atom(_) => ATOM,
        ExprKind::Tuple(_) | ExprKind::Lambda { .. } => OTHER,
        ExprKind::Unary(UnaryOp::Not, _) => BOOL,
        ExprKind::Binary(
            BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge
            | BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::And
            | BinaryOp::Or,
            ..,
        ) => BOOL,
        ExprKind::Unary(UnaryOp::Neg, a)
            if matches!(
                a.kind,
                ExprKind::Int { .. } | ExprKind::Float { .. } | ExprKind::Rat(_)
            ) =>
        {
            of_arg(a, res, param_ty)
        }
        ExprKind::Name(_) => match res.uses.get(&e.span) {
            Some(Ref::Bound(ids)) if ids.len() == 1 => {
                let b = &res.binders[ids[0]];
                match (b.kind, param_ty.get(&b.span)) {
                    (Kind::Param, Some(t)) => of_type(t),
                    _ => ALL,
                }
            }
            _ => ALL,
        },
        _ => ALL,
    }
}

/// A call of an overload set, as [`super::tables::Tables`] meets it: `f(args)`, or
/// `x.f(args)`, which is `f(x, args)`.
pub(crate) struct Call<'a> {
    /// The use of the set: the callee's text.
    pub use_at: Span,
    /// The receiver of `x.f(…)`, the first positional argument.
    pub receiver: Option<&'a Expr>,
    pub positional: &'a [Expr],
    pub named: &'a [(String, Expr)],
}

/// What a call of an overload set waits on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Pick {
    /// The one overload that can run it, as a binder.
    Arm(usize),
    /// None: no overload admits it, which the checker reports, or two or more do, and type
    /// checking chooses (step L2.6).
    Undecided,
}

/// What one overload admits: the carriers of each positional parameter and of each named one.
struct Arm<'a> {
    binder: usize,
    positional: Vec<Mask>,
    named: HashMap<&'a str, Mask>,
}

/// Up to two overloads, by index into the set's overloads: all that matter to tell none, one
/// and several apart.
#[derive(Clone, Copy, Default)]
struct Two([Option<u32>; 2]);

impl Two {
    fn add(&mut self, a: u32) {
        match self.0 {
            [None, _] => self.0[0] = Some(a),
            [Some(x), None] if x != a => self.0[1] = Some(a),
            _ => {}
        }
    }
}

/// The overloads of one set, indexed by argument place and carrier.
struct Index<'a> {
    arms: Vec<Arm<'a>>,
    /// For each positional place, for each carrier, the first two overloads that admit it.
    positional: Vec<[Two; BITS]>,
    /// The same for each named parameter.
    named: HashMap<&'a str, [Two; BITS]>,
}

/// The carriers each parameter of `f` admits, positional and named. A parameter written
/// `positional`, or a tuple-destructuring one, is passed by position only; any other by name
/// only; the one parameter of a function with one takes either form (DESIGN.md
/// sec:values_morphisms,
/// "A parameter is positional or named, as its declaration says").
fn arm<'a>(binder: usize, f: &'a Function) -> Arm<'a> {
    let mask = |p: &Param| p.ty.as_ref().map_or(ALL, of_type);
    let one = f.params.len() == 1;
    let mut a = Arm {
        binder,
        positional: Vec::new(),
        named: HashMap::new(),
    };
    for p in &f.params {
        if one || p.positional || p.tuple.is_some() {
            a.positional.push(mask(p));
        }
        if one || !(p.positional || p.tuple.is_some()) {
            a.named.insert(p.name.as_str(), mask(p));
        }
    }
    a
}

impl<'a> Index<'a> {
    /// The index of the overloads `arms`, `None` when one of them is not a declared function.
    // Complexity tradeoff: the naive pick tests each call against each overload, O(U·K) for U
    // calls of a set of K overloads. The index keeps, per argument place and carrier, the
    // first two overloads that admit it, built in O(K·P·BITS) for P parameters; a call then
    // reads O(BITS) entries per argument and tests one overload, O(A·BITS) for A arguments.
    fn new(arms: &imbl::Vector<usize>, funcs: &HashMap<usize, &'a Function>) -> Option<Self> {
        let mut ix = Index {
            arms: Vec::with_capacity(arms.len()),
            positional: Vec::new(),
            named: HashMap::new(),
        };
        for &b in arms {
            let a = arm(b, funcs.get(&b)?);
            let k = ix.arms.len() as u32;
            for (i, &m) in a.positional.iter().enumerate() {
                if ix.positional.len() <= i {
                    ix.positional.push([Two::default(); BITS]);
                }
                add(&mut ix.positional[i], m, k);
            }
            for (&n, &m) in &a.named {
                add(ix.named.entry(n).or_insert([Two::default(); BITS]), m, k);
            }
            ix.arms.push(a);
        }
        Some(ix)
    }

    /// The overloads that admit an argument of the carriers `m` at the place `at`, up to two.
    fn admitting(at: Option<&[Two; BITS]>, m: Mask) -> Two {
        let mut out = Two::default();
        for (bit, two) in at.into_iter().flatten().enumerate() {
            if m & (1 << bit) != 0 {
                for a in two.0.into_iter().flatten() {
                    out.add(a);
                }
            }
        }
        out
    }

    /// What the call with the argument masks `positional` and `named` waits on.
    fn pick(&self, positional: &[Mask], named: &[(&str, Mask)]) -> Pick {
        let places = (positional.iter().enumerate())
            .map(|(i, &m)| Index::admitting(self.positional.get(i), m))
            .chain(
                named
                    .iter()
                    .map(|(n, m)| Index::admitting(self.named.get(n), *m)),
            );
        let mut one = None;
        for two in places {
            match two.0 {
                [None, _] => return Pick::Undecided,
                [Some(a), None] => one = one.or(Some(a)),
                [Some(_), Some(_)] => {}
            }
        }
        let Some(a) = one else {
            return Pick::Undecided;
        };
        let arm = &self.arms[a as usize];
        let admits = positional.len() <= arm.positional.len()
            && positional
                .iter()
                .zip(&arm.positional)
                .all(|(m, p)| m & p != 0)
            && (named.iter()).all(|(n, m)| arm.named.get(n).is_some_and(|p| m & p != 0));
        if admits {
            Pick::Arm(arm.binder)
        } else {
            Pick::Undecided
        }
    }
}

/// Records the overload `k` at each carrier of `m` at one place.
fn add(at: &mut [Two; BITS], m: Mask, k: u32) {
    for (bit, two) in at.iter_mut().enumerate() {
        if m & (1 << bit) != 0 {
            two.add(k);
        }
    }
}

/// What each call of `calls` waits on, by the use of its overload set. A set with an overload
/// that is not a declared function is left out, so its calls wait on every overload.
pub(crate) fn picks<'a>(
    calls: &[Call<'a>],
    res: &Resolution,
    funcs: &HashMap<usize, &'a Function>,
    param_ty: &HashMap<Span, &Type>,
) -> HashMap<Span, Pick> {
    let mut sets: HashMap<(usize, usize), Option<Index<'a>>> = HashMap::new();
    let mut out = HashMap::new();
    for c in calls {
        let Some(Ref::Bound(arms)) = res.uses.get(&c.use_at) else {
            continue;
        };
        // The overloads of one set share their first binder, the set's first declaration, and
        // their number.
        let Some(ix) = sets
            .entry((arms[0], arms.len()))
            .or_insert_with(|| Index::new(arms, funcs))
        else {
            continue;
        };
        let positional: Vec<Mask> = (c.receiver.into_iter().chain(c.positional))
            .map(|e| of_arg(e, res, param_ty))
            .collect();
        let named: Vec<(&str, Mask)> = (c.named.iter())
            .map(|(n, e)| (n.as_str(), of_arg(e, res, param_ty)))
            .collect();
        out.insert(c.use_at, ix.pick(&positional, &named));
    }
    out
}

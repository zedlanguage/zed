//! Name resolution (steps L1.14 and L2.3): every name a unit uses, tied to the binder it names.
//!
//! A bare name resolves in the order of DESIGN.md sec:units, stopping at the first hit: the
//! block scopes, innermost outward, each with the names its own imports bring in; the unit's
//! top level, `local` declarations included; the selective imports and qualifiers of the top
//! level; the prelude unit the manifest names; the compiler's prelude words. Functions of one
//! name at the top level and in its imports are the arrows of one overload set. Statement order
//! has no meaning, so a name bound anywhere in a scope is in scope throughout it. A scope is a
//! block, or a function's or lambda's parameters, which share one scope with the statements of
//! a body block (so `f(x) { x = 1; }` rebinds `x`), or the names an `else` pattern or a `match`
//! arm binds, in scope in its default or its guard and value. A parameter's type and default
//! see the parameters (`hi: int where lo <= hi`) but not the body's bindings; a function's
//! `test` cases are read in the scope around the function; a type declaration's parameters are
//! in scope in its type only; a method's receiver `this` is in scope in its body.
//!
//! Binding a name twice in one scope is an error, except that functions of one name whose
//! written parameter types differ are the arrows of one overload set; a name in a nested scope
//! shadows the outer one. Two imports in one scope that bring in one name make its uses
//! ambiguous, unless every binder they bring is a function or both come from one unit. A name
//! that resolves to a prelude word of a later layer is an error naming the layer. A member `x.f`
//! whose `f` is in scope may be a uniform call `f(x)`; its resolution is recorded, and
//! elaboration (step L1.16) tells a field from a function. A member `q.f` of a qualifier names
//! the definition `f` of the qualifier's unit, by name ([`Ref::Unit`]); step L2.4 links it.
//!
//! Resolution reads other units only through [`Units`]: their exports, by unit path. The loader
//! (`crate::unit`) gives each unit the exports of the units it imports, in an order where those
//! are resolved first; a unit read alone imports nothing.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::ops::Range;
use std::sync::Arc;

use imbl::Vector;

use zedc_base::address::ContentAddress;
use zedc_base::rejection::{Row, not_yet};
use zedc_syntax::ast::{
    Annot, Arm, Error, Expr, ExprKind, Field, Function, Import, ImportKind, Param, Pattern, Port,
    PortName, RangeEnd, Stmt, StmtKind, StrPart, Struct, Target, TypeDecl,
};
use zedc_syntax::ast::{BinaryOp, Every, Note, Type, TypeBound, TypeKind};
use zedc_syntax::lex::Span;

mod pick;
pub mod tables;
pub mod topo;

/// What binds a name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    /// A binding `x = e;` or a target of `a, b = e;`.
    Binding,
    /// A function declaration.
    Function,
    /// A parameter of a function or a lambda.
    Param,
    /// An output port of `main`, a field of `MainArgs` its body pushes to, `m.stdout`.
    Port,
    /// A name a pattern binds: `#a(f:)`, `Point(x:)`, `n`, `n is int`.
    Pattern,
    /// A struct declaration `struct Point { … }`.
    Struct,
    /// A type declaration `type Shape = …;`.
    Type,
    /// A parameter `T` of a type declaration `type Tree(T) = …;`.
    TypeParam,
    /// A field of a struct. Outside its field list a field is named through a value of the
    /// struct, never alone; inside it, a default or a type names the fields above it.
    Field,
    /// A method `T.m(…) = e;`, bound as `T.m`.
    Method,
    /// The receiver `this` of a method.
    Receiver,
    /// A qualifier: the name `import a.b;` binds to the unit `a.b`, or the `g` of `as g`.
    Unit,
}

impl Kind {
    /// The binder of this kind, as a message names it.
    fn binder(self) -> &'static str {
        match self {
            Kind::Binding => "the binding target",
            Kind::Function => "the function",
            Kind::Param => "the parameter",
            Kind::Port => "the output port",
            Kind::Pattern => "the pattern binder",
            Kind::Struct => "the struct",
            Kind::Type => "the type",
            Kind::TypeParam => "the type parameter",
            Kind::Field => "the field",
            Kind::Method => "the method",
            Kind::Receiver => "the receiver",
            Kind::Unit => "the qualifier",
        }
    }

    /// Whether a binder of this kind names a type.
    pub fn is_type(self) -> bool {
        matches!(self, Kind::Struct | Kind::Type | Kind::TypeParam)
    }
}

/// The text of `name` in a declaration whose text `decl` begins with it, as a function's or an
/// indexed definition's or a port's does (DESIGN.md sec:grammar, `Function`, `IndexedDef`, `Port`).
fn name_at(decl: Span, name: &str) -> Span {
    Span {
        start: decl.start,
        end: decl.start + name.len(),
    }
}

/// A binder: a name, where it is bound, and what binds it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binder {
    /// The name.
    pub name: String,
    /// The text that binds it: the statement, the parameter, the port or the pattern; for a
    /// name an import brings in, the import.
    pub span: Span,
    /// What binds it; for a name an import brings in, what binds it in its unit.
    pub kind: Kind,
}

/// What a use of a name names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ref {
    /// Binders of the unit, by index: one, or the arrows of an overload set. The list is
    /// persistent, so every use of a set of `K` arrows shares it: `U` uses cost `O(U)`, not
    /// `O(U·K)`.
    // Complexity tradeoff (COMPLEXITY.md F46): a `Vec` per use copies the K arrows into each
    // of U uses, O(U·K) time and memory; the persistent `imbl::Vector` is shared, O(1) per
    // use, at a larger constant per element read and an inline copy for lists of three or
    // fewer, which costs O(1).
    Bound(Vector<usize>),
    /// A prelude word of layer L1, or `build` of L2, which `zedc::build` replaces before
    /// elaboration (step L2.8d).
    Prelude(String),
    /// The definition `name` of the unit `unit`: a member `shapes.area` of a qualifier, a type
    /// `shapes.Point`, or a name of the prelude unit. It is named, not numbered, so a unit's
    /// resolution stays valid while the other unit's definitions change but its exports do not;
    /// step L2.4 links it to the definition.
    Unit {
        /// The unit's path.
        unit: Arc<str>,
        /// The name it defines.
        name: String,
    },
    /// The input `main::files` of the program's `main`, read in another function (DESIGN.md
    /// sec:ports, QUESTIONS A68): the port itself, which `main` opens. In `main`'s body the read
    /// is a use of `main`'s parameter of that name, [`Ref::Bound`].
    Main(String),
}

/// The resolution of a unit.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Resolution {
    /// The unit's binders, in the order they are met.
    pub binders: Vec<Binder>,
    /// Each use, by its text: a name, a type name, a push's statement (whose port it names),
    /// a member whose name is in scope, a qualified member or type, or a struct pattern's or a
    /// method's type.
    pub uses: BTreeMap<Span, Ref>,
    /// The binders of each `else` pattern and of each `match` arm, by the `else`'s or the arm's
    /// text: a range of `binders`.
    // Complexity tradeoff (COMPLEXITY.md F12): the naive checker finds an `else` pattern's
    // binders by scanning every pattern binder that starts before the default,
    // O(elses · binders); the range recorded here costs O(log elses) per `else` and one
    // map entry per pattern.
    pub patterns: BTreeMap<Span, Range<usize>>,
    /// The fields of each struct, by the struct's statement: a range of `binders`.
    pub fields: BTreeMap<Span, Range<usize>>,
    /// The unit each import's binder comes from: for a qualifier, the unit it names; for a
    /// name a selective import brings in, the unit that defines it.
    pub imports: BTreeMap<usize, Arc<str>>,
    /// Each import statement, in every scope, with the unit it names and the content address
    /// it is pinned to, if written, in text order: what the loader reads to find the units a
    /// unit needs and to check their pins.
    pub units: Vec<(Arc<str>, Span, Option<ContentAddress>)>,
    /// The binders a `local` declaration binds, which no other unit sees.
    pub local: HashSet<usize>,
    /// What the unit's top level defines, which other units may import.
    pub exports: Exports,
    /// Where each declaration statement starts, in every scope: a binding, a function, a
    /// struct, a type, a method, an import, a `local`, a piece of an indexed
    /// definition, or an annotated one. A doc comment attaches to the declaration that follows
    /// it (DESIGN.md sec:grammar, comments).
    pub decls: HashSet<usize>,
    /// The unit item `@log(#off);`, if the unit has one: it drops the log lines that every
    /// body of the unit writes (DESIGN.md sec:ports). Step L7.3, which writes the lines, reads it.
    pub log_off: Option<Span>,
    /// The regions whose loose atoms reach a handler: the operand of each `e else d`,
    /// `e else #a -> d` and `e is T`, the other side of each `e == #a` and `e != #a`, and the
    /// value of each binding `s = e` of one name. The checker gives an undeclared parameter
    /// the atoms its uses in a region handle (DESIGN.md sec:type_resolution).
    pub regions: Vec<Region>,
    /// Each use of a name whose loose atoms pass by rule 6 to the value of a region, by the
    /// name's text, and the region: the name itself, or an argument, receiver or operand of a
    /// call or an operator in it, a branch of an `if`, a block's result or a hole of a string,
    /// at any depth. In written order.
    pub flows: Vec<(Span, usize)>,
    /// Each use of a name that an imported unit would define but for its syntax errors
    /// ([`Exports`], [`Refused::Unknown`]), by its text: it has no error, and the statement
    /// that holds it is not checked (step L1.29d).
    pub broken: Vec<Span>,
    /// The text of each push statement, in every scope: `uses` holds the port it pushes to at
    /// that text.
    pub pushes: Vec<Span>,
    /// Each call whose callee is a name, with the text of its arguments. With
    /// [`Resolution::pushes`], what the checker reads to tell a port passed whole to a
    /// parameter that is pushed to from a read of the port (DESIGN.md L1.19).
    pub calls: Vec<NamedCall>,
}

/// A call `f(a, x: b)` whose callee is a name, by the text of its parts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedCall {
    /// The text of the whole call.
    pub span: Span,
    /// The text of the callee's name, where `uses` holds what it names.
    pub callee: Span,
    /// The text of each positional argument, in order.
    pub positional: Vec<Span>,
    /// Each named argument's name and text, in written order.
    pub named: Vec<(String, Span)>,
}

/// A region of value flow whose loose atoms reach a handler (DESIGN.md sec:type_resolution).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Region {
    /// The atoms its handler handles.
    pub handles: Vec<Handle>,
    /// The region the value of this one passes on to: the operand of an `else` whose default
    /// or operand holds this region's `else`.
    pub parent: Option<usize>,
    /// The binder of `s` when the region is the value of `s = e`: the uses of `s` handle what
    /// passes out of `e`.
    pub into: Option<usize>,
}

/// The atoms an `else` or an `is` handles.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Handle {
    /// Every loose atom: `e else d`.
    Loose,
    /// The atom with any payload or none: `e else #a -> d`.
    Any(String),
    /// The atom with no payload: `e is #a`, one for each atom of the tested type.
    Bare(String),
}

/// A name a unit's top level defines, as another unit sees it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Export {
    /// What binds it: for a set of overloads, `Function`.
    pub kind: Kind,
    /// Whether every declaration of it is `local`, so that no other unit sees it.
    pub local: bool,
}

/// What a unit's top level defines: each name, by name, and the names it would define but for
/// its syntax errors (step L1.29d). It holds no text position, so an edit that moves or
/// rewrites a definition but keeps its name, its kind and its `local` leaves the exports, and
/// so every importer's resolution, as they were.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Exports {
    names: BTreeMap<String, Export>,
    /// The names a declaration of the unit that does not parse would define, or a declaration
    /// left unchecked since it uses one, and that nothing of the unit defines: an importer's
    /// use of one gets no error, and its statement is not checked ([`Resolution::broken`]).
    broken: BTreeSet<String>,
}

impl Exports {
    /// What the unit defines as `name`, if anything.
    pub fn get(&self, name: &str) -> Option<Export> {
        self.names.get(name).copied()
    }

    /// The names the unit defines, in order.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.names.keys().map(String::as_str)
    }

    /// How many names the unit defines.
    pub fn len(&self) -> usize {
        self.names.len()
    }

    /// Whether the unit defines no name.
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    /// Records a top-level declaration of `name`; one arrow of an overload set that is not
    /// `local` makes the name visible to other units.
    fn add(&mut self, name: &str, kind: Kind, local: bool) {
        self.names
            .entry(name.into())
            .and_modify(|e| e.local &= local)
            .or_insert(Export { kind, local });
    }

    /// Records the names `broken` that declarations of the unit that do not parse would
    /// define, but for those the unit defines.
    pub fn set_broken(&mut self, broken: impl IntoIterator<Item = String>) {
        self.broken = broken
            .into_iter()
            .filter(|n| !self.names.contains_key(n))
            .collect();
    }

    /// Whether `name` is a name a declaration of the unit that does not parse would define,
    /// which the unit does not define.
    pub fn is_broken(&self, name: &str) -> bool {
        self.broken.contains(name)
    }

    /// The names in order, each as its length, its bytes, its kind and `local`, then the
    /// broken names in order, each after the byte 255, which no kind is: what an importer's
    /// resolution reads of the unit, encoded so that two exports have equal bytes only when
    /// they are equal.
    pub fn bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for (name, e) in &self.names {
            out.extend_from_slice(&(name.len() as u64).to_le_bytes());
            out.extend_from_slice(name.as_bytes());
            out.extend_from_slice(&[e.kind as u8, u8::from(e.local)]);
        }
        for name in &self.broken {
            out.extend_from_slice(&(name.len() as u64).to_le_bytes());
            out.extend_from_slice(name.as_bytes());
            out.push(u8::MAX);
        }
        out
    }
}

/// Why a unit cannot read the exports of a unit it imports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refused {
    /// The import is rejected with this reason.
    Because(String),
    /// The import lies on an import cycle, which the loader reports once for the cycle's whole
    /// strongly connected component (`unit::order`): the import is rejected with no error of
    /// its own.
    OnCycle,
    /// The unit's text does not lex, or its statements cannot be built, which is reported in
    /// it: every name it might define is unknown, so the import gets no error, and each use
    /// of a name it brings in is a broken use ([`Resolution::broken`]).
    Unknown,
}

/// The other units a unit's resolution reads.
pub trait Units {
    /// The exports of the unit `path`, or why the unit cannot import it.
    fn exports(&self, path: &str) -> Result<&Exports, Refused>;
    /// The prelude unit the unit sees, by its path, with its exports: the one the manifest
    /// names, for every unit but it and the units it reaches.
    fn prelude(&self) -> Option<(&Arc<str>, &Exports)>;
}

/// A unit read alone, with no manifest above it: it imports no unit and sees no prelude unit.
pub struct Alone;

impl Units for Alone {
    fn exports(&self, _: &str) -> Result<&Exports, Refused> {
        Err(Refused::Because(
            "no manifest `zed.manifest` marks a package root at or above this unit, so it \
             imports no unit"
                .into(),
        ))
    }

    fn prelude(&self) -> Option<(&Arc<str>, &Exports)> {
        None
    }
}

/// A unit's resolution and what it rejects: `errors` are the unit's mistakes, `later` the forms
/// it uses that a later step compiles. Either list stops the unit before elaboration.
#[derive(Debug)]
pub struct Resolved {
    /// The resolution.
    pub res: Resolution,
    /// The errors, in text order.
    pub errors: Vec<Error>,
    /// The forms of later steps, in text order.
    pub later: Vec<Error>,
}

/// The value words of the prelude, each with the layer it belongs to (DESIGN.md, "Defined
/// words by layer"): at L1 the numeric casts, the `String` cast that interpolation calls, the
/// `String` functions the documentation uses, and `min` and `max`, which the table does not list
/// and so enter with the scalars they take; at L2 `build`, the build constant (step L2.8d).
/// The table's other names that are no word are left
/// out: `main` and the ports `clock` and `log`, which a program names, and `abs` of L14, the L1
/// word on more types. The prelude's facet words, the table's third column, are words too: a
/// facet is a value of the prelude struct `Facet` bound to a name, with no facet keyword
/// (sec:checking_in_zed), so `with units("m")` names the value `units`. The facets a program
/// defines (`parity`) are its own names. The step test `l02_03_name_resolution::later_words`
/// checks these tables against the table in DESIGN.md.
pub const WORDS: &[(&str, u32)] = &[
    ("String", 1),
    ("int", 1),
    ("rat", 1),
    ("f64", 1),
    ("f32", 1),
    ("abs", 1),
    ("min", 1),
    ("max", 1),
    ("len", 1),
    ("lower", 1),
    ("upper", 1),
    ("trim", 1),
    ("sum", 1),
    ("bitAnd", 1),
    ("bitOr", 1),
    ("bitXor", 1),
    ("bitNot", 1),
    ("shl", 1),
    ("shr", 1),
    ("popCount", 1),
    ("leadingZeros", 1),
    ("trailingZeros", 1),
    ("rotl", 1),
    ("rotr", 1),
    ("f64Bits", 1),
    ("codePoint", 1),
    ("scalar", 1),
    ("utf8", 1),
    ("fromUtf8", 1),
    ("mulHi", 1),
    ("bitReverse", 1),
    ("byteSwap", 1),
    ("pdep", 1),
    ("pext", 1),
    ("funnelShl", 1),
    ("funnelShr", 1),
    ("sqrt", 1),
    ("fma", 1),
    ("build", 2),
    ("count", 3),
    ("map", 3),
    ("where", 3),
    ("foldl", 3),
    ("foldr", 3),
    ("reduce", 3),
    ("any", 3),
    ("all", 3),
    ("find", 3),
    ("split", 3),
    ("lines", 3),
    ("concat", 3),
    ("fam", 3),
    ("discard", 3),
    ("fold", 3),
    ("reindex", 3),
    ("gen", 3),
    ("rekey", 4),
    ("group", 4),
    ("flatMap", 4),
    ("tag", 4),
    ("sort", 5),
    ("orderedValues", 5),
    ("scan", 5),
    ("zip", 5),
    ("patch", 5),
    ("join", 5),
    ("diff", 5),
    ("first", 5),
    ("last", 5),
    ("minBy", 5),
    ("maxBy", 5),
    ("slice", 5),
    ("take", 5),
    ("drop", 5),
    ("takeWhile", 5),
    ("chunkBy", 5),
    ("upTo", 5),
    ("from", 5),
    ("fix", 6),
    ("window", 7),
    ("merge", 7),
    ("latest", 7),
    ("reducer", 7),
    ("bound", 7),
    ("timeout", 7),
    ("order", 7),
    ("finite", 7),
    ("bits", 7),
    ("endian", 7),
    ("at", 7),
    ("length", 7),
    ("terminated", 7),
    ("tagged", 7),
    ("arg", 7),
    ("release", 7),
    ("transfer", 7),
    ("concurrency", 7),
    ("period", 7),
    ("priority", 7),
    ("coalesce", 7),
    ("cancel", 7),
    ("refine", 10),
    ("meet", 11),
    ("entails", 11),
    ("units", 12),
    ("taint", 13),
    ("layout", 14),
    ("complex", 14),
    ("quat", 14),
    ("oct", 14),
    ("conj", 14),
    ("normSq", 14),
    ("inv", 14),
    ("matmul", 14),
    ("dot", 14),
    ("norm", 14),
    ("cross", 14),
    ("solve", 14),
    ("byInduction", 15),
    ("bySimp", 15),
    ("byCases", 15),
    ("using", 15),
    ("anyIntro", 15),
    ("anyElim", 15),
    ("allElim", 15),
    ("allIntro", 15),
    ("reflect", 15),
    ("unique", 16),
    ("compile", 19),
    ("mix", 19),
    ("store", 21),
    ("retry", 21),
    ("hedge", 21),
    ("breaker", 21),
    ("rate", 21),
    ("peers", 21),
    ("ofNat", 22),
    ("additive", 22),
    ("dual", 22),
    ("byStrongInduction", 22),
    ("byCollectionInduction", 22),
    ("evalPoly", 22),
    ("normalForm", 22),
    ("expand", 22),
    ("simplify", 22),
    ("substitute", 22),
    ("derivative", 22),
    ("target", 24),
    ("verify", 25),
    ("explain", 25),
    ("obligations", 25),
    ("check", 25),
    ("recovery", 27),
];

/// The layer of the prelude value word `name`, if it is one.
pub fn prelude_layer(name: &str) -> Option<u32> {
    WORDS
        .iter()
        .find(|(w, _)| *w == name)
        .map(|&(_, layer)| layer)
}

/// Whether `name` is a prelude value word of any layer or a prelude type name.
pub fn is_prelude_name(name: &str) -> bool {
    prelude_layer(name).is_some()
        || TYPES.contains(&name)
        || later_type_layer(name).is_some()
        || name == MAIN_ARGS
}

/// The prelude struct of `main`'s argument, `main(m: MainArgs)`. The parser reads it in `main`'s
/// header and gives `main` the fields its body uses (MAIN-args), so the resolver meets the name
/// only elsewhere, where this zedc does not take it ([`main_args_elsewhere`]).
const MAIN_ARGS: &str = "MainArgs";

/// The layer of the prelude type `name` of a later layer, if it is one.
fn later_type_layer(name: &str) -> Option<u32> {
    LATER_TYPES
        .iter()
        .find(|(t, _)| *t == name)
        .map(|&(_, layer)| layer)
}

/// The annotations, each with the layer it belongs to (DESIGN.md, "Defined words by layer").
/// `@hash`, of layer L2, pins an import and annotates no declaration; `@nonblocking`, of layer
/// L2 on a function written in Zed, marks one the checker proves never blocks, and at L7 a
/// foreign function, as `@blocking` does.
pub const ANNOTATIONS: &[(&str, u32)] = &[
    ("hash", 2),
    ("nonblocking", 2),
    ("foreign", 7),
    ("export", 7),
    ("borrowed", 7),
    ("stateless", 7),
    ("log", 7),
    ("after", 7),
    ("blocking", 7),
    ("checked", 10),
    ("invariant", 15),
    ("ensure", 15),
    ("exhaustive", 15),
    ("exact", 15),
    ("associative", 16),
    ("commutative", 16),
    ("idempotent", 16),
    ("injective", 16),
    ("assume", 16),
    ("measure", 17),
    ("cost", 18),
    ("fused", 18),
    ("memoized", 18),
    ("noalloc", 18),
    ("preallocated", 18),
    ("decides", 22),
    ("require", 24),
];

/// The layer of the annotation `@name`, if it is one.
pub fn annotation_layer(name: &str) -> Option<u32> {
    ANNOTATIONS
        .iter()
        .find(|(w, _)| *w == name)
        .map(|&(_, layer)| layer)
}

/// Whether `a` is written `@name(#off)`, with the one argument `#off`.
fn is_off(a: &Annot) -> bool {
    a.named.is_empty()
        && matches!(&a.positional[..], [Expr { kind: ExprKind::Atom(x), .. }] if x == "off")
}

/// The type names of the prelude at L1; a unit declares no type before L2.
pub const TYPES: &[&str] = &[
    "int",
    "rat",
    "f64",
    "f32",
    "bool",
    "String",
    "Lines",
    "Files",
    "CommandLine",
    "Never",
];

/// The type names of the prelude's later layers, each with its layer (DESIGN.md, "Defined words
/// by layer"). A use below its layer is an error naming the layer, as for a value word. The
/// number algebras of L14 are words too, applied to build a value; the fixed-width aliases of
/// L7, `i8` to `i64` and `u8 = int[0..=255]`, are types only. The float formats `f16` and
/// `bf16` are of L1 and not yet built (step L1.18a), so neither list holds them.
pub const LATER_TYPES: &[(&str, u32)] = &[
    ("Seq", 5),
    ("Ast", 6),
    ("Facet", 6),
    ("Lattice", 6),
    ("Reduction", 6),
    ("Store", 6),
    ("Rejection", 6),
    ("Interval", 6),
    ("Congruence", 6),
    ("Bound", 6),
    ("Stream", 7),
    ("Instant", 7),
    ("Duration", 7),
    ("Ptr", 7),
    ("i8", 7),
    ("i16", 7),
    ("i32", 7),
    ("i64", 7),
    ("u8", 7),
    ("FloatClass", 11),
    ("Constraints", 11),
    ("UnitText", 12),
    ("UnitDef", 12),
    ("UnitSpelling", 12),
    ("Nonzero", 12),
    ("UnitName", 12),
    ("UnitKind", 12),
    ("UnitPower", 12),
    ("UnitFactor", 12),
    ("UnitProduct", 12),
    ("complex", 14),
    ("quat", 14),
    ("oct", 14),
    ("Proof", 15),
    ("Semigroup", 22),
    ("Monoid", 22),
    ("NonCommRing", 22),
    ("CommRing", 22),
    ("Ring", 22),
    ("Picture", 34),
    ("Pointer", 34),
    ("Keys", 34),
    ("Midi", 34),
    ("Camera", 34),
    ("Audio", 34),
    ("Sensors", 34),
];

/// The carriers, which a bounded type variable ranges over, in the order the checker prints
/// them.
const CARRIERS: &[&str] = &["int", "f32", "f64", "rat", "String", "bool"];

/// The resolution of `unit`, read alone, or every error in it and every form it uses that a
/// later step compiles, in text order.
pub fn resolve(unit: &[Stmt]) -> Result<Resolution, Vec<Error>> {
    resolve_text(unit, None)
}

/// [`resolve`], with the unit's text when it is known, which a message quotes: the lines of a
/// definition used above it ("Name used above its definition").
pub fn resolve_text(unit: &[Stmt], text: Option<&str>) -> Result<Resolution, Vec<Error>> {
    let Resolved {
        res,
        mut errors,
        later,
    } = resolve_in_text(unit, &Alone, text);
    if errors.is_empty() && later.is_empty() {
        return Ok(res);
    }
    errors.extend(later);
    errors.sort_by_key(|e| e.span);
    Err(errors)
}

/// The resolution of `unit`, which reads the other units through `units`, with its errors and
/// its forms of later steps, each in text order.
pub fn resolve_in(unit: &[Stmt], units: &dyn Units) -> Resolved {
    resolve_in_text(unit, units, None)
}

/// [`resolve_in`], with the unit's text when it is known, as [`resolve_text`].
pub fn resolve_in_text(unit: &[Stmt], units: &dyn Units, text: Option<&str>) -> Resolved {
    resolve_kept(unit, None, units, text)
}

/// [`resolve_in_text`] for the statements of `unit` that `keep` marks, one flag per statement,
/// or for all when `keep` is `None`: the unit as if the others were not written, read with no
/// copy of the statements kept (step L1.29d leaves out those that use a name a declaration that
/// does not parse would define).
pub fn resolve_kept(
    unit: &[Stmt],
    keep: Option<&[bool]>,
    units: &dyn Units,
    text: Option<&str>,
) -> Resolved {
    let mut r = Resolver {
        units: Some(units),
        text,
        ..Resolver::default()
    };
    // The top level is two scopes: the outer holds what its imports bring in (tier 3), the
    // inner what it declares (tier 2), which shadows it.
    r.scopes.push(Vec::new());
    r.scopes.push(Vec::new());
    r.walk(Task::Unit(unit, keep));
    r.above_errors();
    r.errors.sort_by_key(|e| e.span);
    r.later.sort_by_key(|e| e.span);
    Resolved {
        res: r.out,
        errors: r.errors,
        later: r.later,
    }
}

/// The errors name resolution finds in the type `t`, read as a type the checker printed
/// (OSP-diag, DESIGN.md "Printed types are syntax"): the walk a written type gets, the names in
/// `leaves` standing for the leaves of layer L10 a printed type holds (`_`, `!_`, a literal),
/// and the forms of step L2.5 the checker prints from L1 on: an atom's payload type, read through
/// to its parts, an atom with any payload `#a(..)` and every struct `{..}`. A type variable no bounds clause around it binds is not defined.
pub fn printed_type(t: &Type, leaves: HashSet<Arc<str>>) -> Result<(), Vec<Error>> {
    let mut r = Resolver {
        printed: Some(leaves),
        ..Resolver::default()
    };
    r.walk(Task::Ty(t));
    r.errors.append(&mut r.later);
    if r.errors.is_empty() {
        Ok(())
    } else {
        r.errors.sort_by_key(|e| e.span);
        Err(r.errors)
    }
}

/// The level of the top level's outer scope, which holds what its imports bring in.
const IMPORTS: usize = 1;
/// The level of the top level's inner scope, which holds what it declares.
const TOP: usize = 2;

/// What a name is found to be: binders of the unit, a name two imports bring in, a name of the
/// prelude unit, or a prelude word of a layer.
enum Found {
    Bound(Vector<usize>),
    /// Two binders from different units, which make the name ambiguous.
    Ambiguous(usize, usize),
    /// The prelude unit, by its path.
    Unit(Arc<str>),
    Word(u32),
}

#[derive(Default)]
struct Resolver<'u> {
    out: Resolution,
    errors: Vec<Error>,
    /// The forms a later step compiles, reported apart from the errors.
    later: Vec<Error>,
    /// The other units, or `None` when a printed type is read.
    units: Option<&'u dyn Units>,
    /// The scopes, outermost first: the names each binds.
    scopes: Vec<Vec<String>>,
    /// The bindings of each name in the open scopes, innermost last, so a name is found in
    /// `O(1)` however deep the scopes nest.
    // Complexity tradeoff (COMPLEXITY.md F16): the naive lookup walks the chain of scopes
    // outward, O(depth) per use and O(uses · depth) over a nest (ratio 34 at 8 times the
    // depth); a stack per name finds the innermost binding in O(1), at one stack entry per
    // binding and a pop of each name a scope binds when it closes (`scopes`).
    visible: HashMap<String, Vec<Bound>>,
    /// Whether the declaration being bound is marked `local`.
    local: bool,
    /// The binders of imports that failed: their uses are not reported again.
    dead: HashSet<usize>,
    /// Those of `dead` that a unit would define but for its syntax errors: each use of one is
    /// recorded in [`Resolution::broken`].
    broken: HashSet<usize>,
    /// The type variables a bounds clause around the type being walked binds, by name.
    tvars: HashMap<String, TypeVar>,
    /// The function types around the type being walked, outermost first, by their text.
    arrows: Vec<Span>,
    /// The bounds clauses around the type being walked, outermost first, by their text.
    clauses: Vec<Span>,
    /// When a printed type is read ([`printed_type`]): the names that stand for its leaves of
    /// layer L10.
    printed: Option<HashSet<Arc<str>>>,
    /// The region of each `else`'s operand, by the `else`'s text: an `else` inside another
    /// region gets its region when that region's flow is walked, before the `else` itself.
    else_regions: HashMap<Span, usize>,
    /// The unit's text, when known, which the message of a name used above its definition
    /// quotes.
    text: Option<&'u str>,
    /// Each binder of a block, a field list or a parameter list used above its definition,
    /// with its first use in the text (DESIGN.md sec:lexical, "A name is defined above every
    /// use"): one error each, made when the walk ends ([`Resolver::above_errors`]).
    // Complexity tradeoff (COMPLEXITY.md F16b): the naive check rescans the block for the
    // binding's line at each use, O(uses · bindings) over a block (a chain of n uses in a
    // block of n bindings is O(n²)); each binder's text position is recorded when it is bound,
    // so a use is compared with it in O(1), at no memory beyond the binder table and one entry
    // here per binder used too early.
    above: HashMap<usize, Span>,
    /// The body of each `main` with its parameter written, `m` in `main(m: MainArgs)`, and that
    /// name: a use of the name alone, not a read of a field, is not defined, and its message
    /// says what `m` is ([`main_param_alone`]).
    main_params: Vec<(Span, String)>,
    /// Each block, parameter list and field list of the unit below the top level that binds a
    /// name, in the order its binders were made: where a definition used above it may move.
    lists: Vec<List>,
    /// The binders of the top level and of its imports.
    tops: HashSet<usize>,
    /// The binders bound to a lambda, `f = (x) -> e;`, which call like functions.
    lambdas: HashSet<usize>,
}

/// A block, a parameter list or a field list: its binders, and each of its items (a statement,
/// a parameter or port, a field) in text order with its binder when it binds one name.
struct List {
    ids: Range<usize>,
    items: Vec<(Span, Option<usize>)>,
}

/// A type variable of a bounds clause, while its type is walked.
struct TypeVar {
    /// Its text in the clause.
    span: Span,
    /// How many function types were open around the clause.
    depth: usize,
    /// Its first use, and the outermost function type inside the clause that holds the use,
    /// if one does.
    first: Option<(Span, Option<Span>)>,
}

/// A name's binders in one scope.
struct Bound {
    /// How many scopes are open around the scope, itself included.
    level: usize,
    ids: Vector<usize>,
    /// The written parameter types of each, which tell an overload's arrows apart: a set, so
    /// declaring `K` overloads costs `O(K)`, not `O(K²)`.
    // Complexity tradeoff (COMPLEXITY.md F16): comparing each new overload with every
    // earlier one costs O(K²); a hash set of the written parameter types costs O(1) per
    // overload (O(length of the types) to hash), at one entry of memory per overload.
    signatures: HashSet<Option<Vec<Option<String>>>>,
    /// Whether every binder is a function, so the binders are arrows of one overload set.
    functions: bool,
    /// Whether every binder is a name an import brings in.
    imported: bool,
    /// Two binders that two imports from different units bring in, when not all are functions:
    /// a use of the name is ambiguous.
    ambiguous: Option<(usize, usize)>,
}

impl Bound {
    fn new(level: usize, kind: Kind, imported: bool) -> Self {
        Bound {
            level,
            ids: Vector::new(),
            signatures: HashSet::new(),
            functions: kind == Kind::Function,
            imported,
            ambiguous: None,
        }
    }
}

impl Resolver<'_> {
    /// Binds `name`, written at `at`, in the innermost scope; `span` is the text that binds it
    /// and `signature` a function's parameter types. A name that names a type is an error, and
    /// is bound all the same, so that its uses are not reported as well.
    fn bind(
        &mut self,
        name: &str,
        at: Span,
        span: Span,
        kind: Kind,
        signature: Option<Vec<Option<String>>>,
    ) {
        if name.ends_with('\'') {
            return self.primed(name, span);
        }
        if TYPES.contains(&name) {
            self.names_type(name, at, span, kind.binder());
        }
        let id = self.out.binders.len();
        let level = self.scopes.len();
        let here = (self.visible.get(name))
            .and_then(|v| v.last())
            .filter(|b| b.level == level);
        if let Some(b) = here {
            let first = &self.out.binders[b.ids[0]];
            let overload =
                kind == Kind::Function && b.functions && !b.signatures.contains(&signature);
            if !overload {
                let (message, note) = match &signature {
                    Some(_) if first.kind == Kind::Function => (
                        format!(
                            "`{name}` is already declared in this scope with these parameter types"
                        ),
                        format!("the first `{name}` with these parameter types"),
                    ),
                    _ if b.imported => (
                        format!("`{name}` is already bound in this scope by an import"),
                        format!("the import that brings `{name}` into this scope"),
                    ),
                    _ => (
                        format!("`{name}` is already bound in this scope"),
                        format!("the first binding of `{name}`"),
                    ),
                };
                let mut notes = vec![
                    Note {
                        span: first.span,
                        text: note,
                    },
                    Note {
                        span,
                        text: "repair: give this binding a new name".into(),
                    },
                ];
                // Shadowing is legal in a nested scope (sec:lexical); the top level has none
                // to move a binding into.
                if level > TOP {
                    notes.push(Note {
                        span,
                        text: "repair: move this binding into a nested block, where it shadows \
                               the first"
                            .into(),
                    });
                }
                self.errors.push(Error {
                    row: Some(Row::Rebinding),
                    menu: String::new(),
                    span,
                    message,
                    notes,
                });
                return;
            }
        }
        let v = self.visible.entry(name.into()).or_default();
        if v.last().is_none_or(|b| b.level != level) {
            v.push(Bound::new(level, kind, false));
            self.scopes.last_mut().expect("a scope").push(name.into());
        }
        let b = v.last_mut().expect("pushed above");
        b.ids.push_back(id);
        b.signatures.insert(signature);
        b.functions &= kind == Kind::Function;
        b.imported = false;
        if level == TOP {
            self.out.exports.add(name, kind, self.local);
            self.tops.insert(id);
        }
        if self.local {
            self.out.local.insert(id);
        }
        self.out.binders.push(Binder {
            name: name.into(),
            span,
            kind,
        });
    }

    /// Binds `name`, which the import at `span` brings in from `unit` with the kind `kind` it
    /// has there: at the top level in the scope of its imports, in a block in the block's
    /// scope. Two imports of one name are kept, and make its uses ambiguous unless all are
    /// functions or both come from one unit.
    fn bind_import(&mut self, name: &str, span: Span, kind: Kind, unit: &Arc<str>) -> usize {
        if TYPES.contains(&name) {
            self.names_type(name, span, span, kind.binder());
        }
        let id = self.out.binders.len();
        let level = match self.scopes.len() {
            TOP => IMPORTS,
            n => n,
        };
        let v = self.visible.entry(name.into()).or_default();
        // At most the two scopes of the top level are open when an import of the top level is
        // bound, so this looks at two entries at most; in a block, at the last.
        let pos = v.iter().rposition(|b| b.level < level).map_or(0, |i| i + 1);
        match v.get_mut(pos).filter(|b| b.level == level) {
            Some(b) if !b.imported => {
                let first = b.ids[0];
                self.errors.push(Error {
                    row: Some(Row::Rebinding),
                    menu: String::new(),
                    span,
                    message: format!("`{name}` is already bound in this scope"),
                    notes: vec![
                        Note {
                            span: self.out.binders[first].span,
                            text: format!("the binding of `{name}` the import would hide"),
                        },
                        Note {
                            span: self.out.binders[first].span,
                            text: "repair: give this binding a new name".into(),
                        },
                    ],
                });
                self.dead.insert(id);
            }
            Some(b) => {
                let first = b.ids[0];
                b.functions &= kind == Kind::Function;
                if b.ambiguous.is_none() && !b.functions && self.out.imports[&first] != *unit {
                    b.ambiguous = Some((first, id));
                }
                b.ids.push_back(id);
            }
            None => {
                let mut b = Bound::new(level, kind, true);
                b.ids.push_back(id);
                v.insert(pos, b);
                self.scopes[level - 1].push(name.into());
            }
        }
        if level == IMPORTS {
            self.tops.insert(id);
        }
        self.out.imports.insert(id, unit.clone());
        self.out.binders.push(Binder {
            name: name.into(),
            span,
            kind,
        });
        id
    }

    fn open(&mut self) {
        self.scopes.push(Vec::new());
    }

    /// Closes the innermost scope, so its names name what they named outside it.
    fn close(&mut self) {
        for name in self.scopes.pop().expect("an open scope") {
            let v = self.visible.get_mut(&name).expect("bound in the scope");
            v.pop();
            if v.is_empty() {
                self.visible.remove(&name);
            }
        }
    }

    /// What `name` names here, or `None`.
    fn find(&self, name: &str) -> Option<Found> {
        if let Some(v) = self.visible.get(name)
            && let Some(b) = v.last()
        {
            if let Some((a, c)) = b.ambiguous {
                return Some(Found::Ambiguous(a, c));
            }
            let mut ids = b.ids.clone();
            // The top level's functions and its imports' are one overload set.
            if let [.., low, top] = &v[..]
                && top.level == TOP
                && low.level == IMPORTS
                && top.functions
                && low.functions
            {
                ids.append(low.ids.clone());
            }
            return Some(Found::Bound(ids));
        }
        if let Some((unit, exports)) = self.units.and_then(|u| u.prelude())
            && exports.get(name).is_some_and(|e| !e.local)
        {
            return Some(Found::Unit(unit.clone()));
        }
        prelude_layer(name).map(Found::Word)
    }

    /// The error that `name`, used at `span`, names the binders `a` and `b`, which two imports
    /// from different units bring in.
    fn ambiguous(&mut self, name: &str, span: Span, a: usize, b: usize) {
        let unit = &self.out.imports[&a];
        let q = unit.rsplit('.').next().unwrap_or_default();
        let notes = [a, b]
            .map(|i| Note {
                span: self.out.binders[i].span,
                text: format!(
                    "this import brings `{name}` in from the unit `{}`",
                    self.out.imports[&i]
                ),
            })
            .into();
        self.errors.push(Error {
            row: None,
            menu: String::new(),
            span,
            message: format!(
                "`{name}` is ambiguous between two imports. Try `{q}.{name}` after `import {unit};` \
                 instead"
            ),
            notes,
        });
    }

    /// Notes the use at `span` of `name`, which names `ids`, when it stands above its
    /// definition in a block, a field list or a parameter list. A unit's top-level
    /// declarations and its imports may be named in any order (DESIGN.md sec:lexical), so only
    /// the binders of an inner scope are compared. `O(1)`.
    fn order(&mut self, name: &str, span: Span, ids: &Vector<usize>) {
        let inner = (self.visible.get(name))
            .and_then(|v| v.last())
            .is_some_and(|b| b.level > TOP && !b.imported);
        let id = ids[0];
        if inner && self.out.binders[id].span.start > span.start {
            let first = self.above.entry(id).or_insert(span);
            *first = (*first).min(span);
        }
    }

    /// The error "Name used above its definition" for each binder [`Resolver::order`] noted,
    /// at its first use: the use and the definition, each with its line, why the text is
    /// written in that order, and the menu of repairs (DESIGN.md sec:diagnostics).
    fn above_errors(&mut self) {
        if self.above.is_empty() {
            return;
        }
        // The first byte of each line, found once, so each line number is a binary search.
        let starts: Vec<usize> = self.text.map_or_else(Vec::new, |t| {
            std::iter::once(0)
                .chain(t.match_indices('\n').map(|(i, _)| i + 1))
                .collect()
        });
        let line = |at: usize| starts.partition_point(|&s| s <= at);
        let quote = |s: Span| self.text.map(|t| t[s.start..s.end].trim().to_string());
        let mut found: Vec<(usize, Span)> = self.above.drain().collect();
        found.sort_by_key(|&(_, s)| s);
        let mut errors = Vec::new();
        for (id, used) in found {
            let def = &self.out.binders[id];
            let (name, d) = (&def.name, def.span);
            let (list, what) = match def.kind {
                Kind::Field => ("a field list", "field"),
                Kind::Param | Kind::Port | Kind::Receiver => ("a parameter list", "parameter"),
                _ => ("a block", "definition"),
            };
            let block = what == "definition";
            let (lu, ld) = (line(used.start), line(d.start));
            let place = match self.text {
                None => " above its definition".to_string(),
                Some(_) if lu == ld => {
                    format!(" on line {lu}, before its definition later on that line")
                }
                Some(_) => format!(" on line {lu}, above its definition on line {ld}"),
            };
            let order = if block {
                "the lines".to_string()
            } else {
                format!("the {what}s")
            };
            let message = format!("`{name}` is used{place}");
            let rule = format!(
                "in {list} a name is used only below its definition, so that the text reads from \
                 the top; the order of {order} changes no result, since evaluation follows the \
                 dependencies, so moving the {what} above its first use changes nothing else"
            );
            let mut notes = vec![
                Note {
                    span: used,
                    text: rule,
                },
                Note {
                    span: used,
                    text: format!("`{name}` is used here, above its definition"),
                },
                Note {
                    span: d,
                    text: if block {
                        format!("the definition of `{name}`, below its first use")
                    } else {
                        format!("the {what} `{name}`, below its first use")
                    },
                },
            ];
            // The item of the list that holds the first use, which the definition moves above.
            let held = self
                .lists
                .partition_point(|l| l.ids.start <= id)
                .checked_sub(1)
                .map(|i| &self.lists[i])
                .filter(|l| l.ids.contains(&id))
                .and_then(|l| {
                    let k = l.items.partition_point(|(s, _)| s.start <= used.start);
                    k.checked_sub(1).map(|k| l.items[k])
                })
                .filter(|(s, _)| s.end > used.start);
            if let Some((s, user)) = held {
                // Moving the definition above `s` puts it above every line from `s` down to
                // it, so the move is offered only when the definition names none of them.
                // Complexity tradeoff (COMPLEXITY.md F16b): this reads the uses inside the
                // reported definition, O(u log n) for its u uses. Definitions of one block do
                // not overlap, so this is linear over a block; only nested definitions that are
                // all reported read a use once per level, O(uses · depth), and a program with
                // no error pays nothing.
                let names_between = self.uses_in(d).any(|b| {
                    let b = self.out.binders[b].span.start;
                    b >= s.start && b < d.start
                });
                if !names_between {
                    let text = match (block, quote(d), quote(s)) {
                        (true, Some(moved), _) => {
                            let ls = line(s.start);
                            let moved = match line(d.end.saturating_sub(1)) {
                                last if last == ld => format!("`{moved}`"),
                                last => {
                                    format!("lines {ld} to {last}, the definition of `{name}`,")
                                }
                            };
                            if ls == lu {
                                format!(
                                    "repair: move {moved} above line {lu}, where `{name}` is first used"
                                )
                            } else {
                                format!(
                                    "repair: move {moved} above line {ls}, where the statement \
                                     that first uses `{name}` begins"
                                )
                            }
                        }
                        (true, None, _) => format!(
                            "repair: move the definition of `{name}` above the statement that \
                             first uses `{name}`"
                        ),
                        (false, Some(moved), Some(user)) => {
                            format!("repair: move `{moved}` in front of `{user}`")
                        }
                        (false, _, _) => format!(
                            "repair: move the {what} `{name}` in front of the {what} whose \
                             default or type uses it"
                        ),
                    };
                    notes.push(Note { span: d, text });
                }
                // Functions that call each other: at the top level they may name each other in
                // any order. Offered when neither reads a value of the block, and the top level
                // has neither name yet.
                if let Some(user) = user
                    && block
                    && names_between
                    && self.function_like(id)
                    && self.function_like(user)
                    && self.out.exports.get(name).is_none()
                    && self.out.exports.get(&self.out.binders[user].name).is_none()
                    && self.closed(d, s, [id, user])
                    && self.closed(s, d, [id, user])
                {
                    let other = &self.out.binders[user].name;
                    let text = match (quote(s), quote(d)) {
                        (Some(a), Some(b)) => format!(
                            "repair: `{other}` and `{name}` call each other, so define both at \
                             the top level of the unit, where definitions may name each other in \
                             any order: move `{a}` and `{b}` out of the block to the top level"
                        ),
                        _ => format!(
                            "repair: `{other}` and `{name}` call each other, so define both at \
                             the top level of the unit, where definitions may name each other in \
                             any order"
                        ),
                    };
                    notes.push(Note { span: d, text });
                }
            }
            errors.push(Error {
                row: Some(Row::NameAboveDefinition),
                menu: String::new(),
                span: used,
                message,
                notes,
            });
        }
        self.errors.extend(errors);
    }

    /// The binders the uses inside `span` name, each use once. `O(k log n)` for `k` uses.
    fn uses_in(&self, span: Span) -> impl Iterator<Item = usize> + '_ {
        let from = Span {
            start: span.start,
            end: span.start,
        };
        let to = Span {
            start: span.end,
            end: span.end,
        };
        self.out.uses.range(from..to).filter_map(|(_, r)| match r {
            Ref::Bound(ids) => Some(ids[0]),
            _ => None,
        })
    }

    /// Whether the name `n`, used here, names a `main` function: every function named `main`
    /// is a `main`, as the builder gives it `main`'s header; a binding or parameter `main` is
    /// another name.
    // Cost: a string compare at each use, and only at a use of the word `main` a hash lookup of
    // the scope and a pass over the binders it finds, O(1) for the one `main` a scope has.
    fn names_main(&self, n: &str) -> bool {
        n == "main"
            && matches!(self.find(n), Some(Found::Bound(ids))
                if ids.iter().any(|&i| self.out.binders[i].kind == Kind::Function))
    }

    /// Whether the binder `id` is a function: declared as one, or bound to a lambda.
    fn function_like(&self, id: usize) -> bool {
        self.out.binders[id].kind == Kind::Function || self.lambdas.contains(&id)
    }

    /// Whether the definition at `span` reads nothing of its block but itself, the definition
    /// at `other` and the binders `own`: every name it uses is of the top level, an import or
    /// the prelude, or bound inside one of the two.
    fn closed(&self, span: Span, other: Span, own: [usize; 2]) -> bool {
        let inside = |s: Span, t: Span| s.start >= t.start && s.end <= t.end;
        self.uses_in(span).all(|b| {
            let at = self.out.binders[b].span;
            own.contains(&b) || self.tops.contains(&b) || inside(at, span) || inside(at, other)
        })
    }

    /// Records the use of `name` at `span`, or the error that it names nothing at L1.
    fn name(&mut self, name: &str, span: Span) {
        if name.ends_with('\'') {
            return self.primed(name, span);
        }
        let message =
            match self.find(name) {
                Some(Found::Bound(ids)) if self.dead.contains(&ids[0]) => {
                    return self.dead_use(ids[0], span);
                }
                Some(Found::Bound(ids)) if self.out.binders[ids[0]].kind == Kind::Unit => {
                    let unit = &self.out.imports[&ids[0]];
                    format!(
                        "`{name}` names the unit `{unit}`, which is no value; a definition of the \
                     unit is written `{name}.f`"
                    )
                }
                Some(Found::Bound(ids)) => {
                    self.order(name, span, &ids);
                    self.out.uses.insert(span, Ref::Bound(ids));
                    return;
                }
                Some(Found::Ambiguous(a, b)) => return self.ambiguous(name, span, a, b),
                Some(Found::Unit(unit)) => return self.prelude_unit(name, span, unit),
                // `build`, the one value word of L2, is read by `zedc::build` before elaboration.
                Some(Found::Word(layer)) if layer == 1 || name == "build" => {
                    self.out.uses.insert(span, Ref::Prelude(name.into()));
                    return;
                }
                Some(Found::Word(_)) => not_yet(&format!("the prelude word `{name}`")),
                // A prelude struct of a later layer is named as a value to build one.
                None if name == MAIN_ARGS => return self.errors.push(main_args_elsewhere(span)),
                // Every function but `main` reads the file port by its name (`zedc_syntax`'s
                // `Builder::main_files`); in `main`'s body the name is bound, to its parameter.
                None if name == "main::files" => {
                    self.out.uses.insert(span, Ref::Main(name.into()));
                    return;
                }
                None => match later_type_layer(name) {
                    Some(_) => not_yet(&format!("the prelude type `{name}`")),
                    None => match self.main_params.iter().any(|(body, m)| {
                        m == name && body.start <= span.start && span.end <= body.end
                    }) {
                        true => return self.errors.push(main_param_alone(name, span)),
                        false if self.prelude_broken(name, span) => return,
                        false => undefined(name),
                    },
                },
            };
        self.errors.push(Error {
            row: None,
            menu: String::new(),
            span,
            message,
            notes: Vec::new(),
        });
    }

    /// The use at `span` of `name`, a definition of the prelude unit `unit`.
    fn prelude_unit(&mut self, name: &str, span: Span, unit: Arc<str>) {
        let what = format!("`{name}`, a definition of the prelude unit `{unit}`,");
        self.out.uses.insert(
            span,
            Ref::Unit {
                unit,
                name: name.into(),
            },
        );
        self.linked(span, &what);
    }

    /// The member `q.name` at `span`, if `q`, used at `q_span`, is a qualifier: its use, and
    /// the definition `name` of its unit, or the error that the unit has no `name` another unit
    /// sees. `false` when `q` names no qualifier.
    fn qualified(&mut self, q: &str, q_span: Span, name: &str, span: Span) -> bool {
        let Some(Found::Bound(ids)) = self.find(q) else {
            return false;
        };
        let id = ids[0];
        if self.out.binders[id].kind != Kind::Unit {
            return false;
        }
        self.out.uses.insert(q_span, Ref::Bound(ids));
        if self.dead.contains(&id) {
            self.dead_use(id, span);
            return true;
        }
        let unit = self.out.imports[&id].clone();
        let import = self.out.binders[id].span;
        if self.export(&unit, name, span, import).is_none() {
            self.broken_member(&unit, name, span);
        } else {
            self.out.uses.insert(
                span,
                Ref::Unit {
                    unit,
                    name: name.into(),
                },
            );
            let what = format!("`{q}.{name}`, a definition of another unit,");
            self.linked(span, &what);
        }
        true
    }

    /// What the unit `unit`, which the import at `import` reads, defines as `name`, used at
    /// `span`; or the error that it defines no `name`, or only a `local` one.
    fn export(&mut self, unit: &Arc<str>, name: &str, span: Span, import: Span) -> Option<Export> {
        let exports = self.units.and_then(|u| u.exports(unit).ok())?;
        let message = match exports.get(name) {
            Some(e) if !e.local => return Some(e),
            // The unit's declaration of `name` does not parse, which is reported there.
            None if exports.is_broken(name) => return None,
            Some(_) => format!(
                "`{name}` is declared `local` in the unit `{unit}`, so no other unit sees it"
            ),
            None => format!("the unit `{unit}` defines no `{name}`"),
        };
        self.errors.push(Error {
            row: None,
            menu: String::new(),
            span,
            message,
            notes: vec![Note {
                span: import,
                text: format!("the import of the unit `{unit}`"),
            }],
        });
        None
    }

    /// The import `i`, the statement at `span`: the names it binds, each in the scope of its
    /// imports. An import of a unit the loader could not give is one error, or none when it lies
    /// on an import cycle, which the loader reports; its names are bound all the same, so that
    /// their uses are not reported as well.
    fn import(&mut self, i: &Import, span: Span) {
        let unit: Arc<str> = i.path.as_str().into();
        self.out.units.push((unit.clone(), span, i.pin));
        let mut unknown = false;
        let exports = match self.units.map(|u| u.exports(&i.path)) {
            Some(Ok(e)) => Some(e),
            Some(Err(Refused::Because(why))) => {
                self.errors.push(Error {
                    row: None,
                    menu: String::new(),
                    span,
                    message: format!("the unit `{unit}` cannot be imported: {why}"),
                    notes: Vec::new(),
                });
                None
            }
            Some(Err(Refused::OnCycle)) => None,
            Some(Err(Refused::Unknown)) => {
                unknown = true;
                None
            }
            None => None,
        };
        let qualifier = match &i.kind {
            ImportKind::Qualified => i.path.rsplit('.').next().unwrap_or_default(),
            ImportKind::Alias(g) => g.as_str(),
            ImportKind::Selective(names) => {
                for n in names {
                    let found = exports.map(|_| self.export(&unit, n, span, span));
                    let kind = found.flatten().map_or(Kind::Binding, |e| e.kind);
                    let id = self.bind_import(n, span, kind, &unit);
                    if !matches!(found, Some(Some(_))) {
                        self.dead.insert(id);
                    }
                    if unknown || exports.is_some_and(|e| e.is_broken(n)) {
                        self.broken.insert(id);
                    }
                }
                return;
            }
        };
        let id = self.bind_import(qualifier, span, Kind::Unit, &unit);
        if exports.is_none() {
            self.dead.insert(id);
        }
        if unknown {
            self.broken.insert(id);
        }
    }

    /// Whether `name`, used at `span` and found nowhere, is a name the prelude unit would
    /// define but for its syntax errors: then the use is recorded as a broken use.
    fn prelude_broken(&mut self, name: &str, span: Span) -> bool {
        let prelude = self.units.and_then(|u| u.prelude());
        let broken = prelude.is_some_and(|(_, e)| e.is_broken(name));
        if broken {
            self.out.broken.push(span);
        }
        broken
    }

    /// The use at `span` of `name` through a qualifier of `unit`, which does not define it:
    /// recorded as a broken use when `unit` would define it but for its syntax errors.
    fn broken_member(&mut self, unit: &str, name: &str, span: Span) {
        let units = self.units.and_then(|u| u.exports(unit).ok());
        if units.is_some_and(|e| e.is_broken(name)) {
            self.out.broken.push(span);
        }
    }

    /// The use at `span` of the binder `id` of an import that failed: recorded as a broken use
    /// when the binder is one a unit would define but for its syntax errors, else nothing,
    /// since the import has its error.
    fn dead_use(&mut self, id: usize, span: Span) {
        if self.broken.contains(&id) {
            self.out.broken.push(span);
        }
    }

    /// Does `root` and every task it leads to, in written order. The tasks wait on a stack on
    /// the heap, so a unit of any nesting depth is resolved on a small thread stack; a task
    /// pushes the pieces it leads to in reverse, so they are done, and their binders numbered,
    /// in the order the text gives.
    fn walk<'a>(&mut self, root: Task<'a>) {
        let mut todo = vec![root];
        while let Some(task) = todo.pop() {
            match task {
                Task::Unit(stmts, None) => self.stmts(stmts.iter(), true, &mut todo),
                Task::Unit(stmts, Some(keep)) => {
                    let kept = stmts.iter().zip(keep).filter(|(_, k)| **k);
                    self.stmts(kept.map(|(s, _)| s), true, &mut todo);
                }
                Task::Stmts(stmts) => self.stmts(stmts.iter(), false, &mut todo),
                Task::Stmt(s, top) => self.stmt(s, top, &mut todo),
                Task::Function {
                    params,
                    ports,
                    body,
                    this,
                } => self.function(params, ports, body, this, &mut todo),
                Task::Expr(e) => self.expr(e, &mut todo),
                Task::Ty(t) => self.ty(t, &mut todo),
                Task::TypeName(n, span) => self.type_name(n, span),
                Task::Pattern(p, report) => self.pattern(p, report, &mut todo),
                Task::BindPattern(name, span) => self.bind(name, span, span, Kind::Pattern, None),
                Task::Else {
                    span,
                    pattern,
                    default,
                } => {
                    self.open();
                    todo.push(Task::Close);
                    todo.push(Task::Expr(default));
                    if let Some(p) = pattern {
                        let start = self.out.binders.len();
                        todo.push(Task::PatternEnd(span, start));
                        todo.push(Task::Pattern(p, true));
                    }
                }
                Task::Arm(arm) => {
                    self.open();
                    todo.push(Task::Close);
                    todo.push(Task::Expr(&arm.body));
                    todo.extend(arm.guard.as_ref().map(Task::Expr));
                    let start = self.out.binders.len();
                    todo.push(Task::PatternEnd(arm.span, start));
                    // The `match` is reported as a form of a later step, so its patterns are
                    // not reported again.
                    todo.push(Task::Pattern(&arm.pattern, false));
                }
                Task::For {
                    binders,
                    guard,
                    body,
                } => {
                    self.open();
                    for t in binders {
                        if let Target::Name(n, at) = t {
                            self.bind(n, *at, *at, Kind::Pattern, None);
                        }
                    }
                    todo.push(Task::Close);
                    todo.push(Task::Expr(body));
                    todo.extend(guard.map(Task::Expr));
                }
                Task::PatternEnd(span, start) => {
                    let end = self.out.binders.len();
                    self.out.patterns.insert(span, start..end);
                }
                Task::Member(span, name) => {
                    if name.ends_with('\'') {
                        self.later(span, &format!("the primed field `{name}`"));
                    } else if let Some(Found::Bound(ids)) = self.find(name) {
                        if self.dead.contains(&ids[0]) {
                            self.dead_use(ids[0], span);
                        } else {
                            self.order(name, span, &ids);
                            self.out.uses.insert(span, Ref::Bound(ids));
                        }
                    }
                }
                Task::Close => self.close(),
                Task::ArrowEnd => {
                    self.arrows.pop();
                }
                Task::ForEnd(ty, bounds) => self.for_end(ty, bounds),
            }
        }
    }

    /// Records the list whose items are `items`, in text order, and whose binders were made
    /// from `first` on, when it binds a name.
    fn list(&mut self, first: usize, items: Vec<(Span, Option<usize>)>) {
        let end = self.out.binders.len();
        if end > first {
            self.lists.push(List {
                ids: first..end,
                items,
            });
        }
    }

    /// The statements of the innermost scope: their binders first, so that a use finds its
    /// binder wherever it stands, and a use above its definition is reported as one.
    /// They are the unit's own statements when `top` holds.
    fn stmts<'a>(
        &mut self,
        stmts: impl DoubleEndedIterator<Item = &'a Stmt> + Clone,
        top: bool,
        todo: &mut Vec<Task<'a>>,
    ) {
        let mut families = HashSet::new();
        let first = self.out.binders.len();
        let mut items = Vec::new();
        for s in stmts.clone() {
            if !matches!(
                s.kind,
                StmtKind::Return(_)
                    | StmtKind::Push { .. }
                    | StmtKind::While(_)
                    | StmtKind::Until(_)
                    | StmtKind::Expr(_)
                    | StmtKind::Initial(_)
                    | StmtKind::UnitAnnot(_)
            ) {
                self.out.decls.insert(s.span.start);
            }
            let id = self.out.binders.len();
            self.declare(s, false, &mut families);
            let one = (self.out.binders.len() == id + 1).then_some(id);
            if let (Some(id), StmtKind::Bind { value, .. }) = (one, &s.kind)
                && matches!(value.kind, ExprKind::Lambda { .. })
            {
                self.lambdas.insert(id);
            }
            items.push((s.span, one));
        }
        if !top {
            self.list(first, items);
        }
        todo.extend(stmts.rev().map(|s| Task::Stmt(s, top)));
    }

    /// Binds the names the statement `s` declares. Resolution refuses the forms of layer L6
    /// whole, but binds their names, so that a use of one is not reported as well; in such a
    /// statement (`whole`) a primed name, a loop step's output, is not bound. The pieces of one
    /// indexed family bind its name once: `families` holds the families bound in this scope.
    fn declare<'s>(&mut self, s: &'s Stmt, whole: bool, families: &mut HashSet<&'s str>) {
        match &s.kind {
            StmtKind::Bind { targets, value } => {
                let id = self.out.binders.len();
                for t in targets {
                    match t {
                        Target::Name(n, _) if whole && n.ends_with('\'') => {}
                        Target::Name(n, at) => self.bind(n, *at, s.span, Kind::Binding, None),
                        Target::Wild => {}
                    }
                }
                if let [Target::Name(..)] = targets.as_slice()
                    && !whole
                    && self.out.binders.len() == id + 1
                {
                    let r = self.region(Vec::new());
                    self.out.regions[r].into = Some(id);
                    self.flow(value, r);
                }
            }
            StmtKind::Function(f) => {
                let signature = f
                    .params
                    .iter()
                    .map(|p| p.ty.as_ref().map(|t| t.to_string()));
                self.bind(
                    &f.name,
                    name_at(s.span, &f.name),
                    s.span,
                    Kind::Function,
                    Some(signature.collect()),
                );
            }
            StmtKind::Struct(st) => self.bind(&st.name, s.span, s.span, Kind::Struct, None),
            StmtKind::Type(t) => self.bind(&t.name, s.span, s.span, Kind::Type, None),
            StmtKind::Method(m)
                if m.receiver.ends_with('\'') || m.function.name.ends_with('\'') => {}
            StmtKind::Method(m) => {
                let name = format!("{}.{}", m.receiver, m.function.name);
                let signature = m
                    .function
                    .params
                    .iter()
                    .map(|p| p.ty.as_ref().map(|t| t.to_string()));
                self.bind(
                    &name,
                    name_at(s.span, &name),
                    s.span,
                    Kind::Method,
                    Some(signature.collect()),
                );
            }
            StmtKind::Import(i) => self.import(i, s.span),
            // The declaration is not annotated again, so this recursion is one level deep.
            StmtKind::Annotated { decl, .. } => self.declare(decl, whole, families),
            // A `local` before a `local` is refused and not walked into, so this recursion is
            // one level deep. A definition `local` marks in a block is refused but still bound
            // there, so its uses are not reported again.
            StmtKind::Local(decl) => {
                let top = self.local_here(s, decl);
                if top
                    || matches!(
                        decl.kind,
                        StmtKind::Bind { .. }
                            | StmtKind::Function(_)
                            | StmtKind::Struct(_)
                            | StmtKind::Type(_)
                            | StmtKind::Method(_)
                    )
                {
                    self.local = top;
                    self.declare(decl, whole, families);
                    self.local = false;
                }
            }
            StmtKind::IndexedDef(d) => {
                if !d.name.ends_with('\'') && families.insert(d.name.as_str()) {
                    self.bind(
                        &d.name,
                        name_at(s.span, &d.name),
                        s.span,
                        Kind::Binding,
                        None,
                    );
                }
            }
            StmtKind::Return(_)
            | StmtKind::Push { .. }
            | StmtKind::While(_)
            | StmtKind::Until(_)
            | StmtKind::Expr(_)
            | StmtKind::Initial(_)
            | StmtKind::UnitAnnot(_) => {}
        }
    }

    /// Whether `local` may mark `decl` in the statement `s`: it marks a definition, at a unit's
    /// top level (a loop body, where it also stands, is of layer L6). Otherwise the error why
    /// not.
    fn local_here(&mut self, s: &Stmt, decl: &Stmt) -> bool {
        let what = match &decl.kind {
            StmtKind::Bind { .. }
            | StmtKind::Function(_)
            | StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Method(_)
                if self.scopes.len() == TOP =>
            {
                return true;
            }
            StmtKind::Bind { .. }
            | StmtKind::Function(_)
            | StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Method(_) => {
                self.errors.push(Error {
                    row: None,
                    menu: String::new(),
                    span: s.span,
                    message: "`local` keeps a declaration from other units, and a declaration in a block is \
                              seen by no other unit already, so `local` stands only at a unit's top \
                              level or in a loop body. Remove the `local`."
                        .into(),
                    notes: Vec::new(),
                });
                return false;
            }
            StmtKind::Return(_) => "a `return`",
            StmtKind::Push { .. } => "a push",
            StmtKind::Initial(_) => "an `initial` statement, which belongs to a loop body",
            StmtKind::Import(_) => "an import, whose names are not definitions of the unit",
            StmtKind::Local(_) => "a `local` declaration again",
            StmtKind::IndexedDef(_) => "an indexed definition",
            StmtKind::While(_) | StmtKind::Until(_) => "a loop guard",
            StmtKind::Expr(_) => "an expression statement",
            StmtKind::Annotated { .. } | StmtKind::UnitAnnot(_) => {
                "an annotated declaration. Write the annotation before `local`"
            }
        };
        self.errors.push(Error {
            row: None,
            menu: String::new(),
            span: s.span,
            message: format!(
                "`local` stands before {what}, and `local` marks only a binding, a function, a \
                 struct, a type or a method. Remove the `local`, or write it before one of those."
            ),
            notes: Vec::new(),
        });
        false
    }

    /// The statement `s`, whose binders its scope has; `top` holds when it is one of the unit's
    /// own statements.
    fn stmt<'a>(&mut self, s: &'a Stmt, top: bool, todo: &mut Vec<Task<'a>>) {
        match &s.kind {
            StmtKind::Initial(_) => self.later(s.span, "an `initial` statement"),
            StmtKind::Bind { value, .. } => todo.push(Task::Expr(value)),
            StmtKind::Return(es) => todo.extend(es.iter().rev().map(Task::Expr)),
            StmtKind::Push { port, .. } if port.ends_with('\'') => {
                self.later(s.span, "a generation push `x' <- e`")
            }
            StmtKind::Push { port, value } => {
                self.name(port, s.span);
                self.out.pushes.push(s.span);
                todo.push(Task::Expr(value));
            }
            StmtKind::Function(f) => {
                if let Some((m, _, _)) = f.main.as_ref().and_then(|h| h.param.as_ref()) {
                    self.main_params.push((f.body.span, m.clone()));
                }
                let ports: &[Port] = f.ports().unwrap_or_default();
                todo.push(Task::Function {
                    params: &f.params,
                    ports,
                    body: &f.body,
                    this: None,
                });
                for (a, b) in f.tests.iter().rev() {
                    todo.push(Task::Expr(b));
                    todo.push(Task::Expr(a));
                }
                self.test_ports(f, todo);
                todo.extend(ports.iter().rev().map(|p| Task::Ty(&p.ty)));
            }
            StmtKind::Struct(st) => {
                self.later(s.span, "a struct declaration");
                self.fields(st, s.span, todo);
            }
            // A primed name is of layer L6 wherever it stands (DESIGN.md sec:grammar).
            StmtKind::Method(m) if m.receiver.ends_with('\'') => self.primed(&m.receiver, s.span),
            StmtKind::Method(m) if m.function.name.ends_with('\'') => {
                self.primed(&m.function.name, s.span)
            }
            StmtKind::Method(m) => {
                self.later(s.span, "a method");
                let f = &m.function;
                let ports: &[Port] = f.ports().unwrap_or_default();
                todo.push(Task::Function {
                    params: &f.params,
                    ports,
                    body: &f.body,
                    this: Some(s.span),
                });
                for (a, b) in f.tests.iter().rev() {
                    todo.push(Task::Expr(b));
                    todo.push(Task::Expr(a));
                }
                self.test_ports(f, todo);
                todo.extend(ports.iter().rev().map(|p| Task::Ty(&p.ty)));
                todo.push(Task::TypeName(&m.receiver, s.span));
            }
            StmtKind::Type(t) => {
                self.later(s.span, "a type declaration");
                self.type_decl(t, s.span, todo);
            }
            StmtKind::Import(_) => {
                self.later.push(Error {
                    row: None,
                    menu: String::new(),
                    span: s.span,
                    message: "an import is part of the Zed language, and this version of zedc \
                              does not yet tie a name an import brings in to the other unit's \
                              definition. Write the definitions this file uses in it, and \
                              remove the import."
                        .into(),
                    notes: Vec::new(),
                });
            }
            StmtKind::Local(decl) => {
                self.later(s.span, "a `local` declaration");
                todo.push(Task::Stmt(decl, top));
            }
            StmtKind::IndexedDef(_) => self.later(s.span, "an indexed definition"),
            StmtKind::While(_) => self.later(s.span, "a `while` guard"),
            StmtKind::Until(_) => self.later(s.span, "an `until` guard"),
            StmtKind::Expr(_) => self.later(s.span, "an expression statement"),
            StmtKind::Annotated { annots, decl } => {
                self.annotations(annots, decl);
                todo.push(Task::Stmt(decl, false));
            }
            StmtKind::UnitAnnot(a) => self.unit_annotation(a, s.span),
        }
    }

    /// The fields of the struct `st`, declared by the statement at `span`: each a binder, named
    /// once. A field's type and default are read in a scope of the field list, which holds the
    /// fields, so a default or a type names the fields declared before it (DESIGN.md
    /// sec:lexical) and a field declared after it is "Name used above its definition"; outside
    /// the list a field is named only through a value of the struct.
    fn fields<'a>(&mut self, st: &'a Struct, span: Span, todo: &mut Vec<Task<'a>>) {
        let start = self.out.binders.len();
        self.open();
        todo.push(Task::Close);
        let level = self.scopes.len();
        let mut items = Vec::new();
        for f in &st.fields {
            match f {
                Field::Typed {
                    name,
                    ty,
                    default,
                    span: at,
                } => {
                    // The builder rejects a field declared twice, so each name is new here.
                    let id = self.out.binders.len();
                    let mut b = Bound::new(level, Kind::Field, false);
                    b.ids.push_back(id);
                    self.visible.entry(name.clone()).or_default().push(b);
                    self.scopes
                        .last_mut()
                        .expect("opened above")
                        .push(name.clone());
                    self.out.binders.push(Binder {
                        name: name.clone(),
                        span: *at,
                        kind: Kind::Field,
                    });
                    items.push((*at, Some(id)));
                    todo.extend(default.as_ref().map(Task::Expr));
                    todo.push(Task::Ty(ty));
                }
                Field::Import { path, span: at } => todo.push(Task::TypeName(path, *at)),
            }
        }
        let end = self.out.binders.len();
        self.out.fields.insert(span, start..end);
        self.list(start, items);
    }

    /// The type declaration `t`, the statement at `span`: its parameters, in scope in its type.
    fn type_decl<'a>(&mut self, t: &'a TypeDecl, span: Span, todo: &mut Vec<Task<'a>>) {
        self.open();
        for p in &t.params {
            self.bind(p, span, span, Kind::TypeParam, None);
        }
        todo.push(Task::Close);
        todo.push(Task::Ty(&t.ty));
    }

    /// The annotations `annots`, written before the declaration `decl`. One has a meaning at
    /// this layer: `@nonblocking` before a function or a method, which the checker then proves
    /// never blocks (DESIGN.md sec:ports, "Every port operation says whether it can block").
    /// It takes no arguments and is written once; before `local` it marks the function `local`
    /// marks. Every other annotation is refused, by [`Self::annotation`].
    fn annotations(&mut self, annots: &[Annot], decl: &Stmt) {
        let decl = match &decl.kind {
            StmtKind::Local(d) => d,
            _ => decl,
        };
        let mut marked = false;
        for a in annots {
            if a.name != "nonblocking" {
                self.annotation(a);
                continue;
            }
            let what = match &decl.kind {
                StmtKind::Function(_) | StmtKind::Method(_) => None,
                StmtKind::Bind { .. } => Some("a binding"),
                StmtKind::Struct(_) => Some("a struct declaration"),
                StmtKind::Type(_) => Some("a type declaration"),
                StmtKind::Import(_) => Some("an import"),
                StmtKind::Return(_) => Some("a `return`"),
                StmtKind::Push { .. } => Some("a push"),
                StmtKind::Initial(_) => Some("an `initial` statement"),
                StmtKind::IndexedDef(_) => Some("an indexed definition"),
                StmtKind::While(_) | StmtKind::Until(_) => Some("a loop guard"),
                StmtKind::Expr(_) => Some("an expression statement"),
                StmtKind::Local(_) => Some("a `local` declaration again"),
                StmtKind::Annotated { .. } | StmtKind::UnitAnnot(_) => {
                    unreachable!("an annotated declaration and a unit item are no `Decl`")
                }
            };
            let message = if marked {
                "`@nonblocking` is written twice before one declaration. Remove one.".into()
            } else if a.called {
                "`@nonblocking` takes no arguments. Write `@nonblocking` alone before the \
                 function."
                    .into()
            } else if let Some(what) = what {
                format!(
                    "`@nonblocking` marks a function, and here it stands before {what}. Remove \
                     it, or write it before a function declaration."
                )
            } else {
                marked = true;
                continue;
            };
            marked = true;
            self.errors.push(Error {
                row: None,
                menu: String::new(),
                span: a.span,
                message,
                notes: Vec::new(),
            });
        }
    }

    /// The annotation `a`, refused with its reason: it is no annotation; it is `@hash`, which
    /// annotates no declaration; it is `@nonblocking` written as a unit item
    /// ([`Self::annotations`] reads it before a declaration); or it is of a later layer.
    fn annotation(&mut self, a: &Annot) {
        let name = &a.name;
        let message = match annotation_layer(name) {
            None => format!("`@{name}` is not an annotation"),
            Some(2) if name == "hash" => "`@hash` pins an import and follows its unit path, as in \
                 `import geometry.shapes @hash(\"…\");`; it annotates no declaration"
                .into(),
            Some(2) => "`@nonblocking;` is not a unit item: `@nonblocking` marks a function, \
                 written before its declaration, as in `@nonblocking scale(positional x: int) = \
                 x * 2;`"
                .into(),
            Some(_) => not_yet(&format!("the annotation `@{name}`")),
        };
        self.errors.push(Error {
            row: None,
            menu: String::new(),
            span: a.span,
            message,
            notes: Vec::new(),
        });
    }

    /// The unit item `a;`, written as the statement at `span`. One annotation is a unit item,
    /// `@log(#off);`, which this layer accepts. Each other way to write one is refused with its
    /// reason.
    fn unit_annotation(&mut self, a: &Annot, span: Span) {
        let name = &a.name;
        let fail = |message: String| Error {
            row: None,
            menu: String::new(),
            span,
            message,
            notes: Vec::new(),
        };
        let error = match annotation_layer(name) {
            None | Some(2) => return self.annotation(a),
            Some(_) if name != "log" => fail(format!(
                "`@{name}` annotates a declaration and is not a unit item; write it before \
                 the declaration it annotates"
            )),
            Some(_) if !a.called => fail(
                "`@log;` is not a unit item: `@log` writes a line at each evaluation of the \
                 definition or statement it annotates, and the unit item `@log(#off);` drops \
                 the lines of every body in the unit"
                    .into(),
            ),
            Some(_) if !is_off(a) => fail(
                "the unit item `@log` takes the one argument `#off`, as in `@log(#off);`, \
                 which drops the lines of every body in the unit"
                    .into(),
            ),
            Some(_) if self.scopes.len() > TOP => fail(
                "`@log(#off);` is an item of a unit and stands at its top level, not in a \
                 block; write `@log(#off)` before a function's declaration to drop the lines \
                 of its body"
                    .into(),
            ),
            Some(_) => match self.out.log_off {
                None => return self.out.log_off = Some(span),
                Some(first) => Error {
                    notes: vec![Note {
                        span: first,
                        text: "the first `@log(#off);`".into(),
                    }],
                    ..fail(
                        "the unit has `@log(#off);` twice, and a unit turns its log off once. \
                         Remove one of the two."
                            .into(),
                    )
                },
            },
        };
        self.errors.push(error);
    }

    /// The primed name `name`, which names a loop step's output.
    fn primed(&mut self, name: &str, span: Span) {
        self.later(span, &format!("the primed name `{name}`"));
    }

    /// A new region that handles `handles`.
    fn region(&mut self, handles: Vec<Handle>) -> usize {
        self.out.regions.push(Region {
            handles,
            ..Region::default()
        });
        self.out.regions.len() - 1
    }

    /// The region of the operand of the `else` written at `span`, made when first asked for.
    fn else_region(&mut self, span: Span) -> usize {
        if let Some(&r) = self.else_regions.get(&span) {
            return r;
        }
        let r = self.region(Vec::new());
        self.else_regions.insert(span, r);
        r
    }

    /// Records in `region` each use of a name in `e` whose loose atoms pass by rule 6 to the
    /// value of `e` (DESIGN.md sec:type_resolution): the arguments and receiver of a call, the
    /// family `m` and the key `k` of `m[k]`, the operands of an operator other than `==` and
    /// `!=`, the branches of an `if`, a block's result and the holes of a string, at any
    /// depth. An `else` in it starts a region of its own whose value passes on to `region`; its
    /// default stays in `region`. A tuple, a record or a lambda ends the walk: its value holds
    /// the atom rather than being it (struct positions follow L2.6b). Every expression is
    /// walked by at most one region, the innermost holding it, so the regions of a unit cost
    /// `O(n)` together.
    fn flow(&mut self, e: &Expr, region: usize) {
        let mut stack = vec![e];
        while let Some(e) = stack.pop() {
            match &e.kind {
                ExprKind::Name(_) => self.out.flows.push((e.span, region)),
                ExprKind::Unary(_, a) | ExprKind::Member { of: a, .. } => stack.push(a),
                ExprKind::Binary(BinaryOp::Eq | BinaryOp::Ne, ..) => {}
                ExprKind::Index(a, k) => {
                    stack.push(k);
                    stack.push(a);
                }
                ExprKind::Binary(_, a, b) => {
                    stack.push(b);
                    stack.push(a);
                }
                ExprKind::Call {
                    callee,
                    positional,
                    named,
                    ..
                } => {
                    stack.extend(named.iter().map(|(_, a)| a));
                    stack.extend(positional);
                    if !matches!(callee.kind, ExprKind::Name(_)) {
                        stack.push(callee);
                    }
                }
                ExprKind::Str(parts) => stack.extend(parts.iter().filter_map(|p| match p {
                    StrPart::Hole(h) => Some(h),
                    StrPart::Text(_) => None,
                })),
                ExprKind::If {
                    then, otherwise, ..
                } => {
                    stack.push(otherwise);
                    stack.push(then);
                }
                ExprKind::Block(stmts) => {
                    for s in stmts {
                        if let StmtKind::Return(es) = &s.kind {
                            stack.extend(es);
                        }
                    }
                }
                ExprKind::Else { default, .. } => {
                    let inner = self.else_region(e.span);
                    self.out.regions[inner].parent = Some(region);
                    stack.push(default);
                }
                _ => {}
            }
        }
    }

    /// The ports the clauses `test with p = e, …` of `f`'s tables give (DESIGN.md sec:ports,
    /// "A test table gives a port its values"), each value resolved as a row is. The builder
    /// has checked each field of `main`; a name is checked here, since what the unit defines
    /// decides it. This zedc declares no port at the top level (no store, no foreign library),
    /// so a name the unit or the prelude binds is Zed code, which a test never replaces, and is
    /// rejected, as a name that names nothing is; a port constructor of the prelude that the
    /// unit does not bind is refused as not compiled yet, since this zedc has none of them.
    /// The menu of a rejection is the ports `f` may reach: `main`'s inputs on `main`'s table,
    /// and on another function's the file port `main::files`, the one port such a function
    /// reads in this zedc (QUESTIONS A68), or the table without the clause.
    fn test_ports<'a>(&mut self, f: &'a Function, todo: &mut Vec<Task<'a>>) {
        const CONSTRUCTORS: [&str; 7] = [
            "now",
            "clock",
            "connect",
            "listen",
            "spawn",
            "run",
            "randomBytes",
        ];
        for p in f.given.iter().rev().flat_map(|g| g.ports.iter().rev()) {
            todo.push(Task::Expr(&p.value));
            let PortName::Name(name, span) = &p.port else {
                continue;
            };
            let found = self.find(name);
            if found.is_none() && CONSTRUCTORS.contains(&name.as_str()) {
                self.later(
                    *span,
                    &format!("a test clause giving the prelude port `{name}`"),
                );
                continue;
            }
            let mut notes = Vec::new();
            if found.is_some() {
                notes.push(Note {
                    span: *span,
                    text: format!(
                        "`{name}` is a value the program computes, and a test gives a port its \
                         value, never a value of Zed code"
                    ),
                });
            }
            match f.main {
                Some(_) => notes.extend(["stdin", "args", "env", "files"].map(|m| Note {
                    span: *span,
                    text: format!("repair: `main::{m} = …`"),
                })),
                None => notes.extend(
                    [
                        "repair: `main::files = …`, the file port, which every function reads"
                            .to_string(),
                        format!("repair: `test {{ … }}`, the table without `{name} = …`"),
                    ]
                    .map(|text| Note { span: *span, text }),
                ),
            }
            self.errors.push(Error {
                row: None,
                menu: String::new(),
                span: *span,
                message: format!("`{name}` in `test with` is not a port"),
                notes,
            });
        }
    }

    /// The form `what`, which the parser builds and this zedc does not compile yet.
    fn later(&mut self, span: Span, what: &str) {
        self.errors.push(Error {
            row: None,
            menu: String::new(),
            span,
            message: not_yet(what),
            notes: Vec::new(),
        });
    }

    /// The row "Binder naming a type" (DESIGN.md sec:diagnostics): `binder`, the name `name`
    /// written at `at` in the text `site`, names a type in scope. A unit declares no type before
    /// L2, so the type is the prelude's. Every binder but a type name in a pattern, which is a
    /// type test, is such an error (DESIGN.md sec:syntax_tour, the `match` row of the operator
    /// inventory), so a cast habit such as `y as (int)` is not read as a binding of `int`.
    fn names_type(&mut self, name: &str, at: Span, site: Span, binder: &str) {
        let cast = prelude_layer(name).is_some();
        let repair = if cast {
            format!(
                "repair: rename the binder; where a cast was meant, write the type application \
                 `{name}(…)`"
            )
        } else {
            "repair: rename the binder".into()
        };
        self.errors.push(Error {
            row: Some(Row::BinderNamingType),
            menu: String::new(),
            span: at,
            message: format!(
                "{binder} `{name}` names the type `{name}`, which the prelude declares: a binder \
                 may not name a type in scope"
            ),
            notes: vec![
                Note {
                    span: site,
                    text: format!("{binder} `{name}`, which binds `{name}` in this scope"),
                },
                Note {
                    span: at,
                    text: repair,
                },
            ],
        });
    }

    /// The use at `span` of `what`, a name another unit defines, which this zedc does not link yet.
    fn linked(&mut self, span: Span, what: &str) {
        self.later.push(Error {
            row: None,
            menu: String::new(),
            span,
            message: format!(
                "{what} is used here, and this version of zedc does not yet link a use to a \
                 definition in another unit. Write the definition in this file instead, and use \
                 it from there."
            ),
            notes: Vec::new(),
        });
    }

    /// A function's, a method's or a lambda's parameters, ports and body: one scope, which a
    /// body block's statements share. A method's receiver `this` is bound in it, at the
    /// method's statement `this`.
    fn function<'a>(
        &mut self,
        params: &'a [Param],
        ports: &'a [Port],
        body: &'a Expr,
        this: Option<Span>,
        todo: &mut Vec<Task<'a>>,
    ) {
        // Step L2.4 elaborates a tuple-destructuring parameter; its names are binders of a
        // pattern, which this step resolves (DESIGN.md L2.3), so the body is walked with them.
        if let Some(p) = params.iter().find(|p| p.tuple.is_some()) {
            self.later(p.span, "a tuple-destructuring parameter");
        }
        self.open();
        if let Some(at) = this {
            self.bind("this", at, at, Kind::Receiver, None);
        }
        let first = self.out.binders.len();
        let mut items = Vec::new();
        for p in params {
            let id = self.out.binders.len();
            match &p.tuple {
                None => self.bind(&p.name, p.name_at, p.span, Kind::Param, None),
                Some(targets) => {
                    for t in targets {
                        if let Target::Name(n, at) = t {
                            self.bind(n, *at, *at, Kind::Param, None);
                        }
                    }
                }
            }
            items.push((p.span, (self.out.binders.len() == id + 1).then_some(id)));
        }
        for p in ports {
            let id = self.out.binders.len();
            self.bind(&p.name, name_at(p.span, &p.name), p.span, Kind::Port, None);
            items.push((p.span, (self.out.binders.len() == id + 1).then_some(id)));
        }
        self.list(first, items);
        todo.push(Task::Close);
        todo.push(match &body.kind {
            ExprKind::Block(stmts) => Task::Stmts(stmts),
            _ => Task::Expr(body),
        });
        for p in params.iter().rev() {
            todo.extend(p.default.as_ref().map(Task::Expr));
            todo.extend(p.ty.as_ref().map(Task::Ty));
        }
    }

    fn expr<'a>(&mut self, e: &'a Expr, todo: &mut Vec<Task<'a>>) {
        match &e.kind {
            ExprKind::Int { .. }
            | ExprKind::Float { .. }
            | ExprKind::Rat(_)
            | ExprKind::Bool(_)
            | ExprKind::Atom(_) => {}
            ExprKind::Str(parts) => todo.extend(parts.iter().rev().filter_map(|p| match p {
                StrPart::Hole(h) => Some(Task::Expr(h)),
                StrPart::Text(_) => None,
            })),
            ExprKind::Name(n) => {
                if self.names_main(n) {
                    self.errors.push(main_value(e.span));
                }
                self.name(n, e.span)
            }
            ExprKind::Unary(_, a) => todo.push(Task::Expr(a)),
            ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
                // `e == #a` and `e != #a`, either way round, handle `#a` for `e`.
                if matches!(e.kind, ExprKind::Binary(BinaryOp::Eq | BinaryOp::Ne, ..)) {
                    let other = match (&a.kind, &b.kind) {
                        (ExprKind::Atom(n), _) => Some((n, b)),
                        (_, ExprKind::Atom(n)) => Some((n, a)),
                        _ => None,
                    };
                    if let Some((n, other)) = other {
                        let r = self.region(vec![Handle::Bare(n.clone())]);
                        self.flow(other, r);
                    }
                }
                todo.push(Task::Expr(b));
                todo.push(Task::Expr(a));
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                ..
            } => {
                // Every function named `main` is a `main` (the builder gives it `main`'s
                // header), so a call of a function the name `main` binds calls `main`.
                let calls_main = matches!(&callee.kind, ExprKind::Name(n) if self.names_main(n));
                if calls_main {
                    self.errors.push(main_called(e.span));
                }
                // The old call `files()`, when the program binds no `files` of its own: the file
                // port is `main::files` now. A bare `files` that names nothing is an ordinary
                // undefined name, as a fragment's list of paths is.
                if let ExprKind::Name(n) = &callee.kind
                    && n == "files"
                    && positional.is_empty()
                    && named.is_empty()
                    && self.find(n).is_none()
                {
                    self.errors.push(files_moved(callee.span));
                    return;
                }
                if let ExprKind::Name(_) = callee.kind {
                    self.out.calls.push(NamedCall {
                        span: e.span,
                        callee: callee.span,
                        positional: positional.iter().map(|a| a.span).collect(),
                        named: named.iter().map(|(n, a)| (n.clone(), a.span)).collect(),
                    });
                }
                todo.extend(named.iter().rev().map(|(_, a)| Task::Expr(a)));
                todo.extend(positional.iter().rev().map(Task::Expr));
                // The callee `main` is resolved here, before the arguments as every callee is,
                // and not as a value, which [`Resolver::main_value`] would reject again.
                match &callee.kind {
                    ExprKind::Name(n) if calls_main => self.name(n, callee.span),
                    _ => todo.push(Task::Expr(callee)),
                }
            }
            ExprKind::Tuple(items) => todo.extend(items.iter().rev().map(Task::Expr)),
            ExprKind::Lambda { params, body } => todo.push(Task::Function {
                params,
                ports: &[],
                body,
                this: None,
            }),
            ExprKind::Is { of, ty, .. } => {
                // The written type's atoms: a union nests as deep as its text.
                let mut handles = Vec::new();
                let mut stack = vec![ty];
                while let Some(t) = stack.pop() {
                    match &t.kind {
                        TypeKind::Atom(a) => handles.push(Handle::Bare(a.clone())),
                        TypeKind::Union(ts) => stack.extend(ts),
                        _ => {}
                    }
                }
                if !handles.is_empty() {
                    let r = self.region(handles);
                    self.flow(of, r);
                }
                todo.push(Task::Ty(ty));
                todo.push(Task::Expr(of));
            }
            ExprKind::Else {
                of,
                pattern,
                default,
            } => {
                let h = match pattern {
                    None => Some(Handle::Loose),
                    Some(Pattern::Atom {
                        name,
                        fields,
                        items,
                        ..
                    }) if fields.is_empty() && items.is_empty() => Some(Handle::Any(name.clone())),
                    Some(_) => None,
                };
                let r = self.else_region(e.span);
                self.out.regions[r].handles.extend(h);
                self.flow(of, r);
                todo.push(Task::Else {
                    span: e.span,
                    pattern: pattern.as_ref(),
                    default,
                });
                todo.push(Task::Expr(of));
            }
            ExprKind::Block(stmts) => {
                self.open();
                todo.push(Task::Close);
                todo.push(Task::Stmts(stmts));
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                todo.push(Task::Expr(otherwise));
                todo.push(Task::Expr(then));
                todo.push(Task::Expr(cond));
            }
            ExprKind::Member { of, name, .. } => {
                if let ExprKind::Name(q) = &of.kind
                    && self.qualified(q, of.span, name, e.span)
                {
                    return;
                }
                todo.push(Task::Member(e.span, name));
                todo.push(Task::Expr(of));
            }
            ExprKind::Record(fields) => {
                self.later(e.span, "a record display");
                todo.extend(fields.iter().rev().map(|(_, v)| Task::Expr(v)));
            }
            ExprKind::With { of, updates } => {
                self.later(e.span, "a `with` clause");
                todo.extend(updates.iter().rev().map(|u| Task::Expr(&u.value)));
                todo.push(Task::Expr(of));
            }
            ExprKind::This => {
                self.later(e.span, "`this`");
                match self.find("this") {
                    Some(Found::Bound(ids)) => {
                        self.out.uses.insert(e.span, Ref::Bound(ids));
                    }
                    _ => self.errors.push(Error {
                        row: None,
                        menu: String::new(),
                        span: e.span,
                        message: "`this` stands outside a method: it names the receiver of a \
                                  method `T.m(…) = …`, in the method's body"
                            .into(),
                        notes: Vec::new(),
                    }),
                }
            }
            ExprKind::Match { of, arms } => {
                self.later(e.span, "a `match`");
                todo.extend(arms.iter().rev().map(Task::Arm));
                todo.push(Task::Expr(of));
            }
            // The forms below are compiled from a later step, and their parts are resolved here
            // as `match`'s are, so a name in them is recorded or reported.
            ExprKind::Range(from, to) => {
                self.later(e.span, "a range");
                todo.extend(to.bound().map(|b| Task::Expr(b)));
                todo.push(Task::Expr(from));
            }
            ExprKind::In { of, set, .. } => {
                self.later(e.span, "an `in` test");
                todo.push(Task::Expr(set));
                todo.push(Task::Expr(of));
            }
            ExprKind::Reduce { of, op } => {
                self.later(e.span, "a reduction `><`");
                todo.push(Task::Expr(op));
                todo.push(Task::Expr(of));
            }
            ExprKind::Read { of, .. } => {
                self.later(e.span, "a metadata read `::`");
                // `main::args` reads the entry point, which is no use of `main` as a value.
                match &of.kind {
                    ExprKind::Name(n) => self.name(n, of.span),
                    _ => todo.push(Task::Expr(of)),
                }
            }
            ExprKind::Section(_) => self.later(e.span, "an operator section"),
            ExprKind::Array(items) => {
                self.later(e.span, "an array display");
                todo.extend(items.iter().rev().map(Task::Expr));
            }
            ExprKind::Set(items) => {
                self.later(e.span, "a set display");
                todo.extend(items.iter().rev().map(Task::Expr));
            }
            ExprKind::Map(entries) => {
                self.later(e.span, "a map display");
                for (k, v) in entries.iter().rev() {
                    todo.push(Task::Expr(v));
                    todo.push(Task::Expr(k));
                }
            }
            // The source is read outside the keypath pattern, which binds in the `where` and the
            // body only (DESIGN.md sec:lexical, the `for` row of the operator inventory).
            ExprKind::For {
                binders,
                source,
                guard,
                body,
            } => {
                self.later(e.span, "a `for`");
                todo.push(Task::For {
                    binders,
                    guard: guard.as_deref(),
                    body,
                });
                todo.push(Task::Expr(source));
            }
            // A loop body's bare and primed names are the frames of step L6.3, which its updates
            // declare and resolution does not bind yet, so the body is not walked: its names would
            // be reported as not defined.
            ExprKind::Loop { .. } => self.later(e.span, "a `loop`"),
            ExprKind::Break(value) => {
                self.later(e.span, "a `break`");
                todo.push(Task::Expr(value));
            }
            ExprKind::Spread { of, name } => {
                self.later(e.span, "a call `*.` that writes its receiver");
                todo.push(Task::Member(e.span, name));
                todo.push(Task::Expr(of));
            }
            ExprKind::SortKey { key, .. } => {
                self.later(e.span, "a sort key `asc` or `desc`");
                todo.extend(key.as_deref().map(Task::Expr));
            }
        }
    }

    /// The pattern `p`: the names it binds, and the types it names. A field written `f:` binds
    /// `f`; a bare name binds itself, unless it names a type, when the pattern is a type test
    /// (DESIGN.md sec:syntax_tour, the `match` row of the operator inventory). Only an atom
    /// pattern has its meaning at this step; the others are compiled from a later one, and are
    /// reported so when `report` holds. The ends of a range pattern are part of the range.
    fn pattern<'a>(&mut self, p: &'a Pattern, report: bool, todo: &mut Vec<Task<'a>>) {
        let later = match p {
            Pattern::Atom { .. } => None,
            Pattern::Is { .. } => Some("a type pattern `n is T`"),
            Pattern::Lit(_) => Some("a literal pattern"),
            Pattern::Range { .. } => Some("a range pattern"),
            Pattern::Struct { .. } | Pattern::Name(..) | Pattern::Wild(_) | Pattern::Tuple(..) => {
                Some("a struct, name, `_` or tuple pattern")
            }
        };
        if report && let Some(what) = later {
            self.later(p.span(), what);
        }
        let bind = |(f, sub): &'a (String, Option<Pattern>), span| match sub {
            Some(sub) => Task::Pattern(sub, report),
            None => Task::BindPattern(f, span),
        };
        match p {
            Pattern::Atom {
                fields,
                items,
                span,
                ..
            } => {
                todo.extend(items.iter().rev().map(|i| Task::Pattern(i, report)));
                todo.extend(fields.iter().rev().map(|f| bind(f, *span)));
            }
            Pattern::Struct { name, fields, span } => {
                todo.extend(fields.iter().rev().map(|f| bind(f, *span)));
                todo.push(Task::TypeName(name, name_at(*span, name)));
            }
            Pattern::Name(n, span) => {
                let names_type = TYPES.contains(&n.as_str())
                    || matches!(self.find(n), Some(Found::Bound(ids))
                        if self.out.binders[ids[0]].kind.is_type());
                if names_type {
                    self.type_name(n, *span);
                } else {
                    self.bind(n, *span, *span, Kind::Pattern, None);
                }
            }
            Pattern::Wild(_) => {}
            Pattern::Tuple(items, _) => {
                todo.extend(items.iter().rev().map(|i| Task::Pattern(i, report)))
            }
            Pattern::Is { name, ty, span } => {
                todo.push(Task::Ty(ty));
                if let Some(n) = name {
                    self.bind(n, *span, *span, Kind::Pattern, None);
                }
            }
            Pattern::Lit(e) => todo.push(Task::Expr(e)),
            Pattern::Range { from, to, .. } => {
                if let RangeEnd::Below(to) | RangeEnd::Through(to) = to {
                    todo.push(Task::Pattern(to, false));
                }
                todo.push(Task::Pattern(from, false));
            }
        }
    }

    fn ty<'a>(&mut self, t: &'a Type, todo: &mut Vec<Task<'a>>) {
        match &t.kind {
            TypeKind::Name(n) => self.type_name(n, t.span),
            TypeKind::For { ty, bounds } => {
                // Each bound is read outside the clause, so `for T in U` with `U` bounded
                // around it is no carrier either.
                for b in bounds {
                    self.carriers(&b.name, &b.carriers);
                }
                for b in bounds {
                    // A type name in the type always names the type, so a variable of its name
                    // binds nothing the type could hold, and is not reported as unheld too.
                    if TYPES.contains(&b.name.as_str()) {
                        self.names_type(&b.name, b.span, t.span, "the type variable");
                        continue;
                    }
                    if let Some(outer) = self.tvars.get(&b.name) {
                        self.errors.push(Error {
                            row: None,
                            menu: String::new(),
                            span: b.span,
                            message: format!(
                                "the type variable `{}` is bounded twice, and a type variable \
                                 has one bound. Remove one of the two bounds.",
                                b.name
                            ),
                            notes: vec![Note {
                                span: outer.span,
                                text: format!("the first bound of `{}`", b.name),
                            }],
                        });
                        continue;
                    }
                    let var = TypeVar {
                        span: b.span,
                        depth: self.arrows.len(),
                        first: None,
                    };
                    self.tvars.insert(b.name.clone(), var);
                }
                self.clauses.push(t.span);
                todo.push(Task::ForEnd(ty, bounds));
                todo.push(Task::Ty(ty));
            }
            TypeKind::Atom(_) | TypeKind::Every(Every::Atom | Every::Tuple) => {}
            TypeKind::Tuple(ts) | TypeKind::Union(ts) => {
                todo.extend(ts.iter().rev().map(Task::Ty));
            }
            // An intersection in parentheses among the operands is read with them, not again
            // on its own.
            TypeKind::And(ts) => {
                let ts = Type::and_operands(ts);
                match Type::overload(&ts) {
                    // The arrows of an overload are one function's, so a variable its bounds
                    // clause binds stands in that one function type in each of them, as the
                    // checker prints `((T) -> T) & ((T | #_) -> T | #_) for T in int | f64`.
                    Ok(true) => {
                        self.arrows.push(t.span);
                        todo.push(Task::ArrowEnd);
                    }
                    Ok(false) => {}
                    Err(message) => self.errors.push(Error {
                        row: None,
                        menu: String::new(),
                        span: t.span,
                        message,
                        notes: Vec::new(),
                    }),
                }
                todo.extend(ts.into_iter().rev().map(Task::Ty));
            }
            TypeKind::Diff(a, b) => {
                todo.push(Task::Ty(b));
                todo.push(Task::Ty(a));
            }
            TypeKind::Arrow { params, result, .. } => {
                self.arrows.push(t.span);
                todo.push(Task::ArrowEnd);
                todo.push(Task::Ty(result));
                todo.extend(params.iter().rev().map(|p| Task::Ty(&p.ty)));
            }
            TypeKind::Bounded {
                lower,
                upper,
                result,
            } => {
                self.arrows.push(t.span);
                todo.push(Task::ArrowEnd);
                todo.extend([result, upper, lower].map(|t| Task::Ty(t)));
            }
            TypeKind::AtomApply(_, ps) if self.printed.is_some() => {
                todo.extend(ps.iter().rev().map(|p| Task::Ty(&p.ty)));
            }
            TypeKind::AtomAny(_) | TypeKind::Every(Every::Struct) if self.printed.is_some() => {}
            TypeKind::Apply(name, ps) => {
                self.later(t.span, "an applied type");
                todo.extend(ps.iter().rev().map(|p| Task::Ty(&p.ty)));
                todo.push(Task::TypeName(name, name_at(t.span, name)));
            }
            TypeKind::AtomApply(_, ps) => {
                self.later(t.span, "an atom type with a payload");
                todo.extend(ps.iter().rev().map(|p| Task::Ty(&p.ty)));
            }
            TypeKind::AtomAny(_) => self.later(t.span, "an atom type with any payload"),
            TypeKind::Every(Every::Struct) => self.later(t.span, "the type of every struct"),
            TypeKind::Record(fields) => {
                self.later(t.span, "a record type");
                todo.extend(fields.iter().rev().map(|(_, t)| Task::Ty(t)));
            }
            TypeKind::Array(_) => self.later(t.span, "a family type `[T]`"),
        }
    }

    /// The type name `n` used at `span`: a prelude type, a bounded type variable, a leaf of a
    /// printed type, a struct, type or type parameter in scope, a qualified type `q.T` of a
    /// qualifier's unit, or a type of the prelude unit. Otherwise the error why not.
    fn type_name(&mut self, n: &str, span: Span) {
        if TYPES.contains(&n) {
            self.out.uses.insert(span, Ref::Prelude(n.into()));
            return;
        }
        if self.tvars.contains_key(n) {
            return self.type_var(n, span);
        }
        if self.printed.as_ref().is_some_and(|l| l.contains(n)) {
            return;
        }
        if let Some((q, name)) = n.split_once('.') {
            return self.qualified_type(q, name, span);
        }
        let message = match self.find(n) {
            Some(Found::Bound(ids)) if self.dead.contains(&ids[0]) => {
                return self.dead_use(ids[0], span);
            }
            Some(Found::Bound(ids)) if self.out.binders[ids[0]].kind.is_type() => {
                self.order(n, span, &ids);
                self.out.uses.insert(span, Ref::Bound(ids));
                return;
            }
            Some(Found::Bound(ids)) => {
                let b = &self.out.binders[ids[0]];
                let binder = b.kind.binder();
                let note = Note {
                    span: b.span,
                    text: format!("{binder} `{n}`, which binds `{n}` here"),
                };
                return self.errors.push(Error {
                    row: None,
                    menu: String::new(),
                    span,
                    message: format!(
                        "`{n}` stands where a type is written, and names {binder} `{n}`, which \
                         is no type"
                    ),
                    notes: vec![note],
                });
            }
            Some(Found::Ambiguous(a, b)) => return self.ambiguous(n, span, a, b),
            Some(Found::Unit(unit)) => {
                // `find` gives the prelude unit only for a name the unit exports.
                let kind = (self.units.and_then(|u| u.prelude()))
                    .and_then(|(_, e)| e.get(n))
                    .map(|e| e.kind)
                    .expect("the prelude unit exports the name found in it");
                if kind.is_type() {
                    return self.prelude_unit(n, span, unit);
                }
                format!(
                    "`{n}` stands where a type is written, and the prelude unit `{unit}` \
                     declares `{n}` as {}, which is no type",
                    kind.binder()
                )
            }
            None if n == MAIN_ARGS => return self.errors.push(main_args_elsewhere(span)),
            Some(Found::Word(_)) | None => match later_type_layer(n) {
                Some(_) => not_yet(&format!("the prelude type `{n}`")),
                None if self.prelude_broken(n, span) => return,
                None => undefined_type(n),
            },
        };
        self.errors.push(Error {
            row: None,
            menu: String::new(),
            span,
            message,
            // Inside a clause, the name reads as a type variable its clause forgot.
            notes: self
                .clauses
                .last()
                .map(|&span| Note {
                    span,
                    text: format!(
                        "a type variable is bounded by the clause after its type, as \
                         `for {n} in int | f64`; this clause does not bound `{n}`"
                    ),
                })
                .into_iter()
                .collect(),
        });
    }

    /// The qualified type `q.name` used at `span`: `q` a qualifier, whose unit defines the
    /// type `name`. Otherwise the error why not.
    fn qualified_type(&mut self, q: &str, name: &str, span: Span) {
        if name.contains('.') {
            return self.errors.push(Error {
                row: None,
                menu: String::new(),
                span,
                message: format!(
                    "the type `{q}.{name}` has more than one qualifier; a qualified type is a \
                     qualifier and a type, as `shapes.Point` after `import geometry.shapes;`"
                ),
                notes: Vec::new(),
            });
        }
        let message = match self.find(q) {
            Some(Found::Bound(ids)) if self.dead.contains(&ids[0]) => {
                return self.dead_use(ids[0], span);
            }
            Some(Found::Bound(ids)) if self.out.binders[ids[0]].kind == Kind::Unit => {
                let id = ids[0];
                let unit = self.out.imports[&id].clone();
                let import = self.out.binders[id].span;
                match self.export(&unit, name, span, import) {
                    None => return self.broken_member(&unit, name, span),
                    Some(e) if e.kind.is_type() => {
                        self.out.uses.insert(
                            span,
                            Ref::Unit {
                                unit,
                                name: name.into(),
                            },
                        );
                        let what = format!("`{q}.{name}`, a type of another unit,");
                        return self.linked(span, &what);
                    }
                    Some(e) => format!(
                        "`{q}.{name}` stands where a type is written, and the unit `{unit}` \
                         declares `{name}` as {}, which is no type",
                        e.kind.binder()
                    ),
                }
            }
            Some(Found::Bound(ids)) => format!(
                "`{q}` in the type `{q}.{name}` names {} `{q}`, not a unit imported as `import \
                 a.{q};`",
                self.out.binders[ids[0]].kind.binder()
            ),
            Some(Found::Ambiguous(a, b)) => return self.ambiguous(q, span, a, b),
            Some(Found::Unit(_) | Found::Word(_)) | None => format!(
                "`{q}` in the type `{q}.{name}` names no unit: no import in scope binds the \
                 qualifier `{q}`"
            ),
        };
        self.errors.push(Error {
            row: None,
            menu: String::new(),
            span,
            message,
            notes: Vec::new(),
        });
    }

    /// A use of the bounded type variable `n` at `span`. Its bound is a bound of the outermost
    /// function type inside its clause that holds it, where a call binds it (DESIGN.md
    /// sec:type_language), so every use stands in that one function type.
    fn type_var(&mut self, n: &str, span: Span) {
        let var = self.tvars.get_mut(n).expect("a bounded variable");
        let home = self.arrows.get(var.depth).copied();
        let first = var.first;
        if first.is_none() {
            var.first = Some((span, home));
        }
        let message = match (home, first) {
            (None, _) => format!(
                "the bounded variable `{n}` stands outside a function type: its bound is a \
                 function type's, which a call binds"
            ),
            // The first use was outside one, and is reported.
            (Some(_), Some((_, None))) => return,
            (Some(h), Some((_, Some(f)))) if h != f => format!(
                "the bounded variable `{n}` stands in two function types: its bound is the bound \
                 of one function type, which a call binds"
            ),
            _ => return,
        };
        let mut notes: Vec<Note> = first
            .map(|(s, _)| Note {
                span: s,
                text: format!("the first use of `{n}`"),
            })
            .into_iter()
            .collect();
        notes.extend(home.or(first.and_then(|(_, h)| h)).map(|f| Note {
            span: f,
            text: "the function type that holds a use".into(),
        }));
        self.errors.push(Error {
            row: None,
            menu: String::new(),
            span,
            message,
            notes,
        });
    }

    /// The end of the type `ty` of a bounds clause of `bounds`: the clause closes, each variable
    /// it bounded leaves scope, and one the type does not hold is an error. A bound of a name
    /// already bounded bound nothing, and the variable in scope under the name is another's:
    /// its text is not the bound's.
    fn for_end(&mut self, ty: &Type, bounds: &[TypeBound]) {
        self.clauses.pop();
        for b in bounds {
            if self.tvars.get(&b.name).is_none_or(|v| v.span != b.span) {
                continue;
            }
            let var = self.tvars.remove(&b.name).expect("bound above");
            if var.first.is_none() {
                self.errors.push(Error {
                    row: None,
                    menu: String::new(),
                    span: b.span,
                    message: format!(
                        "the bound names `{0}`, and the type before `for` does not hold `{0}`, so the \
                         bound constrains nothing. Remove the bound, or write `{0}` in the type.",
                        b.name
                    ),
                    notes: vec![Note {
                        span: ty.span,
                        text: "the type".into(),
                    }],
                });
            }
        }
    }

    /// The bound `t` of the type variable `v`: a union of carriers. Unions nest as deep as the
    /// text, so the parts still to read wait on a stack, in written order.
    fn carriers(&mut self, v: &str, t: &Type) {
        let mut todo = vec![t];
        while let Some(t) = todo.pop() {
            self.carrier(v, t, &mut todo);
        }
    }

    /// One part `t` of the bound of `v`; the parts of a union go to `todo`.
    fn carrier<'t>(&mut self, v: &str, t: &'t Type, todo: &mut Vec<&'t Type>) {
        match &t.kind {
            TypeKind::Name(n) if CARRIERS.contains(&n.as_str()) => {
                self.out.uses.insert(t.span, Ref::Prelude(n.clone()));
            }
            TypeKind::Union(ts) => todo.extend(ts.iter().rev()),
            kind => {
                let what = match kind {
                    TypeKind::Name(n) if self.tvars.contains_key(n) => {
                        format!("`{n}` is a type variable")
                    }
                    TypeKind::Name(n) => format!("`{n}` is no carrier"),
                    TypeKind::Atom(a) => format!("`#{a}` is an atom, no carrier"),
                    _ => "this type is no carrier".into(),
                };
                self.errors.push(Error {
                    row: None,
                    menu: String::new(),
                    span: t.span,
                    message: format!(
                        "the bound of `{v}` is not a union of carriers: {what}; the carriers are \
                         {}",
                        CARRIERS.join(", ")
                    ),
                    notes: Vec::new(),
                });
            }
        }
    }
}

/// A piece of the walk still to do, kept on the walk's stack.
#[derive(Clone, Copy)]
enum Task<'a> {
    /// The unit's own statements, and which of them are kept, if not all.
    Unit(&'a [Stmt], Option<&'a [bool]>),
    Stmts(&'a [Stmt]),
    /// A statement, and whether it is one of the unit's own.
    Stmt(&'a Stmt, bool),
    /// A function's, a method's or a lambda's parameters, ports and body; for a method, the
    /// statement that binds its receiver `this`.
    Function {
        params: &'a [Param],
        ports: &'a [Port],
        body: &'a Expr,
        this: Option<Span>,
    },
    Expr(&'a Expr),
    Ty(&'a Type),
    /// A type name and the text it is written at: a struct pattern's, a method's receiver, a
    /// struct's imported fields, an applied type's.
    TypeName(&'a str, Span),
    /// A pattern, and whether a form of a later step in it is reported.
    Pattern(&'a Pattern, bool),
    /// A pattern field written `f:`, which binds `f` at the pattern's text.
    BindPattern(&'a str, Span),
    /// An `else` whose `of` is done: its pattern and default, in a scope of their own.
    Else {
        span: Span,
        pattern: Option<&'a Pattern>,
        default: &'a Expr,
    },
    /// An arm of a `match`: its pattern, guard and value, in a scope of their own.
    Arm(&'a Arm),
    /// A `for` whose source is done: its keypath pattern binds in its `where` and its body, in
    /// a scope of their own.
    For {
        binders: &'a [Target],
        guard: Option<&'a Expr>,
        body: &'a Expr,
    },
    /// The end of the pattern of the `else` or the arm at the span: its binders are those from
    /// the index.
    PatternEnd(Span, usize),
    /// A member `of.name` whose `of` is done: what `name` names, if anything.
    Member(Span, &'a str),
    /// The end of the innermost scope.
    Close,
    /// The end of a function type, which is no longer open around the place.
    ArrowEnd,
    /// The end of the type of a bounds clause, and the clause's bounds.
    ForEnd(&'a Type, &'a [TypeBound]),
}

/// The message for the use of `name`, which nothing in scope and nothing in the prelude defines.
pub fn undefined(name: &str) -> String {
    format!("`{name}` is not defined.")
}

/// The error for a use at `span` of `m`, the parameter of `main(m: MainArgs)`, other than a
/// read of one of its fields: `m` holds ports, and a port is read or pushed to through its
/// field. A short headline, the rule in the notes (DESIGN.md sec:diagnostics).
fn main_param_alone(m: &str, span: Span) -> Error {
    let note = |text: String| Note { span, text };
    Error {
        row: None,
        menu: String::new(),
        span,
        message: format!("`{m}`, the argument of `main`, is used whole."),
        notes: vec![
            note(format!(
                "`{m}` is of type `MainArgs`, which holds the program's inputs and outputs as \
                 its fields; this zedc reads and pushes to each field, not to `{m}` as a whole"
            )),
            note(format!(
                "read `{m}.args`, `{m}.stdin` or `{m}.env`, or push to `{m}.stdout` or \
                 `{m}.stderr`, as `{m}.stdout <- lines;`"
            )),
        ],
    }
}

/// The error for the call `files()` whose name is at `span`, when the unit binds no `files`: the
/// file port was that call in `main`'s body, and is `main::files` in every function now (DESIGN.md
/// sec:ports, QUESTIONS A68). A short headline, the repairs in the notes.
fn files_moved(span: Span) -> Error {
    let note = |text: &str| Note {
        span,
        text: text.into(),
    };
    Error {
        row: None,
        menu: String::new(),
        span,
        message: "`files` is not defined: the file port is `main::files`.".into(),
        notes: vec![
            note("repair: `main::files` for `files()`, as in `fs = main::files;`"),
            note("repair: `main::files[path]` for `files()(path)`"),
            note(
                "every function of the program reads the file port as `main::files`, and no call \
                 opens it",
            ),
        ],
    }
}

/// The error for a call of `main` at `span`, anywhere in the program, `main`'s own body
/// included (DESIGN.md sec:ports, QUESTIONS A68): `main` is in scope everywhere and runs once,
/// when the program starts. A short headline, the menu in the notes.
fn main_called(span: Span) -> Error {
    let note = |text: &str| Note {
        span,
        text: text.into(),
    };
    Error {
        row: None,
        menu: String::new(),
        span,
        message: "Call of `main`: no function calls `main`, which runs once, when the program \
                  starts."
            .into(),
        notes: vec![
            note("repair: read `main::args` for the argument `main` takes"),
            note(
                "repair: move the code the call wants into a function that `main` and the caller \
                 both call",
            ),
        ],
    }
}

/// The error for the name `main` at `span` used as a value: passed, bound, returned or put in
/// a tuple, anywhere but as a call's callee, which [`main_called`] rejects, or before `::`.
/// Whether such a value is called later is a question of the program's data flow, which no
/// check decides in general; every value of a function is for calling, so the use itself is
/// rejected, in constant time, and no call through it can follow. The alternative, rejecting
/// only the calls through such a value, needs a flow analysis of every function value, for a
/// use that has no other purpose.
fn main_value(span: Span) -> Error {
    let note = |text: &str| Note {
        span,
        text: text.into(),
    };
    Error {
        row: None,
        menu: String::new(),
        span,
        message: "`main` used as a value: no function calls `main`, which runs once, when the \
                  program starts."
            .into(),
        notes: vec![
            note("repair: read `main::args` or `main::files` for what `main` reads"),
            note("repair: in place of `main`, use a function that `main` and this code both call"),
        ],
    }
}

/// The error for `MainArgs` written at `span`, anywhere but as the type of `main`'s parameter.
/// A short headline, the rule in the notes (DESIGN.md sec:diagnostics).
fn main_args_elsewhere(span: Span) -> Error {
    let note = |text: &str| Note {
        span,
        text: text.into(),
    };
    Error {
        row: None,
        menu: String::new(),
        span,
        message: "`MainArgs` is the type of the argument of `main` only.".into(),
        notes: vec![
            note(
                "`main`'s argument is written `main(m: MainArgs)`; no other function takes a \
                 `MainArgs`, and no value of it is built",
            ),
            note(
                "the fields of `m` are read in `main`, and a function is passed the values it \
                 needs, such as `m.args` or a line of `m.stdin`",
            ),
        ],
    }
}

/// The message for the type `name`, which no type in scope and no prelude type has as its name.
pub fn undefined_type(name: &str) -> String {
    format!("The type `{name}` is not defined.")
}

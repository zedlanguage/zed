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

use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::Range;
use std::sync::Arc;

use imbl::Vector;

use zedc_base::rejection::Row;
use zedc_syntax::ast::{
    Annot, Arm, Error, Expr, ExprKind, Field, Import, ImportKind, Param, Pattern, Port, RangeEnd,
    Stmt, StmtKind, StrPart, Struct, Target, TypeDecl,
};
use zedc_syntax::ast::{Every, Note, Type, TypeBound, TypeKind};
use zedc_syntax::lex::Span;

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
    /// An output port of a function's header, `-> (stdout: Lines)`.
    Port,
    /// A name a pattern binds: `#a(f:)`, `Point(x:)`, `n`, `n is int`.
    Pattern,
    /// A struct declaration `struct Point { … }`.
    Struct,
    /// A type declaration `type Shape = …;`.
    Type,
    /// A parameter `T` of a type declaration `type Tree(T) = …;`.
    TypeParam,
    /// A field of a struct. Fields are named through a value of the struct, never alone, so no
    /// scope holds them.
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
    Bound(Vector<usize>),
    /// A prelude word of layer L1.
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
    pub patterns: BTreeMap<Span, Range<usize>>,
    /// The fields of each struct, by the struct's statement: a range of `binders`.
    pub fields: BTreeMap<Span, Range<usize>>,
    /// The unit each import's binder comes from: for a qualifier, the unit it names; for a
    /// name a selective import brings in, the unit that defines it.
    pub imports: BTreeMap<usize, Arc<str>>,
    /// Each import statement, in every scope, with the unit it names, in text order: what the
    /// loader reads to find the units a unit needs.
    pub units: Vec<(Arc<str>, Span)>,
    /// The binders a `local` declaration binds, which no other unit sees.
    pub local: HashSet<usize>,
    /// What the unit's top level defines, which other units may import.
    pub exports: Exports,
    /// Where each declaration statement starts, in every scope: a binding, a function, a
    /// struct, a type, a method, an import, a `mutable`, a `local`, a piece of an indexed
    /// definition, or an annotated one. A doc comment attaches to the declaration that follows
    /// it (DESIGN.md sec:grammar, comments).
    pub decls: HashSet<usize>,
    /// The unit item `@log(#off);`, if the unit has one: it drops the log lines that every
    /// body of the unit writes (DESIGN.md sec:ports). Step L7.3, which writes the lines, reads it.
    pub log_off: Option<Span>,
    /// Each `e else d`, `e else #a -> d` and `e is T` whose `e` is a name, by the name's text,
    /// in the order of the text: the atoms the test or the replacement handles. The checker
    /// gives an undeclared parameter the atoms its uses handle (DESIGN.md sec:type_resolution).
    pub handles: Vec<(Span, Handle)>,
    /// Each binding that is another name, `s = line`: the binder of `s` and the text of
    /// `line`. The uses of `s` handle atoms for `line` (DESIGN.md sec:type_resolution).
    pub aliases: Vec<(usize, Span)>,
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

/// What a unit's top level defines: each name, by name. It holds no text position, so an edit
/// that moves or rewrites a definition but keeps its name, its kind and its `local` leaves the
/// exports, and so every importer's resolution, as they were.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Exports {
    names: BTreeMap<String, Export>,
}

impl Exports {
    /// What the unit defines as `name`, if anything.
    pub fn get(&self, name: &str) -> Option<Export> {
        self.names.get(name).copied()
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

    /// The names in order, each as its length, its bytes, its kind and `local`: what an
    /// importer's resolution reads of the unit, encoded so that two exports have equal bytes
    /// only when they are equal.
    pub fn bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for (name, e) in &self.names {
            out.extend_from_slice(&(name.len() as u64).to_le_bytes());
            out.extend_from_slice(name.as_bytes());
            out.extend_from_slice(&[e.kind as u8, u8::from(e.local)]);
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
/// and so enter with the scalars they take. The table's other names that are no word are left
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
    ("count", 3),
    ("map", 3),
    ("where", 3),
    ("foldl", 3),
    ("foldr", 3),
    ("reduce", 3),
    ("allOk", 3),
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
    ("rank", 5),
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
    ("bf16", 14),
    ("f16", 14),
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
    prelude_layer(name).is_some() || TYPES.contains(&name) || later_type_layer(name).is_some()
}

/// The layer of the prelude type `name` of a later layer, if it is one.
fn later_type_layer(name: &str) -> Option<u32> {
    LATER_TYPES
        .iter()
        .find(|(t, _)| *t == name)
        .map(|&(_, layer)| layer)
}

/// The annotations, each with the layer it belongs to (DESIGN.md, "Defined words by layer").
/// `@hash`, of layer L2, pins an import and annotates no declaration.
const ANNOTATIONS: &[(&str, u32)] = &[
    ("hash", 2),
    ("foreign", 7),
    ("export", 7),
    ("borrowed", 7),
    ("stateless", 7),
    ("log", 7),
    ("after", 7),
    ("checked", 10),
    ("invariant", 15),
    ("ensure", 15),
    ("proved", 15),
    ("exhaustive", 15),
    ("exact", 15),
    ("strict", 15),
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
const TYPES: &[&str] = &[
    "int",
    "rat",
    "f64",
    "bool",
    "String",
    "Lines",
    "Files",
    "CommandLine",
];

/// The type names of the prelude's later layers, each with its layer (DESIGN.md, "Defined words
/// by layer"). A use below its layer is an error naming the layer, as for a value word. The
/// number algebras and float formats of L14 are words too, applied to build a value; the
/// fixed-width aliases of L7, `i8` to `i64` and `u8 = int[0..=255]`, are types only.
pub const LATER_TYPES: &[(&str, u32)] = &[
    ("Seq", 5),
    ("Ast", 6),
    ("Facet", 6),
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
    ("complex", 14),
    ("quat", 14),
    ("oct", 14),
    ("bf16", 14),
    ("f16", 14),
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
const CARRIERS: &[&str] = &["int", "f64", "rat", "String", "bool"];

/// The resolution of `unit`, read alone, or every error in it and every form it uses that a
/// later step compiles, in text order.
pub fn resolve(unit: &[Stmt]) -> Result<Resolution, Vec<Error>> {
    let Resolved {
        res,
        mut errors,
        later,
    } = resolve_in(unit, &Alone);
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
    let mut r = Resolver {
        units: Some(units),
        ..Resolver::default()
    };
    // The top level is two scopes: the outer holds what its imports bring in (tier 3), the
    // inner what it declares (tier 2), which shadows it.
    r.scopes.push(Vec::new());
    r.scopes.push(Vec::new());
    r.walk(Task::Unit(unit));
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
    visible: HashMap<String, Vec<Bound>>,
    /// Whether the declaration being bound is marked `local`.
    local: bool,
    /// The binders of imports that failed: their uses are not reported again.
    dead: HashSet<usize>,
    /// The type variables a bounds clause around the type being walked binds, by name.
    tvars: HashMap<String, TypeVar>,
    /// The function types around the type being walked, outermost first, by their text.
    arrows: Vec<Span>,
    /// The bounds clauses around the type being walked, outermost first, by their text.
    clauses: Vec<Span>,
    /// When a printed type is read ([`printed_type`]): the names that stand for its leaves of
    /// layer L10.
    printed: Option<HashSet<Arc<str>>>,
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
                            "`{name}` is already declared in this scope with these parameter \
                             types"
                        ),
                        format!("the first `{name}` with these parameter types"),
                    ),
                    _ if b.imported => (
                        format!("`{name}` is already bound in this scope, by an import"),
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
            span,
            message: format!(
                "`{name}` is ambiguous: two imports bring it into scope from different units; \
                 name the one meant through a qualifier, as `{q}.{name}` after `import {unit};`",
                unit = self.out.imports[&a],
                q = self.out.imports[&a].rsplit('.').next().unwrap_or_default(),
            ),
            notes,
        });
    }

    /// Records the use of `name` at `span`, or the error that it names nothing at L1.
    fn name(&mut self, name: &str, span: Span) {
        if name.ends_with('\'') {
            return self.primed(name, span);
        }
        let message = match self.find(name) {
            Some(Found::Bound(ids)) if self.dead.contains(&ids[0]) => return,
            Some(Found::Bound(ids)) if self.out.binders[ids[0]].kind == Kind::Unit => {
                let unit = &self.out.imports[&ids[0]];
                format!(
                    "`{name}` names the unit `{unit}`, which is no value; a definition of the \
                     unit is written `{name}.f`"
                )
            }
            Some(Found::Bound(ids)) => {
                self.out.uses.insert(span, Ref::Bound(ids));
                return;
            }
            Some(Found::Ambiguous(a, b)) => return self.ambiguous(name, span, a, b),
            Some(Found::Unit(unit)) => return self.prelude_unit(name, span, unit),
            Some(Found::Word(1)) => {
                self.out.uses.insert(span, Ref::Prelude(name.into()));
                return;
            }
            Some(Found::Word(layer)) => format!("`{name}` is a prelude word of layer L{layer}"),
            // A prelude struct of a later layer is named as a value to build one.
            None => match later_type_layer(name) {
                Some(layer) => format!("`{name}` is a prelude type of layer L{layer}"),
                None => format!("`{name}` is not defined"),
            },
        };
        self.errors.push(Error {
            row: None,
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
            return true;
        }
        let unit = self.out.imports[&id].clone();
        let import = self.out.binders[id].span;
        if self.export(&unit, name, span, import).is_some() {
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
            Some(_) => format!(
                "`{name}` is declared `local` in the unit `{unit}`, so no other unit sees it"
            ),
            None => format!("the unit `{unit}` defines no `{name}`"),
        };
        self.errors.push(Error {
            row: None,
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
        self.out.units.push((unit.clone(), span));
        let exports = match self.units.map(|u| u.exports(&i.path)) {
            Some(Ok(e)) => Some(e),
            Some(Err(Refused::Because(why))) => {
                self.errors.push(Error {
                    row: None,
                    span,
                    message: format!("the unit `{unit}` cannot be imported: {why}"),
                    notes: Vec::new(),
                });
                None
            }
            Some(Err(Refused::OnCycle)) => None,
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
                }
                return;
            }
        };
        let id = self.bind_import(qualifier, span, Kind::Unit, &unit);
        if exports.is_none() {
            self.dead.insert(id);
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
                Task::Unit(stmts) => self.stmts(stmts, true, &mut todo),
                Task::Stmts(stmts) => self.stmts(stmts, false, &mut todo),
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
                        self.later(span, &format!("the primed field `{name}`"), "L6.3");
                    } else if let Some(Found::Bound(ids)) = self.find(name)
                        && !self.dead.contains(&ids[0])
                    {
                        self.out.uses.insert(span, Ref::Bound(ids));
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

    /// The statements of the innermost scope: their binders first, since order has no meaning.
    /// They are the unit's own statements when `top` holds.
    fn stmts<'a>(&mut self, stmts: &'a [Stmt], top: bool, todo: &mut Vec<Task<'a>>) {
        let mut families = HashSet::new();
        for s in stmts {
            if !matches!(
                s.kind,
                StmtKind::Return(_)
                    | StmtKind::Push { .. }
                    | StmtKind::While(_)
                    | StmtKind::Until(_)
                    | StmtKind::Expr(_)
                    | StmtKind::UnitAnnot(_)
            ) {
                self.out.decls.insert(s.span.start);
            }
            self.declare(s, false, &mut families);
        }
        todo.extend(stmts.iter().rev().map(|s| Task::Stmt(s, top)));
    }

    /// Binds the names the statement `s` declares. Resolution refuses the forms of layer L6
    /// whole, but binds their names, so that a use of one is not reported as well; in such a
    /// statement (`whole`) a primed name, a loop step's output, is not bound. The pieces of one
    /// indexed family bind its name once: `families` holds the families bound in this scope.
    fn declare<'s>(&mut self, s: &'s Stmt, whole: bool, families: &mut HashSet<&'s str>) {
        match &s.kind {
            StmtKind::Bind {
                targets,
                value,
                boundary,
            } => {
                let whole = whole || !boundary.is_empty();
                let id = self.out.binders.len();
                for t in targets {
                    match t {
                        Target::Name(n, _) if whole && n.ends_with('\'') => {}
                        Target::Name(n, at) => self.bind(n, *at, s.span, Kind::Binding, None),
                        Target::Wild => {}
                    }
                }
                if let ([Target::Name(..)], ExprKind::Name(_)) = (targets.as_slice(), &value.kind)
                    && !whole
                    && self.out.binders.len() == id + 1
                {
                    self.out.aliases.push((id, value.span));
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
            // The declaration is not annotated again, and a `mutable` holds a binding, so this
            // recursion is one level deep.
            StmtKind::Annotated { decl, .. } => self.declare(decl, whole, families),
            StmtKind::Mutable(decl) => self.declare(decl, true, families),
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
                    span: s.span,
                    message: "`local` stands at a unit's top level or in a loop body; a \
                              declaration in this block is seen by no other unit already"
                        .into(),
                    notes: Vec::new(),
                });
                return false;
            }
            StmtKind::Return(_) => "a `return`",
            StmtKind::Push { .. } => "a push",
            StmtKind::Import(_) => "an import, whose names are not definitions of the unit",
            StmtKind::Local(_) => "a `local` declaration again",
            StmtKind::Mutable(_) => "a `mutable` binding, which belongs to a loop body",
            StmtKind::IndexedDef(_) => "an indexed definition",
            StmtKind::While(_) | StmtKind::Until(_) => "a loop guard",
            StmtKind::Expr(_) => "an expression statement",
            StmtKind::Annotated { .. } | StmtKind::UnitAnnot(_) => {
                "an annotated declaration; write the annotation before `local`"
            }
        };
        self.errors.push(Error {
            row: None,
            span: s.span,
            message: format!(
                "`local` marks a binding, a function, a struct, a type or a method, and not {what}"
            ),
            notes: Vec::new(),
        });
        false
    }

    /// The statement `s`, whose binders its scope has; `top` holds when it is one of the unit's
    /// own statements.
    fn stmt<'a>(&mut self, s: &'a Stmt, top: bool, todo: &mut Vec<Task<'a>>) {
        match &s.kind {
            StmtKind::Bind { boundary, .. } if !boundary.is_empty() => {
                self.later(s.span, "a boundary `with`", "L6.2")
            }
            StmtKind::Bind { value, .. } => todo.push(Task::Expr(value)),
            StmtKind::Return(es) => todo.extend(es.iter().rev().map(Task::Expr)),
            StmtKind::Push { port, .. } if port.ends_with('\'') => {
                self.later(s.span, "a generation push `x' <- e`", "L6.3")
            }
            StmtKind::Push { port, value } => {
                self.name(port, s.span);
                todo.push(Task::Expr(value));
            }
            StmtKind::Function(f) => {
                let ports: &[Port] = f.ports.as_deref().unwrap_or_default();
                // At L1 an output port is `Lines` (DESIGN.md step L1.19). The ports of a `main`
                // among the unit's own statements are checked with its inputs when the unit is
                // loaded as a program (`run::program`); a `main` nested in a block is checked here.
                if !(top && f.name == "main") {
                    for p in ports {
                        if !matches!(&p.ty.kind, TypeKind::Name(n) if n == "Lines") {
                            self.errors.push(Error {
                                row: None,
                                span: p.span,
                                message: format!(
                                    "output port `{}` of `{}` is `Lines` at layer L1",
                                    p.name, f.name
                                ),
                                notes: Vec::new(),
                            });
                        }
                    }
                }
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
                todo.extend(ports.iter().rev().map(|p| Task::Ty(&p.ty)));
            }
            StmtKind::Struct(st) => {
                self.later(s.span, "a struct declaration", "L2.4");
                self.fields(st, s.span, todo);
            }
            // A primed name is of layer L6 wherever it stands (DESIGN.md sec:grammar).
            StmtKind::Method(m) if m.receiver.ends_with('\'') => self.primed(&m.receiver, s.span),
            StmtKind::Method(m) if m.function.name.ends_with('\'') => {
                self.primed(&m.function.name, s.span)
            }
            StmtKind::Method(m) => {
                self.later(s.span, "a method", "L2.4");
                let f = &m.function;
                let ports: &[Port] = f.ports.as_deref().unwrap_or_default();
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
                todo.extend(ports.iter().rev().map(|p| Task::Ty(&p.ty)));
                todo.push(Task::TypeName(&m.receiver, s.span));
            }
            StmtKind::Type(t) => {
                self.later(s.span, "a type declaration", "L2.5");
                self.type_decl(t, s.span, todo);
            }
            StmtKind::Import(_) => {
                self.later.push(Error {
                    row: None,
                    span: s.span,
                    message: "an import is linked from step L2.4, which ties each name it \
                              brings in to the other unit's definition"
                        .into(),
                    notes: Vec::new(),
                });
            }
            StmtKind::Local(decl) => {
                self.later(s.span, "a `local` declaration", "L2.4");
                todo.push(Task::Stmt(decl, top));
            }
            StmtKind::Mutable(_) => self.later(s.span, "a `mutable` binding", "L6.3"),
            StmtKind::IndexedDef(_) => self.later(s.span, "an indexed definition", "L6.2"),
            StmtKind::While(_) => self.later(s.span, "a `while` guard", "L6.3"),
            StmtKind::Until(_) => self.later(s.span, "an `until` guard", "L6.3"),
            StmtKind::Expr(_) => self.later(s.span, "an expression statement", "L6.3"),
            StmtKind::Annotated { annots, decl } => {
                annots.iter().for_each(|a| self.annotation(a));
                todo.push(Task::Stmt(decl, false));
            }
            StmtKind::UnitAnnot(a) => self.unit_annotation(a, s.span),
        }
    }

    /// The fields of the struct `st`, declared by the statement at `span`: each a binder no
    /// scope holds, named once. A field's type and default are read in the struct's scope.
    fn fields<'a>(&mut self, st: &'a Struct, span: Span, todo: &mut Vec<Task<'a>>) {
        let start = self.out.binders.len();
        let mut seen: HashMap<&str, Span> = HashMap::new();
        for f in &st.fields {
            match f {
                Field::Typed {
                    name,
                    ty,
                    default,
                    span: at,
                } => {
                    if let Some(&first) = seen.get(name.as_str()) {
                        self.errors.push(Error {
                            row: None,
                            span: *at,
                            message: format!(
                                "the struct `{}` has the field `{name}` twice",
                                st.name
                            ),
                            notes: vec![Note {
                                span: first,
                                text: format!("the first field `{name}`"),
                            }],
                        });
                    } else {
                        seen.insert(name, *at);
                        self.out.binders.push(Binder {
                            name: name.clone(),
                            span: *at,
                            kind: Kind::Field,
                        });
                    }
                    todo.extend(default.as_ref().map(Task::Expr));
                    todo.push(Task::Ty(ty));
                }
                Field::Import { path, span: at } => todo.push(Task::TypeName(path, *at)),
            }
        }
        let end = self.out.binders.len();
        self.out.fields.insert(span, start..end);
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

    /// The annotation `a`. None has a meaning before layer L7, so each is refused with its
    /// reason: it is no annotation, it is `@hash`, which annotates no declaration, or it is of
    /// a later layer.
    fn annotation(&mut self, a: &Annot) {
        let name = &a.name;
        let message = match annotation_layer(name) {
            None => format!("`@{name}` is not an annotation"),
            Some(2) => "`@hash` pins an import and follows its unit path, as in \
                 `import geometry.shapes @hash(\"…\");`; it annotates no declaration"
                .into(),
            Some(layer) => format!("`@{name}` is an annotation of layer L{layer}"),
        };
        self.errors.push(Error {
            row: None,
            span: a.span,
            message,
            notes: Vec::new(),
        });
    }

    /// The unit item `a;`, written as the statement at `span`. Two annotations are unit items:
    /// `@log(#off);`, which this layer accepts, and `@strict;`, of layer L15. Each other way to
    /// write one is refused with its reason.
    fn unit_annotation(&mut self, a: &Annot, span: Span) {
        let name = &a.name;
        let fail = |message: String| Error {
            row: None,
            span,
            message,
            notes: Vec::new(),
        };
        let error = match annotation_layer(name) {
            Some(_) if name == "strict" => return self.annotation(a),
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
                    ..fail("the unit has `@log(#off);` twice".into())
                },
            },
        };
        self.errors.push(error);
    }

    /// The primed name `name`, which names a loop step's output.
    fn primed(&mut self, name: &str, span: Span) {
        self.later(span, &format!("the primed name `{name}`"), "L6.3");
    }

    /// The form `what`, which the parser builds, has its meaning from step `step`.
    fn later(&mut self, span: Span, what: &str, step: &str) {
        self.errors.push(Error {
            row: None,
            span,
            message: format!("{what} is compiled from step {step}"),
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

    /// The use at `span` of `what`, a name another unit defines, which step L2.4 links.
    fn linked(&mut self, span: Span, what: &str) {
        self.later.push(Error {
            row: None,
            span,
            message: format!("{what} is linked from step L2.4"),
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
            self.later(p.span, "a tuple-destructuring parameter", "L2.4");
        }
        self.open();
        if let Some(at) = this {
            self.bind("this", at, at, Kind::Receiver, None);
        }
        for p in params {
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
        }
        for p in ports {
            self.bind(&p.name, name_at(p.span, &p.name), p.span, Kind::Port, None);
        }
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
            | ExprKind::Float(_)
            | ExprKind::Rat(_)
            | ExprKind::Bool(_)
            | ExprKind::Atom(_) => {}
            ExprKind::Str(parts) => todo.extend(parts.iter().rev().filter_map(|p| match p {
                StrPart::Hole(h) => Some(Task::Expr(h)),
                StrPart::Text(_) => None,
            })),
            ExprKind::Name(n) => self.name(n, e.span),
            ExprKind::Unary(_, a) => todo.push(Task::Expr(a)),
            ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
                todo.push(Task::Expr(b));
                todo.push(Task::Expr(a));
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                ..
            } => {
                todo.extend(named.iter().rev().map(|(_, a)| Task::Expr(a)));
                todo.extend(positional.iter().rev().map(Task::Expr));
                todo.push(Task::Expr(callee));
            }
            ExprKind::Tuple(items) => todo.extend(items.iter().rev().map(Task::Expr)),
            ExprKind::Lambda { params, body } => todo.push(Task::Function {
                params,
                ports: &[],
                body,
                this: None,
            }),
            ExprKind::Is { of, ty, .. } => {
                if let ExprKind::Name(_) = of.kind {
                    // The written type's atoms: a union nests as deep as its text.
                    let mut stack = vec![ty];
                    while let Some(t) = stack.pop() {
                        match &t.kind {
                            TypeKind::Atom(a) => {
                                self.out.handles.push((of.span, Handle::Bare(a.clone())))
                            }
                            TypeKind::Union(ts) => stack.extend(ts),
                            _ => {}
                        }
                    }
                }
                todo.push(Task::Ty(ty));
                todo.push(Task::Expr(of));
            }
            ExprKind::Else {
                of,
                pattern,
                default,
            } => {
                if let ExprKind::Name(_) = of.kind {
                    let h = match pattern {
                        None => Some(Handle::Loose),
                        Some(Pattern::Atom {
                            name,
                            fields,
                            items,
                            ..
                        }) if fields.is_empty() && items.is_empty() => {
                            Some(Handle::Any(name.clone()))
                        }
                        Some(_) => None,
                    };
                    self.out.handles.extend(h.map(|h| (of.span, h)));
                }
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
                self.later(e.span, "a record display", "L2.4");
                todo.extend(fields.iter().rev().map(|(_, v)| Task::Expr(v)));
            }
            ExprKind::With { of, updates } => {
                self.later(e.span, "a `with` clause", "L2.4");
                todo.extend(updates.iter().rev().map(|u| Task::Expr(&u.value)));
                todo.push(Task::Expr(of));
            }
            ExprKind::This => {
                self.later(e.span, "`this`", "L2.4");
                match self.find("this") {
                    Some(Found::Bound(ids)) => {
                        self.out.uses.insert(e.span, Ref::Bound(ids));
                    }
                    _ => self.errors.push(Error {
                        row: None,
                        span: e.span,
                        message: "`this` stands outside a method: it names the receiver of a \
                                  method `T.m(…) = …`, in the method's body"
                            .into(),
                        notes: Vec::new(),
                    }),
                }
            }
            ExprKind::Match { of, arms } => {
                self.later(e.span, "a `match`", "L2.4");
                todo.extend(arms.iter().rev().map(Task::Arm));
                todo.push(Task::Expr(of));
            }
            // The forms below are compiled from a later step, and their parts are resolved here
            // as `match`'s are, so a name in them is recorded or reported.
            ExprKind::Range(from, to) => {
                self.later(e.span, "a range", "L3.2");
                todo.extend(to.bound().map(|b| Task::Expr(b)));
                todo.push(Task::Expr(from));
            }
            ExprKind::In { of, set, .. } => {
                self.later(e.span, "an `in` test", "L3.2");
                todo.push(Task::Expr(set));
                todo.push(Task::Expr(of));
            }
            ExprKind::Reduce { of, op } => {
                self.later(e.span, "a reduction `><`", "L3.2");
                todo.push(Task::Expr(op));
                todo.push(Task::Expr(of));
            }
            ExprKind::Read { of, .. } => {
                self.later(e.span, "a metadata read `::`", "L3.2");
                todo.push(Task::Expr(of));
            }
            ExprKind::Section(_) => self.later(e.span, "an operator section", "L3.2"),
            ExprKind::Array(items) => {
                self.later(e.span, "an array display", "L3.2");
                todo.extend(items.iter().rev().map(Task::Expr));
            }
            ExprKind::Set(items) => {
                self.later(e.span, "a set display", "L3.2");
                todo.extend(items.iter().rev().map(Task::Expr));
            }
            ExprKind::Map(entries) => {
                self.later(e.span, "a map display", "L3.2");
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
                self.later(e.span, "a `for`", "L3.2");
                todo.push(Task::For {
                    binders,
                    guard: guard.as_deref(),
                    body,
                });
                todo.push(Task::Expr(source));
            }
            // A loop body's bare and primed names are the frames of step L6.3, which a
            // `mutable` or a `with` boundary declares and resolution does not bind yet, so the
            // body is not walked: its names would be reported as not defined.
            ExprKind::Loop { .. } => self.later(e.span, "a `loop`", "L6.3"),
            ExprKind::Break(value) => {
                self.later(e.span, "a `break`", "L6.3");
                todo.push(Task::Expr(value));
            }
            ExprKind::Spread { of, name } => {
                self.later(e.span, "a call `*.` that writes its receiver", "L6.3");
                todo.push(Task::Member(e.span, name));
                todo.push(Task::Expr(of));
            }
            ExprKind::SortKey { key, .. } => {
                self.later(e.span, "a sort key `asc` or `desc`", "L5.1");
                todo.push(Task::Expr(key));
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
            Pattern::Is { .. } => Some(("a type pattern `n is T`", "L2.4")),
            Pattern::Lit(_) => Some(("a literal pattern", "L2.4")),
            Pattern::Range { .. } => Some(("a range pattern", "L3.2")),
            Pattern::Struct { .. } | Pattern::Name(..) | Pattern::Wild(_) | Pattern::Tuple(..) => {
                Some(("a struct, name, `_` or tuple pattern", "L2.4"))
            }
        };
        if report && let Some((what, step)) = later {
            self.later(p.span(), what, step);
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
                            span: b.span,
                            message: format!("the type variable `{}` is bounded twice", b.name),
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
                if let Err(message) = Type::overload(&ts) {
                    self.errors.push(Error {
                        row: None,
                        span: t.span,
                        message,
                        notes: Vec::new(),
                    });
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
                self.later(t.span, "an applied type", "L2.5");
                todo.extend(ps.iter().rev().map(|p| Task::Ty(&p.ty)));
                todo.push(Task::TypeName(name, name_at(t.span, name)));
            }
            TypeKind::AtomApply(_, ps) => {
                self.later(t.span, "an atom type with a payload", "L2.5");
                todo.extend(ps.iter().rev().map(|p| Task::Ty(&p.ty)));
            }
            TypeKind::AtomAny(_) => self.later(t.span, "an atom type with any payload", "L2.5"),
            TypeKind::Every(Every::Struct) => {
                self.later(t.span, "the type of every struct", "L2.5")
            }
            TypeKind::Record(fields) => {
                self.later(t.span, "a record type", "L2.5");
                todo.extend(fields.iter().rev().map(|(_, t)| Task::Ty(t)));
            }
            TypeKind::Array(_) => self.later(t.span, "a family type `[T]`", "L3.2"),
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
            Some(Found::Bound(ids)) if self.dead.contains(&ids[0]) => return,
            Some(Found::Bound(ids)) if self.out.binders[ids[0]].kind.is_type() => {
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
                let kind = (self.units.and_then(|u| u.prelude()))
                    .and_then(|(_, e)| e.get(n))
                    .map(|e| e.kind);
                if kind.is_some_and(Kind::is_type) {
                    return self.prelude_unit(n, span, unit);
                }
                format!("the type `{n}` is not defined")
            }
            Some(Found::Word(_)) | None => match later_type_layer(n) {
                Some(layer) => format!("the type `{n}` is a prelude type of layer L{layer}"),
                None => format!("the type `{n}` is not defined"),
            },
        };
        self.errors.push(Error {
            row: None,
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
                span,
                message: format!(
                    "the type `{q}.{name}` has more than one qualifier; a qualified type is a \
                     qualifier and a type, as `shapes.Point` after `import geometry.shapes;`"
                ),
                notes: Vec::new(),
            });
        }
        let message = match self.find(q) {
            Some(Found::Bound(ids)) if self.dead.contains(&ids[0]) => return,
            Some(Found::Bound(ids)) if self.out.binders[ids[0]].kind == Kind::Unit => {
                let id = ids[0];
                let unit = self.out.imports[&id].clone();
                let import = self.out.binders[id].span;
                match self.export(&unit, name, span, import) {
                    None => return,
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
                    span: b.span,
                    message: format!(
                        "the bound names `{}`, which the type before `for` does not hold",
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
    /// The unit's own statements.
    Unit(&'a [Stmt]),
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

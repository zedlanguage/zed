//! The nodes of the syntax tree: expressions, statements, declarations, types, parameters and
//! patterns, which hold each other, and the errors of building them. The builder (the parent
//! module and its `stmts`, `types`, `body` and `neglit`) makes them; `show` prints them and
//! `drop` drops them.

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use crate::lex::{Digits, Span};
use zedc_base::address::ContentAddress;

/// An expression and its span.
pub struct Expr {
    /// What it is.
    pub kind: ExprKind,
    /// Its text.
    pub span: Span,
}

/// The kinds of expression.
#[derive(Debug)]
pub enum ExprKind {
    /// An integer: its base and digits.
    Int {
        /// The base.
        radix: u32,
        /// The digits, shared with the token.
        digits: Digits,
    },
    /// A decimal literal.
    Float {
        /// Its decimal text, shared with the token.
        digits: Digits,
        /// Whether it is written with the suffix `f64`, which forces that format; without it,
        /// the literal takes the carrier its use fixes (step L1.26b).
        forced: bool,
    },
    /// An exact rational, as its decimal text, shared with the token.
    Rat(Digits),
    /// A string: its text and its holes.
    Str(Vec<StrPart>),
    /// `true` or `false`.
    Bool(bool),
    /// An atom, without its `#`.
    Atom(String),
    /// A name.
    Name(String),
    /// A prefix operator, `-` or `!`, and its operand.
    Unary(&'static str, Box<Expr>),
    /// A binary operator and its operands.
    Binary(&'static str, Box<Expr>, Box<Expr>),
    /// A call `f(…)`.
    Call {
        /// The function.
        callee: Box<Expr>,
        /// The positional arguments, in order.
        positional: Vec<Expr>,
        /// The named arguments, in written order; `x:` is `x: x`.
        named: Vec<(String, Expr)>,
        /// Whether the arguments end in `...`, currying the named parameters left out.
        curry: bool,
    },
    /// An index `e[k]`.
    Index(Box<Expr>, Box<Expr>),
    /// A tuple `(a, b, …)`.
    Tuple(Vec<Expr>),
    /// A lambda `x -> e` or `(params) -> e`.
    Lambda {
        /// The parameters.
        params: Vec<Param>,
        /// The body.
        body: Box<Expr>,
    },
    /// A type test `e is T`, or `e is not T` when `negated`: whether the value of `e` is in the
    /// set of `T`, decided when the program runs. It is not the subtype relation `S <: T`
    /// between two types, which the checker decides and Zed has no syntax for
    /// (DESIGN.md sec:type_language).
    Is {
        /// The value tested.
        of: Box<Expr>,
        /// The type.
        ty: Type,
        /// Whether it is `is not`.
        negated: bool,
    },
    /// `e else d`, or `e else #a -> d` with its atom pattern.
    Else {
        /// The value whose atom members are replaced.
        of: Box<Expr>,
        /// The members replaced: every loose atom member when `None`.
        pattern: Option<Pattern>,
        /// The default.
        default: Box<Expr>,
    },
    /// A block `{ … }`: its statements in written order, except that its `return` is last
    /// (none in a function's body block that only pushes).
    Block(Vec<Stmt>),
    /// `if c { a } else { b }`; `else if` is an `If` in the `else` branch.
    If {
        /// The condition.
        cond: Box<Expr>,
        /// The branch taken when it holds.
        then: Box<Expr>,
        /// The other branch.
        otherwise: Box<Expr>,
    },
    /// A member `e.n`, or `e?.n` when `safe`.
    Member {
        /// The value.
        of: Box<Expr>,
        /// The member's name.
        name: String,
        /// Whether it is `?.`, which passes an atom member of the value's type through.
        safe: bool,
    },
    /// A record display `{x: 1, y:}`: its fields in written order; `y:` is `y: y`.
    Record(Vec<(String, Expr)>),
    /// A struct update `e with { x = 1, c.y = 2 }`.
    With {
        /// The value updated.
        of: Box<Expr>,
        /// The updates, in written order.
        updates: Vec<Update>,
    },
    /// `this`, a method's receiver.
    This,
    /// `match e { p -> a, q where c -> b }`: the value matched and its arms, in written order.
    Match {
        /// The value matched.
        of: Box<Expr>,
        /// The arms.
        arms: Vec<Arm>,
    },
    /// A range `a..<b`, `a..=b` or `a..`: its first value and its end.
    Range(Box<Expr>, RangeEnd<Box<Expr>>),
    /// A membership test `e in s`, or `e not in s` when `negated`.
    In {
        /// The value tested.
        of: Box<Expr>,
        /// The family whose domain it is tested against.
        set: Box<Expr>,
        /// Whether it is `not in`.
        negated: bool,
    },
    /// A reduction `m >< op`, which folds `op` over the innermost level of `m`.
    Reduce {
        /// The family reduced.
        of: Box<Expr>,
        /// The operator.
        op: Box<Expr>,
    },
    /// A metadata read `e::name`, such as `xs::len` or `m::domain`.
    Read {
        /// The value read.
        of: Box<Expr>,
        /// The metadata's name.
        name: String,
    },
    /// An operator section `(+)`: the binary operator as a function.
    Section(&'static str),
    /// An array display `[a, b, c]`, its elements in written order: the array
    /// `{0 -> a, 1 -> b, 2 -> c}` of type `int[0..<3] -> T`, keyed by rank, each element's
    /// rank its position (sec:grammar, `ArrayExpr`). It is not a `Seq` (sec:order), whose keys
    /// are origins.
    Array(Vec<Expr>),
    /// A set display `{a, b}`, its elements in written order.
    Set(Vec<Expr>),
    /// A map display `{k -> v, …}`, its entries in written order. `{}` is the empty family,
    /// built as the map with no entries: a set is a map from each element to itself.
    Map(Vec<(Expr, Expr)>),
    /// `for k -> v in m where c { … }`: a family with one frame per entry of the source.
    For {
        /// The binders of the keypath pattern, outermost level first; a bare name binds the
        /// value.
        binders: Vec<Target>,
        /// The family iterated.
        source: Box<Expr>,
        /// The `where` restriction of the source's domain, if written.
        guard: Option<Box<Expr>>,
        /// The block run for each entry.
        body: Box<Expr>,
    },
    /// `loop t { … }`: a body run once per generation, `t` naming the step index if written.
    Loop {
        /// The name of the step index, if written.
        label: Option<String>,
        /// The body, a block that need not export.
        body: Box<Expr>,
    },
    /// `break e`: ends the loop, `e` its result.
    Break(Box<Expr>),
    /// `c*.m`: the member `m` of `c` called so that it writes `c'`.
    Spread {
        /// The receiver.
        of: Box<Expr>,
        /// The member's name.
        name: String,
    },
    /// `asc e` or `desc e`: a sort key, written only as a positional argument (`SortArg`).
    SortKey {
        /// Whether it is `desc`.
        desc: bool,
        /// The key; `None` for a direction word written alone, the key `x -> x`, the value
        /// itself (`xs.sort(desc)`).
        key: Option<Box<Expr>>,
    },
}

/// How a range ends: below `b` (`..<b`), through `b` (`..=b`), or not at all (`..`).
#[derive(Debug)]
pub enum RangeEnd<T> {
    /// `..<b`.
    Below(T),
    /// `..=b`.
    Through(T),
    /// `..`.
    Open,
}

impl<T> RangeEnd<T> {
    /// The operator written.
    pub fn op(&self) -> &'static str {
        match self {
            RangeEnd::Below(_) => "..<",
            RangeEnd::Through(_) => "..=",
            RangeEnd::Open => "..",
        }
    }

    /// The last value, or the bound below it, if written.
    pub fn bound(&self) -> Option<&T> {
        match self {
            RangeEnd::Below(b) | RangeEnd::Through(b) => Some(b),
            RangeEnd::Open => None,
        }
    }
}

/// An arm of a `match`: a pattern, a guard `where c` if written, and the arm's value.
#[derive(Debug)]
pub struct Arm {
    /// The pattern.
    pub pattern: Pattern,
    /// The guard.
    pub guard: Option<Expr>,
    /// The value when the pattern matches and the guard holds.
    pub body: Expr,
    /// Its text.
    pub span: Span,
}

/// One update of a `with`: a field path, `c.y`, and its new value.
#[derive(Debug)]
pub struct Update {
    /// The fields of the path, outermost first.
    pub path: Vec<String>,
    /// The new value.
    pub value: Expr,
    /// Its text.
    pub span: Span,
}

/// A part of a string expression.
#[derive(Debug)]
pub enum StrPart {
    /// Text, shared with the token it was read from.
    Text(Arc<String>),
    /// A `${…}` hole.
    Hole(Expr),
}

/// Why an expression could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    /// Where.
    pub span: Span,
    /// Why.
    pub message: String,
    /// How the checker reached it: each constraint and step, in the order it met them.
    pub notes: Vec<Note>,
    /// The menu of fixes, written after the steps of `notes` (DESIGN.md sec:diagnostics): its
    /// heading line, then each fix on a line of its own, every line starting with a newline.
    /// Empty when the error has none.
    pub menu: String,
    /// The row of the rejection table (DESIGN.md sec:diagnostics) the error is a case of, if any.
    pub row: Option<zedc_base::rejection::Row>,
}

/// One step of a derivation: a place in the source and what holds there.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Note {
    /// Where.
    pub span: Span,
    /// What holds there.
    pub text: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

/// A statement and its span.
#[derive(Debug)]
pub struct Stmt {
    /// What it is.
    pub kind: StmtKind,
    /// Its text, its `;` included.
    pub span: Span,
}

/// The kinds of statement.
#[derive(Debug)]
pub enum StmtKind {
    /// `a = e;`, or `a, b = e;` destructuring a tuple.
    Bind {
        /// The targets, in order.
        targets: Vec<Target>,
        /// The value.
        value: Expr,
    },
    /// `initial x = e;`, the start value of a variable its loop updates, or a boundary entry
    /// `initial p[-2] = e;` (DESIGN.md sec:generations).
    Initial(Initial),
    /// `mutable x = e;`: the binding, whose variable carries forward when a step leaves it
    /// unassigned.
    Mutable(Box<Stmt>),
    /// `local d`: the declaration `d`, visible in its unit only (DESIGN.md sec:units).
    Local(Box<Stmt>),
    /// `x[i in s] = e;` or `x[i] = e;`, an indexed definition, one piece of a piecewise one.
    IndexedDef(IndexedDef),
    /// `while c;`, the guard tested before each step.
    While(Expr),
    /// `until c;`, the guard tested after each step.
    Until(Expr),
    /// `e;`, an expression statement, which may write a generation, as `c*.tick();` does.
    Expr(Expr),
    /// `return e;` or `return a, b;`, the block's export; a trailing expression is `return e;`.
    Return(Vec<Expr>),
    /// A function declaration.
    Function(Function),
    /// `p <- e;`, the whole value `e` pushed to the port `p`.
    Push {
        /// The port.
        port: String,
        /// The value.
        value: Expr,
    },
    /// A struct declaration.
    Struct(Struct),
    /// A type declaration.
    Type(TypeDecl),
    /// A method declaration.
    Method(Method),
    /// An import of a unit.
    Import(Import),
    /// A declaration and the annotations written before it, in written order.
    Annotated {
        /// The annotations.
        annots: Vec<Annot>,
        /// The declaration.
        decl: Box<Stmt>,
    },
    /// `@log(#off);`: an annotation of the enclosing unit, an item of its own.
    UnitAnnot(Annot),
}

/// `import geometry.shapes;`, `import geometry.shapes as gs;` or
/// `import geometry.shapes.{Circle, area};`, each with an optional pin `@hash("…")`.
#[derive(Debug)]
pub struct Import {
    /// The unit's path, joined by `.`.
    pub path: String,
    /// What it binds.
    pub kind: ImportKind,
    /// The content address it is pinned to, if written.
    pub pin: Option<ContentAddress>,
}

/// What an import binds.
#[derive(Debug)]
pub enum ImportKind {
    /// The unit, under the last name of its path.
    Qualified,
    /// The unit, under this name.
    Alias(String),
    /// These names of the unit, in written order.
    Selective(Vec<String>),
}

/// An annotation: `@log`, or `@cost(n)` with its arguments.
#[derive(Debug)]
pub struct Annot {
    /// Its name, without its `@`.
    pub name: String,
    /// Whether parentheses follow it, `@log()` rather than `@log`.
    pub called: bool,
    /// The positional arguments, in order.
    pub positional: Vec<Expr>,
    /// The named arguments, in written order; `x:` is `x: x`.
    pub named: Vec<(String, Expr)>,
    /// Its text.
    pub span: Span,
}

/// `struct Point { x: f64, y: f64 = 0.0, import geometry.Named }`.
#[derive(Debug)]
pub struct Struct {
    /// Its name.
    pub name: String,
    /// Its fields, in written order.
    pub fields: Vec<Field>,
}

/// A field of a struct.
#[derive(Debug)]
pub enum Field {
    /// `x: T`, or `x: T = e` with a default.
    Typed {
        /// Its name.
        name: String,
        /// Its type.
        ty: Type,
        /// Its default, if written.
        default: Option<Expr>,
        /// Its text.
        span: Span,
    },
    /// `import geometry.Named`: the fields of the struct or interface of that path.
    Import {
        /// The path, joined by `.`.
        path: String,
        /// Its text.
        span: Span,
    },
}

/// `type Shape = Circle | Square;` or `type Tree(T) = #leaf | #node(l: Tree(T), r: Tree(T));`:
/// a name for a type, which may name itself, with its type parameters.
#[derive(Debug)]
pub struct TypeDecl {
    /// Its name.
    pub name: String,
    /// Its type parameters, in written order.
    pub params: Vec<String>,
    /// The type it names.
    pub ty: Type,
}

/// A method `T.m(params) = e;`, the function `T.m` whose receiver `this: T` is its first,
/// positional parameter; or `T.m = e;` with no parentheses, a constant member of `T`.
#[derive(Debug)]
pub struct Method {
    /// The receiver's type, `T`.
    pub receiver: String,
    /// Whether its parameters are written in parentheses, `T.m()` rather than `T.m`.
    pub called: bool,
    /// The method: its name `m`, its written parameters, which do not include the receiver,
    /// and its body.
    pub function: Function,
}

/// A function: `f(params) = e;` or `f(params) { … }`, either followed by `test` tables.
#[derive(Debug)]
pub struct Function {
    /// Its name.
    pub name: String,
    /// Its parameters.
    pub params: Vec<Param>,
    /// For `main`, its header as written and its output ports; its `params` are then the
    /// fields of its argument the body reads. Boxed, so that a statement keeps its size.
    pub main: Option<Box<MainHeader>>,
    /// Whether its body is an equation `= e`; otherwise it is a block, which may export
    /// nothing, as a `main` that only pushes does.
    pub equation: bool,
    /// Its body.
    pub body: Expr,
    /// The cases of its `test` tables, `input -> expected`, in written order.
    pub tests: Vec<(Expr, Expr)>,
}

/// The header of `main` as written, `main(m: MainArgs) -> int` (DESIGN.md sec:ports).
#[derive(Debug)]
pub struct MainHeader {
    /// Its parameter, `m: MainArgs`, if written: its name, its text and its type if written.
    pub param: Option<(String, Span, Option<Type>)>,
    /// Its result type, `int`, if written.
    pub result: Option<Type>,
    /// Its output ports: the fields of its argument the body pushes to, `m.stdout` and
    /// `m.stderr`, which the builder makes from the body.
    pub ports: Vec<Port>,
}

impl Function {
    /// The output ports of `main` ([`MainHeader::ports`]), or `None` for any other function.
    pub fn ports(&self) -> Option<&[Port]> {
        self.main.as_ref().map(|h| &h.ports[..])
    }
}

/// An output port of `main`, a field of `MainArgs` its body pushes to: `m.stdout`, of type
/// `Lines`.
#[derive(Debug)]
pub struct Port {
    /// Its name.
    pub name: String,
    /// Its type.
    pub ty: Type,
    /// Its text.
    pub span: Span,
}

/// An indexed definition `x[i in s][j] = e with x[-1] = 0;`.
#[derive(Debug)]
pub struct IndexedDef {
    /// The family defined.
    pub name: String,
    /// Its keys, outermost first.
    pub keys: Vec<IndexKey>,
    /// The value at those keys.
    pub value: Expr,
    /// The boundary values, in written order; empty when there is no `with`.
    pub boundary: Vec<BoundaryItem>,
}

/// A key of an indexed definition or a boundary value.
#[derive(Debug)]
pub enum IndexKey {
    /// `i in s`: the name `i` bound over the domain `s`.
    In {
        /// The name bound.
        name: String,
        /// The domain.
        set: Expr,
    },
    /// `e`: the key `e`.
    At(Expr),
}

/// `initial x = e;`, `initial x: T = e;`, `initial a, b = e;`, `initial x[k] = e;` or
/// `initial x[i in r] = e;`.
#[derive(Debug)]
pub struct Initial {
    /// The names, in order, each with its text: one but for `initial a, b = e;`.
    pub names: Vec<(String, Span)>,
    /// The declared type of `initial x: T = e;`.
    pub ty: Option<Type>,
    /// The keys of a boundary entry, outermost first; none for a start value.
    pub keys: Vec<IndexKey>,
    /// The value.
    pub value: Expr,
}

/// A boundary entry of an indexed definition's `with` clause, `with d[-1] = e`.
#[derive(Debug)]
pub struct BoundaryItem {
    /// The family.
    pub name: String,
    /// Its keys, outermost first; never none, which the grammar requires.
    pub keys: Vec<IndexKey>,
    /// The value.
    pub value: Expr,
    /// Its text.
    pub span: Span,
}

/// A binding target.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Target {
    /// A name bound, and the name's text.
    Name(String, Span),
    /// `_`, the component discarded.
    Wild,
}

impl StmtKind {
    /// Where the statement stands among those of its block, which the builder and the
    /// formatter both order by it, keeping the written order among equals: a `while` guard,
    /// tested before a step, first; an `until` guard, tested after it, last but for the
    /// export (DESIGN.md sec:generations). Order has no meaning, so this is only where the
    /// text shows the timing the keyword fixes.
    pub fn place(&self) -> u8 {
        match self {
            StmtKind::While(_) => 0,
            StmtKind::Bind { .. }
            | StmtKind::Initial(_)
            | StmtKind::Mutable(_)
            | StmtKind::Local(_)
            | StmtKind::IndexedDef(_)
            | StmtKind::Push { .. }
            | StmtKind::Expr(_)
            | StmtKind::Function(_)
            | StmtKind::Method(_)
            | StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Import(_)
            | StmtKind::Annotated { .. }
            | StmtKind::UnitAnnot(_) => 1,
            StmtKind::Until(_) => 2,
            StmtKind::Return(_) => 3,
        }
    }
}

/// A type expression and its span.
pub struct Type {
    /// What it is.
    pub kind: TypeKind,
    /// Its text.
    pub span: Span,
}

/// The kinds of type expression.
#[derive(Debug)]
pub enum TypeKind {
    /// A type name, its unit path included (`geometry.Point`).
    Name(String),
    /// An atom, without its `#`.
    Atom(String),
    /// Every member of one kind: `#_` every atom, `(..)` every tuple, `{..}` every struct.
    Every(Every),
    /// An atom with any payload, `#a(..)`: the atom, without its `#`.
    AtomAny(String),
    /// A tuple type `(A, B)`.
    Tuple(Vec<Type>),
    /// A union `A | B | …`.
    Union(Vec<Type>),
    /// An intersection `A & B & …`.
    And(Vec<Type>),
    /// A difference `A \ B`.
    Diff(Box<Type>, Box<Type>),
    /// A function type: one parameter per level, right-associative.
    Arrow {
        /// The parameters.
        params: Vec<TypeParam>,
        /// Whether it is `->?`, a partial map.
        partial: bool,
        /// The result.
        result: Box<Type>,
    },
    /// A morphism type with its two domain bounds, `L .. U -> V`.
    Bounded {
        /// The guarantee `L`, the keys certainly present.
        lower: Box<Type>,
        /// The permission `U`, the keys possibly present.
        upper: Box<Type>,
        /// The value type `V`.
        result: Box<Type>,
    },
    /// A type applied to arguments, `Tree(T)` or `geometry.Grid(int)`: its name, its unit path
    /// included, and the arguments.
    Apply(String, Vec<TypeParam>),
    /// An atom with a payload type, `#node(left: Tree, right: Tree)` or `#pair(int, int)`:
    /// the atom, without its `#`, and the payload's components.
    AtomApply(String, Vec<TypeParam>),
    /// A record type `{x: int, y: f64}`, its fields in written order.
    Record(Vec<(String, Type)>),
    /// The family type `[T]`, the array type `int[0..<_] -> T`: a `T` at each rank of a
    /// domain `0..<n` the type leaves open (sec:grammar, `RankArrayType`). It is not `Seq(T)`
    /// (sec:order), whose keys are origins.
    Array(Box<Type>),
    /// A type with its type variables bounded, `(x: T) -> T for T in int | f64`: each variable
    /// ranges over the carriers of its bound, one carrier at every place it stands.
    For {
        /// The type the variables stand in.
        ty: Box<Type>,
        /// The variables, in written order.
        bounds: Vec<TypeBound>,
    },
}

impl Type {
    /// The operands of the intersection of `ts`, with each intersection in parentheses among
    /// them replaced by its own operands, in written order: `(A & B) & C` has `A`, `B` and `C`.
    /// The walk keeps its own stack, as parentheses nest as deep as the text.
    // Complexity tradeoff (COMPLEXITY.md row F82): naive version, each nested intersection
    // joined again at each depth by copying the inner signature, O(n^2) bytes for n levels
    // (31 times the bytes at 8n against n), on the thread's stack. Used: the operands gathered
    // once on a heap stack, O(n) time and heap. Tradeoff: one `Vec` of references; none given up.
    pub fn and_operands(ts: &[Type]) -> Vec<&Type> {
        let mut out = Vec::with_capacity(ts.len());
        let mut stack: Vec<&Type> = ts.iter().rev().collect();
        while let Some(t) = stack.pop() {
            match &t.kind {
                TypeKind::And(ts) => stack.extend(ts.iter().rev()),
                _ => out.push(t),
            }
        }
        out
    }

    /// Its parameter list if it is a function type, a bounds clause around one included: `x`
    /// for a parameter named and not `positional`, and `_` for the others, which a call does
    /// not name; and the clauses around it.
    fn param_list(&self) -> Option<(Vec<&str>, Vec<&TypeBound>)> {
        let mut t = self;
        let mut bounds = Vec::new();
        while let TypeKind::For { ty, bounds: bs } = &t.kind {
            bounds.extend(bs);
            t = ty;
        }
        match &t.kind {
            TypeKind::Arrow { params, .. } => Some((
                params
                    .iter()
                    .map(|p| match &p.name {
                        Some(n) if !p.positional => n.as_str(),
                        _ => "_",
                    })
                    .collect(),
                bounds,
            )),
            TypeKind::Bounded { .. } => Some((vec!["_"], bounds)),
            _ => None,
        }
    }

    /// Of `ts`, the operands of an intersection as [`Type::and_operands`] gives them: whether
    /// they are all function types, and so one function's list of arrows, an overload
    /// (DESIGN.md sec:type_language, "Relation to semantic subtyping" (2)), or why they are no
    /// type. The arrows of one function share its parameter list and its bounds, so function
    /// types that take different parameter lists are no type, as are two that bound one
    /// variable by different carriers, and a bounds clause around an intersection that is
    /// itself an operand, since its variables would be bounded on part of the function.
    pub fn overload(ts: &[&Type]) -> Result<bool, String> {
        let mut lists = Vec::with_capacity(ts.len());
        let mut clause_around_and = false;
        for t in ts {
            match t.param_list() {
                Some(l) => lists.push(l),
                None if t.is_clause_around_and() => clause_around_and = true,
                None => return Ok(false),
            }
        }
        if clause_around_and {
            return Err(
                "a bounds clause stands around an intersection of function types that is \
                        part of another; write the clause once, after the whole intersection"
                    .to_string(),
            );
        }
        let Some(((list, _), _)) = lists.split_first() else {
            return Ok(false);
        };
        if let Some((other, _)) = lists.iter().find(|(l, _)| l != list) {
            return Err(format!(
                "the arrows of an intersection of function types share one parameter list, but \
                 one takes ({}) and another ({})",
                list.join(", "),
                other.join(", ")
            ));
        }
        let mut carriers: HashMap<&str, Vec<&str>> = HashMap::new();
        for b in lists.iter().flat_map(|(_, bs)| bs) {
            let these = b.carriers.carrier_names();
            match carriers.get(b.name.as_str()) {
                Some(first) if *first != these => {
                    return Err(format!(
                        "the type variable `{}` is bounded by {} on one arrow of an intersection \
                         of function types and by {} on another, but the arrows of one function \
                         share its bounds",
                        b.name,
                        first.join(" | "),
                        these.join(" | ")
                    ));
                }
                Some(_) => {}
                None => {
                    carriers.insert(b.name.as_str(), these);
                }
            }
        }
        Ok(true)
    }

    /// Whether it is a bounds clause around an intersection.
    fn is_clause_around_and(&self) -> bool {
        let mut t = self;
        while let TypeKind::For { ty, .. } = &t.kind {
            t = ty;
        }
        matches!(t.kind, TypeKind::And(_))
    }

    /// The carrier names of a bound, a union of them, sorted and each once, so two bounds
    /// written in different orders compare equal.
    fn carrier_names(&self) -> Vec<&str> {
        let mut out = Vec::new();
        let mut stack = vec![self];
        while let Some(t) = stack.pop() {
            match &t.kind {
                TypeKind::Union(ts) => stack.extend(ts),
                TypeKind::Name(n) => out.push(n.as_str()),
                // Resolve and the reader of printed types reject any other bound.
                _ => {}
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }
}

/// The kind a kind-wide type `#_`, `(..)` or `{..}` names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Every {
    /// Every atom, `#_`.
    Atom,
    /// Every tuple, `(..)`.
    Tuple,
    /// Every struct, `{..}`.
    Struct,
}

/// One variable of a bounds clause, `T in int | f64`.
#[derive(Debug)]
pub struct TypeBound {
    /// The variable.
    pub name: String,
    /// The variable's text.
    pub span: Span,
    /// The bound, a union of carriers.
    pub carriers: Type,
}

/// A parameter of a function type: `int`, `x: int` or `positional x: int`.
#[derive(Debug)]
pub struct TypeParam {
    /// Its name, which documents it, if written.
    pub name: Option<String>,
    /// Whether it is written `positional`.
    pub positional: bool,
    /// Its type.
    pub ty: Type,
}

/// A parameter of a lambda or a declaration.
#[derive(Debug)]
pub struct Param {
    /// Its name. A tuple-destructuring parameter `(a, b)` has none in the source; its name is
    /// its text, `(a, b)`, which no identifier spells, so it names the fresh parameter of the
    /// desugaring (`let a = p[0]`, `let b = p[1]` in the body) and meets no other name.
    pub name: String,
    /// The targets of a tuple-destructuring parameter `(a, b)`, in order; such a parameter is
    /// positional.
    pub tuple: Option<Vec<Target>>,
    /// Whether it is written `positional`.
    pub positional: bool,
    /// Its type, if written.
    pub ty: Option<Type>,
    /// Its default, if written.
    pub default: Option<Expr>,
    /// Its text.
    pub span: Span,
    /// The text of its name; for a tuple-destructuring parameter, its text.
    pub name_at: Span,
}

/// A pattern: an atom pattern, which `else` takes at L1, and from step L2.1 the patterns a
/// struct is destructured with, which a payload or a `match` arm holds.
pub enum Pattern {
    /// `Point(x:, y: b)`: a struct's fields matched by name; `x:` (no pattern) binds the field
    /// to the name `x`.
    Struct {
        /// The struct's name.
        name: String,
        /// The fields matched, in written order.
        fields: Vec<(String, Option<Pattern>)>,
        /// Its text.
        span: Span,
    },
    /// A name, bound to the value matched.
    Name(String, Span),
    /// `_`, matching any value and binding nothing.
    Wild(Span),
    /// `(p, q, …)`, a tuple's components matched by position.
    Tuple(Vec<Pattern>, Span),
    /// `#name`, `#name(f: p, g:)` or `#name(p, q)`.
    Atom {
        /// The atom, without its `#`.
        name: String,
        /// Fields matched by name; `g:` (no pattern) binds the field to the name `g`.
        fields: Vec<(String, Option<Pattern>)>,
        /// Payload components matched by position.
        items: Vec<Pattern>,
        /// Its text.
        span: Span,
    },
    /// `n is T`, the value matched when it is in the set of `T`, bound to `n` if written.
    Is {
        /// The name bound.
        name: Option<String>,
        /// The type.
        ty: Box<Type>,
        /// Its text.
        span: Span,
    },
    /// A literal, `-1`, `"a"` or `true`, matching the value equal to it.
    Lit(Box<Expr>),
    /// A range pattern `0..<10`, `1..=9` or `0..`, matching the values in the range; its ends
    /// are literal patterns.
    Range {
        /// The first value.
        from: Box<Pattern>,
        /// The end.
        to: RangeEnd<Box<Pattern>>,
        /// Its text.
        span: Span,
    },
}

impl Pattern {
    /// Its text.
    pub fn span(&self) -> Span {
        match self {
            Pattern::Struct { span, .. }
            | Pattern::Atom { span, .. }
            | Pattern::Is { span, .. }
            | Pattern::Range { span, .. } => *span,
            Pattern::Lit(e) => e.span,
            Pattern::Name(_, span) | Pattern::Wild(span) | Pattern::Tuple(_, span) => *span,
        }
    }
}

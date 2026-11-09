//! The pretty-printer of kernel terms (step L1.15), in the notation of DESIGN.md sec:kernel:
//! `fam(D, i -> e)`, `reindex(F, kf, vf)`, `fold(F, op, ev)` and the rest, with Tier 0 written
//! as Zed writes it (`(x, y) -> e`, `f(a)`, `x = e; body`, `if c { a } else { b }`).
//!
//! [`Term`]'s `Display` writes a term on one line. [`pretty`] writes the same text, broken
//! into lines of at most a given width where it can: a term that does not fit puts each of
//! its parts on its own line, indented two spaces, so the only difference from the one-line
//! form is whitespace. Binary primitives are written infix and always parenthesized. Negation,
//! `!`, an index and an atom are written as a program writes them (`-x`, `!x`, `t[0]`, `f[k]`,
//! `#err(code: 3)`), their operands parenthesized wherever sec:grammar would read the text
//! otherwise, so the text reads back as the same term.
//!
//! A term is laid out as a sequence of tokens, not a tree, and each pass over it (laying out,
//! writing, measuring, breaking) is a loop with a stack of its own, so that a term of any depth
//! prints on a small call stack (step T2-types-rest).
//!
//! [`written`] writes a term as the program it came from wrote it, as far as the term shows:
//! each name through a function the caller gives, which maps a name elaboration made back to
//! the one the program wrote, and the `if` forms that elaboration gives `&&` and `||` as those
//! operators, for a message about the term (sec:diagnostics).

use std::borrow::Cow;
use std::fmt;

use crate::term::{Evidence, FixKind, Grade, GuardPos, Pattern, Prim, Term, Witness};
use crate::value::Value;

/// How a name is written: as it is (`None`), or through the function a message gives
/// ([`written`]).
type Names = Option<fn(&str) -> &str>;

/// `t` broken into lines of at most `width` columns where its parts allow.
pub fn pretty(t: &Term, width: usize) -> String {
    let mut out = String::new();
    Doc::of(Piece::Term(t), None).render(width, &mut out);
    out
}

/// `t` on one line as the program wrote it, for a message: each name a variable, a binder or
/// a call's head writes is `name` of it, and `if c { b } else { false }` and
/// `if c { true } else { b }`, the terms elaboration gives `c && b` and `c || b`, are written
/// `(c && b)` and `(c || b)`, parenthesized as every binary operator is. A program that wrote
/// the `if` itself reads the operator, which means the same. Otherwise the text is that of
/// `Display`, and costs the same: linear in the text.
pub fn written(t: &Term, name: fn(&str) -> &str) -> String {
    let mut out = String::new();
    Doc::of(Piece::Term(t), Some(name))
        .write_flat(&mut out)
        .expect("writing to a string does not fail");
    out
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Doc::of(Piece::Term(self), None).write_flat(f)
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Doc::of(Piece::Pattern(self), None).write_flat(f)
    }
}

/// How a binary primitive is written between its operands, with its spaces.
fn infix(p: Prim) -> Option<&'static str> {
    use Prim::*;
    Some(match p {
        Add => " + ",
        Sub => " - ",
        Mul => " * ",
        Div => " / ",
        IntDiv => " div ",
        Mod => " mod ",
        Eq => " == ",
        Ne => " != ",
        Lt => " < ",
        Le => " <= ",
        Gt => " > ",
        Ge => " >= ",
        And => " && ",
        Or => " || ",
        Concat => " ++ ",
        Pow => "^",
        _ => return None,
    })
}

/// The name of a primitive written as a function, `get(f, k)`.
fn name(p: Prim) -> &'static str {
    use Prim::*;
    match p {
        Neg => "neg",
        Not => "not",
        Min => "min",
        Max => "max",
        Get => "get",
        Count => "count",
        Union => "union",
        Path => "path",
        PathKey => "pathKey",
        PathLen => "pathLen",
        Tuple => "tuple",
        TupleGet => "tupleGet",
        Atom => "atom",
        Show => "String",
        CastInt => "int",
        CastRat => "rat",
        CastF64 => "f64",
        Abs => "abs",
        Len => "len",
        Lower => "lower",
        Upper => "upper",
        Trim => "trim",
        Sum => "sum",
        BitAnd => "bitAnd",
        BitOr => "bitOr",
        BitXor => "bitXor",
        BitNot => "bitNot",
        Shl => "shl",
        Shr => "shr",
        PopCount => "popCount",
        LeadingZeros => "leadingZeros",
        TrailingZeros => "trailingZeros",
        Rotl => "rotl",
        Rotr => "rotr",
        F64Bits => "f64Bits",
        CodePoint => "codePoint",
        Scalar => "scalar",
        Utf8 => "utf8",
        FromUtf8 => "fromUtf8",
        MulHi => "mulHi",
        BitReverse => "bitReverse",
        ByteSwap => "byteSwap",
        Pdep => "pdep",
        Pext => "pext",
        FunnelShl => "funnelShl",
        FunnelShr => "funnelShr",
        _ => infix(p)
            .expect("every primitive has a name or an infix spelling")
            .trim(),
    }
}

impl Prim {
    /// How a message names the primitive: as a program writes it, the operator (`>`, `++`,
    /// `-` for both `Sub` and `Neg`, `!` for `Not`), the prelude word (`popCount`,
    /// `String`), or the form DESIGN.md gives one with no word of its own: a tuple `(..)`, a
    /// component `[i]` (`p[0]`), an entry `[k]` (`f[k]`), and the methods `.count` and
    /// `.union`. An atom is `#_(..)`, an atom of any name with any payload, since a fixed text
    /// cannot carry its name; a message that has the name writes `#err(..)` instead
    /// ([`Prim::written_with`]). `path`, `pathKey` and `pathLen` keep the kernel's words, for
    /// which DESIGN.md gives no written form.
    pub fn written(self) -> &'static str {
        match self {
            Prim::Neg => "-",
            Prim::Not => "!",
            Prim::Tuple => "(..)",
            Prim::TupleGet => "[i]",
            Prim::Get => "[k]",
            Prim::Count => ".count",
            Prim::Union => ".union",
            Prim::Atom => "#_(..)",
            p => name(p),
        }
    }

    /// As [`Prim::written`], with the primitive's first argument where a message has it: an
    /// atom whose first argument is its name, the string `"err"`, is `#err(..)`.
    pub fn written_with(self, first: Option<&Value>) -> Cow<'static, str> {
        match (self, first) {
            (Prim::Atom, Some(Value::Str(name))) => Cow::Owned(format!("#{name}(..)")),
            _ => Cow::Borrowed(self.written()),
        }
    }

    /// The name the printer writes the primitive by in function form (`neg`, `get`, `+`),
    /// a different one for each primitive, so the ZIR text form reads it back.
    pub fn printed(self) -> &'static str {
        name(self)
    }
}

/// A field name stored as a string value, written bare.
fn field(v: &Value) -> String {
    match v {
        Value::Str(s) => s.to_string(),
        other => other.to_string(),
    }
}

fn grade(g: Grade) -> &'static str {
    match g {
        Grade::Axiom => "axiom",
        Grade::CheckedExhaustive => "checkedExhaustive",
        Grade::Proved => "proved",
        Grade::Bounded => "bounded",
        Grade::Obligated => "obligated",
        Grade::Assumed => "assumed",
    }
}

/// A term laid out: a sequence of tokens, in which a group is written on one line when it fits
/// and its parts on lines of their own when it does not.
struct Doc<'a> {
    toks: Vec<Tok<'a>>,
    /// For a `Start`, the index of its `End`; for a `Sep` or an `End`, that of its `Start`.
    link: Vec<usize>,
}

enum Tok<'a> {
    Text(Cow<'a, str>),
    /// The start of a group, whose parts are the tokens and groups up to its `End`.
    Start(Group<'a>),
    /// Between two items of a `List`.
    Sep,
    End,
}

enum Group<'a> {
    /// Always written on one line, as the head of a call.
    Flat,
    /// Its parts one after another, on the line where they start.
    Cat,
    /// As `Cat`, but when it does not fit every list among its parts breaks, so the two
    /// branches of an `if` break alike.
    Together,
    /// `open`, the items separated by `sep`, `close`, each item one part. Broken, each item
    /// goes on its own line indented two spaces, `sep` with its trailing spaces removed ending
    /// all but the last.
    List {
        open: Cow<'a, str>,
        sep: &'static str,
        close: &'static str,
    },
}

/// What is left to lay out: a token, or a term, an operand or a pattern to lay out.
enum Piece<'a> {
    Tok(Tok<'a>),
    Term(&'a Term),
    /// A term as the operand of a prefix `-` or `!` or the receiver of `[k]`: parenthesized
    /// unless it is written as a primary or a postfix expression (sec:grammar, Prefix and
    /// Postfix).
    Operand(&'a Term),
    Pattern(&'a Pattern),
}

/// The pieces one term or pattern is laid out as, in order, and how names are written.
struct Pieces<'a>(Vec<Piece<'a>>, Names);

impl<'a> Pieces<'a> {
    /// How the name `x` is written.
    fn name(&self, x: &'a str) -> &'a str {
        self.1.map_or(x, |f| f(x))
    }

    fn text(&mut self, s: impl Into<Cow<'a, str>>) -> &mut Self {
        self.0.push(Piece::Tok(Tok::Text(s.into())));
        self
    }

    fn term(&mut self, t: &'a Term) -> &mut Self {
        self.0.push(Piece::Term(t));
        self
    }

    fn operand(&mut self, t: &'a Term) -> &mut Self {
        self.0.push(Piece::Operand(t));
        self
    }

    fn pattern(&mut self, p: &'a Pattern) -> &mut Self {
        self.0.push(Piece::Pattern(p));
        self
    }

    fn start(&mut self, g: Group<'a>) -> &mut Self {
        self.0.push(Piece::Tok(Tok::Start(g)));
        self
    }

    fn cat(&mut self) -> &mut Self {
        self.start(Group::Cat)
    }

    fn list(
        &mut self,
        open: impl Into<Cow<'a, str>>,
        sep: &'static str,
        close: &'static str,
    ) -> &mut Self {
        self.start(Group::List {
            open: open.into(),
            sep,
            close,
        })
    }

    /// `head(`, the start of a call's list of arguments.
    fn call(&mut self, head: &str) -> &mut Self {
        self.list(format!("{head}("), ", ", ")")
    }

    fn sep(&mut self) -> &mut Self {
        self.0.push(Piece::Tok(Tok::Sep));
        self
    }

    fn end(&mut self) -> &mut Self {
        self.0.push(Piece::Tok(Tok::End));
        self
    }

    /// The terms as the items of a list.
    fn items(&mut self, ts: &'a [Term]) -> &mut Self {
        for (i, t) in ts.iter().enumerate() {
            if i > 0 {
                self.sep();
            }
            self.term(t);
        }
        self
    }

    /// `key: `, before the value of a named part of a generator such as `depth: 2`.
    fn named(&mut self, key: &str) -> &mut Self {
        self.cat().text(format!("{key}: "))
    }

    /// `(x, y) -> body`, or `x -> body` for one parameter.
    fn lambda(&mut self, params: &[&str], body: &'a Term) -> &mut Self {
        let head = match params {
            [p] => format!("{p} -> "),
            _ => format!("({}) -> ", params.join(", ")),
        };
        self.cat().text(head).term(body).end()
    }

    fn evidence(&mut self, ev: &Evidence) -> &mut Self {
        self.named("ev").list("{", ", ", "}");
        for (i, (p, g)) in ev.iter().enumerate() {
            if i > 0 {
                self.sep();
            }
            self.text(format!("{p}: {}", grade(*g)));
        }
        self.end().end()
    }

    /// `{ e }`, an `if` branch in its braces.
    fn block(&mut self, t: &'a Term) -> &mut Self {
        self.list("{", " ", "}").term(t).end()
    }

    fn lay_out(&mut self, t: &'a Term) {
        match t {
            Term::Lit(v) => {
                self.text(v.to_string());
            }
            Term::Var(x) => {
                let x = self.name(x);
                self.text(x);
            }
            Term::Lam(params, body) => {
                let ps: Vec<&str> = params.iter().map(|p| self.name(p)).collect();
                self.lambda(&ps, body);
            }
            Term::App(f, args) => match &**f {
                Term::Var(x) => {
                    let x = self.name(x);
                    self.call(x).items(args).end();
                }
                Term::PrimFn(p) => {
                    self.call(&prim_fn(*p)).items(args).end();
                }
                // The head is written on one line, as the list after it starts where it ends.
                _ => {
                    self.cat()
                        .start(Group::Flat)
                        .cat()
                        .text("(")
                        .term(f)
                        .text(")")
                        .end()
                        .end();
                    self.call("").items(args).end().end();
                }
            },
            Term::Prim(Prim::Tuple, items) if items.len() == 1 => {
                self.cat().text("(").term(&items[0]).text(",)").end();
            }
            Term::Prim(Prim::Tuple, items) => {
                self.list("(", ", ", ")").items(items).end();
            }
            // An atom is written as Zed writes it: `#err(1)`, `#err(code: 3)`. Elaboration gives
            // the name and the field names as literals; a term that gives them any other way has
            // no written form, so its name is written `#_` and its payload positionally.
            Term::Prim(Prim::Atom, args) if !args.is_empty() => {
                let open = match &args[0] {
                    Term::Lit(Value::Str(name)) => format!("#{name}("),
                    _ => "#_(".into(),
                };
                let rest = args.get(2..).unwrap_or_default();
                let fs: &[Value] = match args.get(1) {
                    Some(Term::Lit(Value::Tuple(fs))) if fs.len() == rest.len() => fs,
                    _ => &[],
                };
                self.list(open, ", ", ")");
                for (i, a) in rest.iter().enumerate() {
                    if i > 0 {
                        self.sep();
                    }
                    match fs.get(i) {
                        Some(f) => self.cat().text(format!("{}: ", field(f))).term(a).end(),
                        None => self.term(a),
                    };
                }
                self.end();
            }
            // `-x` and `!x`: the operator before its operand (sec:grammar, Prefix).
            Term::Prim(p @ (Prim::Neg | Prim::Not), args) if args.len() == 1 => {
                self.cat().text(p.written()).operand(&args[0]).end();
            }
            // `t[0]` and `f[k]`: the key in brackets after its receiver (sec:grammar, IndexSuffix).
            // A chain `t[0][1]` is one `Cat` of its receiver and its indices, gathered by a loop, so
            // that `fits` meets the receiver's text first rather than after walking down the
            // chain, which made a broken layout quadratic in the chain's length.
            Term::Prim(Prim::TupleGet | Prim::Get, args) if args.len() == 2 => {
                let mut keys = vec![&args[1]];
                let mut receiver = &args[0];
                while let Term::Prim(Prim::TupleGet | Prim::Get, inner) = receiver
                    && inner.len() == 2
                {
                    keys.push(&inner[1]);
                    receiver = &inner[0];
                }
                self.cat().operand(receiver);
                for k in keys.into_iter().rev() {
                    self.list("[", ", ", "]").term(k).end();
                }
                self.end();
            }
            Term::Prim(p, args) => match (infix(*p), &args[..]) {
                // The left operand of `^` is a postfix expression (sec:grammar, Power), so
                // `-x^2` would read as `-(x^2)`.
                (Some(sep), [a, b]) => {
                    self.list("(", sep, ")");
                    if *p == Prim::Pow {
                        self.operand(a)
                    } else {
                        self.term(a)
                    };
                    self.sep().term(b).end();
                }
                _ => {
                    self.call(name(*p)).items(args).end();
                }
            },
            Term::PrimFn(p) => {
                self.text(prim_fn(*p));
            }
            Term::Let(..) => {
                self.list("{", " ", "}");
                let mut t = t;
                while let Term::Let(x, e, body) = t {
                    let x = self.name(x);
                    self.cat()
                        .text(format!("{x} = "))
                        .term(e)
                        .text(";")
                        .end()
                        .sep();
                    t = body;
                }
                self.term(t).end();
            }
            // `c && b` and `c || b` as elaboration gives them, written as the operators when
            // the text is for a message ([`written`]).
            Term::If(c, a, b)
                if self.1.is_some()
                    && (matches!(**b, Term::Lit(Value::Bool(false)))
                        || matches!(**a, Term::Lit(Value::Bool(true)))) =>
            {
                let (sep, rhs) = match **b {
                    Term::Lit(Value::Bool(false)) => (" && ", a),
                    _ => (" || ", b),
                };
                self.list("(", sep, ")").term(c).sep().term(rhs).end();
            }
            Term::If(c, a, b) => {
                self.cat()
                    .text("if ")
                    .term(c)
                    .text(" ")
                    .start(Group::Together);
                self.block(a).text(" else ").block(b).end().end();
            }
            Term::Match(e, arms) => {
                self.cat()
                    .text("match ")
                    .term(e)
                    .text(" ")
                    .list("{", ", ", "}");
                for (i, (p, t)) in arms.iter().enumerate() {
                    if i > 0 {
                        self.sep();
                    }
                    self.cat().pattern(p).text(" -> ").term(t).end();
                }
                self.end().end();
            }
            Term::Fam { domain, var, body } => {
                let var = self.name(var);
                self.call("fam")
                    .term(domain)
                    .sep()
                    .lambda(&[var], body)
                    .end();
            }
            Term::Reindex {
                family,
                kf,
                vf,
                witness,
            } => {
                let w = match witness {
                    Witness::Residue => "residue".to_string(),
                    Witness::Catalog(name) => format!("catalog({name:?})"),
                };
                self.call("reindex")
                    .term(family)
                    .sep()
                    .term(kf)
                    .sep()
                    .term(vf)
                    .sep();
                self.named("witness").text(w).end().end();
            }
            Term::Discard { family, sel } => {
                self.call("discard").term(family).sep().term(sel).end();
            }
            Term::Fold {
                family,
                op,
                identity,
                depth,
                ev,
            } => {
                self.call("fold").term(family).sep().term(op).sep();
                if let Some(i) = identity {
                    self.named("identity").term(i).end().sep();
                }
                self.named("depth").text(depth.to_string()).end().sep();
                self.evidence(ev).end();
            }
            Term::Fix {
                init,
                step,
                this,
                key,
                kind,
                ev,
            } => {
                self.call("fix").term(init).sep();
                match kind {
                    FixKind::Lattice { join } => {
                        self.term(step).sep().named("join").term(join).end();
                    }
                    FixKind::Definedness => {
                        let names = [self.name(this), self.name(key)];
                        self.lambda(&names, step).sep().text("definedness");
                    }
                }
                self.sep().evidence(ev).end();
            }
            Term::Gen {
                init,
                step,
                guard,
                pos,
            } => {
                let pos = match pos {
                    GuardPos::Before => "before",
                    GuardPos::After => "after",
                };
                self.call("gen")
                    .term(init)
                    .sep()
                    .term(step)
                    .sep()
                    .term(guard)
                    .sep();
                self.named("guard").text(pos).end().end();
            }
            Term::Read(port) => {
                self.call("port.read").text(&**port).end();
            }
            Term::Push(port, v) => {
                self.call("port.push").text(&**port).sep().term(v).end();
            }
        }
    }

    /// The pattern as text, which never breaks.
    fn pattern_out(&mut self, pat: &'a Pattern) {
        match pat {
            Pattern::Wild => self.text("_"),
            Pattern::Bind(x) => self.text(self.name(x)),
            Pattern::Lit(v) => self.text(v.to_string()),
            Pattern::Atom(name, ps) if ps.is_empty() => self.text(format!("#{name}")),
            Pattern::Atom(name, ps) => self
                .text(format!("#{name}("))
                .patterns(ps.iter().map(|p| (None, p)))
                .text(")"),
            Pattern::Fields(name, fs) => self
                .text(format!("#{name}("))
                .patterns(fs.iter().map(|(k, p)| (Some(&**k), p)))
                .text(")"),
            Pattern::Tuple(ps) if ps.len() == 1 => self.text("(").pattern(&ps[0]).text(",)"),
            Pattern::Tuple(ps) => self
                .text("(")
                .patterns(ps.iter().map(|p| (None, p)))
                .text(")"),
            Pattern::AnyAtom => self.text("#_"),
            // The type as a program writes it after `is`: only an arrow is parenthesized.
            Pattern::Is(t) => self.text(format!("(is {})", t.surface_after_is())),
        };
    }

    /// The patterns, each after its field name if it has one, separated by commas.
    fn patterns(&mut self, ps: impl Iterator<Item = (Option<&'a str>, &'a Pattern)>) -> &mut Self {
        for (i, (key, p)) in ps.enumerate() {
            if i > 0 {
                self.text(", ");
            }
            if let Some(k) = key {
                self.text(format!("{k}: "));
            }
            self.pattern(p);
        }
        self
    }
}

/// The text of a primitive written as a function, a call's head or an argument. A primitive with
/// no operator function of its own is written as the lambda a program writes for it (DESIGN.md
/// writes `neg: (a -> -a)`), parenthesized as `(+)` is, so that a call or an operator after it
/// is not read as part of its body.
fn prim_fn(p: Prim) -> Cow<'static, str> {
    match p {
        Prim::Neg | Prim::Not => format!("(x -> {}x)", p.written()).into(),
        Prim::TupleGet => "((t, i) -> t[i])".into(),
        Prim::Get => "((f, k) -> f[k])".into(),
        _ => match infix(p) {
            Some(op) => format!("({})", op.trim()).into(),
            None => name(p).into(),
        },
    }
}

/// Whether the printer writes `t` as a primary or a postfix expression: a name, a call, a
/// parenthesized or bracketed form, or a literal with no sign or slash in its text. A prefix
/// operation, a lambda, a block, an `if`, a `match` and the other literals are not; nor is
/// `-x` a primary, as `-x[0]` reads as `-(x[0])`.
fn primary(t: &Term) -> bool {
    match t {
        Term::Lit(v) => match v {
            Value::Int(n) => *n >= 0,
            Value::Bool(_) | Value::Str(_) | Value::Atom(_) | Value::Tuple(_) => true,
            Value::Big(_) | Value::Rat(_) | Value::Float(_) | Value::Path(_) | Value::Family(_) => {
                false
            }
        },
        Term::Prim(Prim::Neg | Prim::Not, args) => args.len() != 1,
        Term::Lam(..) | Term::Let(..) | Term::If(..) | Term::Match(..) => false,
        Term::Var(_)
        | Term::App(..)
        | Term::Prim(..)
        | Term::PrimFn(_)
        | Term::Fam { .. }
        | Term::Reindex { .. }
        | Term::Discard { .. }
        | Term::Fold { .. }
        | Term::Fix { .. }
        | Term::Gen { .. }
        | Term::Read(_)
        | Term::Push(..) => true,
    }
}

/// What is left of a group being broken: a `Cat` or `Together` whose parts from `at` are still to
/// write, or a `List` whose items are.
enum Frame {
    Parts {
        at: usize,
        ind: usize,
        together: bool,
    },
    Items {
        at: usize,
        ind: usize,
    },
}

impl<'a> Doc<'a> {
    /// The doc of what `root` lays out, one group. Each term and pattern is laid out once, its
    /// pieces taken from a stack.
    fn of(root: Piece<'a>, names: Names) -> Doc<'a> {
        let mut toks = Vec::new();
        let mut todo = vec![
            Piece::Tok(Tok::End),
            root,
            Piece::Tok(Tok::Start(Group::Cat)),
        ];
        let mut out = Pieces(Vec::new(), names);
        while let Some(piece) = todo.pop() {
            match piece {
                Piece::Tok(t) => {
                    toks.push(t);
                    continue;
                }
                Piece::Term(t) => out.lay_out(t),
                Piece::Operand(t) if primary(t) => out.lay_out(t),
                Piece::Operand(t) => {
                    out.cat().text("(").term(t).text(")").end();
                }
                Piece::Pattern(p) => out.pattern_out(p),
            }
            todo.extend(out.0.drain(..).rev());
        }
        let mut link: Vec<usize> = (0..toks.len()).collect();
        let mut open = Vec::new();
        for (i, t) in toks.iter().enumerate() {
            match t {
                Tok::Start(_) => open.push(i),
                Tok::Sep => link[i] = *open.last().expect("a separator inside a list"),
                Tok::End => {
                    let s = open.pop().expect("each end after its start");
                    link[i] = s;
                    link[s] = i;
                }
                Tok::Text(_) => {}
            }
        }
        Doc { toks, link }
    }

    /// The index after the token or group starting at `i`.
    fn next(&self, i: usize) -> usize {
        match self.toks[i] {
            Tok::Start(_) => self.link[i] + 1,
            _ => i + 1,
        }
    }

    /// The list a `Sep` or `End` at `i` is in, if it is in one.
    fn list_of(&self, i: usize) -> Option<(&'static str, &'static str)> {
        match &self.toks[self.link[i]] {
            Tok::Start(Group::List { sep, close, .. }) => Some((sep, close)),
            _ => None,
        }
    }

    /// The space inside the braces of a nonempty `{ … }` written on one line, the list starting
    /// at `s`.
    fn pad(&self, s: usize, close: &str) -> &'static str {
        if close == "}" && self.link[s] > s + 1 {
            " "
        } else {
            ""
        }
    }

    /// Gives `f` the pieces of the one-line text of the token or group at `i`, in order, until
    /// it returns `false`; returns whether every piece was given.
    fn flat(&self, i: usize, mut f: impl FnMut(&str) -> bool) -> bool {
        (i..self.next(i)).all(|k| match &self.toks[k] {
            Tok::Text(s) => f(s),
            Tok::Start(Group::List { open, close, .. }) => f(open) && f(self.pad(k, close)),
            Tok::Start(_) => true,
            Tok::Sep => f(self.list_of(k).expect("a separator inside a list").0),
            Tok::End => match self.list_of(k) {
                Some((_, close)) => f(self.pad(self.link[k], close)) && f(close),
                None => true,
            },
        })
    }

    /// Writes the one-line text.
    fn write_flat(&self, w: &mut impl fmt::Write) -> fmt::Result {
        let mut r = Ok(());
        self.flat(0, |s| {
            r = w.write_str(s);
            r.is_ok()
        });
        r
    }

    /// Whether the one-line text of the token or group at `i` fits in `room` columns. It stops
    /// once the room runs out, so it reads at most `room` columns of text.
    fn fits(&self, i: usize, mut room: usize) -> bool {
        self.flat(i, |s| match room.checked_sub(s.len()) {
            Some(r) => {
                room = r;
                true
            }
            None => false,
        })
    }

    /// Writes the doc in at most `width` columns where it can.
    fn render(&self, width: usize, out: &mut String) {
        let mut frames = Vec::new();
        let mut col = 0;
        self.enter(0, 0, width, &mut col, out, &mut frames);
        while let Some(frame) = frames.last_mut() {
            match frame {
                Frame::Parts { at, ind, together } => {
                    let (c, ind, together) = (*at, *ind, *together);
                    if let Tok::End = self.toks[c] {
                        frames.pop();
                        continue;
                    }
                    *at = self.next(c);
                    match &self.toks[c] {
                        Tok::Start(Group::List { open, .. }) if together => {
                            *out += open;
                            frames.push(Frame::Items { at: c + 1, ind });
                        }
                        _ => self.enter(c, ind, width, &mut col, out, &mut frames),
                    }
                }
                Frame::Items { at, ind } => {
                    let (c, ind) = (*at, *ind);
                    match &self.toks[c] {
                        Tok::End => {
                            let close = self.list_of(c).expect("items inside a list").1;
                            *out += "\n";
                            *out += &" ".repeat(ind);
                            *out += close;
                            col = ind + close.len();
                            frames.pop();
                        }
                        Tok::Sep => {
                            *at = c + 1;
                            *out += self
                                .list_of(c)
                                .expect("a separator inside a list")
                                .0
                                .trim_end();
                        }
                        _ => {
                            *at = self.next(c);
                            let inner = ind + 2;
                            *out += "\n";
                            *out += &" ".repeat(inner);
                            col = inner;
                            self.enter(c, inner, width, &mut col, out, &mut frames);
                        }
                    }
                }
            }
        }
    }

    /// Starts the token or group at `i`, at column `col` of a line indented `ind`: writes it
    /// on one line when it fits, and otherwise pushes what is left of it to write.
    fn enter(
        &self,
        i: usize,
        ind: usize,
        width: usize,
        col: &mut usize,
        out: &mut String,
        frames: &mut Vec<Frame>,
    ) {
        let flat = matches!(self.toks[i], Tok::Text(_) | Tok::Start(Group::Flat))
            || self.fits(i, width.saturating_sub(*col));
        if flat {
            self.flat(i, |s| {
                *out += s;
                *col += s.len();
                true
            });
            return;
        }
        match &self.toks[i] {
            Tok::Start(Group::Cat) => frames.push(Frame::Parts {
                at: i + 1,
                ind,
                together: false,
            }),
            Tok::Start(Group::Together) => frames.push(Frame::Parts {
                at: i + 1,
                ind,
                together: true,
            }),
            Tok::Start(Group::List { open, .. }) => {
                *out += open;
                frames.push(Frame::Items { at: i + 1, ind });
            }
            _ => unreachable!("a text, a flat group, a separator or an end is not entered broken"),
        }
    }
}

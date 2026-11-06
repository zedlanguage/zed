//! The pretty-printer of kernel terms (step L1.15), in the notation of DESIGN.md sec:kernel:
//! `fam(D, i -> e)`, `reindex(F, kf, vf)`, `fold(F, op, ev)` and the rest, with Tier 0 written
//! as Zed writes it (`(x, y) -> e`, `f(a)`, `x = e; body`, `if c { a } else { b }`).
//!
//! [`Term`]'s `Display` writes a term on one line. [`pretty`] writes the same text, broken
//! into lines of at most a given width where it can be: a term that does not fit puts each of
//! its parts on its own line, indented two spaces, so the only difference from the one-line
//! form is whitespace. Binary primitives are written infix and always parenthesized. Negation,
//! `!`, an index and an atom are written as a program writes them (`-x`, `!x`, `t[0]`, `f[k]`,
//! `#err(code: 3)`), their operands parenthesized wherever sec:grammar would read the text
//! otherwise, so the text reads back as the same term.

use std::borrow::Cow;
use std::fmt;

use crate::term::{Evidence, FixKind, Grade, GuardPos, Pattern, Prim, Term, Witness};
use crate::value::Value;

/// `t` broken into lines of at most `width` columns where its parts allow.
pub fn pretty(t: &Term, width: usize) -> String {
    let mut out = String::new();
    doc(t).render(0, 0, width, &mut out);
    out
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = String::new();
        doc(self).write_flat(&mut out);
        f.write_str(&out)
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pattern::Wild => f.write_str("_"),
            Pattern::Bind(x) => f.write_str(x),
            Pattern::Lit(v) => write!(f, "{v}"),
            Pattern::Atom(name, ps) if ps.is_empty() => write!(f, "#{name}"),
            Pattern::Atom(name, ps) => write!(f, "#{name}({})", list(ps)),
            Pattern::Fields(name, fs) => {
                let fs: Vec<String> = fs.iter().map(|(k, p)| format!("{k}: {p}")).collect();
                write!(f, "#{name}({})", fs.join(", "))
            }
            Pattern::Tuple(ps) if ps.len() == 1 => write!(f, "({},)", ps[0]),
            Pattern::Tuple(ps) => write!(f, "({})", list(ps)),
            Pattern::AnyAtom => f.write_str("#_"),
            Pattern::Is(t) => write!(f, "(is {t})"),
        }
    }
}

fn list<T: fmt::Display>(items: &[T]) -> String {
    let items: Vec<String> = items.iter().map(|i| i.to_string()).collect();
    items.join(", ")
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
        Pow => " ** ",
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
            (Prim::Atom, Some(Value::Str(name))) => Cow::Owned(format!("#{}(..)", name.flat())),
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

/// A term laid out: text, or parts that are written on one line when they fit and on lines
/// of their own when they do not.
enum Doc {
    Text(String),
    /// A doc always written on one line, as the head of a call.
    Flat(Box<Doc>),
    /// Docs written one after another, on the line where they start.
    Cat(Vec<Doc>),
    /// As `Cat`, but when it does not fit every list in it breaks, so the two branches of
    /// an `if` break alike.
    Together(Vec<Doc>),
    /// `open`, the items separated by `sep`, `close`. Broken, each item goes on its own line
    /// indented two spaces, `sep` with its trailing spaces removed ending all but the last.
    List {
        open: String,
        items: Vec<Doc>,
        sep: &'static str,
        close: &'static str,
    },
}

fn text(s: impl Into<String>) -> Doc {
    Doc::Text(s.into())
}

fn call(head: &str, items: Vec<Doc>) -> Doc {
    Doc::List {
        open: format!("{head}("),
        items,
        sep: ", ",
        close: ")",
    }
}

/// `key: value`, a named part of a generator such as `depth: 2`.
fn named(name: &str, value: Doc) -> Doc {
    Doc::Cat(vec![text(format!("{name}: ")), value])
}

fn evidence(ev: &Evidence) -> Doc {
    let items = ev
        .iter()
        .map(|(p, g)| text(format!("{p}: {}", grade(*g))))
        .collect();
    named(
        "ev",
        Doc::List {
            open: "{".into(),
            items,
            sep: ", ",
            close: "}",
        },
    )
}

/// `(x, y) -> body`, or `x -> body` for one parameter.
fn lambda(params: &[impl AsRef<str>], body: Doc) -> Doc {
    let ps: Vec<&str> = params.iter().map(|p| p.as_ref()).collect();
    let head = match ps[..] {
        [p] => format!("{p} -> "),
        _ => format!("({}) -> ", ps.join(", ")),
    };
    Doc::Cat(vec![text(head), body])
}

fn doc(t: &Term) -> Doc {
    match t {
        Term::Lit(v) => text(v.to_string()),
        Term::Var(x) => text(&**x),
        Term::Lam(params, body) => lambda(params, doc(body)),
        Term::App(f, args) => match &**f {
            Term::Var(_) | Term::PrimFn(_) => call(&doc(f).flat(), args.iter().map(doc).collect()),
            // The head is a doc of its own, not a copy of its text, so heads nested in heads
            // stay linear; it is written on one line, as the list after it starts where it
            // ends.
            _ => Doc::Cat(vec![
                Doc::Flat(Box::new(Doc::Cat(vec![text("("), doc(f), text(")")]))),
                call("", args.iter().map(doc).collect()),
            ]),
        },
        Term::Prim(Prim::Tuple, items) if items.len() == 1 => {
            Doc::Cat(vec![text("("), doc(&items[0]), text(",)")])
        }
        Term::Prim(Prim::Tuple, items) => Doc::List {
            open: "(".into(),
            items: items.iter().map(doc).collect(),
            sep: ", ",
            close: ")",
        },
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
            let items = rest
                .iter()
                .enumerate()
                .map(|(i, a)| match fs.get(i) {
                    Some(f) => Doc::Cat(vec![text(format!("{}: ", field(f))), doc(a)]),
                    None => doc(a),
                })
                .collect();
            Doc::List {
                open,
                items,
                sep: ", ",
                close: ")",
            }
        }
        // `-x` and `!x`: the operator before its operand (sec:grammar, Prefix).
        Term::Prim(p @ (Prim::Neg | Prim::Not), args) if args.len() == 1 => {
            Doc::Cat(vec![text(p.written()), operand(&args[0])])
        }
        // `t[0]` and `f[k]`: the key in brackets after its receiver (sec:grammar, IndexSuffix).
        // A chain `t[0][1]` is one `Cat` of its receiver and its indices, gathered by a loop, so
        // that `fits` meets the receiver's text first rather than after walking down the
        // chain, which made a broken layout quadratic in the chain's length.
        Term::Prim(Prim::TupleGet | Prim::Get, args) if args.len() == 2 => {
            let mut parts = vec![index(doc(&args[1]))];
            let mut receiver = &args[0];
            while let Term::Prim(Prim::TupleGet | Prim::Get, inner) = receiver
                && inner.len() == 2
            {
                parts.push(index(doc(&inner[1])));
                receiver = &inner[0];
            }
            parts.push(operand(receiver));
            parts.reverse();
            Doc::Cat(parts)
        }
        Term::Prim(p, args) => match (infix(*p), &args[..]) {
            // The left operand of `**` is a postfix expression (sec:grammar, Power), so
            // `-x ** 2` would read as `-(x ** 2)`.
            (Some(sep), [a, b]) => Doc::List {
                open: "(".into(),
                items: vec![if *p == Prim::Pow { operand(a) } else { doc(a) }, doc(b)],
                sep,
                close: ")",
            },
            _ => call(name(*p), args.iter().map(doc).collect()),
        },
        // A primitive with no operator function of its own is written as the lambda a program
        // writes for it (DESIGN.md writes `neg: (a -> -a)`), parenthesized as `(+)` is, so
        // that a call or an operator after it is not read as part of its body.
        Term::PrimFn(p @ (Prim::Neg | Prim::Not)) => text(format!("(x -> {}x)", p.written())),
        Term::PrimFn(Prim::TupleGet) => text("((t, i) -> t[i])"),
        Term::PrimFn(Prim::Get) => text("((f, k) -> f[k])"),
        Term::PrimFn(p) => match infix(*p) {
            Some(op) => text(format!("({})", op.trim())),
            None => text(name(*p)),
        },
        Term::Let(..) => {
            let mut items = Vec::new();
            let mut t = t;
            while let Term::Let(x, e, body) = t {
                items.push(Doc::Cat(vec![text(format!("{x} = ")), doc(e), text(";")]));
                t = body;
            }
            items.push(doc(t));
            Doc::List {
                open: "{".into(),
                items,
                sep: " ",
                close: "}",
            }
        }
        Term::If(c, a, b) => Doc::Cat(vec![
            text("if "),
            doc(c),
            text(" "),
            Doc::Together(vec![block(doc(a)), text(" else "), block(doc(b))]),
        ]),
        Term::Match(e, arms) => Doc::Cat(vec![
            text("match "),
            doc(e),
            text(" "),
            Doc::List {
                open: "{".into(),
                items: arms
                    .iter()
                    .map(|(p, t)| Doc::Cat(vec![text(format!("{p} -> ")), doc(t)]))
                    .collect(),
                sep: ", ",
                close: "}",
            },
        ]),
        Term::Fam { domain, var, body } => {
            call("fam", vec![doc(domain), lambda(&[&**var], doc(body))])
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
            call(
                "reindex",
                vec![doc(family), doc(kf), doc(vf), named("witness", text(w))],
            )
        }
        Term::Discard { family, sel } => call("discard", vec![doc(family), doc(sel)]),
        Term::Fold {
            family,
            op,
            identity,
            depth,
            ev,
        } => {
            let mut items = vec![doc(family), doc(op)];
            if let Some(i) = identity {
                items.push(named("identity", doc(i)));
            }
            items.push(named("depth", text(depth.to_string())));
            items.push(evidence(ev));
            call("fold", items)
        }
        Term::Fix {
            init,
            step,
            this,
            key,
            kind,
            ev,
        } => {
            let mut items = vec![doc(init)];
            match kind {
                FixKind::Lattice { join } => {
                    items.push(doc(step));
                    items.push(named("join", doc(join)));
                }
                FixKind::Definedness => {
                    items.push(lambda(&[&**this, &**key], doc(step)));
                    items.push(text("definedness"));
                }
            }
            items.push(evidence(ev));
            call("fix", items)
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
            call(
                "gen",
                vec![doc(init), doc(step), doc(guard), named("guard", text(pos))],
            )
        }
        Term::Read(port) => call("port.read", vec![text(&**port)]),
        Term::Push(port, v) => call("port.push", vec![text(&**port), doc(v)]),
    }
}

/// `t` as the operand of a prefix `-` or `!` or the receiver of `[k]`: parenthesized unless it
/// is written as a primary or a postfix expression (sec:grammar, Prefix and Postfix).
fn operand(t: &Term) -> Doc {
    if primary(t) {
        doc(t)
    } else {
        Doc::Cat(vec![text("("), doc(t), text(")")])
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

/// `[k]`, the brackets of an index.
fn index(k: Doc) -> Doc {
    Doc::List {
        open: "[".into(),
        items: vec![k],
        sep: ", ",
        close: "]",
    }
}

/// `{ e }`, the braces of an `if` branch.
fn block(d: Doc) -> Doc {
    Doc::List {
        open: "{".into(),
        items: vec![d],
        sep: " ",
        close: "}",
    }
}

impl Doc {
    /// The one-line text.
    fn flat(&self) -> String {
        let mut out = String::new();
        self.write_flat(&mut out);
        out
    }

    /// Writes the one-line text.
    fn write_flat(&self, out: &mut String) {
        match self {
            Doc::Text(s) => *out += s,
            Doc::Flat(d) => d.write_flat(out),
            Doc::Cat(ds) | Doc::Together(ds) => ds.iter().for_each(|d| d.write_flat(out)),
            Doc::List {
                open,
                items,
                sep,
                close,
            } => {
                let pad = Doc::pad(close, items);
                *out += open;
                *out += pad;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        *out += sep;
                    }
                    item.write_flat(out);
                }
                *out += pad;
                *out += close;
            }
        }
    }

    /// The space inside the braces of a nonempty `{ … }` written on one line.
    fn pad(close: &str, items: &[Doc]) -> &'static str {
        if close == "}" && !items.is_empty() {
            " "
        } else {
            ""
        }
    }

    /// The room left after the one-line text in `room` columns, or `None` when it does not
    /// fit. It stops once the room runs out, so it reads at most `room` columns of text.
    fn fits(&self, room: usize) -> Option<usize> {
        let take = |room: usize, s: &str| room.checked_sub(s.len());
        match self {
            Doc::Text(s) => take(room, s),
            Doc::Flat(d) => d.fits(room),
            Doc::Cat(ds) | Doc::Together(ds) => ds.iter().try_fold(room, |room, d| d.fits(room)),
            Doc::List {
                open,
                items,
                sep,
                close,
            } => {
                let pad = Doc::pad(close, items);
                let room = take(take(room, open)?, pad)?;
                let room = items.iter().enumerate().try_fold(room, |room, (i, item)| {
                    item.fits(if i > 0 { take(room, sep)? } else { room })
                })?;
                take(take(room, pad)?, close)
            }
        }
    }

    /// Writes the doc at column `col` of a line indented `ind`, in at most `width` columns
    /// where it can; returns the column it ends at.
    fn render(&self, ind: usize, col: usize, width: usize, out: &mut String) -> usize {
        if matches!(self, Doc::Text(_) | Doc::Flat(_))
            || self.fits(width.saturating_sub(col)).is_some()
        {
            let start = out.len();
            self.write_flat(out);
            return col + out.len() - start;
        }
        match self {
            Doc::Text(_) | Doc::Flat(_) => unreachable!("written flat above"),
            Doc::Cat(ds) => ds.iter().fold(col, |col, d| d.render(ind, col, width, out)),
            Doc::Together(ds) => ds.iter().fold(col, |col, d| match d {
                Doc::List { .. } => d.broken(ind, out, width),
                _ => d.render(ind, col, width, out),
            }),
            Doc::List { .. } => self.broken(ind, out, width),
        }
    }

    /// Writes a list with each item on its own line; returns the column it ends at.
    fn broken(&self, ind: usize, out: &mut String, width: usize) -> usize {
        match self {
            Doc::List {
                open,
                items,
                sep,
                close,
            } => {
                *out += open;
                let inner = ind + 2;
                for (i, item) in items.iter().enumerate() {
                    *out += "\n";
                    *out += &" ".repeat(inner);
                    item.render(inner, inner, width, out);
                    if i + 1 < items.len() {
                        *out += sep.trim_end();
                    }
                }
                *out += "\n";
                *out += &" ".repeat(ind);
                *out += close;
                ind + close.len()
            }
            _ => unreachable!("only a list breaks into lines"),
        }
    }
}

//! The pretty-printer of kernel terms (step L1.15), in the notation of DESIGN.md sec:kernel:
//! `fam(D, i -> e)`, `reindex(F, kf, vf)`, `fold(F, op, ev)` and the rest, with Tier 0 written
//! as Zed writes it (`(x, y) -> e`, `f(a)`, `x = e; body`, `if c { a } else { b }`).
//!
//! [`Term`]'s `Display` writes a term on one line. [`pretty`] writes the same text, broken
//! into lines of at most a given width where it can be: a term that does not fit puts each of
//! its parts on its own line, indented two spaces, so the only difference from the one-line
//! form is whitespace. Binary primitives are written infix and always parenthesized, so the
//! text needs no precedence to be read.

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
        f.write_str(&doc(self).flat())
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
        _ => infix(p)
            .expect("every primitive has a name or an infix spelling")
            .trim(),
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
        Term::App(f, args) => {
            let head = match &**f {
                Term::Var(_) | Term::PrimFn(_) => doc(f).flat(),
                _ => format!("({})", doc(f).flat()),
            };
            call(&head, args.iter().map(doc).collect())
        }
        Term::Prim(Prim::Tuple, items) if items.len() == 1 => {
            Doc::Cat(vec![text("("), doc(&items[0]), text(",)")])
        }
        Term::Prim(Prim::Tuple, items) => Doc::List {
            open: "(".into(),
            items: items.iter().map(doc).collect(),
            sep: ", ",
            close: ")",
        },
        // An atom built from a literal name and field names is written as Zed writes it.
        Term::Prim(Prim::Atom, args)
            if matches!(
                &args[..],
                [Term::Lit(Value::Str(_)), Term::Lit(Value::Tuple(fs)), rest @ ..]
                    if fs.is_empty() || fs.len() == rest.len()
            ) =>
        {
            let (Term::Lit(Value::Str(name)), Term::Lit(Value::Tuple(fs))) = (&args[0], &args[1])
            else {
                unreachable!("matched above")
            };
            let items = args[2..]
                .iter()
                .enumerate()
                .map(|(i, a)| match fs.get(i) {
                    Some(f) => Doc::Cat(vec![text(format!("{}: ", field(f))), doc(a)]),
                    None => doc(a),
                })
                .collect();
            Doc::List {
                open: format!("#{name}("),
                items,
                sep: ", ",
                close: ")",
            }
        }
        Term::Prim(p, args) => match (infix(*p), &args[..]) {
            (Some(sep), [a, b]) => Doc::List {
                open: "(".into(),
                items: vec![doc(a), doc(b)],
                sep,
                close: ")",
            },
            _ => call(name(*p), args.iter().map(doc).collect()),
        },
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
        match self {
            Doc::Text(s) => s.clone(),
            Doc::Cat(ds) | Doc::Together(ds) => ds.iter().map(Doc::flat).collect(),
            Doc::List {
                open,
                items,
                sep,
                close,
            } => {
                let items: Vec<String> = items.iter().map(Doc::flat).collect();
                let pad = if *close == "}" && !items.is_empty() {
                    " "
                } else {
                    ""
                };
                format!("{open}{pad}{}{pad}{close}", items.join(sep))
            }
        }
    }

    /// Writes the doc at column `col` of a line indented `ind`, in at most `width` columns
    /// where it can; returns the column it ends at.
    fn render(&self, ind: usize, col: usize, width: usize, out: &mut String) -> usize {
        let flat = self.flat();
        if col + flat.len() <= width || matches!(self, Doc::Text(_)) {
            *out += &flat;
            return col + flat.len();
        }
        match self {
            Doc::Text(_) => unreachable!("written flat above"),
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

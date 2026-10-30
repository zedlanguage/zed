//! Recursive type definitions (step L1.23, DESIGN.md sec:type_language): a group of mutually
//! recursive definitions, checked when it is defined and instantiated at its arguments.
//!
//! A group is accepted when it is
//! - *contractive*: every cycle of recursive occurrences passes through a constructor (a tuple
//!   component, an atom payload, or a morphism bound or value), so a type unfolds to its
//!   parts in finitely many steps;
//! - *regular*: every recursive occurrence passes the group's parameters unchanged, so a type
//!   has finitely many components;
//! - *monotone in emptiness*: no recursive occurrence stands under a complement, to the right
//!   of `\`, or in the guarantee of a morphism type whose value type may be empty or mentions
//!   the group, since `type T = (T) -> (#a & #b)` is inhabited exactly when it is empty.
//!
//! A value type that mentions a parameter may be empty when that parameter is: it counts as
//! possibly empty when it is empty with every parameter empty, or has a parameter under a
//! complement or to the right of `\`, where a larger argument shrinks it.

use std::collections::BTreeSet;
use std::fmt;
use std::sync::{Arc, OnceLock};

use super::Type;

/// A type expression in a definition's body.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr {
    /// The definition's parameter of this index.
    Param(usize),
    /// The group's definition of this index, at these arguments.
    Ref(usize, Vec<Expr>),
    /// A type that does not mention the group.
    Type(Type),
    /// `a | b | …`.
    Union(Vec<Expr>),
    /// `a & b & …`.
    And(Vec<Expr>),
    /// `!a`.
    Not(Box<Expr>),
    /// `a \ b`.
    Diff(Box<Expr>, Box<Expr>),
    /// `(a, b, …)`.
    Tuple(Vec<Expr>),
    /// `#name(a, b, …)`, whose payload is the tuple of its items.
    Atom(String, Vec<Expr>),
    /// The morphism type with this guarantee, permission and value type.
    Morphism(Box<Expr>, Box<Expr>, Box<Expr>),
}

impl Expr {
    /// `K -> V`, exact.
    pub fn exact(key: Expr, value: Expr) -> Expr {
        Expr::Morphism(Box::new(key.clone()), Box::new(key), Box::new(value))
    }

    /// Whether a recursive occurrence is in `self`.
    fn recursive(&self) -> bool {
        let mut found = false;
        self.walk(&mut |e| found |= matches!(e, Expr::Ref(..)));
        found
    }

    /// Applies `f` to `self` and every expression in it.
    fn walk(&self, f: &mut impl FnMut(&Expr)) {
        f(self);
        for e in self.children() {
            e.walk(f);
        }
    }

    fn children(&self) -> Vec<&Expr> {
        match self {
            Expr::Param(_) | Expr::Type(_) => Vec::new(),
            Expr::Ref(_, xs)
            | Expr::Union(xs)
            | Expr::And(xs)
            | Expr::Tuple(xs)
            | Expr::Atom(_, xs) => xs.iter().collect(),
            Expr::Not(a) => vec![a],
            Expr::Diff(a, b) => vec![a, b],
            Expr::Morphism(l, u, v) => vec![l, u, v],
        }
    }
}

/// A definition `type name(params) = body`.
#[derive(Clone, Debug)]
pub struct Def {
    /// Its name.
    pub name: String,
    /// Its parameters' names.
    pub params: Vec<String>,
    /// Its body.
    pub body: Expr,
}

/// A checked group of mutually recursive definitions.
#[derive(Clone, Debug)]
pub struct Group(Arc<[Def]>);

/// Why a group is rejected: the definition at fault and the reason.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Rejection {
    /// The index of the definition.
    pub def: usize,
    /// The reason, naming the definition.
    pub message: String,
}

impl Group {
    /// The group of `defs`, if it is contractive, regular and monotone in emptiness.
    pub fn new(defs: Vec<Def>) -> Result<Group, Rejection> {
        let g = Group(defs.into());
        g.regular()?;
        g.contractive()?;
        g.monotone()?;
        Ok(g)
    }

    /// The definitions.
    pub fn defs(&self) -> &[Def] {
        &self.0
    }

    fn reject(&self, def: usize, why: String) -> Rejection {
        Rejection {
            def,
            message: format!("the type `{}` {why}", self.0[def].name),
        }
    }

    fn regular(&self) -> Result<(), Rejection> {
        let arity = self.0[0].params.len();
        for (i, d) in self.0.iter().enumerate() {
            if d.params.len() != arity {
                return Err(self.reject(
                    i,
                    "takes other parameters than the definitions it is recursive with".into(),
                ));
            }
            let mut bad = None;
            d.body.walk(&mut |e| {
                if let Expr::Ref(_, args) = e {
                    let same = args.len() == arity
                        && args.iter().enumerate().all(|(k, a)| *a == Expr::Param(k));
                    if !same && bad.is_none() {
                        bad = Some(e.clone());
                    }
                }
            });
            if let Some(e) = bad {
                return Err(self.reject(
                    i,
                    format!(
                        "is not regular: its recursive occurrence `{}` changes the parameters, \
                         so the type has no end of components",
                        self.show(i, &e)
                    ),
                ));
            }
        }
        Ok(())
    }

    fn contractive(&self) -> Result<(), Rejection> {
        // The definitions each one names outside every constructor.
        let bare: Vec<BTreeSet<usize>> = self
            .0
            .iter()
            .map(|d| {
                let mut out = BTreeSet::new();
                unguarded(&d.body, &mut out);
                out
            })
            .collect();
        for start in 0..self.0.len() {
            let mut seen = BTreeSet::new();
            let mut todo: Vec<usize> = bare[start].iter().copied().collect();
            while let Some(i) = todo.pop() {
                if i == start {
                    return Err(self.reject(
                        start,
                        "is not contractive: it reaches itself with no constructor between".into(),
                    ));
                }
                if seen.insert(i) {
                    todo.extend(&bare[i]);
                }
            }
        }
        Ok(())
    }

    fn monotone(&self) -> Result<(), Rejection> {
        for (i, d) in self.0.iter().enumerate() {
            if let Some(why) = self.flipped(&d.body) {
                return Err(self.reject(i, format!("is not monotone in emptiness: {why}")));
            }
        }
        Ok(())
    }

    /// Where in `e` a recursive occurrence stands at a place that makes emptiness not
    /// monotone, if one does.
    fn flipped(&self, e: &Expr) -> Option<String> {
        match e {
            Expr::Not(a) if a.recursive() => {
                Some("a recursive occurrence stands under a complement".into())
            }
            Expr::Diff(_, b) if b.recursive() => {
                Some("a recursive occurrence stands to the right of `\\`".into())
            }
            Expr::Morphism(l, _, v) if l.recursive() && (v.recursive() || self.may_be_empty(v)) => {
                Some(
                    "a recursive occurrence stands in the guaranteed domain of a morphism type \
                     whose value type may be empty or mentions the group"
                        .into(),
                )
            }
            _ => e.children().into_iter().find_map(|c| self.flipped(c)),
        }
    }

    /// Whether `v`, which mentions no recursive occurrence, is empty at some arguments.
    fn may_be_empty(&self, v: &Expr) -> bool {
        let mut shrinks = false;
        v.walk(&mut |e| match e {
            Expr::Not(a) | Expr::Diff(_, a) => {
                a.walk(&mut |x| shrinks |= matches!(x, Expr::Param(_)));
            }
            _ => {}
        });
        let none = vec![Type::empty(); self.0[0].params.len()];
        shrinks || eval(v, &Arc::new(Env::ground(none))).is_empty()
    }

    /// The group's types at `args`, one per definition. Each is a recursive node that unfolds
    /// to its body.
    ///
    /// # Panics
    ///
    /// When `args` is not one type per parameter.
    pub fn instance(&self, args: Vec<Type>) -> Vec<Type> {
        assert_eq!(
            args.len(),
            self.0[0].params.len(),
            "one argument per parameter"
        );
        let env = Arc::new(Env {
            group: Some(self.clone()),
            args,
            members: OnceLock::new(),
        });
        let members: Vec<Type> = (0..self.0.len())
            .map(|i| {
                let e = env.clone();
                Type::rec(env.name(i), move || eval(&e.group().0[i].body, &e))
            })
            .collect();
        env.members
            .set(members.clone())
            .expect("the members are set once");
        members
    }

    /// `e`, an expression of definition `def`, in the surface syntax.
    fn show(&self, def: usize, e: &Expr) -> String {
        Show {
            defs: &self.0,
            params: &self.0[def].params,
            args: None,
            e,
        }
        .to_string()
    }
}

/// The definitions `e` names outside every constructor.
fn unguarded(e: &Expr, out: &mut BTreeSet<usize>) {
    match e {
        Expr::Ref(i, _) => {
            out.insert(*i);
        }
        Expr::Tuple(_) | Expr::Atom(..) | Expr::Morphism(..) => {}
        _ => {
            for c in e.children() {
                unguarded(c, out);
            }
        }
    }
}

/// What an expression is evaluated in: the arguments, and the group's types at them.
struct Env {
    group: Option<Group>,
    args: Vec<Type>,
    members: OnceLock<Vec<Type>>,
}

impl Env {
    fn ground(args: Vec<Type>) -> Env {
        Env {
            group: None,
            args,
            members: OnceLock::new(),
        }
    }

    fn group(&self) -> &Group {
        self.group
            .as_ref()
            .expect("a recursive occurrence is in a group")
    }

    /// The name of definition `i` at the arguments: `Tree(int)`.
    fn name(&self, i: usize) -> String {
        let d = &self.group().0[i];
        match self.args.is_empty() {
            true => d.name.clone(),
            false => {
                let args: Vec<String> = self.args.iter().map(Type::to_string).collect();
                format!("{}({})", d.name, args.join(", "))
            }
        }
    }
}

fn eval(e: &Expr, env: &Arc<Env>) -> Type {
    let all = |xs: &[Expr]| xs.iter().map(|x| eval(x, env)).collect::<Vec<_>>();
    match e {
        Expr::Param(i) => env.args[*i].clone(),
        Expr::Ref(i, _) => env.members.get().expect("members are set before use")[*i].clone(),
        Expr::Type(t) => t.clone(),
        Expr::Union(xs) => Type::union_all(all(xs)),
        Expr::And(xs) => Type::meet_all(all(xs)),
        Expr::Not(a) => !eval(a, env),
        Expr::Diff(a, b) => eval(a, env) - &eval(b, env),
        Expr::Tuple(xs) => Type::tuple(xs.iter().map(|x| component(x, env)).collect()),
        Expr::Atom(name, xs) => Type::atom_with(
            name,
            &Type::tuple(xs.iter().map(|x| component(x, env)).collect()),
        ),
        Expr::Morphism(l, u, v) => {
            Type::morphism(component(l, env), component(u, env), component(v, env))
        }
    }
}

/// `e` in a constructor: when it mentions the group and is more than one occurrence, it is
/// kept as a node evaluated on first use, since evaluating it now could need the parts of the
/// type being built.
fn component(e: &Expr, env: &Arc<Env>) -> Type {
    if matches!(e, Expr::Ref(..)) || !e.recursive() {
        return eval(e, env);
    }
    let name = Show {
        defs: &env.group().0,
        params: &[],
        args: Some(&env.args),
        e,
    }
    .to_string();
    let (e, env) = (e.clone(), env.clone());
    Type::rec(name, move || eval(&e, &env))
}

/// An expression in the surface syntax, its parameters by name or, with `args`, by value.
struct Show<'a> {
    defs: &'a [Def],
    params: &'a [String],
    args: Option<&'a [Type]>,
    e: &'a Expr,
}

impl fmt::Display for Show<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sub = |e: &'_ Expr| {
            let s = Show { e, ..*self }.to_string();
            match e {
                Expr::Union(_) | Expr::And(_) | Expr::Diff(..) | Expr::Morphism(..) => {
                    format!("({s})")
                }
                _ => s,
            }
        };
        let list = |xs: &[Expr], sep: &str| xs.iter().map(sub).collect::<Vec<_>>().join(sep);
        match self.e {
            Expr::Param(i) => match self.args {
                Some(args) => write!(f, "{}", args[*i]),
                None => f.write_str(&self.params[*i]),
            },
            Expr::Ref(i, args) if args.is_empty() => f.write_str(&self.defs[*i].name),
            Expr::Ref(i, args) => {
                let args: Vec<String> = args
                    .iter()
                    .map(|a| Show { e: a, ..*self }.to_string())
                    .collect();
                write!(f, "{}({})", self.defs[*i].name, args.join(", "))
            }
            Expr::Type(t) => write!(f, "{t}"),
            Expr::Union(xs) => f.write_str(&list(xs, " | ")),
            Expr::And(xs) => f.write_str(&list(xs, " & ")),
            Expr::Not(a) => write!(f, "!{}", sub(a)),
            Expr::Diff(a, b) => write!(f, "{} \\ {}", sub(a), sub(b)),
            Expr::Tuple(xs) => write!(f, "({})", list(xs, ", ")),
            Expr::Atom(name, xs) => write!(f, "#{name}({})", list(xs, ", ")),
            Expr::Morphism(l, u, v) if l == u => write!(f, "({}) -> {}", sub(l), sub(v)),
            Expr::Morphism(l, u, v) if **l == Expr::Type(Type::empty()) => {
                write!(f, "{} ->? {}", sub(u), sub(v))
            }
            Expr::Morphism(l, u, v) => write!(f, "({} ⊆ dom ⊆ {}) -> {}", sub(l), sub(u), sub(v)),
        }
    }
}

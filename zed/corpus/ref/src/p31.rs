//! 31 tiny typechecker, written independently of the Zed program's structure: an RPN evaluator, a
//! map symbol table with duplicate detection, and the least solution of the type equations from
//! all-unknown, found with one evaluation of a declaration when its names are settled, not by
//! rounds over all of them. The equations are monotone in unknown < int, bool < error, and an
//! error in any operand is an error of the whole expression, so a use of a name that became an
//! error needs no evaluation. Diagnostics per declaration line, in the check-name order cyclic,
//! duplicate, malformed, type, unbound (code-point order of the names); typings in name order
//! (code-point).

use std::collections::BTreeMap;

use crate::zedrt::try_parse_int;

/// One token of a right side, in the postfix order it is written in.
#[derive(Clone, Copy)]
enum Tok<'a> {
    Num,
    BoolLit,
    Var(&'a str),
    Add,
    Eq,
    Cond,
}

struct Decl<'a> {
    line: usize,
    name: &'a str,
    /// The right side. An operand it does not supply is an error; a malformed one has no tokens.
    toks: Vec<Tok<'a>>,
    malformed: bool,
}

impl<'a> Decl<'a> {
    /// The names used, left to right, with repeats.
    fn vars(&self) -> impl Iterator<Item = &'a str> {
        self.toks.iter().filter_map(|t| match t {
            Tok::Var(name) => Some(*name),
            _ => None,
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Ty {
    Integer,
    Boolean,
    Error,
    Unknown,
}

impl Ty {
    fn label(self) -> &'static str {
        match self {
            Ty::Integer => "int",
            Ty::Boolean => "bool",
            Ty::Error => "error",
            Ty::Unknown => "unknown",
        }
    }
}

fn parse(line: usize, l: &str) -> Decl<'_> {
    let w: Vec<&str> = l.split(' ').collect();
    let mut toks = Vec::new();
    let mut height: usize = 0; // of the operand stack, what is missing counted as supplied
    for &tok in w.iter().skip(2) {
        let (t, pops) = match tok {
            "+" => (Tok::Add, 2),
            "==" => (Tok::Eq, 2),
            "?" => (Tok::Cond, 3),
            "true" | "false" => (Tok::BoolLit, 0),
            _ if try_parse_int(tok).is_some() => (Tok::Num, 0),
            _ => (Tok::Var(tok), 0),
        };
        toks.push(t);
        height = height.saturating_sub(pops) + 1;
    }
    let malformed = w.get(1) != Some(&"=") || height != 1;
    if malformed {
        toks.clear();
    }
    Decl {
        line,
        name: w[0],
        toks,
        malformed,
    }
}

fn lift(a: Ty, b: Ty, ok: Ty) -> Ty {
    if a == Ty::Error || b == Ty::Error {
        Ty::Error
    } else if a == Ty::Unknown || b == Ty::Unknown {
        Ty::Unknown
    } else {
        ok
    }
}

/// The type of a right side under the types `ty`.
fn infer(toks: &[Tok<'_>], ty: &BTreeMap<&str, Ty>) -> Ty {
    fn pop(st: &mut Vec<Ty>) -> Ty {
        st.pop().unwrap_or(Ty::Error)
    }
    let mut st = Vec::new();
    for t in toks {
        let v = match t {
            Tok::Num => Ty::Integer,
            Tok::BoolLit => Ty::Boolean,
            Tok::Var(name) => ty.get(name).copied().unwrap_or(Ty::Error),
            Tok::Add => {
                let (y, x) = (pop(&mut st), pop(&mut st));
                let ok = if x == Ty::Integer && y == Ty::Integer {
                    Ty::Integer
                } else {
                    Ty::Error
                };
                lift(x, y, ok)
            }
            Tok::Eq => {
                let (y, x) = (pop(&mut st), pop(&mut st));
                lift(x, y, if x == y { Ty::Boolean } else { Ty::Error })
            }
            Tok::Cond => {
                let (b, a, c) = (pop(&mut st), pop(&mut st), pop(&mut st));
                let ok = if c == Ty::Boolean && a == b {
                    a
                } else {
                    Ty::Error
                };
                lift(c, lift(a, b, a), ok)
            }
        };
        st.push(v);
    }
    pop(&mut st)
}

/// The least solution of the type equations, as the program's rounds from all-unknown reach it.
struct Solver<'s, 'a> {
    decls: &'s [Decl<'a>],
    sites: &'s BTreeMap<&'a str, Vec<usize>>,
    ty: BTreeMap<&'a str, Ty>,
    /// The declarations that use each declared name, once per use.
    users: BTreeMap<&'a str, Vec<usize>>,
    /// For each declaration, its uses of names whose type is not settled.
    waiting: Vec<usize>,
    /// The names just settled, whose users have not been told.
    settled: Vec<&'a str>,
}

impl<'a> Solver<'_, 'a> {
    /// Settles an unknown `name` at `t`.
    fn settle(&mut self, name: &'a str, t: Ty) {
        self.ty.insert(name, t);
        self.settled.push(name);
    }

    /// The declaration index if `name` has one declaration and its type is unknown.
    fn open(&self, name: &str) -> Option<usize> {
        match self.sites[name][..] {
            [d] if self.ty[name] == Ty::Unknown => Some(d),
            _ => None,
        }
    }

    /// Tells the users of every settled name, until no more settle.
    fn spread(&mut self) {
        while let Some(name) = self.settled.pop() {
            let t = self.ty[name];
            let users = self.users.remove(name).unwrap_or_default();
            for d in users {
                self.waiting[d] -= 1;
                let target = self.decls[d].name;
                if self.open(target) != Some(d) {
                    continue;
                }
                if t == Ty::Error {
                    self.settle(target, Ty::Error);
                } else if self.waiting[d] == 0 {
                    self.settle(target, infer(&self.decls[d].toks, &self.ty));
                }
            }
        }
    }
}

/// Solves the type equations. A declaration is evaluated when its last name settles. What is
/// still unknown after that uses a name on a cycle; it can only become an error, which one more
/// evaluation with what is known finds, and which then spreads to its users.
fn solve<'a>(decls: &[Decl<'a>], sites: &BTreeMap<&'a str, Vec<usize>>) -> BTreeMap<&'a str, Ty> {
    let mut users: BTreeMap<&'a str, Vec<usize>> = BTreeMap::new();
    let mut waiting = vec![0; decls.len()];
    for (d, decl) in decls.iter().enumerate() {
        for x in decl.vars().filter(|x| sites.contains_key(x)) {
            users.entry(x).or_default().push(d);
            waiting[d] += 1;
        }
    }
    let mut s = Solver {
        decls,
        sites,
        ty: sites.keys().map(|n| (*n, Ty::Unknown)).collect(),
        users,
        waiting,
        settled: Vec::new(),
    };
    for (name, ds) in sites {
        match ds[..] {
            [d] if s.waiting[d] == 0 => s.settle(name, infer(&decls[d].toks, &s.ty)),
            [_] => {}
            _ => s.settle(name, Ty::Error),
        }
    }
    s.spread();
    for name in sites.keys() {
        if let Some(d) = s.open(name)
            && infer(&decls[d].toks, &s.ty) == Ty::Error
        {
            s.settle(name, Ty::Error);
            s.spread();
        }
    }
    s.ty
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let decls: Vec<Decl<'_>> = lines
        .iter()
        .enumerate()
        .map(|(i, l)| parse(i + 1, l))
        .collect();
    let mut sites: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
    for (i, d) in decls.iter().enumerate() {
        sites.entry(d.name).or_default().push(i);
    }
    let ty = solve(&decls, &sites);
    for (n, t) in &ty {
        say!(out, "{n} : {}", t.label());
    }
    let clean =
        |x: &str| sites.get(x).is_some_and(|d| d.len() == 1) && ty.get(x) != Some(&Ty::Error);
    for d in &decls {
        let (line, name) = (d.line, d.name);
        let ds = &sites[name];
        let mine = ds.len() == 1;
        let first = decls[ds[0]].line;
        let unbound: Vec<&str> = d.vars().filter(|x| !sites.contains_key(x)).collect();
        if mine && ty[name] == Ty::Unknown {
            say!(out, "line {line}: {name} is cyclic");
        }
        if !mine && line != first {
            say!(out, "line {line}: duplicate {name} (first at line {first})");
        }
        if d.malformed {
            say!(out, "line {line}: malformed {name}");
        }
        if mine && !d.malformed && ty[name] == Ty::Error && d.vars().all(clean) {
            say!(out, "line {line}: type error in {name}");
        }
        if !unbound.is_empty() {
            say!(out, "line {line}: unbound {}", unbound.join(", "));
        }
    }
    Ok(())
}

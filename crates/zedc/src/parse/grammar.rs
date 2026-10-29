//! The syntactic grammar of DESIGN.md sec:grammar, read from its copy in `zed/grammar/`.
//!
//! Each line is `Rule = body Lk` or `| body Lk`: an alternative and the layer it joins. A body
//! is a parsing expression: ordered choice `|` below sequence, below the prefixes `&` and `!`,
//! below the postfixes `*`, `+`, `?` and `e % sep` (`e (sep e)*`); `head(e)` and `nest(e)` set
//! and clear the flag that `HEAD` tests, and a name in capitals that is no rule is a token kind.

use std::collections::HashMap;

/// A kind of token, as the grammar names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// `IDENT`, a name.
    Ident,
    /// `WILD`, the wildcard `_`.
    Wild,
    /// `INT`.
    Int,
    /// `FLOAT`.
    Float,
    /// `RAT`.
    Rat,
    /// `STRING`.
    Str,
    /// `ATOM`.
    Atom,
    /// `ANNOT`.
    Annot,
    /// A keyword.
    Keyword,
    /// An operator or punctuation mark.
    Op,
    /// `END`, after the last token.
    End,
}

/// A parsing expression.
#[derive(Clone, Debug)]
pub enum Expr {
    /// A keyword, operator or name with this text.
    Lit(String),
    /// A rule, by index.
    Rule(usize),
    /// A token of this kind.
    Kind(Kind),
    /// `HEAD`: succeeds inside `head(…)` and outside any `nest(…)` within it.
    Head,
    /// A sequence.
    Seq(Vec<Expr>),
    /// An ordered choice.
    Choice(Vec<Expr>),
    /// `e*`.
    Star(Box<Expr>),
    /// `e+`.
    Plus(Box<Expr>),
    /// `e?`.
    Opt(Box<Expr>),
    /// `&e`.
    And(Box<Expr>),
    /// `!e`.
    Not(Box<Expr>),
    /// `head(e)`.
    SetHead(Box<Expr>),
    /// `nest(e)`.
    ClearHead(Box<Expr>),
}

/// A rule: its name and its alternatives, in order, each with its layer.
#[derive(Clone, Debug)]
pub struct Rule {
    /// The name.
    pub name: String,
    /// The alternatives and their layers.
    pub alts: Vec<(Expr, u32)>,
}

/// A grammar: its rules, in the order they are written.
#[derive(Clone, Debug)]
pub struct Grammar {
    /// The rules.
    pub rules: Vec<Rule>,
    index: HashMap<String, usize>,
}

impl Grammar {
    /// Reads the grammar written in `texts`, in order.
    pub fn read(texts: &[&str]) -> Result<Grammar, String> {
        let lines: Vec<&str> = texts
            .iter()
            .flat_map(|t| t.lines())
            .filter(|l| !l.trim().is_empty())
            .collect();
        let mut index = HashMap::new();
        for l in &lines {
            if let Some((name, _)) = l.split_once('=').filter(|_| !l.starts_with(' ')) {
                let name = name.trim();
                if index.insert(name.to_string(), index.len()).is_some() {
                    return Err(format!("the rule {name} is defined twice"));
                }
            }
        }
        let mut rules: Vec<Rule> = Vec::new();
        for l in lines {
            let (head, body) = if l.starts_with(' ') {
                let body = l.trim_start().strip_prefix('|');
                (None, body.ok_or_else(|| format!("no `|` in {l:?}"))?)
            } else {
                let (name, body) = l.split_once('=').expect("a rule line has `=`");
                (Some(name.trim()), body)
            };
            let body = body.trim_end();
            let (body, layer) = body
                .rsplit_once(char::is_whitespace)
                .and_then(|(b, k)| Some((b, k.strip_prefix('L')?.parse().ok()?)))
                .ok_or_else(|| format!("no layer at the end of {l:?}"))?;
            let toks = tokens(body)?;
            let mut p = Reader {
                toks: &toks,
                i: 0,
                index: &index,
            };
            let e = p.choice()?;
            if p.i != toks.len() {
                return Err(format!("trailing text in {l:?}"));
            }
            match head {
                Some(name) => rules.push(Rule {
                    name: name.into(),
                    alts: vec![(e, layer)],
                }),
                None => rules
                    .last_mut()
                    .ok_or("an alternative before any rule")?
                    .alts
                    .push((e, layer)),
            }
        }
        Ok(Grammar { rules, index })
    }

    /// The index of the rule `name`, if there is one.
    pub fn rule(&self, name: &str) -> Option<usize> {
        self.index.get(name).copied()
    }
}

/// A token of a grammar line.
#[derive(Clone, Debug, PartialEq)]
enum GTok {
    Lit(String),
    Name(String),
    Wrap(&'static str),
    Op(char),
}

fn tokens(body: &str) -> Result<Vec<GTok>, String> {
    let mut out = Vec::new();
    let mut chars = body.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        match c {
            ' ' | '\t' => {}
            '\'' => {
                let mut lit = String::new();
                loop {
                    match chars.next() {
                        Some((_, '\\')) => {
                            lit.push(chars.next().ok_or("a `\\` ends the line")?.1);
                        }
                        Some((_, '\'')) => break,
                        Some((_, c)) => lit.push(c),
                        None => return Err(format!("an unclosed literal in {body:?}")),
                    }
                }
                out.push(GTok::Lit(lit));
            }
            '(' | ')' | '|' | '*' | '+' | '?' | '&' | '!' | '%' => out.push(GTok::Op(c)),
            c if c.is_ascii_alphabetic() || c == '_' => {
                let mut end = i + 1;
                while let Some(&(j, d)) = chars.peek() {
                    if !(d.is_ascii_alphanumeric() || d == '_') {
                        break;
                    }
                    end = j + 1;
                    chars.next();
                }
                let name = &body[i..end];
                match (name, chars.peek()) {
                    ("head", Some((_, '('))) => {
                        chars.next();
                        out.push(GTok::Wrap("head"));
                    }
                    ("nest", Some((_, '('))) => {
                        chars.next();
                        out.push(GTok::Wrap("nest"));
                    }
                    _ => out.push(GTok::Name(name.into())),
                }
            }
            _ => return Err(format!("{c:?} in {body:?} is no grammar token")),
        }
    }
    Ok(out)
}

struct Reader<'a> {
    toks: &'a [GTok],
    i: usize,
    index: &'a HashMap<String, usize>,
}

impl Reader<'_> {
    fn eat(&mut self, c: char) -> bool {
        let hit = self.toks.get(self.i) == Some(&GTok::Op(c));
        self.i += usize::from(hit);
        hit
    }

    fn choice(&mut self) -> Result<Expr, String> {
        let mut alts = vec![self.seq()?];
        while self.eat('|') {
            alts.push(self.seq()?);
        }
        Ok(if alts.len() == 1 {
            alts.pop().expect("one")
        } else {
            Expr::Choice(alts)
        })
    }

    fn seq(&mut self) -> Result<Expr, String> {
        let mut items = Vec::new();
        while !matches!(self.toks.get(self.i), None | Some(GTok::Op('|' | ')'))) {
            items.push(self.prefix()?);
        }
        Ok(if items.len() == 1 {
            items.pop().expect("one")
        } else {
            Expr::Seq(items)
        })
    }

    fn prefix(&mut self) -> Result<Expr, String> {
        if self.eat('&') {
            Ok(Expr::And(Box::new(self.prefix()?)))
        } else if self.eat('!') {
            Ok(Expr::Not(Box::new(self.prefix()?)))
        } else {
            self.postfix()
        }
    }

    fn postfix(&mut self) -> Result<Expr, String> {
        let mut e = self.primary()?;
        loop {
            e = if self.eat('*') {
                Expr::Star(Box::new(e))
            } else if self.eat('+') {
                Expr::Plus(Box::new(e))
            } else if self.eat('?') {
                Expr::Opt(Box::new(e))
            } else if self.eat('%') {
                let sep = self.primary()?;
                Expr::Seq(vec![
                    e.clone(),
                    Expr::Star(Box::new(Expr::Seq(vec![sep, e]))),
                ])
            } else {
                return Ok(e);
            }
        }
    }

    fn primary(&mut self) -> Result<Expr, String> {
        let t = self
            .toks
            .get(self.i)
            .cloned()
            .ok_or("an expression is missing")?;
        self.i += 1;
        match t {
            GTok::Lit(s) => Ok(Expr::Lit(s)),
            GTok::Name(n) => match self.index.get(&n) {
                Some(&r) => Ok(Expr::Rule(r)),
                None => kind(&n).ok_or(format!("the rule {n} is not defined")),
            },
            GTok::Wrap(w) => {
                let e = Box::new(self.choice()?);
                if !self.eat(')') {
                    return Err(format!("`{w}(` is not closed"));
                }
                Ok(if w == "head" {
                    Expr::SetHead(e)
                } else {
                    Expr::ClearHead(e)
                })
            }
            GTok::Op('(') => {
                let e = self.choice()?;
                if !self.eat(')') {
                    return Err("`(` is not closed".into());
                }
                Ok(e)
            }
            GTok::Op(c) => Err(format!("unexpected {c:?}")),
        }
    }
}

impl Kind {
    /// The name the grammar writes for this kind.
    pub fn name(self) -> &'static str {
        match self {
            Kind::Ident => "IDENT",
            Kind::Wild => "WILD",
            Kind::Int => "INT",
            Kind::Float => "FLOAT",
            Kind::Rat => "RAT",
            Kind::Str => "STRING",
            Kind::Atom => "ATOM",
            Kind::Annot => "ANNOT",
            Kind::Keyword => "KW",
            Kind::Op => "OP",
            Kind::End => "END",
        }
    }
}

fn kind(name: &str) -> Option<Expr> {
    Some(match name {
        "HEAD" => Expr::Head,
        "IDENT" => Expr::Kind(Kind::Ident),
        "WILD" => Expr::Kind(Kind::Wild),
        "INT" => Expr::Kind(Kind::Int),
        "FLOAT" => Expr::Kind(Kind::Float),
        "RAT" => Expr::Kind(Kind::Rat),
        "STRING" => Expr::Kind(Kind::Str),
        "ATOM" => Expr::Kind(Kind::Atom),
        "ANNOT" => Expr::Kind(Kind::Annot),
        "END" => Expr::Kind(Kind::End),
        _ => return None,
    })
}

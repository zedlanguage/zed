//! The grammars of DESIGN.md sec:grammar, read from their text. The compiler reads the
//! syntactic grammar, read from the spec by `build.rs`, with [`Grammar::read`]; the grammar tools
//! read all three fences with [`Grammar::read_open`].
//!
//! Each line is `Rule = body Lk` or `| body Lk`, then an optional `-- comment`: an alternative
//! and the layer it joins. A body is a parsing expression: ordered choice `|` below sequence,
//! below the prefixes `&` and `!`, below the postfixes `*`, `+`, `?` and `e % sep` (`e (sep e)*`);
//! `head(e)` and `nest(e)` set and clear the flag that `HEAD` tests, and a name in capitals that
//! is no rule is a token kind. `~R` at the top of an alternative that holds nothing else but
//! lookaheads means that the alternative builds no node, and the match is the node of the rule
//! `R`. Its layer is not above the lowest layer of `R`, since the node of `R` is what reports a
//! layer.
//!
//! The lexical grammar adds what only a grammar over characters can read: double-quoted
//! literals, `[a-z]` classes and `ANY`.

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
    /// `e % sep`, which matches `e (sep e)*`, held as `[sep, e]` so that `e` is written once
    /// and the two items are the sequence repeated.
    Sep(Box<[Expr; 2]>),
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
    /// `[…]`: a character in these inclusive ranges. Only [`Grammar::read_open`] reads this.
    Class(Vec<(char, char)>),
    /// `ANY`: any character. Only [`Grammar::read_open`] reads this.
    Any,
    /// A name that is no rule and nothing built in, which never matches. Only
    /// [`Grammar::read_open`] reads this, so that the grammar checker can report every one.
    Undefined(String),
}

/// An alternative of a rule.
#[derive(Clone, Debug)]
pub struct Alt {
    /// Its expression.
    pub expr: Expr,
    /// The layer it joins.
    pub layer: u32,
    /// Whether it is a `~` alternative, which builds no node.
    pub pass: bool,
}

/// A rule: its name and its alternatives, in order.
#[derive(Clone, Debug)]
pub struct Rule {
    /// The name.
    pub name: String,
    /// The alternatives.
    pub alts: Vec<Alt>,
}

/// A grammar: its rules, in the order they are written.
#[derive(Clone, Debug)]
pub struct Grammar {
    /// The rules.
    pub rules: Vec<Rule>,
    index: HashMap<String, usize>,
}

/// Whether `c` is white space to the grammar reader: Unicode's, and the four separators
/// U+001C to U+001F.
pub fn is_space(c: char) -> bool {
    c.is_whitespace() || ('\x1c'..='\x1f').contains(&c)
}

/// A grammar line taken apart: the rule it starts, if any, the body, the layer.
pub type Line<'a> = (Option<&'a str>, &'a str, u32);

/// Reads the line `raw` as `Rule = body Lk` or `| body Lk`, then an optional `-- comment`.
/// The body ends at the first `Lk` with nothing after it but white space and the comment.
pub fn split_line(raw: &str) -> Option<Line<'_>> {
    let (rule, rest) = if let Some(rest) = raw.trim_start_matches(is_space).strip_prefix('|') {
        (None, rest)
    } else {
        let end = raw
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .filter(|&i| i > 0 && !raw.as_bytes()[0].is_ascii_digit())?;
        let rest = raw[end..].trim_start_matches(is_space).strip_prefix('=')?;
        (Some(&raw[..end]), rest)
    };
    let mut after_space = false;
    for (at, c) in rest.char_indices() {
        if after_space && let Some(layer) = layer_at(&rest[at..]) {
            return Some((rule, rest[..at].trim_matches(is_space), layer));
        }
        after_space = is_space(c);
    }
    None
}

/// The layer of `Lk` at the start of `text`, when nothing but white space and a comment
/// follows it.
fn layer_at(text: &str) -> Option<u32> {
    let digits = text.strip_prefix('L')?;
    let end = digits
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(digits.len());
    let tail = digits[end..].trim_start_matches(is_space);
    if tail.is_empty() || tail.starts_with("--") {
        digits[..end].parse().ok()
    } else {
        None
    }
}

impl Grammar {
    /// Reads the grammar written in `texts`, in order, as the compiler's parser takes it: over
    /// tokens, every name a rule or a token kind, every `~` mark at a layer its rule has.
    pub fn read(texts: &[&str]) -> Result<Grammar, String> {
        let g = Grammar::read_with(texts, false)?;
        let lowest = g.lowest_layers();
        for rule in &g.rules {
            for alt in rule.alts.iter().filter(|a| a.pass) {
                let r = marked_rule(&alt.expr).expect("read above");
                if alt.layer > lowest[r] {
                    return Err(format!(
                        "{} marks {} at L{}, above its lowest layer L{}",
                        rule.name, g.rules[r].name, alt.layer, lowest[r]
                    ));
                }
            }
        }
        Ok(g)
    }

    /// Reads the grammar written in `texts`, in order, as the grammar tools take it: a grammar
    /// over characters is read too, and a name that is not defined becomes
    /// [`Expr::Undefined`], for the checker to report.
    pub fn read_open(texts: &[&str]) -> Result<Grammar, String> {
        Grammar::read_with(texts, true)
    }

    fn read_with(texts: &[&str], open: bool) -> Result<Grammar, String> {
        let is_line = |l: &&str| !l.trim_matches(is_space).is_empty();
        let lines: Vec<&str> = texts
            .iter()
            .flat_map(|t| t.split('\n'))
            .filter(is_line)
            .collect();
        let mut split = Vec::with_capacity(lines.len());
        let mut index = HashMap::new();
        for l in &lines {
            let line = split_line(l).ok_or_else(|| format!("no layer at the end of {l:?}"))?;
            if let Some(name) = line.0
                && index.insert(name.to_string(), index.len()).is_some()
            {
                return Err(format!("the rule {name} is defined twice"));
            }
            split.push(line);
        }
        let mut rules: Vec<Rule> = Vec::new();
        for (l, (head, body, layer)) in lines.into_iter().zip(split) {
            let toks = tokens(body)?;
            let mut p = Reader {
                toks: &toks,
                i: 0,
                index: &index,
                open,
                depth: 0,
                marked: false,
            };
            let e = p.choice()?;
            if p.i != toks.len() {
                return Err(format!("trailing text in {l:?}"));
            }
            let pass = p.marked;
            if pass && marked_rule(&e).is_none() && !marks_undefined(&e) {
                return Err(format!("beside a ~ mark {l:?} holds only lookaheads"));
            }
            let alt = Alt {
                expr: e,
                layer,
                pass,
            };
            match head {
                Some(name) => rules.push(Rule {
                    name: name.into(),
                    alts: vec![alt],
                }),
                None => rules
                    .last_mut()
                    .ok_or("an alternative before any rule")?
                    .alts
                    .push(alt),
            }
        }
        Ok(Grammar { rules, index })
    }

    /// The lowest layer of each rule.
    pub fn lowest_layers(&self) -> Vec<u32> {
        self.rules
            .iter()
            .map(|r| {
                r.alts
                    .iter()
                    .map(|a| a.layer)
                    .min()
                    .expect("a rule starts with an alternative")
            })
            .collect()
    }

    /// The index of the rule `name`, if there is one.
    pub fn rule(&self, name: &str) -> Option<usize> {
        self.index.get(name).copied()
    }
}

/// Whether the `~` alternative `e` marks a name that is not defined and holds nothing else
/// but lookaheads.
fn marks_undefined(e: &Expr) -> bool {
    match e {
        Expr::Undefined(_) => true,
        Expr::Seq(items) => {
            let mut rest = items
                .iter()
                .filter(|x| !matches!(x, Expr::And(_) | Expr::Not(_)));
            matches!((rest.next(), rest.next()), (Some(Expr::Undefined(_)), None))
        }
        _ => false,
    }
}

/// The rule of the `~` mark in the alternative `e`, if `e` holds nothing else but lookaheads.
pub fn marked_rule(e: &Expr) -> Option<usize> {
    match e {
        Expr::Rule(r) => Some(*r),
        Expr::Seq(items) => {
            let mut rest = items
                .iter()
                .filter(|x| !matches!(x, Expr::And(_) | Expr::Not(_)));
            match (rest.next(), rest.next()) {
                (Some(Expr::Rule(r)), None) => Some(*r),
                _ => None,
            }
        }
        _ => None,
    }
}

/// A token of a grammar line.
#[derive(Clone, Debug, PartialEq)]
enum GTok {
    Lit(String),
    Class(Vec<(char, char)>),
    Name(String),
    Wrap(&'static str),
    Op(char),
}

/// The character a backslash escape stands for: `\n`, `\t`, `\r`, `\0`, or the character
/// itself.
fn escaped(c: char) -> char {
    match c {
        'n' => '\n',
        't' => '\t',
        'r' => '\r',
        '0' => '\0',
        c => c,
    }
}

/// The ranges of a character class's body: `a-z` is a range unless `-` is first or last.
fn class_ranges(body: &[char]) -> Result<Vec<(char, char)>, String> {
    // `None` is a range's `-`.
    let mut chars: Vec<Option<char>> = Vec::with_capacity(body.len());
    let mut i = 0;
    while i < body.len() {
        match body[i] {
            '\\' => {
                let c = *body.get(i + 1).ok_or("a `\\` ends a character class")?;
                chars.push(Some(escaped(c)));
                i += 2;
            }
            '-' if !chars.is_empty() && i + 1 < body.len() => {
                chars.push(None);
                i += 1;
            }
            c => {
                chars.push(Some(c));
                i += 1;
            }
        }
    }
    let mut ranges = Vec::new();
    let mut k = 0;
    while k < chars.len() {
        let low = chars[k].ok_or("a character class holds `--`")?;
        if k + 2 < chars.len() && chars[k + 1].is_none() {
            let high = chars[k + 2].ok_or("a character class holds `--`")?;
            ranges.push((low, high));
            k += 3;
        } else {
            ranges.push((low, low));
            k += 1;
        }
    }
    Ok(ranges)
}

fn tokens(body: &str) -> Result<Vec<GTok>, String> {
    let mut out = Vec::new();
    let mut chars = body.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        match c {
            c if is_space(c) => {}
            '\'' | '"' => {
                let mut lit = String::new();
                loop {
                    match chars.next() {
                        Some((_, '\\')) => {
                            lit.push(escaped(chars.next().ok_or("a `\\` ends the line")?.1));
                        }
                        Some((_, d)) if d == c => break,
                        Some((_, d)) => lit.push(d),
                        None => return Err(format!("an unclosed literal in {body:?}")),
                    }
                }
                out.push(GTok::Lit(lit));
            }
            '[' => {
                let mut class = Vec::new();
                loop {
                    match chars.next() {
                        Some((_, '\\')) => {
                            class.push('\\');
                            class.push(chars.next().ok_or("a `\\` ends the line")?.1);
                        }
                        Some((_, ']')) => break,
                        Some((_, d)) => class.push(d),
                        None => return Err(format!("an unclosed class in {body:?}")),
                    }
                }
                out.push(GTok::Class(class_ranges(&class)?));
            }
            '(' | ')' | '|' | '*' | '+' | '?' | '&' | '!' | '%' | '~' => out.push(GTok::Op(c)),
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
    /// Whether a grammar over characters is read, and undefined names kept.
    open: bool,
    /// How many groups and lookaheads are open.
    depth: usize,
    /// Whether the alternative holds a `~` mark.
    marked: bool,
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
            Ok(Expr::And(Box::new(self.within(Self::prefix)?)))
        } else if self.eat('!') {
            Ok(Expr::Not(Box::new(self.within(Self::prefix)?)))
        } else if self.eat('~') {
            self.mark()
        } else {
            self.postfix()
        }
    }

    /// Reads with `read` inside a group or a lookahead.
    // Complexity tradeoff: the reader recurses once per group and lookahead open around the
    // place it reads (about six thread-stack frames per level), and the derived `Drop` and
    // `Clone` of [`Expr`] recurse once per level of the expression read, so a grammar line
    // nested thousands deep would overflow the thread stack instead of being read or refused. Every
    // line is written by the spec's author (sec:grammar, read in place),
    // whose deepest nest is a few levels, and the cost stays linear in the line. An explicit
    // stack of open groups, each with its alternatives, items and pending prefixes, would read
    // any depth; a complete solution also needs an iterative `Drop` for [`Expr`] and explicit
    // stacks in the fuzzer's `Depths::of`, `refs` and `Gen::gen_of` (zed-tools), which recurse
    // per level too. Test:
    // `l01_08_parser::grammar_read::a_nest_of_separators_is_read_in_linear_time`; COMPLEXITY.md
    // F88.
    fn within(&mut self, read: fn(&mut Self) -> Result<Expr, String>) -> Result<Expr, String> {
        self.depth += 1;
        let e = read(self);
        self.depth -= 1;
        e
    }

    /// The rule after a `~`.
    fn mark(&mut self) -> Result<Expr, String> {
        if self.depth != 0 {
            return Err("a ~ mark must stand at the top of its alternative".into());
        }
        if self.marked {
            return Err("an alternative holds at most one ~ mark".into());
        }
        self.marked = true;
        let plain = "a ~ mark must be on a plain rule name";
        if !matches!(self.toks.get(self.i), Some(GTok::Name(_))) {
            return Err(plain.into());
        }
        let e = self.primary()?;
        let repeated = matches!(self.toks.get(self.i), Some(GTok::Op('*' | '+' | '?' | '%')));
        if repeated || !matches!(e, Expr::Rule(_) | Expr::Undefined(_)) {
            return Err(plain.into());
        }
        Ok(e)
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
                Expr::Sep(Box::new([self.primary()?, e]))
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
            GTok::Class(ranges) if self.open => Ok(Expr::Class(ranges)),
            GTok::Class(_) => Err("a character class in a grammar over tokens".into()),
            GTok::Name(n) => match (self.index.get(&n), n.as_str(), self.open) {
                (Some(&r), _, _) => Ok(Expr::Rule(r)),
                (None, "ANY", true) => Ok(Expr::Any),
                (None, _, true) => Ok(kind(&n).unwrap_or(Expr::Undefined(n))),
                (None, _, false) => kind(&n).ok_or(format!("the rule {n} is not defined")),
            },
            GTok::Wrap(w) => {
                let e = Box::new(self.within(Self::choice)?);
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
                let e = self.within(Self::choice)?;
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

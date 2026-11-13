//! The builder of a syntax tree (`super`) and the steps every form's builder reads: the span,
//! words and children of a parse-tree node, the result a child built to, and the parts written
//! the same way in expressions, statements, types and patterns (arguments, a name written
//! once, a range's end, a literal). The forms' own steps are in the files above this one
//! (`super`, `super::stmts`, `super::types`, `super::body`, `super::neglit`), each file's
//! steps below the files that call them, since Zed forbids a cycle between files
//! (ZED_PORT_GAPS.md gap 10).

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use super::{Error, Expr, ExprKind, Note, Pattern, RangeEnd, Stmt, StmtKind, StrPart, Type};
use crate::lex::{Part, Span, Tok, Token};
use crate::parse::Tree;
use zedc_base::rejection::{Row, not_yet};

/// A tree to build from: a text's, or a string hole's.
pub(super) struct Level<'t> {
    pub(super) tokens: &'t [Token],
    pub(super) tree: &'t Tree,
    /// Where its own holes start in the list of all holes.
    pub(super) first: usize,
}

/// What a node of a parse tree builds to.
pub(super) enum Built {
    Expr(Expr),
    Type(Type),
    Pattern(Pattern),
    Stmt(Box<Stmt>),
}

/// The cache [`Builder::written_bare`] reads, one per source.
// Complexity tradeoff (COMPLEXITY.md F60): listing the names written bare again at each
// rejected chain costs O(chains · source) (59.7 times for 8 times the size, per the row); the
// list made once per source on the first rejection, in one pass, makes each word of a chain one
// hash lookup, for one set of the source's names held while the builder runs.
pub(super) type Bare<'a> = std::cell::OnceCell<std::collections::HashSet<&'a str>>;

/// The fields of `MainArgs` that `main` reads (DESIGN.md sec:ports, step L1.19), in the
/// struct's order, then the file port `main::files`: what a body built to [`Mains`] records it
/// reads. `main::files` is also the name every function reads the file port by.
pub const MAIN_INPUTS: [&str; 4] = ["args", "stdin", "env", "main::files"];

/// The fields of `MainArgs` that `main` pushes to, in the struct's order.
pub const MAIN_OUTPUTS: [&str; 2] = ["stdout", "stderr"];

/// The `main` functions of a text, each with the text of its body, the name of its parameter
/// when it has one written, and the fields of `MainArgs` its body reads and pushes to. The
/// builder rewrites a read `m.stdin` in such a body to the name `m.stdin`, a push `m.stdout <-
/// e` to a push to the port `m.stdout`, and the read `main::files` to the name `main::files`,
/// each a name no source spells, and makes the parameters and ports of the old header from what
/// was read and pushed: the rest of the compiler runs `main` with a parameter for each input it
/// reads and a port for each output it pushes to, and a field that is never read is never
/// opened. A read of `main::files` in another function of the text (QUESTIONS A68) opens the
/// file port too, so `main` of the text's top level takes it as a parameter, as if its body read
/// it: the port is the program's whichever function reads it.
/// A string hole is a tree of its own, built before the text around it, so the table is made
/// from the text's tree before any builder runs, and found by the place a form starts.
pub(super) struct Mains {
    /// By the start of the body's text; bodies nest only when a `main` is declared inside
    /// another's body.
    list: Vec<MainBody>,
    /// For each body of `list`, the body that holds it, by its place in `list`.
    outer: Vec<Option<usize>>,
    /// Where `main::files` is first read outside every body of `list`.
    outside: std::cell::Cell<Option<Span>>,
}

/// A `main`'s body in [`Mains`].
pub(super) struct MainBody {
    /// The text of the body.
    pub(super) body: Span,
    /// The name of its one parameter, `m` in `main(m: MainArgs)`, when it has one written.
    pub(super) param: Option<String>,
    /// Where each of [`MAIN_INPUTS`] is first read, and each of [`MAIN_OUTPUTS`] first pushed
    /// to, in the body.
    pub(super) uses: std::cell::RefCell<FieldUses>,
}

/// Where each input field of `main`'s argument is first read, and each output field first pushed
/// to, in the order of [`MAIN_INPUTS`] and [`MAIN_OUTPUTS`].
pub(super) type FieldUses = ([Option<Span>; 4], [Option<Span>; 2]);

impl Mains {
    /// The `main` functions of the text `tree` is the tree of, at any depth of blocks.
    // Complexity tradeoff: one pass over the tree's nodes, O(n), and a sort of the k mains,
    // O(k log k); finding each form's `main` then costs O(log k) ([`Mains::at`]) instead of a
    // walk up the form's ancestors, O(depth) per form.
    pub(super) fn new(text: &str, tokens: &[Token], tree: &Tree) -> Mains {
        let word = |i: usize| {
            let s = tokens[i].span;
            &text[s.start..s.end]
        };
        let span = |n: usize| Span {
            start: tokens[tree.nodes[n].start].span.start,
            end: tokens[tree.nodes[n].end - 1].span.end,
        };
        let mut list = Vec::new();
        for (n, node) in tree.nodes.iter().enumerate() {
            if tree.name(n) != "Function" || word(node.start) != "main" {
                continue;
            }
            let Some(&body) = node.kids.last() else {
                continue;
            };
            let param = node
                .kids
                .iter()
                .find(|&&k| tree.name(k) == "Params")
                .and_then(|&ps| tree.nodes[ps].kids.first())
                .filter(|&&p| tree.name(p) == "Param")
                .map(|&p| word(tree.nodes[p].start).to_string());
            list.push(MainBody {
                body: span(body),
                param,
                uses: std::cell::RefCell::new(([None; 4], [None; 2])),
            });
        }
        list.sort_by_key(|b| b.body.start);
        // The body that holds each, by a stack of the bodies open at its start: bodies are
        // nested or apart, so O(k) in all.
        let mut outer = Vec::with_capacity(list.len());
        let mut open: Vec<usize> = Vec::new();
        for (i, b) in list.iter().enumerate() {
            while open
                .last()
                .is_some_and(|&o| list[o].body.end <= b.body.start)
            {
                open.pop();
            }
            outer.push(open.last().copied());
            open.push(i);
        }
        let mains = Mains {
            list,
            outer,
            outside: std::cell::Cell::new(None),
        };
        // The tokens of `n` are the one word `main`, in any number of parentheses, `((main))`:
        // a sequence of tokens `(`ᵏ `main` `)`ᵏ parses only as `k` nested `Group`s of the name,
        // which the builder builds to the name. O(k) for `k` parentheses.
        let main_word = |n: usize| {
            let (mut from, mut to) = (tree.nodes[n].start, tree.nodes[n].end);
            while to - from >= 3 && word(from) == "(" && word(to - 1) == ")" {
                (from, to) = (from + 1, to - 1);
            }
            to - from == 1 && word(from) == "main"
        };
        // The reads `main::files` outside every body: a `Postfix` whose operand is the word
        // `main`, in parentheses or not, and whose suffix is `::files`. `fill` builds deeper nodes first, so a
        // function written after `main` can be built after `main`'s header, which must already
        // know of the read. A string hole is a tree of its own, built before the text's, and
        // [`Builder::main_files`] records the reads in it as it builds them.
        // Complexity: one walk of the nodes reached from the root, O(n) for n nodes, plus
        // O(log k) to place each read among k bodies ([`Mains::at`]). The naive method, a
        // walk of the whole text from `main`'s header when it is built, costs O(n) per `main`,
        // O(n k) for k `main`s; this walk is done once, before any builder runs.
        let mut stack = vec![tree.root];
        while let Some(n) = stack.pop() {
            let kids = &tree.nodes[n].kids;
            if let [of, s] = kids[..]
                && tree.name(n) == "Postfix"
                && tree.name(s) == "ReadSuffix"
                && word(tree.nodes[s].end - 1) == "files"
                && main_word(of)
                && mains.at(span(n).start).is_none()
            {
                mains.read_outside(span(n));
            }
            stack.extend_from_slice(kids);
        }
        mains
    }

    /// Records a read of `main::files` at `span`, outside every body.
    pub(super) fn read_outside(&self, span: Span) {
        let mut first = self.outside.get();
        first_use(&mut first, span);
        self.outside.set(first);
    }

    /// Where `main::files` is first read outside every body, when `body` is the body of a
    /// `main` of the text's top level, which runs the program: no other holds the port.
    pub(super) fn outside(&self, body: Span) -> Option<Span> {
        let i = self.list.partition_point(|b| b.body.start < body.start);
        (self.outer.get(i) == Some(&None)).then(|| self.outside.get())?
    }

    /// The innermost `main` whose body holds the text at `at`, if any.
    // Complexity tradeoff: the last body that starts at or before `at`, O(log k), then the
    // bodies that hold it, O(d) for d bodies nested there; a walk back over every earlier
    // body was O(k) for a form that follows k bodies and lies in none of them.
    pub(super) fn at(&self, at: usize) -> Option<&MainBody> {
        let mut i = self
            .list
            .partition_point(|b| b.body.start <= at)
            .checked_sub(1);
        while let Some(j) = i {
            if at < self.list[j].body.end {
                return Some(&self.list[j]);
            }
            i = self.outer[j];
        }
        None
    }

    /// The `main` whose body is the text `body`.
    pub(super) fn of(&self, body: Span) -> Option<&MainBody> {
        let i = self.list.partition_point(|b| b.body.start < body.start);
        self.list.get(i).filter(|b| b.body == body)
    }
}

/// What [`Methods`] records of one method `T.m` of a source.
pub(super) struct MethodInfo {
    /// `T`, the type it is declared on.
    pub(super) receiver: String,
    /// Whether its body writes the next receiver, so that `x*.m(…)` is a call of it (DESIGN.md
    /// sec:tour_methods): a primed target, `n' = …`, `n'[k] = …` or `n' <- e`, or a `*.` call,
    /// outside the loops, functions and methods its body declares.
    pub(super) mutates: bool,
    /// Whether it declares a result type, `-> int`.
    pub(super) result: bool,
}

/// The methods declared in a source, by name, listed on first use: a rejection of a loop
/// variable that a `.` call leaves without an update asks whether the call's method has a `*.`
/// form (`initial`).
// Complexity tradeoff: one walk of the tree from its root lists every method and what its body
// writes, O(n) for a tree of n nodes, made once per source on the first rejection that asks; a
// walk of the source for each `.` call asked about would be O(n) per call.
pub(super) struct Methods<'t> {
    text: &'t str,
    tokens: &'t [Token],
    tree: &'t Tree,
    table: std::cell::OnceCell<HashMap<String, Vec<MethodInfo>>>,
}

impl<'t> Methods<'t> {
    pub(super) fn new(text: &'t str, tokens: &'t [Token], tree: &'t Tree) -> Methods<'t> {
        Methods {
            text,
            tokens,
            tree,
            table: std::cell::OnceCell::new(),
        }
    }

    /// The methods named `name` declared in the source, in no set order.
    pub(super) fn named(&self, name: &str) -> &[MethodInfo] {
        let table = self.table.get_or_init(|| self.list());
        table.get(name).map_or(&[], |v| &v[..])
    }

    fn list(&self) -> HashMap<String, Vec<MethodInfo>> {
        let (text, tokens, tree) = (self.text, self.tokens, self.tree);
        let word = |i: usize| {
            let s = tokens[i].span;
            &text[s.start..s.end]
        };
        let first = |n: usize| word(tree.nodes[n].start);
        let mut table: HashMap<String, Vec<MethodInfo>> = HashMap::new();
        // Each method's entry, by name and place, for the nodes of its body.
        let mut found: Vec<(String, MethodInfo)> = Vec::new();
        // Each node reached from the root once, with the method whose body holds it, if any;
        // the parser's abandoned nodes are not reached.
        let mut stack: Vec<(usize, Option<usize>)> = vec![(tree.root, None)];
        while let Some((n, owner)) = stack.pop() {
            let kids = &tree.nodes[n].kids;
            match tree.name(n) {
                "Method" if kids.len() >= 3 => {
                    let (&body, head) = kids.split_last().expect("a method ends in its body");
                    let result = head.iter().any(|&k| tree.name(k) == "Result");
                    found.push((
                        first(head[1]).to_string(),
                        MethodInfo {
                            receiver: first(head[0]).to_string(),
                            mutates: false,
                            result,
                        },
                    ));
                    stack.push((body, Some(found.len() - 1)));
                    continue;
                }
                "Loop" | "Function" | "Method" => {
                    stack.extend(kids.iter().map(|&k| (k, None)));
                    continue;
                }
                "Target" | "IndexedDef" | "WholePush" if first(n).ends_with('\'') => {
                    if let Some(m) = owner {
                        found[m].1.mutates = true;
                    }
                }
                "SpreadSuffix" => {
                    if let Some(m) = owner {
                        found[m].1.mutates = true;
                    }
                }
                _ => {}
            }
            stack.extend(kids.iter().map(|&k| (k, owner)));
        }
        for (name, info) in found {
            table.entry(name).or_default().push(info);
        }
        table
    }
}

/// The builder of one tree, a text's or a string hole's: what each node built to, until its
/// parent takes it.
pub(super) struct Builder<'a, 's: 'a> {
    pub(super) text: &'s str,
    pub(super) tokens: &'a [Token],
    pub(super) tree: &'a Tree,
    /// For each token, the index in `tree.holes` of its first hole.
    holes: Vec<usize>,
    /// The built holes of every level, and where this level's start.
    done: &'a mut [Option<Result<Expr, Error>>],
    first: usize,
    /// What the nodes built to, until their parents take them: those after `front` in the walk
    /// of `fill`, the latest at the front. What is taken leaves from the back, so this holds
    /// about one width of the tree, and the depth of a tree costs no stack. An error is a
    /// result like any other: the parent takes its children in written order, so the first
    /// error is the first in written order.
    pub(super) live: VecDeque<Option<Result<Built, Error>>>,
    /// Where in the walk of `fill` each node is, and where the walk has reached.
    pub(super) place: Vec<usize>,
    pub(super) front: usize,
    /// The names written in the source other than after a `.`, listed on first use.
    pub(super) bare: &'a Bare<'s>,
    /// The `main` functions of the text this tree is in.
    pub(super) mains: &'a Mains,
    /// The names written in the text only as the qualifier of an imported unit
    /// ([`super::initial::qualifiers`]).
    pub(super) qualifiers: &'a std::collections::HashSet<&'s str>,
    /// The methods declared in the text this tree is in.
    pub(super) methods: &'a Methods<'a>,
    /// The parent of each node of the tree, listed on the first rejection that names one.
    pub(super) parents: std::cell::OnceCell<Vec<usize>>,
    /// The text of each expression that is a whole argument of a call, listed on the first
    /// use of an output of `main` ([`Builder::passed`]).
    pub(super) args: std::cell::OnceCell<HashMap<Span, Span>>,
}

impl<'a, 's> Builder<'a, 's> {
    /// The name `p` when `of` is the name of the parameter of the `main` whose body holds it,
    /// `m` in `main(m: MainArgs)`.
    pub(super) fn main_param(&self, of: &Expr) -> Option<&'a str> {
        let ExprKind::Name(n) = &of.kind else {
            return None;
        };
        let main = self.mains.at(of.span.start)?;
        main.param.as_deref().filter(|p| p == n)
    }

    /// The read `of.field`, at `span`, of the parameter `of` of the `main` whose body holds it:
    /// the name of the field's input, recorded as read ([`Mains`]); the name of an output passed
    /// whole as an argument of a call, recorded as pushed to; or why it cannot be read, when the
    /// field is an output read otherwise or `MainArgs` has no such field.
    pub(super) fn main_field(&self, of: Expr, field: &str, span: Span) -> Result<Expr, Error> {
        let m = self.main_param(&of).expect("a read of main's parameter");
        let error = |message: String| Error {
            row: None,
            menu: String::new(),
            span,
            message,
            notes: Vec::new(),
        };
        match field {
            "args" | "stdin" | "env" => Ok(self.main_use(field, span)),
            // Passed whole to a parameter, the output is given to the function called, which
            // pushes to it, and `main` declares it as it declares an output it pushes to. The
            // port is declared at its first use, the whole argument, which is also the text a
            // group around the name gives it.
            "stdout" | "stderr" if let Some(whole) = self.passed(span) => {
                let main = self.mains.at(span.start).expect("a use inside main's body");
                first_use(
                    &mut main.uses.borrow_mut().1[(field == "stderr") as usize],
                    whole,
                );
                Ok(Expr {
                    kind: ExprKind::Name(format!("{m}.{field}")),
                    span: whole,
                })
            }
            "stdout" | "stderr" => Err(error(format!(
                "`{m}.{field}` is read here, and `{m}.{field}` is an output of the program: \
                 `main` writes lines to it with a push, as `{m}.{field} <- lines;`, and never \
                 reads it. To read the program's input, read `{m}.stdin` (its standard input), \
                 `{m}.args` (the words after `--` on the command line) or `{m}.env` (its \
                 environment variables); to use lines this program computes, read them from \
                 the binding that holds them before it pushes them."
            ))),
            _ => Err(error(format!(
                "`{m}.{field}` is read here, and `{m}` is the argument of `main`, of type \
                 `MainArgs`, which has no field `{field}`. Its fields are `args` (the words \
                 after `--` on the command line), `stdin` (the lines of standard input), \
                 `stdout` and `stderr` (the lines the program writes) and `env` (the \
                 environment variables, by name). Read one of `{m}.args`, `{m}.stdin` or \
                 `{m}.env`; files are read with `main::files`."
            ))),
        }
    }

    /// The read `main::files` at `span` (DESIGN.md sec:ports, QUESTIONS A68): in `main`'s body,
    /// the use of its file port ([`Builder::main_use`]); in any other function, the name
    /// `main::files`, which names the program's file port there, recorded as read outside
    /// `main` so that `main` opens the port. In a text that declares no `main`, a library, the
    /// name is the same and names the program's entry point (QUESTIONS Q54): a test table's
    /// clause `test with main::files = e` gives it to a row, and the program that imports the
    /// library gives it under the grant `port(Files)`, which this zedc does not check yet.
    pub(super) fn main_files(&self, span: Span) -> Expr {
        if self.mains.at(span.start).is_some() {
            return self.main_use("main::files", span);
        }
        self.mains.read_outside(span);
        Expr {
            kind: ExprKind::Name("main::files".into()),
            span,
        }
    }

    /// The name of the input `use_` of the `main` whose body holds `span` (one of
    /// [`MAIN_INPUTS`]), recorded as read there: `m.stdin` for `stdin`, and `main::files` for
    /// `main::files`.
    pub(super) fn main_use(&self, use_: &str, span: Span) -> Expr {
        let main = self.mains.at(span.start).expect("a use inside main's body");
        let i = MAIN_INPUTS
            .iter()
            .position(|u| *u == use_)
            .expect("an input");
        first_use(&mut main.uses.borrow_mut().0[i], span);
        let name = match (use_, &main.param) {
            ("main::files", _) | (_, None) => use_.to_string(),
            (_, Some(m)) => format!("{m}.{use_}"),
        };
        Expr {
            kind: ExprKind::Name(name),
            span,
        }
    }

    /// The port the push target node `t`, `PushTarget = Name ('.' Name)* ('::' Name)?`,
    /// names: the name itself, or `m.stdout` and `m.stderr` for the parameter `m` of the
    /// `main` whose body holds it, recorded as pushed to ([`Mains`]); or why the target
    /// cannot be pushed to. A target ending in a view (`m.stdout::bytes`, DESIGN step L7.3h)
    /// is not compiled yet. The tokens alternate a name and a separator, `.` or `::`, and the
    /// grammar allows `::` only before the last name.
    pub(super) fn push_target(&self, t: usize) -> Result<String, Error> {
        let node = &self.tree.nodes[t];
        if node.end - node.start > 1 && self.word(node.end - 2) == "::" {
            return Err(self.later_as(t, "a push to a view of a port"));
        }
        let names: Vec<&str> = (node.start..node.end)
            .step_by(2)
            .map(|i| self.word(i))
            .collect();
        let span = self.span(t);
        let main = self.mains.at(span.start);
        let m = main.and_then(|b| b.param.as_deref());
        match names[..] {
            [name] => Ok(name.into()),
            [p, field] if Some(p) == m => {
                let error = |message: String| Error {
                    row: None,
                    menu: String::new(),
                    span,
                    message,
                    notes: Vec::new(),
                };
                match field {
                    "stdout" | "stderr" => {
                        let main = main.expect("m is main's parameter");
                        let i = (field == "stderr") as usize;
                        first_use(&mut main.uses.borrow_mut().1[i], span);
                        Ok(format!("{p}.{field}"))
                    }
                    "stdin" | "args" | "env" => Err(error(format!(
                        "`{p}.{field} <- …` pushes to `{p}.{field}`, and `{p}.{field}` is an \
                         input of the program, which `main` reads and never writes. Push the \
                         lines the program writes to `{p}.stdout` (its standard output) or \
                         `{p}.stderr` (its standard error), as `{p}.stdout <- lines;`."
                    ))),
                    _ => Err(error(format!(
                        "`{p}.{field} <- …` pushes to `{p}.{field}`, and `{p}` is the argument \
                         of `main`, of type `MainArgs`, which has no field `{field}`. The \
                         program writes lines with a push to `{p}.stdout` (its standard \
                         output) or `{p}.stderr` (its standard error), as `{p}.stdout <- \
                         lines;`."
                    ))),
                }
            }
            _ => Err(self.later_as(t, "a push to a field of a value")),
        }
    }
    pub(super) fn new(
        text: &'s str,
        level: &Level<'a>,
        done: &'a mut [Option<Result<Expr, Error>>],
        bare: &'a Bare<'s>,
        mains: &'a Mains,
        qualifiers: &'a std::collections::HashSet<&'s str>,
        methods: &'a Methods<'a>,
    ) -> Builder<'a, 's> {
        let mut holes = Vec::with_capacity(level.tokens.len());
        let mut count = 0;
        for (j, t) in level.tokens.iter().enumerate() {
            holes.push(count);
            // A skipped declaration's holes have no tree (`Tree::skipped`).
            if let Tok::Str(parts) = &t.tok
                && !level.tree.skips(j)
            {
                count += parts
                    .iter()
                    .filter(|p| matches!(p, Part::Hole { .. }))
                    .count();
            }
        }
        Builder {
            text,
            tokens: level.tokens,
            tree: level.tree,
            holes,
            done,
            first: level.first,
            live: VecDeque::new(),
            place: Vec::new(),
            front: 0,
            bare,
            mains,
            qualifiers,
            methods,
            parents: std::cell::OnceCell::new(),
            args: std::cell::OnceCell::new(),
        }
    }

    /// The parent of node `n`, `None` for the root. The parents are listed on the first call.
    pub(super) fn parent(&self, n: usize) -> Option<usize> {
        let tree = self.tree;
        let parents = self.parents.get_or_init(|| {
            // One walk from the root lists each node's parent; the parser's abandoned nodes are
            // not reached, so none of them is taken for a parent.
            let mut parents = vec![usize::MAX; tree.nodes.len()];
            let mut stack = vec![tree.root];
            while let Some(k) = stack.pop() {
                for &c in &tree.nodes[k].kids {
                    parents[c] = k;
                    stack.push(c);
                }
            }
            parents
        });
        parents.get(n).copied().filter(|&p| p != usize::MAX)
    }

    /// The text of the whole argument of a call that the expression written at `span` is, as
    /// `m.stdout` in `f(m.stdout)`, `f(out: m.stdout)` or `f(out: (m.stdout))`: where an output
    /// of `main` is passed to a parameter, which the checker decides is an output port
    /// (DESIGN.md L1.19), and not read. `None` when it is no whole argument.
    // Complexity tradeoff: the naive test walks up from the expression's node to its
    // parent, but the builder knows the expression by its text only; listing the arguments
    // once, on the first use of an output, costs one walk of the tree, O(nodes), and O(1) per
    // test after, where a search for the node by its text would cost O(nodes) per use.
    pub(super) fn passed(&self, span: Span) -> Option<Span> {
        let tree = self.tree;
        let args = self.args.get_or_init(|| {
            // A walk from the root, as in [`Builder::parent`], reaches no abandoned node.
            let mut args = HashMap::new();
            let mut stack = vec![tree.root];
            while let Some(k) = stack.pop() {
                let kids = &tree.nodes[k].kids;
                if let ("PlainArg", [v]) | ("NamedArg", [_, v]) = (tree.name(k), &kids[..]) {
                    // Grouping parentheses only shape parsing, so `f((m.stdout))` passes
                    // `m.stdout` whole; a node with one child of its own text is a step of
                    // the grammar's chain of precedence levels, which the walk passes through.
                    let mut inner = *v;
                    while let [c] = tree.nodes[inner].kids[..] {
                        if tree.name(inner) != "Group" && self.span(c) != self.span(inner) {
                            break;
                        }
                        inner = c;
                    }
                    args.insert(self.span(inner), self.span(*v));
                }
                stack.extend(kids);
            }
            args
        });
        args.get(&span).copied()
    }

    pub(super) fn span(&self, n: usize) -> Span {
        let node = &self.tree.nodes[n];
        Span {
            start: self.tokens[node.start].span.start,
            end: self.tokens[node.end - 1].span.end,
        }
    }

    pub(super) fn word(&self, i: usize) -> &'a str {
        let s = self.tokens[i].span;
        &self.text[s.start..s.end]
    }

    pub(super) fn kids(&self, n: usize) -> &'a [usize] {
        &self.tree.nodes[n].kids
    }

    /// The error for node `n`, a form this zedc parses and does not compile yet. The message
    /// names the kind of form in plain words ([`kind_of`]) and quotes its first line, cut at
    /// 60 characters, since a form may be a whole block.
    pub(super) fn later(&self, n: usize) -> Error {
        self.later_as(n, kind_of(self.tree.name(n)))
    }

    /// [`Builder::later`] for node `n`, with the kind of form named `kind` where the node's name
    /// alone does not tell it (a `StructField` that is a law member).
    pub(super) fn later_as(&self, n: usize, kind: &str) -> Error {
        let s = self.span(n);
        let line = self.text[s.start..s.end]
            .lines()
            .next()
            .unwrap_or("")
            .trim_end();
        let quoted = match line.char_indices().nth(60) {
            Some((cut, _)) => format!("{}…", &line[..cut]),
            None if line.len() < s.end - s.start => format!("{line} …"),
            None => line.into(),
        };
        Error {
            row: None,
            menu: String::new(),
            span: s,
            message: not_yet(&format!("{kind} `{quoted}`")),
            notes: Vec::new(),
        }
    }

    /// The expression node `n` built to.
    pub(super) fn node(&mut self, n: usize) -> Result<Expr, Error> {
        let e = self.body(n)?;
        if let ExprKind::Block(stmts) = &e.kind
            && self.tree.name(n) == "Block"
            && !matches!(
                stmts.last(),
                Some(Stmt {
                    kind: StmtKind::Return(_),
                    ..
                })
            )
        {
            // Only a brace in body position, after `->`, `else`, or an `if` or `for` head, makes
            // an empty block; elsewhere `{}` is the empty family (sec:lexical), which is what a
            // writer of `{}` there most likely meant.
            let message = if stmts.is_empty() {
                "this `{}` is an empty block, and a block gives a value, so it must export one: a brace \
                 after `->`, `else`, or the head of an `if` or a `for` is a block. To write the empty \
                 family there, write `{ {} }`, or `({})` after `->` or a fallback's `else`."
            } else {
                "this block exports nothing, and a block gives a value, so it must export one. End it \
                 with an expression, or with `return e;` to give the value `e`."
            };
            return Err(Error {
                row: None,
                menu: String::new(),
                span: e.span,
                message: message.into(),
                notes: Vec::new(),
            });
        }
        Ok(e)
    }

    /// What node `n` built to.
    pub(super) fn take(&mut self, n: usize) -> Option<Result<Built, Error>> {
        let i = self.place[n].checked_sub(self.front)?;
        self.live.get_mut(i)?.take()
    }

    /// The expression node `n` built to, which may be a block that exports nothing.
    pub(super) fn body(&mut self, n: usize) -> Result<Expr, Error> {
        match self.take(n) {
            Some(Ok(Built::Expr(e))) => Ok(e),
            Some(Err(e)) => Err(e),
            None if self.tree.name(n) == "Name" => Ok(Expr {
                kind: ExprKind::Name(self.word(self.tree.nodes[n].start).into()),
                span: self.span(n),
            }),
            Some(Ok(Built::Type(_) | Built::Pattern(_) | Built::Stmt(_))) | None => {
                Err(self.later(n))
            }
        }
    }

    /// The operator token at `i`, as the lexer's static text.
    pub(super) fn op(&self, i: usize) -> &'static str {
        match self.tokens[i].tok {
            Tok::Op(o) | Tok::Keyword(o) => o,
            _ => unreachable!("an operator token"),
        }
    }

    /// The end of a range whose operator is token `op`, its bound node `bound` built by `f`.
    pub(super) fn range_end<T>(
        &mut self,
        op: usize,
        bound: Option<usize>,
        f: impl FnOnce(&mut Self, usize) -> Result<T, Error>,
    ) -> Result<RangeEnd<T>, Error> {
        Ok(match (self.word(op), bound) {
            ("..<", Some(b)) => RangeEnd::Below(f(self, b)?),
            ("..=", Some(b)) => RangeEnd::Through(f(self, b)?),
            ("..", None) => RangeEnd::Open,
            _ => unreachable!("RangeTail = '..<' Additive | '..=' Additive | '..'"),
        })
    }

    /// Records the `what` named `name`, written at node `n`, in `seen`, or the error that it
    /// is `done` twice, with a note at the first.
    pub(super) fn once(
        &self,
        seen: &mut HashMap<&'a str, Span>,
        name: &'a str,
        n: usize,
        what: &str,
        done: &str,
    ) -> Result<(), Error> {
        let span = self.span(n);
        if let Some(&first) = seen.get(name) {
            return Err(Error {
                row: None,
                menu: String::new(),
                span,
                message: format!(
                    "the {what} `{name}` is {done} twice, and each {what} is {done} once. Remove \
                     one of the two."
                ),
                notes: vec![Note {
                    span: first,
                    text: format!("the first {what} `{name}`"),
                }],
            });
        }
        seen.insert(name, span);
        Ok(())
    }

    /// The arguments of node `n`, an `Args`, of the call or annotation written at `call`. The
    /// grammar takes them in any order; a positional one after a named one is the row "Named
    /// argument before a positional one".
    #[allow(clippy::type_complexity)]
    pub(super) fn args(
        &mut self,
        n: usize,
        call: Span,
    ) -> Result<(Vec<Expr>, Vec<(String, Expr)>, bool), Error> {
        let node = &self.tree.nodes[n];
        let curry = self.word(node.end - 1) == "...";
        let (mut positional, mut named) = (Vec::new(), Vec::new());
        let mut seen: HashMap<&str, Span> = HashMap::new();
        let mut first_named: Option<(&str, Span)> = None;
        for &k in &node.kids {
            let kids = self.kids(k);
            let rule = self.tree.name(k);
            if let (Some((word, at)), "PlainArg" | "SortArg") = (first_named, rule) {
                return Err(Error {
                    row: Some(Row::NamedBeforePositional),
                    menu: String::new(),
                    span: self.span(k),
                    message: format!(
                        "this positional argument comes after the named argument `{word}`, and a \
                         call passes its positional arguments first, then its named ones."
                    ),
                    notes: vec![
                        Note {
                            span: at,
                            text: format!("the first named argument, `{word}`"),
                        },
                        Note {
                            span: call,
                            text: "the call".into(),
                        },
                        Note {
                            span: self.span(k),
                            text: format!(
                                "repair: pass this argument before `{word}`, the positional \
                                 arguments first"
                            ),
                        },
                    ],
                });
            }
            match rule {
                "PlainArg" => {
                    positional.push(self.node(kids[0])?);
                    continue;
                }
                "SortArg" => {
                    positional.push(Expr {
                        kind: ExprKind::SortKey {
                            desc: self.word(self.tree.nodes[k].start) == "desc",
                            key: match kids.first() {
                                Some(&key) => Some(Box::new(self.node(key)?)),
                                None => None,
                            },
                        },
                        span: self.span(k),
                    });
                    continue;
                }
                _ => {}
            }
            let span = self.span(kids[0]);
            let word = self.word(self.tree.nodes[kids[0]].start);
            if let Some(first) = seen.get(word) {
                return Err(Error {
                    row: None,
                    menu: String::new(),
                    span,
                    message: format!(
                        "the argument `{word}` is named twice in this call, and a call names \
                         each argument once. Remove one of the two."
                    ),
                    notes: vec![Note {
                        span: *first,
                        text: format!("the first argument named `{word}`"),
                    }],
                });
            }
            seen.insert(word, span);
            first_named.get_or_insert((word, span));
            let value = match kids {
                [_, v] => self.node(*v)?,
                _ => self.node(kids[0])?,
            };
            named.push((word.to_string(), value));
        }
        Ok((positional, named, curry))
    }

    /// The literal of token `i`, written in `span`, which holds its grouping parentheses.
    pub(super) fn literal_at(&mut self, i: usize, span: Span) -> Result<Expr, Error> {
        let kind = match &self.tokens[i].tok {
            Tok::Int { radix, digits } => ExprKind::Int {
                radix: *radix,
                digits: Arc::clone(digits),
            },
            Tok::Float { digits, forced } => ExprKind::Float {
                digits: Arc::clone(digits),
                forced: *forced,
            },
            Tok::Rat(s) => ExprKind::Rat(Arc::clone(s)),
            Tok::Keyword(k) => ExprKind::Bool(*k == "true"),
            Tok::Str(parts) => {
                let mut out = Vec::with_capacity(parts.len());
                let mut hole = self.first + self.holes[i];
                for p in parts {
                    out.push(match p {
                        Part::Text(t) => StrPart::Text(Arc::clone(t)),
                        Part::Hole { .. } => {
                            let e = self.done[hole].take();
                            hole += 1;
                            StrPart::Hole(e.expect("a hole's expression is taken once")?)
                        }
                    });
                }
                ExprKind::Str(out)
            }
            _ => unreachable!("Literal = INT | FLOAT | RAT | STRING | 'true' | 'false'"),
        };
        Ok(Expr { kind, span })
    }
}

/// The kind of form the grammar rule `rule` reads, in plain words, for the message of a form
/// this zedc does not compile yet; `the form` for a rule with no plainer name.
fn kind_of(rule: &str) -> &'static str {
    match rule {
        "ReduceTail" => "the reduction",
        "ReducePolicy" => "the reduction order",
        "TypeSuffix" => "the refinement",
        "Result" => "the declared result type",
        "Law" => "the law",
        "TypeFacet" => "the facet",
        "Interface" => "the interface",
        "Signature" => "the signature",
        "TypedBinding" => "the binding with a declared type",
        "InferType" => "the wildcard type",
        "FieldType" => "the named type",
        "Struct" => "the struct declaration",
        "TypeParams" => "the struct's type parameter list",
        "StructField" => "the struct field",
        "MoreGen" => "the inner generator",
        "KeyedPush" => "the push at a key",
        "LitType" => "the literal type",
        "ArrayType" => "the array type",
        "Update" => "the field update",
        "AnnotExpr" => "the annotated expression",
        _ => "the form",
    }
}

/// Records `span` as a use of a field of `main`'s argument, keeping the first in the text:
/// the field's parameter or port is placed there, and a use before it would read as a use
/// above its definition. The builder does not build the uses in text order, so the earliest
/// is kept, not the first built.
fn first_use(slot: &mut Option<Span>, span: Span) {
    *slot = Some(slot.map_or(span, |s| s.min(span)));
}
